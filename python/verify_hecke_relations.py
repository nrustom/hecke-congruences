"""Call the native relation verifier from Sage, using existing source loaders.

Only the prepared cyclic orders and ordinary Hecke matrices cross the process
boundary. No Smith computation, global p-division or pickle loading is done
here. The native executable handles the polynomial's presentation by linear
equations, including division relations and the terminal equation y=p^b*rho.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import selectors
import tempfile
import time
import signal
from multiprocessing import get_context
from queue import Empty
from collections import OrderedDict

from sage.all import ZZ, Integer, Integers
from identity_verification import _hecke_matrix_on_source


def _json_integer(value):
    """Encode Sage notebook integers without silently coercing other objects."""
    if isinstance(value, Integer):
        return int(value)
    raise TypeError(f"not JSON serializable: {type(value).__name__}")


def _recursive_archived_sources(config, spec, source_cache=None):
    """Load the root and its Dickson dependencies, with untwisted actions.

    Only compact recursive Manin archives use the reconstructed coordinate
    convention. An arbitrary Smith basis or an ideal archive is not accepted.
    These are trusted producer outputs, not an independent Manin/Hecke replay.
    """
    from load_source_data import load_source_data

    p, m = int(config['prime']), int(config['exponent'])
    a, b = p**m*(p-1), p**(m-1)*(p+1)
    directory = Path(config['archive_directory']).resolve()
    seen, records = set(), []

    def visit(d, q):
        """Collect the archived source and all required recursive lower sources.

        Reuse only matching archive records; missing lower orientations do not count as verified inputs.
        """
        key = (d, 0 if p == 2 else q % 2)
        if key in seen:
            return
        seen.add(key)
        path = directory / f'degree_{d}.npz'
        indices = tuple(sorted(set(int(n) for n in spec['hecke_operators'].values())))
        stamp = _archive_stamp(path)
        cache_key = (str(path), stamp, p, m, d, key[1], indices)
        record = source_cache.get(cache_key) if source_cache is not None else None
        if record is not None:
            records.append(record)
            if d >= b and not (p == 2 and m == 1):
                if d >= a:
                    visit(d-a, q)
                visit(d-b, q if p == 2 else (q+1) % (p-1))
            return
        try:
            # The loader's legacy path-only hash cache must not bind a
            # replaced archive to its previous contents on a cache miss.
            from load_source_data import _sha256
            _sha256.cache_clear()
            data = load_source_data(Integers(p**m), d, key[1],
                                    path)
        except ValueError as error:
            if (config.get('allow_missing_lower_orientations', False)
                    and d < b and (d, q) != (int(config['degree']), int(config['orientation']))
                    and str(error) == 'the requested ideal orientation is not stored'):
                return  # Native verifier must use a whole-source fallback.
            raise
        if (data.get('source_metadata', {}).get('construction') != 'recursive'
                or data['source_scope'] != 'manin'):
            raise ValueError('require compact recursive Manin source archives')
        actions = {}
        for n in indices:
            T = data['archived_hecke_matrices'][n]['normalized_matrix']
            actions[str(n)] = [[int(v) for v in row] for row in T.rows()]
        record = {
            'degree': d, 'sign': 0 if p == 2 else (-1)**key[1],
            'exponents': [int(e) for e in data['coordinates']['surviving_exponents']],
            'actions': actions, 'path': data['source_path'],
            'sha256': data['source_sha256'],
            'recursive_maps': data.get('recursive_maps'),
        }
        if _archive_stamp(path) != stamp:
            raise RuntimeError(f'source archive changed while loading: {path}')
        if source_cache is not None:
            source_cache.put(cache_key, record)
        records.append(record)
        if d >= b and not (p == 2 and m == 1):
            if d >= a:
                visit(d-a, q)
            visit(d-b, q if p == 2 else (q+1) % (p-1))

    if config.get('ideal') is not None or config.get('sign') is not None:
        raise ValueError('archive reuse currently requires the default full Manin source')
    visit(int(config['degree']), int(config['orientation']))
    return records


def _archive_stamp(path):
    """Invalidate preparation on replacement or normal in-place modification."""
    st = path.stat()
    return (st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns)


class _SourcePreparationCache:
    """Bounded session cache of converted source records, never proof claims.

    Store serialized records so callers cannot mutate cached matrices. Hits
    avoid NPZ decompression and all Sage matrix construction/conversion.
    Native content hashes and mathematical checks are unchanged.
    """

    def __init__(self, maximum_bytes=64*1024**2):
        """Initialize an empty bounded cache of serialized source records."""
        self.maximum_bytes = int(maximum_bytes)
        if self.maximum_bytes < 0:
            raise ValueError('source cache size must be nonnegative')
        self.entries = OrderedDict()
        self.bytes = self.hits = self.misses = 0

    def get(self, key):
        """Return a fresh decoded copy of a matching cached source, or None on a miss."""
        if key not in self.entries:
            self.misses += 1
            return None
        self.hits += 1
        value = self.entries.pop(key)
        self.entries[key] = value
        return json.loads(value)

    def put(self, key, record):
        """Cache the serialized source if it fits, evicting least-recently used entries within the byte budget."""
        value = json.dumps(record, default=_json_integer, separators=(',', ':')).encode('utf-8')
        if len(value) > self.maximum_bytes:
            return
        if key in self.entries:
            self.bytes -= len(self.entries.pop(key))
        while self.entries and self.bytes + len(value) > self.maximum_bytes:
            _, removed = self.entries.popitem(last=False)
            self.bytes -= len(removed)
        self.entries[key] = value
        self.bytes += len(value)

    def clear(self):
        """Release cached source records without changing any archived files."""
        self.entries.clear()
        self.bytes = 0


def relation_spec(relations, hecke_operators, divisions=None,
                  witness_semantics="independent_monomials",
                  max_howell_dimension=4096):
    """Build a JSON-serializable spec from Sage polynomials in one common ring.

    ``relations`` is [(name, F, terminal_power), ...]. ``hecke_operators``
    maps ordinary variable names to Hecke indices, e.g. {"T": 2, "U": 7}.
    ``divisions`` maps later variable names to (Q, a), meaning Q/p^a.
    Use expanded polynomials, with variable order matching the manuscript's
    displayed composition order. Division numerators use only earlier names.

    The default matches the paper's independent-monomial relation. Selecting
    common_chain instead tests the stronger common-chain presentation.
    The legacy option name ``witness_semantics`` is retained for compatibility.
    A congruence means every input has an output in p^b*M, equivalently full
    domain after composing with D_{1,p^b}; it need not define an endomorphism.
    """
    relations = list(relations)
    if not relations:
        raise ValueError("supply at least one relation")
    ring = relations[0][1].parent()
    names = tuple(ring.variable_names())

    def terms(F):
        """Encode the expanded polynomial with integer coefficient lifts and the prescribed variable order."""
        if F.parent() != ring:
            raise ValueError("all relation and numerator polynomials must share a ring")
        answer = []
        for powers, c in F.dict().items():
            if not isinstance(powers, (tuple, list)) and not hasattr(powers, '__iter__'):
                powers = (powers,)
            answer.append([str(ZZ(c)), [int(e) for e in powers]])
        return answer

    divisions = divisions or {}
    if set(hecke_operators) & set(divisions) or set(hecke_operators) | set(divisions) != set(names):
        raise ValueError("define every variable exactly once")
    return {
        "schema": "hecke.relations.v1",
        "coefficient_modulus": int(ring.base_ring().characteristic()),
        "variables": list(names),
        "hecke_operators": {name: int(n) for name, n in hecke_operators.items()},
        "divisions": [
            {"variable": name, "numerator": terms(divisions[name][0]),
             "power": int(divisions[name][1])}
            for name in names if name in divisions
        ],
        "relations": [
            {"name": str(name), "polynomial": terms(F), "terminal_power": int(b)}
            for name, F, b in relations
        ],
        "witness_semantics": witness_semantics,
        "max_howell_dimension": int(max_howell_dimension),
    }


def verify_hecke_relations_nim(spec, data=None, *, compute=None,
                              executable=None, timeout=None,
                              check_descent=False, session=None,
                              witness_directory=None, witness_mode='produce',
                              witness_solver_limit=None):
    """Verify a batch in Nim on prepared ``data`` or a native ``compute`` spec.

    Prepared data can come from prepare_source_data, load_source_data or
    load_ideal_source_data. Stored matrices are untwisted: apply chi_m(n)^q
    exactly once here (and no twist for p=2). Every intermediate and rho
    remains in the selected source module, including when it is IM.

    Alternatively, omit data and pass compute={prime, exponent, degree,
    orientation, ideal?} to construct the source entirely in Nim.
    Ideal polynomial variables follow the ordinary names in spec[variables].

    Recursive source construction and recursive verification are the default
    below a_m+b_m. Nim verifies the same presentation on lower
    sources in their transfer orientations, checks the transfer maps and
    spanning, then tests only supplement generators. All auxiliary elements
    still belong to the whole selected M or IM. Unsuccessful lower checks
    trigger a whole-target fallback, not an inferred target failure.
    The report includes recursive_trace and checked_input_count. Recursive
    archive requests use compute, not a single prepared data object, because
    the lower sources must also be loaded. Set compute['archive_directory']
    to a directory of compact recursive degree_{d}.npz Manin sources to
    reuse their untwisted Hecke matrices and stored transfer/complement maps.
    For older archives, only missing presentation and transfer maps are
    reconstructed. The producer's deterministic coordinate convention
    is required; cyclic orders and transfer compatibility are checked.
    The matrices remain trusted archived inputs, not independently replayed
    Hecke constructions. Missing sources raise an error, with no fresh-action
    fallback. Set recursive_verification=False
    in compute for a full-source check on recursively constructed data, or
    recursive=False for direct construction and a full-source check. Setting
    recursive=False together with recursive_verification=True is an error.
    The lowest degrees (and p=2,m=1) use direct base cases.

    No compiler or scan is launched implicitly. Build the executable once
    with ./build_verify_hecke_relations.sh. Reports distinguish passed,
    failed and inconclusive. Malformed inputs/process errors raise exceptions;
    none is reported as a mathematical counterexample. A failed common-chain
    test does not rule out independent intermediate elements in the expanded
    polynomial relation. Report names such as explicit_witness_replay are
    retained: they mean replay of the presentation's auxiliary elements.
    Pass a NimRelationVerifier session to reuse successfully checked lower
    presentations between calls. Its in-memory cache is bound to the exact
    presentation and the root/dependency archive contents.
    The session also caches converted source records, invalidating entries
    when file identity, size or modification/change timestamps differ.

    Optional witness_directory saves compressed per-relation division choices.
    In 'produce' mode missing packets are solved, replayed and written atomically;
    existing packets are checked by equation replay. In 'replay' mode missing
    packets raise an error and no witness search is performed. The ordinary
    and recursive transfer/spanning checks are still performed. Packets bind
    the oriented actions, input rows and exact relation specification.
    witness_solver_limit optionally overrides the production resource cap
    without changing that specification or invalidating existing packets.
    """
    if (data is None) == (compute is None):
        raise ValueError("supply exactly one of data and compute")
    if isinstance(spec, (str, Path)):
        spec = json.loads(Path(spec).read_text())
    request = {"relations": spec}
    if witness_directory is not None:
        if witness_mode not in ('produce', 'replay'):
            raise ValueError('witness_mode must be produce or replay')
        request['witness_directory'] = str(Path(witness_directory).resolve())
        request['witness_mode'] = witness_mode
        if witness_solver_limit is not None:
            if int(witness_solver_limit) < 1:
                raise ValueError('witness_solver_limit must be positive')
            request['witness_solver_limit'] = int(witness_solver_limit)
    if compute is not None:
        request["compute"] = dict(compute)
        if 'archive_directory' in compute:
            if not compute.get('recursive', True) or not compute.get('recursive_verification', True):
                raise ValueError('archive_directory requires recursive verification')
            request['compute']['archived_sources'] = _recursive_archived_sources(
                compute, spec, session._source_cache if session is not None else None)
            del request['compute']['archive_directory']
    else:
        p, m, q = int(data['p']), int(data['m']), int(data['q'])
        R = data['coefficient_ring']
        if p == 2 and q != 0:
            raise ValueError("p=2 uses the unsplit source with q=0")
        operators, moduli = {}, None
        for name, n in spec['hecke_operators'].items():
            if not data['coordinates']['surviving_indices']:
                operators[name], moduli = [], []
                continue
            T_data = _hecke_matrix_on_source(ZZ(n), data, check_descent)
            current_moduli = [int(v) for v in T_data['coordinate_moduli']]
            if moduli is not None and moduli != current_moduli:
                raise ValueError("Hecke matrices use different coordinate moduli")
            moduli = current_moduli
            scalar = R(1) if p == 2 else R(n)**(q*p**(m-1))
            T = T_data['normalized_matrix']
            operators[name] = [
                [int(ZZ(scalar*T[i,j])) % moduli[j] for j in range(T.ncols())]
                for i in range(T.nrows())
            ]
        if moduli is None:
            raise ValueError("supply at least one ordinary Hecke variable")
        request['source'] = {
            'schema': 'hecke.mixed-source.v1',
            'prime': p, 'exponent': m,
            'coordinate_moduli': moduli,
            'operators': operators,
            'operators_are_oriented': True,
            'metadata': {
                'degree': int(data['d']), 'orientation': q,
                'sign': None if data['sign'] is None else int(data['sign']),
                'source_scope': data.get('source_scope', 'manin'),
            },
        }
    if session is not None:
        if executable is not None:
            raise ValueError('choose the executable when opening the session')
        return session.verify_request(request, timeout=timeout)
    root = Path(__file__).resolve().parents[1]
    binary = Path(executable) if executable else root/'nim/.verify-hecke-relations-build/verify_hecke_relations'
    if not binary.is_file():
        raise FileNotFoundError(f"Build the native verifier first: {root / 'build_verify_hecke_relations.sh'}")
    environment = os.environ.copy()
    # Sage/Conda may supply FLINT outside the system dynamic-library path.
    library_directory = Path(sys.prefix)/'lib'
    if (library_directory/'libflint.so').exists():
        environment['LD_LIBRARY_PATH'] = str(library_directory) + os.pathsep + environment.get('LD_LIBRARY_PATH', '')
    completed = subprocess.run(
        [str(binary.resolve()), '-'], input=json.dumps(request, default=_json_integer),
        text=True, capture_output=True, timeout=timeout, env=environment,
    )
    try:
        report = json.loads(completed.stdout)
    except ValueError as error:
        raise RuntimeError(f"native verifier exited {completed.returncode}: {completed.stderr[-2000:]}") from error
    if report.get('schema') != 'hecke.relation-verification.v1':
        raise RuntimeError('unexpected native verifier response')
    expected = {'passed': 0, 'failed': 1, 'error': 2, 'inconclusive': 3}
    if completed.returncode != expected.get(report.get('state')) or report.get('state') == 'error':
        raise RuntimeError(report.get('error', f'native verifier exited {completed.returncode}'))
    return report


class NimRelationVerifier:
    """A sequential native session retaining verified recursive lower cases.

    Use as a context manager. Closing or interrupting the context stops its
    single native process; it never launches source-computation workers.
    No reports from disk are accepted as proof-cache entries.
    source_cache_bytes bounds the serialized preparation cache (64 MiB by
    default, zero to disable); closing the session releases it. Nim separately
    bounds its decoded source-matrix cache to 128 MiB of matrix entries.
    """

    def __init__(self, executable=None, source_cache_bytes=64*1024**2,
                 on_progress=None):
        """Start a persistent native verifier process and its bounded source cache.

        The executable must already exist; this constructor does not build or certify it.
        """
        self._source_cache = _SourcePreparationCache(source_cache_bytes)
        self._on_progress = on_progress
        self._output_buffer = b''
        root = Path(__file__).resolve().parents[1]
        binary = Path(executable) if executable else root/'nim/.verify-hecke-relations-build/verify_hecke_relations'
        if not binary.is_file():
            raise FileNotFoundError('run ./build_verify_hecke_relations.sh first')
        environment = os.environ.copy()
        library = Path(sys.prefix)/'lib'
        if (library/'libflint.so').exists():
            environment['LD_LIBRARY_PATH'] = str(library)+os.pathsep+environment.get('LD_LIBRARY_PATH', '')
        self._stderr = tempfile.TemporaryFile(mode='w+t')
        try:
            self._process = subprocess.Popen(
                [str(binary.resolve()), '--server'], stdin=subprocess.PIPE,
                stdout=subprocess.PIPE, stderr=self._stderr, text=True,
                bufsize=1, env=environment,
            )
        except BaseException:
            self._stderr.close()
            raise

    def verify_request(self, request, timeout=None):
        """Check one request; timeout or interruption closes the session."""
        try:
            if self._process.poll() is not None:
                raise RuntimeError('native verifier session is closed')
            if self._on_progress is not None:
                request = dict(request, progress=True)
            self._process.stdin.write(json.dumps(request, default=_json_integer)+'\n')
            self._process.stdin.flush()
            deadline = None if timeout is None else time.monotonic() + timeout
            with selectors.DefaultSelector() as selector:
                selector.register(self._process.stdout, selectors.EVENT_READ)
                while True:
                    while b'\n' not in self._output_buffer:
                        remaining = None if deadline is None else deadline - time.monotonic()
                        if remaining is not None and remaining <= 0:
                            raise TimeoutError('native verification timed out')
                        if not selector.select(remaining):
                            raise TimeoutError('native verification timed out')
                        chunk = os.read(self._process.stdout.fileno(), 65536)
                        if not chunk:
                            self._stderr.seek(0)
                            raise RuntimeError('native verifier exited: '+self._stderr.read()[-2000:])
                        self._output_buffer += chunk
                    line, self._output_buffer = self._output_buffer.split(b'\n', 1)
                    report = json.loads(line)
                    if report.get('schema') != 'hecke.relation-progress.v1':
                        break
                    if self._on_progress is not None:
                        self._on_progress(report)
            if (report.get('schema') != 'hecke.relation-verification.v1'
                    or report.get('state') not in ('passed', 'failed', 'inconclusive')):
                raise RuntimeError(report.get('error', 'unexpected native verifier response'))
            report['source_preparation_cache'] = {
                'hits': self._source_cache.hits,
                'misses': self._source_cache.misses,
                'bytes': self._source_cache.bytes,
                'maximum_bytes': self._source_cache.maximum_bytes,
            }
            return report
        except BaseException:
            self.close()
            raise

    def close(self):
        """Release the native process and its in-memory proof cache."""
        self._source_cache.clear()
        if self._process.poll() is None:
            self._process.terminate()
            try:
                self._process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                self._process.kill()
                self._process.wait()
        for stream in (self._process.stdin, self._process.stdout, self._stderr):
            if not stream.closed:
                stream.close()

    def __enter__(self):
        """Return this verifier session for use in a context manager."""
        return self

    def __exit__(self, *args):
        """Close the verifier process and release its resources on leaving the context."""
        self.close()


def _relation_chain_worker(verify_case, cases, messages, stop, native):
    """Own one persistent session and process its assigned chains in order."""
    from contextlib import nullcontext
    os.setsid()  # The native child belongs to this worker's process group.

    def interrupted(*args):
        """Exit the command-line interface after an interrupt, allowing its cleanup handlers to run."""
        raise SystemExit(0)

    signal.signal(signal.SIGTERM, interrupted)
    try:
        with (NimRelationVerifier(on_progress=lambda event: messages.put(
                ('progress', event))) if native else nullcontext()) as session:
            for d, q in cases:
                if stop.is_set():
                    break
                messages.put(('case_start', {'degree': d, 'orientation': q}))
                try:
                    test = verify_case(d, q, session=session)
                except Exception as error:
                    stop.set()
                    messages.put(('error', {'degree': d, 'orientation': q,
                                            'error': repr(error)}))
                    break
                if test['passed'] is not True:
                    stop.set()
                messages.put(('result', test))
    except Exception as error:
        stop.set()
        messages.put(('error', {'error': repr(error)}))
    finally:
        messages.put(('done', os.getpid()))


def parallel_relation_cases(verify_case, cases, *, dependency_period, workers=4,
                            native=True, on_progress=None):
    """Yield results from persistent, ascending dependency chains (Linux/fork).

    Both Dickson degree shifts must be divisible by dependency_period. All
    orientations and degrees in one residue class stay with the same worker,
    so lower-degree proof caches remain available. Results arrive out of order.
    A failed case stops new scheduling; already active cases may finish.
    Interrupting/closing this iterator stops workers AND their native children.
    """
    workers, dependency_period = int(workers), int(dependency_period)
    if workers < 1 or dependency_period < 1:
        raise ValueError('workers and dependency_period must be positive')
    cases = [(int(d), int(q)) for d, q in cases]
    if len(set(cases)) != len(cases):
        raise ValueError('duplicate verification cases')
    chains = {}
    for case in cases:
        chains.setdefault(case[0] % dependency_period, []).append(case)
    if not chains:
        return
    groups = [[] for _ in range(min(workers, len(chains)))]
    for chain in sorted(chains.values(), key=len, reverse=True):
        min(groups, key=len).extend(chain)
    context = get_context('fork')
    messages, stop = context.Queue(), context.Event()
    processes = []
    try:
        for group in groups:
            process = context.Process(target=_relation_chain_worker,
                args=(verify_case, sorted(group), messages, stop, native))
            process.start()
            processes.append(process)
        done = set()
        errors = []
        while len(done) < len(processes):
            try:
                kind, payload = messages.get(timeout=0.5)
            except Empty:
                crashed = [p for p in processes if p.pid not in done
                           and p.exitcode is not None]
                if crashed:
                    raise RuntimeError('verification worker exited without completing: '
                                       + str([(p.pid, p.exitcode) for p in crashed]))
                continue
            if kind == 'done':
                done.add(payload)
            elif kind == 'result':
                yield payload
            elif kind == 'error':
                errors.append(payload)
                if on_progress is not None:
                    on_progress(dict(payload, stage='error'))
            elif on_progress is not None:
                on_progress(dict(payload, stage='case_start') if kind == 'case_start'
                            else payload)
        if errors:
            raise RuntimeError(f'verification worker errors: {errors}')
    finally:
        stop.set()
        for process in processes:
            if process.is_alive():
                try:
                    os.killpg(process.pid, signal.SIGTERM)
                except ProcessLookupError:
                    process.terminate()
        for process in processes:
            process.join(timeout=5)
            # Also kill surviving native children if their Python owner died.
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            if process.is_alive():
                process.kill()
                process.join()
        messages.close()

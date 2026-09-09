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

from sage.all import ZZ
from identity_verification import _hecke_matrix_on_source


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
                              check_descent=False):
    """Verify a batch in Nim on prepared ``data`` or a native ``compute`` spec.

    Prepared data can come from prepare_source_data, load_source_data or
    load_ideal_source_data. Stored matrices are untwisted: apply chi_m(n)^q
    exactly once here (and no twist for p=2). Every intermediate and rho
    remains in the selected source module, including when it is IM.

    Alternatively, omit data and pass compute={prime, exponent, degree,
    orientation, recursive, ideal?} to construct the source entirely in Nim.
    Ideal polynomial variables follow the ordinary names in spec[variables].

    No compiler or scan is launched implicitly. Build the executable once
    with ./build_verify_hecke_relations.sh. Reports distinguish passed,
    failed and inconclusive. Malformed inputs/process errors raise exceptions;
    none is reported as a mathematical counterexample. A failed common-chain
    test does not rule out independent intermediate elements in the expanded
    polynomial relation. Report names such as explicit_witness_replay are
    retained: they mean replay of the presentation's auxiliary elements.
    """
    if (data is None) == (compute is None):
        raise ValueError("supply exactly one of data and compute")
    if isinstance(spec, (str, Path)):
        spec = json.loads(Path(spec).read_text())
    request = {"relations": spec}
    if compute is not None:
        request["compute"] = compute
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
        [str(binary.resolve()), '-'], input=json.dumps(request),
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

"""Resumable compact full-source scan; run under a process-group supervisor."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import time
import zipfile


def digest(path):
    """Return the content digest used to identify this input file."""
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_json(path, value):
    """Publish a JSON record by replacing the destination only after writing the complete temporary file."""
    temporary = path.with_suffix('.json.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def main():
    """Run the resumable source scan with bounded workers and atomic degree publication.

    This produces source data; it does not test the classification relations.
    """
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--executable', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prime', type=int, required=True)
    parser.add_argument('--exponent', type=int, required=True)
    parser.add_argument('--hecke', required=True)
    parser.add_argument('--degree-modulus', type=int, required=True)
    parser.add_argument('--residues', required=True)
    parser.add_argument('--minimum-degree', type=int, default=0)
    parser.add_argument('--degree-bound', type=int, default=None,
                        help='exclusive upper bound; defaults to the Dickson bound')
    parser.add_argument('--module-cache-dir', type=Path, default=None,
                        help='share optional recursive maps between degree jobs')
    parser.add_argument('--workers', type=int, choices=range(1, 5), default=4)
    parser.add_argument('--orientations', default=None,
                        help='comma-separated orientations; default uses the producer defaults')
    parser.add_argument('--orientation-threshold', type=int, default=None,
                        help='below this degree use --lower-orientations')
    parser.add_argument('--lower-orientations', default=None)
    args = parser.parse_args()
    p, m = args.prime, args.exponent
    if p < 2 or m < 1 or args.degree_modulus < 1:
        parser.error('invalid prime, exponent or degree modulus')
    bound = p**m*(p-1) + p**(m-1)*(p+1)
    if args.degree_bound is not None:
        bound = args.degree_bound
    if not 0 <= args.minimum_degree < bound:
        parser.error('require 0 <= minimum-degree < degree-bound')
    residues = [int(r) for r in args.residues.split(',')]
    orientations = None if args.orientations is None else [int(q) for q in args.orientations.split(',')]
    if orientations is not None and (not orientations or len(set(orientations)) != len(orientations)
                                     or any(q < 0 or q >= p-1 for q in orientations)):
        parser.error('orientations must be distinct integers in 0..p-2')
    lower = None if args.lower_orientations is None else [int(q) for q in args.lower_orientations.split(',')]
    if (args.orientation_threshold is None) != (lower is None):
        parser.error('supply orientation-threshold and lower-orientations together')
    if lower is not None and (args.orientation_threshold < 0 or not lower
                             or len(set(lower)) != len(lower) or any(q < 0 or q >= p-1 for q in lower)):
        parser.error('invalid lower orientations or threshold')
    degrees = [d for d in range(0, bound, 2)
               if d >= args.minimum_degree and d % args.degree_modulus in residues]
    work = args.output.resolve()
    work.mkdir(parents=True, exist_ok=True)
    (work/'logs').mkdir(exist_ok=True)
    configuration = dict(prime=p, exponent=m, hecke_indices=[int(n) for n in args.hecke.split(',')],
                         degrees=degrees, construction='recursive', executable_sha256=digest(args.executable))
    if orientations is not None:
        configuration['orientations'] = orientations
    if lower is not None:
        configuration.update(orientation_threshold=args.orientation_threshold, lower_orientations=lower)
    config_path = work/'configuration.json'
    if config_path.exists() and json.loads(config_path.read_text()) != configuration:
        raise ValueError('existing output has a different configuration; refusing to overwrite')
    write_json(config_path, configuration)
    active, completed, failed = {}, [], []
    started = time.time()
    stopping = False

    def stop(*unused):
        """Request that the controller stop scheduling new degree computations."""
        nonlocal stopping
        stopping = True

    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)

    def status(state):
        """Publish current progress, including active cases and recorded failures."""
        write_json(work/'status.json', dict(
            schema='hecke.full-source-status.v1', state=state, pid=os.getpid(),
            prime=p, exponent=m, hecke_indices=configuration['hecke_indices'],
            working_modulus=p**m, orientations=orientations,
            orientation_threshold=args.orientation_threshold, lower_orientations=lower,
            workers=args.workers, total_degrees=len(degrees), completed_count=len(completed),
            completed_degrees=sorted(completed), active_degrees=sorted(active), failed=failed,
            heartbeat_at=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
            elapsed_seconds=round(time.time()-started, 2),
            archive_bytes=sum((work/f'degree_{d}.npz').stat().st_size for d in completed),
            classification_identities_tested=False))

    pending = []
    for d in degrees:
        target = work/f'degree_{d}.npz'
        record = work/f'degree_{d}.json'
        if target.exists():
            if not record.exists() or json.loads(record.read_text())['sha256'] != digest(target):
                raise ValueError(f'unverified existing archive: {target}')
            completed.append(d)
        else:
            pending.append(d)
    status('running')
    while pending or active:
        if stopping:
            for process, log, partial, began in active.values():
                if process.poll() is None:
                    process.terminate()
        while pending and len(active) < args.workers and not stopping and not failed:
            if shutil.disk_usage(work).free < 4*1024**3:
                failed.append({'error': 'less than 4 GiB free; no new degrees scheduled'})
                break
            d = pending.pop(0)
            partial = work/f'degree_{d}.partial.npz'
            log = (work/'logs'/f'degree_{d}.log').open('a')
            command = [
                str(args.executable.resolve()), '--prime', str(p), '--exponent', str(m),
                '--degree', str(d), '--hecke', args.hecke, '--recursive', '--compact',
                '--output', str(partial)]
            if lower is not None and d < args.orientation_threshold:
                command.extend(['--orientations', args.lower_orientations])
            elif orientations is not None:
                command.extend(['--orientations', args.orientations])
            if args.module_cache_dir is not None:
                args.module_cache_dir.mkdir(parents=True, exist_ok=True)
                command.extend(['--module-cache-dir', str(args.module_cache_dir.resolve())])
            process = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT)
            active[d] = (process, log, partial, time.time())
        for d, (process, log, partial, began) in list(active.items()):
            code = process.poll()
            if code is None:
                continue
            log.close()
            try:
                if code != 0:
                    if not stopping:
                        raise RuntimeError(f'worker exited {code}; see logs/degree_{d}.log')
                else:
                    with zipfile.ZipFile(partial) as bundle:
                        if 'source_data_version.npy' not in bundle.namelist() or bundle.testzip() is not None:
                            raise ValueError('invalid source archive')
                    target = work/f'degree_{d}.npz'
                    if target.exists():
                        raise FileExistsError(target)
                    write_json(work/f'degree_{d}.json', dict(degree=d, sha256=digest(partial),
                               elapsed_seconds=round(time.time()-began, 2)))
                    partial.rename(target)
                    completed.append(d)
            except Exception as error:
                failed.append(dict(degree=d, error=str(error)))
            del active[d]
        status('stopping' if stopping else 'draining_after_failure' if failed else 'running')
        if not active and (failed or stopping):
            break
        if pending or active:
            time.sleep(2)
    status('stopped' if stopping else 'failed' if failed else 'completed')
    return 1 if failed else 0


if __name__ == '__main__':
    raise SystemExit(main())

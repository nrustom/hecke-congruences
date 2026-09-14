"""Bounded production/replay benchmark; uses only the native verifier and archives.

Run after build_verify_hecke_relations.sh. No source data are recomputed.
Packets are retained in verification_data/mod125_compact for the production run.
Each native process has a 3 GiB address-space cap and a five-minute timeout.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
OUTPUT = ROOT / 'verification_data/mod125_compact'
BINARY = ROOT / 'nim/.verify-hecke-relations-build/verify_hecke_relations'
CASES = ((798, 0), (760, 3), (810, 0), (780, 3))


def main():
    """Measure memory use while constructing and replaying the selected relation data."""
    plan = json.loads((ROOT / 'relations/p5_mod125_native.json').read_text())
    directory = OUTPUT / 'benchmarks' / str(time.time_ns())
    directory.mkdir(parents=True)
    env = os.environ.copy()
    env['LD_LIBRARY_PATH'] = '/home/nrustom/.conda/envs/sage/lib'
    env['OMP_NUM_THREADS'] = env['OPENBLAS_NUM_THREADS'] = '1'
    results = []
    for d, q in CASES:
        for mode in ('produce', 'replay'):
            request = {
                'relations': plan['relation_specifications'][str((d+50*q) % 100)],
                'witness_directory': str(OUTPUT / 'packets'), 'witness_mode': mode,
                'witness_solver_limit': 8192,
                'compute': {'prime': 5, 'exponent': 4, 'degree': d, 'orientation': q,
                            'recursive': True, 'recursive_verification': True,
                            'archive_directory': str(ROOT / plan['source_directory']),
                            'allow_missing_lower_orientations': True},
            }
            metrics = directory / f'degree_{d}_q{q}_{mode}.time'
            started = time.monotonic()
            child = subprocess.run(
                ['/usr/bin/time', '-f', '%e %M', '-o', str(metrics),
                 'prlimit', '--as=3221225472', '--cpu=290', str(BINARY), '-'],
                input=json.dumps(request), text=True, capture_output=True,
                env=env, timeout=300,
            )
            report = json.loads(child.stdout)
            (directory / f'degree_{d}_q{q}_{mode}.json').write_text(json.dumps(report, indent=2))
            timing = metrics.read_text().splitlines()[-1].split()
            result = dict(degree=d, orientation=q, mode=mode, exit_code=child.returncode,
                          state=report['state'], elapsed_seconds=time.monotonic()-started,
                          peak_rss_kib=int(timing[-1]),
                          recursive=report.get('recursive_verification'),
                          routes=[r['verification_route'] for r in report.get('relations', [])])
            results.append(result)
            (directory / 'summary.json').write_text(json.dumps(results, indent=2))
            print(json.dumps(result), flush=True)
            if child.returncode or report['state'] != 'passed':
                print(child.stderr, flush=True)
                return 1
    print(f'Benchmark reports: {directory}', flush=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())

"""Bounded old/new native production comparison; no production files are changed."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import time
import hashlib
import signal

ROOT = Path(__file__).resolve().parents[2]


def main():
    """Benchmark local kernel choices for the specified modulo-125 relation cases."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--old', type=Path, default=ROOT / 'nim/.verify-hecke-relations-build/verify_hecke_relations')
    parser.add_argument('--new', type=Path, default=Path('/tmp/mod49-local-verifier'))
    args = parser.parse_args()
    OLD, NEW = args.old.resolve(), args.new.resolve()
    plan = json.loads((ROOT / 'relations/p5_mod125_native.json').read_text())
    output = ROOT / 'verification_data/mod125_compact/benchmarks' / ('local_kernel_' + str(time.time_ns()))
    output.mkdir(parents=True)
    env = dict(os.environ, LD_LIBRARY_PATH='/home/nrustom/.conda/envs/sage/lib',
               OPENBLAS_NUM_THREADS='1', OMP_NUM_THREADS='1')
    summary = {'binary_sha256': {label: hashlib.sha256(binary.read_bytes()).hexdigest()
                                for label, binary in [('old', OLD), ('new', NEW)]},
               'cases': [], 'scope': 'whole archived source; fresh packets; no checkpoints'}
    print('OUTPUT', output, flush=True)
    for d, q in [(810, 0), (1270, 2), (1320, 1)]:
        new_passed = False
        for label, binary, mode in [('old', OLD, 'produce'), ('new', NEW, 'produce'),
                                     ('old_replay_new', OLD, 'replay')]:
            if mode == 'replay' and not new_passed:
                continue
            packet_label = 'new' if mode == 'replay' else label
            request = {'relations': plan['relation_specifications'][str((d + 50*q) % 100)],
                       'witness_directory': str(output / f'{d}_{q}_{packet_label}_packets'),
                       'witness_mode': mode, 'witness_solver_limit': 8192,
                       'witness_memory_limit_mb': 1536,
                       'compute': {'prime': 5, 'exponent': 4, 'degree': d, 'orientation': q,
                                   'recursive': True, 'recursive_verification': False,
                                   'archive_directory': str(ROOT / plan['source_directory']),
                                   'supplementary_archive_directories': [str(ROOT / 'source_data/p5_mod625_lower_minus')],
                                   'allow_missing_lower_orientations': False}}
            metrics = output / f'{d}_{q}_{label}.time'
            start = time.monotonic()
            result = dict(degree=d, orientation=q, variant=label)
            try:
                child = subprocess.Popen(['/usr/bin/time', '-f', '%e %U %S %M', '-o', str(metrics),
                                        'prlimit', '--as=3221225472', '--cpu=100', str(binary), '-'],
                                       stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                       text=True, env=env, start_new_session=True)
                stdout, stderr = child.communicate(json.dumps(request), timeout=110)
                result['exit_code'] = child.returncode
                (output / f'{d}_{q}_{label}.json').write_text(stdout)
                (output / f'{d}_{q}_{label}.stderr').write_text(stderr)
                report = json.loads(stdout)
                result.update(exit_code=child.returncode, state=report.get('state'),
                              relations=[{k: r.get(k) for k in ('name', 'elapsed_seconds', 'verification_route')}
                                         for r in report.get('relations', [])])
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGKILL)
                child.communicate()
                result['state'] = 'timeout'
            except KeyboardInterrupt:
                os.killpg(child.pid, signal.SIGKILL)
                child.communicate()
                raise
            except (ValueError, OSError) as error:
                timing_text = metrics.read_text() if metrics.exists() else ''
                fields = timing_text.splitlines()[-1].split() if timing_text else []
                cpu_limited = ('signal 24' in timing_text or
                               ('signal 9' in timing_text and len(fields) == 4 and
                                float(fields[1]) + float(fields[2]) >= 99))
                result.update(state='cpu_limit' if cpu_limited else 'error', error=str(error))
            result['wall_seconds'] = time.monotonic() - start
            if metrics.exists():
                fields = metrics.read_text().splitlines()[-1].split()
                if len(fields) == 4:
                    result.update(cpu_seconds=float(fields[1])+float(fields[2]), peak_rss_kib=int(fields[3]))
            summary['cases'].append(result)
            if label == 'new':
                new_passed = result['state'] == 'passed'
            (output / 'summary.json').write_text(json.dumps(summary, indent=2))
            print(json.dumps(result), flush=True)
    print('SAVED', output / 'summary.json', flush=True)


if __name__ == '__main__':
    main()

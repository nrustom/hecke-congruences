"""Verify and replay the supplementary lower minus sources as they arrive."""
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'source_data/p5_mod625_lower_minus'
OUT = ROOT / 'verification_data/mod125_lower_minus'
BINARY = ROOT / 'nim/.verify-hecke-relations-build/verify_hecke_relations_watchdog'


def main():
    """Produce and replay the additional low-degree minus-source relations required for recursion."""
    OUT.mkdir(exist_ok=True)
    reports = OUT / 'reports'
    reports.mkdir(exist_ok=True)
    plan = json.loads((ROOT / 'relations/p5_mod125_native.json').read_text())
    status = {'state': 'running', 'completed_count': 0, 'total_cases': 752,
              'active': None, 'failed': [], 'workers': 1}

    def publish(**changes):
        """Update the progress record and its observation time.

        This records execution status, not a new mathematical verification.
        """
        status.update(changes)
        status['heartbeat_at'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
        tmp = OUT / 'status.tmp'
        tmp.write_text(json.dumps(status, indent=2)+'\n')
        tmp.replace(OUT / 'status.json')

    try:
        for degree in range(0, 752, 2):
            archive = SOURCE / f'degree_{degree}.npz'
            while not archive.exists():
                publish(state='waiting_for_source', active={'degree': degree})
                if (SOURCE / 'status.json').exists():
                    source_status = json.loads((SOURCE / 'status.json').read_text())
                    if source_status.get('failed') or source_status.get('state') in ('failed', 'stopped'):
                        raise RuntimeError('source producer stopped before required archive was available')
                time.sleep(10)
            for orientation in (1, 3):
                request = {
                    'relations': plan['relation_specifications'][str((degree+50*orientation) % 100)],
                    'witness_directory': str(OUT / 'packets'),
                    'witness_solver_limit': 8192, 'witness_memory_limit_mb': 1536,
                    # Check the entire lower module, not merely a complement.
                    'compute': {'prime': 5, 'exponent': 4, 'degree': degree,
                                'orientation': orientation, 'recursive': True,
                                'recursive_verification': True,
                                'archive_directory': str(SOURCE),
                                'allow_missing_lower_orientations': True}}
                for mode in ('produce', 'replay'):
                    publish(state='running', active={'degree': degree, 'orientation': orientation}, stage=mode)
                    request['witness_mode'] = mode
                    path = reports / f'degree_{degree}_q{orientation}_{mode}.json'
                    with path.open('w') as report, path.with_suffix('.log').open('w') as log:
                        child = subprocess.Popen([str(BINARY), '-'], stdin=subprocess.PIPE,
                                                 stdout=report, stderr=log, text=True)
                        child.stdin.write(json.dumps(request)); child.stdin.close()
                        start = time.monotonic()
                        while child.poll() is None:
                            publish(pid=child.pid, case_elapsed_seconds=time.monotonic()-start)
                            if time.monotonic()-start > 1800:
                                child.terminate()
                                try:
                                    child.wait(timeout=10)
                                except subprocess.TimeoutExpired:
                                    child.kill(); child.wait()
                                raise RuntimeError('lower case exceeded 30-minute bound')
                            time.sleep(1)
                    result = json.loads(path.read_text())
                    if child.returncode or result.get('state') != 'passed':
                        status['failed'].append({'degree': degree, 'orientation': orientation,
                                                 'mode': mode, 'report': str(path),
                                                 'state': result.get('state')})
                        publish(state='needs_attention', active=None)
                        return
                status['completed_count'] += 1
                publish(active=None)
        publish(state='completed', active=None, stage=None)
    except Exception as error:
        publish(state='error', error=str(error))
        raise


if __name__ == '__main__':
    main()

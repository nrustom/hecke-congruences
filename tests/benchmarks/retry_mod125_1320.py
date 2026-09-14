"""Retry the stopped case; resume production only after successful replay."""
import json
import os
from pathlib import Path
import subprocess
import time
import argparse

parser = argparse.ArgumentParser()
parser.add_argument('--orientation', type=int, choices=range(4), default=1)
args = parser.parse_args()
orientation = args.orientation

root = Path(__file__).resolve().parents[2]
output = root / f'verification_data/mod125_compact/retry_degree_1320_q{orientation}'
output.mkdir(exist_ok=True)
attempt = output / str(time.time_ns())
attempt.mkdir()
status = {'state': 'running', 'degree': 1320, 'orientation': orientation,
          'workers': 1, 'solver_budget_mib': 640}


def publish():
    """Update the progress record and its observation time.

    This records execution status, not a new mathematical verification.
    """
    status['heartbeat_at'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
    temporary = output / 'status.tmp'
    temporary.write_text(json.dumps(status, indent=2) + '\n')
    temporary.replace(output / 'status.json')


try:
    plan = json.loads((root / 'relations/p5_mod125_native.json').read_text())
    request = {
        'relations': plan['relation_specifications'][str((1320 + 50*orientation) % 100)],
        'progress': True,
        'witness_directory': str(root / 'verification_data/mod125_compact/packets'),
        'witness_mode': 'produce', 'witness_solver_limit': 4096,
        'witness_memory_limit_mb': 640,
        'compute': {'prime': 5, 'exponent': 4, 'degree': 1320,
                    'orientation': orientation, 'recursive': True,
                    'recursive_verification': True,
                    'archive_directory': str(root / plan['source_directory']),
                    'allow_missing_lower_orientations': True},
    }
    env = dict(os.environ, LD_LIBRARY_PATH='/home/nrustom/.conda/envs/sage/lib',
               OPENBLAS_NUM_THREADS='1', OMP_NUM_THREADS='1')
    for mode in ('produce', 'replay'):
        status['stage'] = mode
        publish()
        request['witness_mode'] = mode
        with (attempt / (mode + '.jsonl')).open('w') as report_file, \
                (attempt / (mode + '.log')).open('w') as log:
            child = subprocess.Popen(
                [str(root / 'nim/.verify-hecke-relations-build/verify_hecke_relations'), '-'],
                stdin=subprocess.PIPE, stdout=report_file, stderr=log,
                text=True, cwd=root, env=env)
            child.stdin.write(json.dumps(request))
            child.stdin.close()
            status['pid'] = child.pid
            while child.poll() is None:
                publish()
                time.sleep(5)
        # Progress-enabled native output is JSON Lines, not one JSON document.
        messages = [json.loads(line) for line in
                    (attempt / (mode + '.jsonl')).read_text().splitlines()
                    if line.strip()]
        reports = [message for message in messages if
                   message.get('schema') == 'hecke.relation-verification.v1']
        if len(reports) != 1 or messages[-1] != reports[0]:
            raise RuntimeError('missing or ambiguous final native report')
        report = reports[0]
        report_path = attempt / (mode + '.json')
        report_path.write_text(json.dumps(report, indent=2) + '\n')
        status['report'] = str(report_path)
        if child.returncode != 0 or report.get('state') != 'passed':
            status['state'] = report.get('state', 'error')
            publish()
            raise SystemExit(1)
    status['stage'] = 'resume'
    publish()
    subprocess.run(['bash', 'run_mod125_witnesses.sh', 'resume', '4'],
                   cwd=root, check=True)
    status.update(state='completed', stage=None, regular_runner_resumed=True)
    publish()
except Exception as error:
    status.update(state='error', error=repr(error))
    publish()
    raise

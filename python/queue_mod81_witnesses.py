"""Queue pure-Nim mod81 witness production after successful mod49 completion."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'verification_data/mod81_compact'
PREDECESSOR = ROOT / 'verification_data/mod49_compact'
BINARY = ROOT / 'nim/.verify-hecke-relations-build/produce_mod81_verification_data'
STAGES = ('T7_mod81', 'nonzero_mod243', 'zero_ideal_mod2187')
MODULUS = 81
TOTAL_CASES = 3240
PLAN_PREFIX = 'p3_mod81'
PREDECESSOR_LABEL = 'mod49'


def load(path):
    """Read and decode the specified JSON status or configuration file."""
    return json.loads(path.read_text()) if path.exists() else {}


def stage_succeeded(status, total):
    """Require completed coverage with no active or failed cases before accepting this stage."""
    return (status.get('state') == 'completed'
            and status.get('completed_count') == status.get('total_cases') == total
            and status.get('all_requested_witnesses_produced') is True
            and status.get('failed') == [] and status.get('active') == [])


def predecessor_succeeded():
    """Check the required coverage and success fields before releasing the queued computation."""
    status = load(PREDECESSOR / 'status.json')
    if status.get('state') != 'completed' or status.get('completed_count') != 7280:
        return False
    probe = subprocess.run(['systemctl', '--user', 'show', 'hecke-mod49-witnesses.service',
                            '-p', 'ActiveState', '--value'], capture_output=True, text=True)
    if probe.returncode or probe.stdout.strip() not in ('inactive', 'failed'):
        return False
    for stage, total, modulus in [('G_mod49', 910, 49), ('Q_selectors_mod343', 6370, 343)]:
        report = load(PREDECESSOR / stage / 'status.json')
        if not stage_succeeded(report, total) or report.get('working_modulus') != modulus:
            return False
    return True


def run(workers):
    """Wait for the required predecessor, then run the modulo-81 stages with the requested worker limit."""
    OUT.mkdir(parents=True, exist_ok=True)
    status = dict(schema=f'hecke.mod{MODULUS}-witness-queue-status.v1', state=f'waiting_for_{PREDECESSOR_LABEL}',
                  workers=workers, total_cases=TOTAL_CASES, completed_stages=[], current_stage=None,
                  active=[], active_degrees=[], failed=[], pid=os.getpid(),
                  verification_mode='whole_compact_source', recursive_verification=False)
    def publish(**updates):
        """Update the progress record and its observation time.

        This records execution status, not a new mathematical verification.
        """
        status.update(updates)
        status['heartbeat_at'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
        path = OUT / f'status.{os.getpid()}.tmp'
        path.write_text(json.dumps(status, indent=2)+'\n')
        path.replace(OUT / 'status.json')
    try:
        publish()
        while not predecessor_succeeded():
            time.sleep(30)
            publish()
        plans = []
        for stage in STAGES:
            path = ROOT / f'relations/{PLAN_PREFIX}_{stage}_native.json'
            plan = load(path)
            assert plan['classification_modulus'] == MODULUS
            degrees = [d for d in range(0, plan['degree_bound'], 2)
                       if d % plan['degree_residue_modulus'] in plan['degree_residues']]
            missing = [d for d in degrees if not
                       (ROOT / plan['source_directory'] / f'degree_{d}.npz').is_file()]
            if missing:
                raise RuntimeError(f'{stage}: missing source degrees {missing[:10]}')
            plans.append((stage, path, len(degrees)*(plan['prime']-1)))
        publish(binary_sha256=hashlib.sha256(BINARY.read_bytes()).hexdigest(),
                plan_sha256={s: hashlib.sha256(p.read_bytes()).hexdigest() for s,p,_ in plans})
        for stage, plan, total in plans:
            directory = OUT / stage
            directory.mkdir(exist_ok=True)
            publish(state='running', current_stage=stage, completed_count=0, stage_total_cases=total)
            with (directory / 'producer.log').open('a') as log:
                child = subprocess.Popen([str(BINARY), '--project-root', str(ROOT),
                                          '--plan', str(plan), '--output', str(directory),
                                          '--workers', str(workers), '--solver-memory-mb', '1536'],
                                         cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
                while child.poll() is None:
                    report = load(directory / 'status.json')
                    publish(child_pid=child.pid, completed_count=report.get('completed_count', 0),
                            active=report.get('active', []), active_degrees=report.get('active_degrees', []),
                            failed=report.get('failed', []))
                    time.sleep(5)
            report = load(directory / 'status.json')
            if child.returncode or not stage_succeeded(report, total):
                publish(state='needs_attention', active=[], active_degrees=[],
                        failed=[dict(stage=stage, exit_code=child.returncode, details=report.get('failed'))])
                return 1
            status['completed_stages'].append(stage)
        publish(state='completed', current_stage=None, completed_count=TOTAL_CASES,
                active=[], active_degrees=[], failed=[], child_pid=None)
        return 0
    except Exception as error:
        publish(state='error', error=str(error))
        raise


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers', type=int, choices=range(1,5), default=4)
    raise SystemExit(run(parser.parse_args().workers))

"""Queue native mod49 witness production after successful mod125 completion.

Only scheduling/status uses Python; all relation arithmetic is native Nim.
The predecessor is never stopped or restarted by this controller.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'verification_data/mod49_compact'
PREDECESSOR = ROOT/'verification_data/mod125_compact/status.json'
PREDECESSOR_UNIT = 'hecke-mod125-witnesses.service'
BINARY = ROOT/'nim/.verify-hecke-relations-build/produce_mod49_verification_data'
STAGES = ('G_mod49', 'Q_selectors_mod343')


def load(path):
    """Read and decode the specified JSON status or configuration file."""
    return json.loads(path.read_text())


def predecessor_succeeded(status, active):
    """Check the required coverage and success fields before releasing the queued computation."""
    return (not active and status.get('schema') == 'hecke.mod125-witness-production-status.v2'
            and status.get('state') == 'completed'
            and status.get('working_modulus') == 625
            and status.get('classification_modulus') == 125
            and status.get('completed_count') == status.get('total_cases') == 5375
            and status.get('all_requested_witnesses_produced') is True
            and status.get('failed') == [] and status.get('active') == [])


def active_predecessor():
    """Read the predecessor service state; an unknown state prevents launching the next computation."""
    probe = subprocess.run(['systemctl', '--user', 'show', PREDECESSOR_UNIT,
                            '-p', 'ActiveState', '--value'], capture_output=True, text=True)
    if probe.returncode:
        raise RuntimeError('cannot establish predecessor service state: '+probe.stderr.strip())
    return probe.stdout.strip() not in ('inactive', 'failed')


def stage_succeeded(status, total):
    """Require completed coverage with no active or failed cases before accepting this stage."""
    return (status.get('state') == 'completed'
            and status.get('completed_count') == status.get('total_cases') == total
            and status.get('all_requested_witnesses_produced') is True
            and status.get('failed') == [] and status.get('active') == [])


def run(workers):
    """Wait for the required predecessor, then run the modulo-49 stages with the requested worker limit."""
    OUT.mkdir(parents=True, exist_ok=True)
    status = dict(schema='hecke.mod49-witness-queue-status.v1', state='waiting_for_mod125',
                  workers=workers, total_cases=7280, completed_stages=[], current_stage=None,
                  predecessor=str(PREDECESSOR), failed=[], pid=os.getpid())
    def publish(**updates):
        """Update the progress record and its observation time.

        This records execution status, not a new mathematical verification.
        """
        status.update(updates)
        status['heartbeat_at'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
        tmp=OUT/f'status.{os.getpid()}.tmp'
        tmp.write_text(json.dumps(status, indent=2)+'\n')
        tmp.replace(OUT/'status.json')
    try:
        publish()
        while True:
            previous=load(PREDECESSOR)
            if predecessor_succeeded(previous, active_predecessor()):
                break
            publish(state='waiting_for_mod125', predecessor_state=previous.get('state'),
                    predecessor_completed_count=previous.get('completed_count'),
                    predecessor_failed=previous.get('failed', []))
            time.sleep(30)
        publish(state='preflight', predecessor_state='completed')
        plans={}
        for stage in STAGES:
            path=ROOT/f'relations/p7_mod49_{stage}_native.json'
            plan=load(path)
            if plan['prime']!=7 or plan['classification_modulus']!=49:
                raise RuntimeError('incorrect mod49 production plan')
            missing=[d for d in range(0,plan['degree_bound'],2)
                     if not (ROOT/plan['source_directory']/f'degree_{d}.npz').is_file()]
            if missing:raise RuntimeError(f'{stage}: missing source degrees {missing[:10]}')
            plans[stage]=(path,plan)
        publish(plan_sha256={stage:hashlib.sha256(path.read_bytes()).hexdigest()
                             for stage,(path,_) in plans.items()},
                binary_sha256=hashlib.sha256(BINARY.read_bytes()).hexdigest())
        for stage in STAGES:
            path,plan=plans[stage]
            total=plan['low_orientation_bound']//2+(plan['degree_bound']-plan['low_orientation_bound'])//2*6
            directory=OUT/stage
            directory.mkdir(exist_ok=True)
            publish(state='running',current_stage=stage)
            with (directory/'producer.log').open('a') as log:
                child=subprocess.Popen([str(BINARY),'--project-root',str(ROOT),
                    '--plan',str(path),'--output',str(directory),'--workers',str(workers),
                    '--solver-memory-mb','1536'], cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
                while child.poll() is None:
                    publish(child_pid=child.pid)
                    time.sleep(5)
            report=load(directory/'status.json')
            if child.returncode or not stage_succeeded(report,total):
                publish(state='needs_attention',child_pid=None,
                        failed=[{'stage':stage,'exit_code':child.returncode,'state':report.get('state'),
                                 'details':report.get('failed',[])}])
                return 1
            status['completed_stages'].append(stage)
            publish(child_pid=None)
        publish(state='completed',current_stage=None,completed_count=7280)
        return 0
    except Exception as error:
        publish(state='error',error=str(error))
        raise


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers',type=int,choices=range(1,5),default=4)
    raise SystemExit(run(parser.parse_args().workers))

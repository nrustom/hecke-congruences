"""Configure the existing finite-source queue for mod256 after mod81."""
import argparse
import subprocess
import queue_mod81_witnesses as queue

PREDECESSOR = queue.ROOT / 'verification_data/mod81_compact'


def predecessor_succeeded():
    """Check the required coverage and success fields before releasing the queued computation."""
    status = queue.load(PREDECESSOR / 'status.json')
    if status.get('state') != 'completed' or status.get('completed_count') != 3240:
        return False
    probe = subprocess.run(['systemctl', '--user', 'show', 'hecke-mod81-witnesses.service',
                            '-p', 'ActiveState', '--value'], capture_output=True, text=True)
    if probe.returncode or probe.stdout.strip() not in ('inactive', 'failed'):
        return False
    for stage, total, modulus in [('T7_mod81',270,81), ('nonzero_mod243',540,243),
                                  ('zero_ideal_mod2187',2430,2187)]:
        report = queue.load(PREDECESSOR / stage / 'status.json')
        if not queue.stage_succeeded(report,total) or report.get('working_modulus') != modulus:
            return False
    return True


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers', type=int, choices=range(1,5), default=4)
    args = parser.parse_args()
    queue.MODULUS = 256
    queue.TOTAL_CASES = 320
    queue.PLAN_PREFIX = 'p2_mod256'
    queue.PREDECESSOR_LABEL = 'mod81'
    queue.STAGES = ('T3_T5',)
    queue.OUT = queue.ROOT / 'verification_data/mod256_compact'
    queue.BINARY = queue.ROOT / 'nim/.verify-hecke-relations-build/produce_mod256_verification_data'
    queue.predecessor_succeeded = predecessor_succeeded
    raise SystemExit(queue.run(args.workers))

"""Bounded, fail-closed recovery of memory-limited native witness jobs."""
import fcntl
import gzip
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'verification_data/mod125_compact'
WATCH = OUT / 'watchdog'
UNIT = 'hecke-mod125-witnesses.service'
BINARY = ROOT / 'nim/.verify-hecke-relations-build/verify_hecke_relations_watchdog'
BUDGETS = (1024, 1536, 2048, 3072, 4096)


def load(path):
    """Read a plain or gzip-compressed JSON progress or verification record."""
    with (gzip.open(path, 'rt') if str(path).endswith('.gz') else open(path)) as f:
        return json.load(f)


def save(path, value):
    """Publish the complete JSON record through a temporary file."""
    tmp = path.with_suffix('.tmp')
    tmp.write_text(json.dumps(value, indent=2) + '\n')
    tmp.replace(path)


def service_active():
    """Query whether the designated user service is active, without changing its state."""
    return subprocess.run(['systemctl', '--user', 'is-active', '--quiet', UNIT]).returncode == 0


def needed_memory(report):
    """Choose the smaller, sufficient shared solve when available; no guesses."""
    if report.get('state') != 'inconclusive':
        return None
    requests = []
    for relation in report.get('relations', []):
        if relation.get('state') == 'passed':
            continue
        if relation.get('verification_route') != 'howell_memory_limit':
            return None
        shared = relation.get('shared_chain_attempt', {})
        candidate = (shared if shared.get('verification_route') == 'howell_memory_limit'
                     else relation)
        if candidate.get('howell_dimension', 0) > 8192:
            return None
        requests.append(candidate['estimated_bytes'])
    return max(requests) if requests else None


def check_resources(budget):
    """Require the configured RAM margin and free disk space before starting a bounded retry."""
    fields = dict(line.split(':', 1) for line in Path('/proc/meminfo').read_text().splitlines())
    available = int(fields['MemAvailable'].split()[0]) * 1024
    if available < (budget + 1024) * 1024**2:
        raise RuntimeError('insufficient available RAM for bounded retry')
    if shutil.disk_usage(OUT).free < 10 * 1024**3:
        raise RuntimeError('less than 10 GiB disk space available')


def main():
    """Monitor the designated job and retry only documented memory-limit refusals within the resource bounds."""
    WATCH.mkdir(exist_ok=True)
    status = {'state': 'monitoring', 'maximum_solver_mib': 4096,
              'retry_workers': 1, 'resume_workers': 4}
    def publish(**changes):
        """Update the progress record and its observation time.

        This records execution status, not a new mathematical verification.
        """
        status.update(changes)
        status['heartbeat_at'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
        save(WATCH / 'status.json', status)

    def execute(request, directory, mode):
        """Run one bounded native production or replay request and require an unambiguous final report."""
        request['witness_mode'] = mode
        publish(stage=mode)
        with (directory / (mode + '.jsonl')).open('w') as out, \
                (directory / (mode + '.log')).open('w') as err:
            child = subprocess.Popen([str(BINARY), '-'], stdin=subprocess.PIPE,
                                     stdout=out, stderr=err, text=True, cwd=ROOT)
            child.stdin.write(json.dumps(request))
            child.stdin.close()
            begin = time.monotonic()
            while child.poll() is None:
                publish(retry_pid=child.pid, retry_elapsed_seconds=time.monotonic()-begin)
                if time.monotonic()-begin > 2700:
                    child.terminate()
                    try:
                        child.wait(timeout=10)
                    except subprocess.TimeoutExpired:
                        child.kill(); child.wait()
                    raise RuntimeError('retry exceeded 45-minute limit')
                time.sleep(5)
        messages = [json.loads(line) for line in
                    (directory / (mode + '.jsonl')).read_text().splitlines() if line.strip()]
        reports = [x for x in messages if x.get('schema') == 'hecke.relation-verification.v1']
        if len(reports) != 1 or messages[-1] != reports[0]:
            raise RuntimeError('missing or ambiguous final native report')
        report = reports[0]
        save(directory / (mode + '.json'), report)
        if child.returncode not in (0, 1, 3) or (report.get('state') == 'passed' and child.returncode):
            raise RuntimeError('native retry exited abnormally')
        return report

    try:
        with (WATCH / '.lock').open('a') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            while True:
                publish(state='monitoring', stage=None)
                if service_active():
                    time.sleep(30); continue
                current = load(OUT / 'status.json')
                if current.get('state') == 'completed':
                    publish(state='completed'); return
                failures = current.get('failed', [])
                if not failures:
                    publish(state='paused', reason='producer stopped without a reported memory failure')
                    return
                # Prevent a second producer from starting while packets are written.
                with (OUT / '.producer.lock').open('a') as producer_lock:
                    fcntl.flock(producer_lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    if service_active():
                        raise RuntimeError('producer restarted during watchdog handoff')
                    plan = load(ROOT / 'relations/p5_mod125_native.json')
                    manifest = load(OUT / 'manifest.json')
                    for failure in failures:
                        if failure.get('state') != 'inconclusive' or 'report' not in failure:
                            raise RuntimeError('non-memory failure requires inspection')
                        report = load(failure['report'])['native']
                        degree, orientation = failure['degree'], failure['orientation']
                        required = needed_memory(report)
                        if required is None:
                            raise RuntimeError('inconclusive result is not a supported memory-limit retry')
                        case = WATCH / f'degree_{degree}_q{orientation}'
                        case.mkdir(exist_ok=True)
                        success = False
                        for budget in BUDGETS:
                            if budget*1024**2 < required:
                                continue
                            attempt = case / f'budget_{budget}'
                            if attempt.exists():
                                raise RuntimeError('retry already attempted; refusing an automatic loop')
                            check_resources(budget)
                            attempt.mkdir()
                            publish(state='retrying', degree=degree, orientation=orientation,
                                    solver_memory_mb=budget, attempt=str(attempt))
                            request = {
                                'relations': plan['relation_specifications'][str(
                                    (degree + plan['orientation_shift']*orientation) % plan['coefficient_period'])],
                                'progress': True, 'witness_memory_limit_mb': budget,
                                'witness_solver_limit': 8192,
                                'witness_directory': str(OUT / 'packets'),
                                'compute': {'prime': plan['prime'], 'exponent': plan['exponent'],
                                            'degree': degree, 'orientation': orientation,
                                            'recursive': True, 'recursive_verification': True,
                                            'archive_directory': str(ROOT / plan['source_directory']),
                                            'allow_missing_lower_orientations': True}}
                            extra_sources = manifest.get('supplementary_source_directory')
                            extra_witnesses = manifest.get('supplementary_witness_directory')
                            if extra_sources:
                                request['compute']['supplementary_archive_directories'] = [extra_sources]
                            if extra_witnesses:
                                request['witness_read_directories'] = [extra_witnesses]
                            report = execute(request, attempt, 'produce')
                            if report.get('state') == 'passed':
                                replay = execute(request, attempt, 'replay')
                                if replay.get('state') != 'passed':
                                    raise RuntimeError('independent witness replay did not pass')
                                save(OUT / 'memory_budget_worker_watchdog.json',
                                     {'solver_memory_mb': budget})
                                success = True
                                break
                            required = needed_memory(report)
                            if required is None:
                                raise RuntimeError('retry returned a non-memory obstruction')
                        if not success:
                            raise RuntimeError('required solve exceeds the 4 GiB retry ceiling')
                publish(state='resuming', stage=None)
                subprocess.run(['bash', 'run_mod125_witnesses.sh', 'resume', '4'], cwd=ROOT, check=True)
                time.sleep(5)
    except Exception as error:
        publish(state='needs_attention', reason=str(error))
        raise


if __name__ == '__main__':
    main()

"""Resumable four-worker-capable producer for compact (9,T2) source images."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import tempfile
import time
import zipfile

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "source_data/p3_ideal_9_T2_mod2187"
BUILD = ROOT / "nim/.p3-ideal-build"
DEGREES = tuple(range(2, 7290, 6))
SOURCES = ["compute_p3_ideal_source_data.nim", "compute_source_data.nim",
           "manin_quotient.nim", "hecke_action.nim", "mixed_endomorphisms.nim",
           "modular_matrix.nim", "modular_polynomial.nim"]


def prune_module_cache(directory, next_degree, maximum_bytes=1024**3):
    """Evict optional maps after their last consumer, or oldest first at 1 GiB.

    Only this producer's named .gz cache files are removed. Final source
    archives and unfinished stage checkpoints are never touched.
    """
    files = []
    for path in directory.glob("degree_*_*.gz"):
        degree = int(path.name.split("_")[1])
        consumers = [degree + step for step in (2916, 4374) if degree + step < 7290]
        if not consumers or max(consumers) < next_degree:
            path.unlink(missing_ok=True)
        else:
            stat = path.stat()
            files.append((stat.st_mtime, stat.st_size, path))
    total = sum(size for _, size, _ in files)
    for _, size, path in sorted(files):
        if total <= maximum_bytes:
            break
        path.unlink(missing_ok=True)
        total -= size
    return total


def sha(path):
    """Return the SHA-256 digest used to identify this source archive."""
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024*1024), b""):
            h.update(block)
    return h.hexdigest()


def write_json(path, value):
    """Publish a JSON record by replacing the destination only after writing the complete temporary file."""
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def validate_archive(path):
    """Check the required archive member names, compression and CRCs before reuse.

    This checks the container, not its mathematical arrays or parameter values.
    """
    expected = {"ideal_source_version.npy", "full_replay.npy", "parameters.npy",
                "plus_order_exponents.npy", "minus_order_exponents.npy",
                "plus_T2.npy", "minus_T2.npy"}
    with zipfile.ZipFile(path) as archive:
        if set(archive.namelist()) != expected or archive.testzip() is not None:
            raise ValueError("invalid compact archive members or CRC")
        if any(item.compress_type != zipfile.ZIP_DEFLATED for item in archive.infolist()):
            raise ValueError("archive is not compressed")


def run(workers):
    """Run the resumable ideal-image source scan with bounded workers and stop scheduling after a failure."""
    WORK.mkdir(parents=True, exist_ok=True)
    (WORK / "logs").mkdir(exist_ok=True)
    (WORK / ".staging").mkdir(exist_ok=True)
    executable = BUILD / "compute_p3_ideal_source_data"
    code = {name: sha(ROOT / "nim" / name) for name in SOURCES}
    code["executable"] = sha(executable)
    module_cache = WORK / ".module_cache" / code["executable"]
    module_cache.mkdir(parents=True, exist_ok=True)
    # The wrapper refuses a second active service. These are unfinished
    # atomic writes from a stopped attempt, not published map entries.
    for temporary in module_cache.glob("*.gz.tmp.*"):
        temporary.unlink()
    cache_bytes = 0
    compatibility_path = ROOT / "python/p3_ideal_compatible_producers.json"
    compatible = json.loads(compatibility_path.read_text()) if compatibility_path.exists() else []
    started = time.time()
    active, completed, reused, failed = {}, [], [], []
    stopping = False

    def stop(signum, frame):
        """Request that the controller stop scheduling new degree computations."""
        nonlocal stopping
        stopping = True

    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)

    def status(state):
        """Publish current progress, including active cases and recorded failures."""
        write_json(WORK / "status.json", {
            "schema": "hecke.p3-ideal-source-status.v1", "state": state,
            "pid": os.getpid(), "workers": workers,
            "heartbeat_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "elapsed_seconds": round(time.time()-started, 2),
            "prime": 3, "exponent": 7, "ideal": "(9,T2)M",
            "signs": [1, -1], "hecke_indices": [2],
            "total_degrees": len(DEGREES), "completed_count": len(completed),
            "reused_count": len(reused), "completed_degrees": sorted(completed),
            "active_degrees": sorted(active), "failed": failed,
            "archive_bytes": sum((WORK / f"degree_{d}.npz").stat().st_size for d in completed),
            "source_construction": "exact_recursive_Dickson_with_direct_low_degrees",
            "module_cache_bytes": cache_bytes,
            "module_cache_limit_bytes": 1024**3,
            "identities_tested": False,
        })

    status("validating_reusable_files")
    pending = []
    for d in DEGREES:
        record_path = WORK / f"degree_{d}.json"
        target = WORK / f"degree_{d}.npz"
        if target.exists() or record_path.exists():
            try:
                record = json.loads(record_path.read_text())
                if record["degree"] != d or (record["producer_hashes"] != code
                        and record["producer_hashes"] not in compatible):
                    raise ValueError("existing archive has a different producer fingerprint")
                validate_archive(target)
                if sha(target) != record["archive_sha256"]:
                    raise ValueError("archive hash mismatch")
                completed.append(d)
                reused.append(d)
            except Exception as error:
                failed.append({"degree": d, "error": str(error)})
                status("failed")
                return 1
        else:
            pending.append(d)

    environment = os.environ.copy()
    environment["LD_LIBRARY_PATH"] = "/home/nrustom/.conda/envs/sage/lib:" + environment.get("LD_LIBRARY_PATH", "")
    while pending or active:
        if stopping:
            for job in active.values():
                if job["process"].poll() is None:
                    job["process"].terminate()
        while pending and len(active) < workers and not failed and not stopping:
            if shutil.disk_usage(WORK).free < 8*1024**3:
                failed.append({"error": "less than 8 GiB disk free; no new degrees scheduled"})
                break
            d = pending.pop(0)
            stage = tempfile.TemporaryDirectory(prefix=f"degree_{d}_", dir=WORK / ".staging")
            output = Path(stage.name) / "source.npz"
            log_path = WORK / "logs" / f"degree_{d}_{time.time_ns()}.log"
            log = log_path.open("w")
            checkpoint = WORK / ".checkpoints" / code["executable"] / f"degree_{d}"
            checkpoint.mkdir(parents=True, exist_ok=True)
            # Only unfinished temporary checkpoint writes from dead attempts.
            for temporary in checkpoint.glob("*.tmp.*"):
                temporary.unlink()
            try:
                process = subprocess.Popen([str(executable), str(d), str(output),
                    "--recursive", f"--checkpoint-dir={checkpoint}",
                    f"--module-cache-dir={module_cache}"],
                    cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, env=environment)
            except Exception:
                log.close()
                stage.cleanup()
                raise
            active[d] = {"process": process, "log": log, "log_path": log_path,
                         "stage": stage, "output": output, "checkpoint": checkpoint,
                         "started": time.time()}
            print(f"started degree {d}, pid {process.pid}", flush=True)
        for d, job in list(active.items()):
            code_result = job["process"].poll()
            if code_result is None:
                continue
            job["log"].close()
            try:
                if code_result != 0:
                    if not stopping:
                        raise RuntimeError(f"worker exited {code_result}; see {job['log_path']}")
                else:
                    validate_archive(job["output"])
                    digest = sha(job["output"])
                    target = WORK / f"degree_{d}.npz"
                    if target.exists():
                        raise FileExistsError(f"refusing to overwrite {target}")
                    job["output"].rename(target)
                    write_json(WORK / f"degree_{d}.json", {
                        "schema": "hecke.p3-ideal-source-degree.v1", "degree": d,
                        "prime": 3, "exponent": 7, "ideal": "(9,T2)M",
                        "signs": [1,-1], "producer_hashes": code,
                        "archive_sha256": digest, "archive_bytes": target.stat().st_size,
                        "elapsed_seconds": round(time.time()-job["started"],2),
                        "producer_structural_checks_passed": True,
                        "descent_verification_performed": False,
                        "inclusion_action_replay_performed": False,
                        "source_construction": "recursive_Dickson" if d >= 2916 else "direct",
                        "classification_identities_tested": False,
                    })
                    completed.append(d)
                    # Completed compact archive replaces temporary stage checkpoints.
                    shutil.rmtree(job["checkpoint"])
                    print(f"completed degree {d}: {len(completed)}/{len(DEGREES)}", flush=True)
            except Exception as error:
                failed.append({"degree": d, "error": str(error)})
                print(f"FAILED degree {d}: {error}", flush=True)
            finally:
                job["stage"].cleanup()
                del active[d]
        next_needed = min([*pending, *active], default=7290)
        cache_bytes = prune_module_cache(module_cache, next_needed)
        status("stopping" if stopping else "draining_after_failure" if failed else "running")
        if not active and (stopping or failed):
            break
        time.sleep(2)
    state = "stopped" if stopping else "failed" if failed else "completed"
    status(state)
    return 1 if failed else 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("workers", type=int, choices=range(1,5))
    args = parser.parse_args()
    raise SystemExit(run(args.workers))

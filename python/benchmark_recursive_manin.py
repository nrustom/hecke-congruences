"""Time direct and recursive compact producers; exact-map tests are separate."""
import argparse
import json
import os
from pathlib import Path
import resource
import subprocess
import tempfile
import time

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("executable")
    parser.add_argument("degrees", type=int, nargs="+")
    args = parser.parse_args()
    directory = Path(tempfile.mkdtemp(prefix="hecke-recursive-benchmark-"))
    print(directory, flush=True)
    records = []
    env = os.environ.copy()
    env["LD_LIBRARY_PATH"] = "/home/nrustom/.conda/envs/sage/lib:" + env.get("LD_LIBRARY_PATH", "")
    for d in args.degrees:
        for method in ("direct", "recursive"):
            start = time.monotonic()
            before = resource.getrusage(resource.RUSAGE_CHILDREN)
            with (directory / f"{d}_{method}.log").open("w") as log:
                subprocess.run([args.executable, str(d), str(directory / f"{d}_{method}.npz"),
                                "--" + method], stdout=log, stderr=subprocess.STDOUT, env=env, check=True)
            after = resource.getrusage(resource.RUSAGE_CHILDREN)
            record = dict(degree=d, method=method, seconds=time.monotonic()-start,
                          cpu_seconds=after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,
                          archive_bytes=(directory / f"{d}_{method}.npz").stat().st_size)
            records.append(record)
            (directory / "timings.json").write_text(json.dumps(records, indent=2)+"\n")
            print(record, flush=True)

if __name__ == "__main__":
    main()

"""Paired producer benchmark, comparing every output array to the baseline."""
import argparse
import json
import os
from pathlib import Path
import resource
import subprocess
import tempfile
import time
import numpy as np

if __name__ == "__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("baseline")
    parser.add_argument("optimized")
    parser.add_argument("--degrees",type=int,nargs="+",default=[2000,3134])
    args=parser.parse_args()
    directory=Path(tempfile.mkdtemp(prefix="hecke-ideal-benchmark-"))
    print(f"benchmark directory: {directory}",flush=True)
    environment=os.environ.copy()
    environment["LD_LIBRARY_PATH"]="/home/nrustom/.conda/envs/sage/lib:"+environment.get("LD_LIBRARY_PATH","")
    records=[]
    for degree in args.degrees:
        baseline_arrays=None
        for mode,binary,flags in [("baseline",args.baseline,[]),
                                  ("optimized_audit",args.optimized,["--audit"]),
                                  ("optimized_fast",args.optimized,[])]:
            output=directory/f"{mode}_{degree}.npz"
            before=resource.getrusage(resource.RUSAGE_CHILDREN)
            start=time.monotonic()
            with (directory/f"{mode}_{degree}.log").open("w") as log:
                subprocess.run([binary,str(degree),str(output),*flags],env=environment,
                               stdout=log,stderr=subprocess.STDOUT,check=True)
            elapsed=time.monotonic()-start
            after=resource.getrusage(resource.RUSAGE_CHILDREN)
            with np.load(output,allow_pickle=False) as bundle:
                arrays={name:bundle[name].copy() for name in bundle.files}
            if baseline_arrays is None:
                baseline_arrays=arrays
            else:
                assert arrays.keys()==baseline_arrays.keys()
                for key in arrays:
                    assert np.array_equal(arrays[key],baseline_arrays[key]),key
            record=dict(degree=degree,mode=mode,wall_seconds=round(elapsed,3),
                        cpu_seconds=round(after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,3),
                        all_arrays_match=True)
            records.append(record)
            (directory/"results.json").write_text(json.dumps(records,indent=2))
            print(record,flush=True)

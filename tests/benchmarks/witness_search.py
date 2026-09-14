"""Bounded, isolated comparison of native structured-choice search variants.

Usage: python3 tests/benchmarks/witness_search.py --build-directory DIR
DIR must contain baseline, cached, and screen executables. No producer binary,
production packet, source archive, or running service is modified. Each timed
case starts with a new packet directory, and optimized packets are independently
replayed by the unmodified baseline executable. Results describe whole-source
selector checks, not an end-to-end recursive classification scan.
"""
import argparse
import copy
import gzip
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

import numpy as np


ROOT = Path(__file__).resolve().parents[2]


def main():
    """Benchmark candidate intermediate-element constructions, retaining the original equation checks."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build-directory', type=Path, required=True)
    parser.add_argument('--degrees', type=int, nargs='+', default=[26, 810, 1270])
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    output = args.output or ROOT / 'tests/benchmarks/witness_search_results' / str(time.time_ns())
    output.mkdir(parents=True, exist_ok=False)
    binaries = {name: (args.build_directory / name).resolve()
                for name in ('baseline', 'cached', 'screen')}
    plan = json.loads((ROOT / 'relations/p5_mod125_native.json').read_text())
    env = dict(os.environ, LD_LIBRARY_PATH='/home/nrustom/.conda/envs/sage/lib',
               OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1')
    records = []
    bindings = {'binary_sha256': {name: hashlib.sha256(path.read_bytes()).hexdigest()
                                for name, path in binaries.items()},
                'source_sha256': {}, 'production_outputs_modified': False,
                'note': 'Concurrent production workload; timings are indicative.'}

    def save():
        """Write the current benchmark measurements to the summary file."""
        (output / 'summary.json').write_text(json.dumps(
            {'bindings': bindings, 'measurements': records}, indent=2) + '\n')

    def run(binary, request, label):
        """Run one benchmark command and save its output, exit status and resource measurements."""
        metrics = output / (label + '.time')
        begin = time.monotonic()
        child = subprocess.run(
            ['/usr/bin/time', '-f', '%e %U %S %M', '-o', str(metrics),
             'nice', '-n', '15', 'prlimit', '--as=1073741824', '--cpu=300',
             str(binary), '-'], input=json.dumps(request), text=True,
            capture_output=True, env=env, timeout=600)
        (output / (label + '.stderr')).write_text(child.stderr)
        report = json.loads(child.stdout)
        (output / (label + '.json')).write_text(json.dumps(report, indent=2) + '\n')
        values = metrics.read_text().splitlines()[-1].split()
        result = {'label': label, 'state': report.get('state'),
                  'wall_seconds': time.monotonic() - begin,
                  'cpu_seconds': float(values[1]) + float(values[2]),
                  'peak_rss_kib': int(values[3]),
                  'relations': [{key: r.get(key) for key in
                                 ('name', 'verification_route', 'structured_candidates',
                                  'elapsed_seconds', 'witnesses_replayed')}
                                for r in report.get('relations', [])]}
        records.append(result)
        save()
        print(json.dumps(result), flush=True)
        if child.returncode or report.get('state') != 'passed':
            raise RuntimeError(f'{label} failed: {report}')
        return report

    for degree in args.degrees:
        path = ROOT / plan['source_directory'] / f'degree_{degree}.npz'
        bindings['source_sha256'][str(degree)] = hashlib.sha256(path.read_bytes()).hexdigest()
        with np.load(path, allow_pickle=False) as arrays:
            meta = json.loads(bytes(arrays['metadata_json'].tolist()))
            assert (meta['prime'], meta['exponent'], meta['degree'], meta['source_scope']) == (
                5, 4, degree, 'manin')
            orders = [5 ** int(e) for e in arrays['q0_order_exponents']]
            operators = {f'T{ell}': arrays[f'q0_T{ell}'].tolist() for ell in (2, 19)}
        specification = copy.deepcopy(plan['relation_specifications'][str(degree % 100)])
        specification['relations'] = [r for r in specification['relations']
                                       if r['name'] in ('selector_0', 'selector_1')]
        source = {'schema': 'hecke.mixed-source.v1', 'prime': 5, 'exponent': 4,
                  'coordinate_moduli': orders, 'operators': operators,
                  'operators_are_oriented': True,
                  'metadata': {'degree': degree, 'orientation': 0,
                               'source_scope': 'manin', 'benchmark': True}}
        expected_packets = None
        expected_candidates = None
        for variant, binary in binaries.items():
            packets = output / f'degree_{degree}_{variant}_packets'
            request = {'relations': specification, 'source': source,
                       'witness_directory': str(packets), 'witness_mode': 'produce',
                       'witness_solver_limit': 4096}
            label = f'degree_{degree}_{variant}'
            report = run(binary, request, label)
            payloads = {p.name: json.loads(gzip.decompress(p.read_bytes()))
                        for p in packets.glob('*.json.gz')}
            candidates = [r.get('structured_candidates') for r in report['relations']]
            if expected_packets is None:
                expected_packets, expected_candidates = payloads, candidates
            else:
                assert payloads == expected_packets, f'{label}: witness choices changed'
                assert candidates == expected_candidates, f'{label}: search decisions changed'
            request['witness_mode'] = 'replay'
            run(binaries['baseline'], request, label + '_original_replay')
        print(f'degree {degree}: identical witnesses and candidate counts; original replay passed', flush=True)
    bindings['all_packets_identical_and_original_replay_passed'] = True
    save()
    print(f'Results: {output}', flush=True)


if __name__ == '__main__':
    main()

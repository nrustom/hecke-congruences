"""Consolidate degree-indexed replay bundles into one sealed NPZ archive."""

from __future__ import annotations

import argparse
import hashlib
import os
from pathlib import Path
import tempfile

import numpy as np


SCHEMA = "hecke-congruences.source-data-archive.v1"


def sha256(path):
    """Return the SHA-256 digest of a file without interpreting its mathematical contents."""
    answer = hashlib.sha256()

    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            answer.update(block)

    return answer.hexdigest()


def main():
    """Combine per-degree arrays into a notebook archive and record each input file's digest.

    The caller supplies the degree range and precision; this packaging step
    does not independently verify the mathematical contents of the sources.
    """
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-root", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--prime", required=True, type=int)
    parser.add_argument("--exponent", required=True, type=int)
    parser.add_argument("--minimum-degree", required=True, type=int)
    parser.add_argument("--maximum-degree", required=True, type=int)
    parser.add_argument("--degree-step", default=2, type=int)
    args = parser.parse_args()

    root = Path(args.input_root).expanduser().resolve()
    output = Path(args.output).expanduser().resolve()
    degrees = tuple(range(
        args.minimum_degree,
        args.maximum_degree + 1,
        args.degree_step,
    ))
    arrays = {
        "schema": np.asarray([SCHEMA]),
        "prime": np.asarray([args.prime], dtype=np.uint16),
        "exponent": np.asarray([args.exponent], dtype=np.uint16),
        "degrees": np.asarray(degrees, dtype=np.uint32),
    }
    bundle_hashes = []

    for position, degree in enumerate(degrees, start=1):
        bundle_path = root / f"degree_{degree}" / "replay_bundle.npz"

        if not bundle_path.is_file():
            raise FileNotFoundError(bundle_path)

        bundle_hashes.append(sha256(bundle_path))

        with np.load(bundle_path, allow_pickle=False) as bundle:
            for name in bundle.files:
                arrays[f"degree_{degree}__{name}"] = np.asarray(
                    bundle[name]
                ).copy()

        if position % 100 == 0 or position == len(degrees):
            print(
                f"loaded {position}/{len(degrees)} degree bundles",
                flush=True,
            )

    arrays["bundle_sha256"] = np.asarray(bundle_hashes)
    output.parent.mkdir(parents=True, exist_ok=True)

    with tempfile.NamedTemporaryFile(
        dir=output.parent,
        prefix=output.name + ".",
        suffix=".npz",
        delete=False,
    ) as stream:
        temporary = Path(stream.name)

    try:
        np.savez_compressed(temporary, **arrays)
        os.replace(temporary, output)
    finally:
        temporary.unlink(missing_ok=True)

    print(f"archive: {output}")
    print(f"sha256: {sha256(output)}")
    print(f"degrees: {len(degrees)}")


if __name__ == "__main__":
    main()

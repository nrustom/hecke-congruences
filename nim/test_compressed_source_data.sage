"""Replay new Nim coordinate maps and Hecke actions against fresh Sage sources.

Usage: sage nim/test_compressed_source_data.sage P M D PATH.npz
"""
import sys
from pathlib import Path
import numpy as np

sys.path.insert(0, str(Path("python").resolve()))
from hecke_congruences import prepare_source_data, load_source_data
from identity_verification import _hecke_matrix_on_source
from mixed_endomorphisms import normalize_mixed_matrix

p, m, d = map(ZZ, sys.argv[1:4])
path = sys.argv[4]
R = Integers(p^m)

with np.load(path, allow_pickle=False) as arrays:
    for q in ((0,) if p == 2 else (0, 1)):
        prefix = "unsigned" if p == 2 else ("plus" if q == 0 else "minus")
        fresh = prepare_source_data(R, d, q)
        archived = load_source_data(R, d, q, path, projection_mode="coordinates")
        coordinates = fresh["coordinates"]
        indices = coordinates["surviving_indices"]
        V = coordinates["V_R"]
        encoded_forward = arrays[prefix + "_monomials_to_mixed"]
        encoded_backward = arrays[prefix + "_mixed_to_monomials"]
        to_mixed = matrix(R, *encoded_forward.shape, encoded_forward.flatten().tolist())
        to_monomials = matrix(R, *encoded_backward.shape, encoded_backward.flatten().tolist())
        forward = V.inverse().matrix_from_rows(indices) * to_mixed
        backward = (to_monomials * V).matrix_from_columns(indices)
        actions = archived["archived_hecke_matrices"]
        sample = next(iter(actions.values()))
        moduli = sample["coordinate_moduli"]
        old_moduli = tuple(p^e for e in coordinates["surviving_exponents"])
        assert sorted(moduli) == sorted(old_moduli)
        assert normalize_mixed_matrix(forward * backward, old_moduli) == identity_matrix(R, len(indices))
        assert normalize_mixed_matrix(backward * forward, moduli) == identity_matrix(R, len(moduli))
        relations = fresh["presentation"]["B_mod"]
        assert normalize_mixed_matrix(relations * to_mixed, moduli).is_zero()
        for n, action in actions.items():
            ordinary = _hecke_matrix_on_source(n, fresh, True)
            assert normalize_mixed_matrix(ordinary["matrix"] * forward, moduli) == normalize_mixed_matrix(forward * action["matrix"], moduli)
        print(f"d={d}, q={q}: inverse maps, original relations, and Hecke actions replayed")

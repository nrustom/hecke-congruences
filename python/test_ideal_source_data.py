"""Audit a small full-replay ideal archive against freshly computed Sage M.

sage -python python/test_ideal_source_data.py FULL.npz COMPACT.npz
This deliberately computes M for an independent test, not for production.
"""
import sys
import zipfile
import numpy as np
from sage.all import ZZ, Integers, matrix, diagonal_matrix, PolynomialRing, identity_matrix
from load_ideal_source_data import load_ideal_source_data
from identity_verification import prepare_source_data, _hecke_matrix_on_source, verify_divided_identities
from pari_howell import pari_howell_row_span
from mixed_endomorphisms import mixed_matrix_is_zero


def basis(A):
    return pari_howell_row_span(A)["H_R"].transpose()


full, compact = sys.argv[1:]
R = Integers(2187)
with np.load(full, allow_pickle=False) as source, np.load(compact, allow_pickle=False) as small:
    d = int(source["parameters"][-1])
    for name in small.files:
        if name != "full_replay":
            assert np.array_equal(source[name], small[name]), name
    for q, prefix in enumerate(("plus", "minus")):
        data = load_ideal_source_data(R, d, q, compact)
        fresh = prepare_source_data(R, d, q)
        fresh_T = _hecke_matrix_on_source(2, fresh, True)
        T = fresh_T["normalized_matrix"]
        moduli = fresh_T["coordinate_moduli"]
        coordinates = fresh["coordinates"]
        retained = list(map(int, source[prefix + "_retained_monomial_indices"]))
        signed_indices = [i for i in range(d+1) if i % 2 == q]
        section = matrix(R, len(retained), len(signed_indices))
        for i, monomial in enumerate(retained):
            section[i, signed_indices.index(monomial)] = 1
        inclusion = matrix(R, source[prefix + "_ideal_to_compressed"].tolist())
        to_M = (inclusion * section * coordinates["V_R"]).matrix_from_columns(
            coordinates["surviving_indices"])
        A = data["archived_hecke_matrices"][2]["normalized_matrix"]
        assert mixed_matrix_is_zero(to_M*T - A*to_M, moduli)
        J = diagonal_matrix(R, moduli)
        ideal_rows = (9*identity_matrix(R, len(moduli))).stack(T)
        assert basis(J.stack(to_M)) == basis(J.stack(ideal_rows))
        # Independent cardinality calculation over Z proves the inclusion injective.
        # Keep the integer modulus relations: lifting J from R would turn
        # each full-order relation 2187*e_i into the zero row.
        integer_lattice = diagonal_matrix(ZZ, moduli).stack(matrix(ZZ, to_M))
        hnf = integer_lattice.row_module().basis_matrix()
        image_order = abs(diagonal_matrix(ZZ, moduli).det() // hnf.det())
        expected_order = 3**sum(data["coordinates"]["surviving_exponents"])
        assert image_order == expected_order
        X = PolynomialRing(R, "X").gen()
        assert verify_divided_identities(F=X, Q=0*X, n=2, a=1, b=1, data=data)["passed"]
for path in (full, compact):
    with zipfile.ZipFile(path) as archive:
        assert archive.testzip() is None
        assert all(item.compress_type == zipfile.ZIP_DEFLATED for item in archive.infolist())
print("Fresh Sage ideal-image identification, inclusion, order, T2 action and compact-loader tests passed")

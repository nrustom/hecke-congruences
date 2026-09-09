"""Load compact (9,T2) Manin ideal images for the existing identity verifiers.

This checks the finite module/action encoding, NOT its identification with
the Manin ideal image. Reconstruct the source to audit that identification.
"""
import hashlib
from pathlib import Path
import numpy as np
from sage.all import ZZ, matrix
from mixed_endomorphisms import mixed_endomorphism_is_well_defined


def load_ideal_source_data(R, d, q, path):
    """Load one sign of I_d=(9,T2)M_d over Z/2187 for polynomial testing.

    ``q`` chooses sign (-1)^q. The ordinary/divided verifiers subsequently
    apply the twist scalar, so it is not stored twice. Use this INSTEAD of
    load_source_data: these are ideal-image coordinates, not coordinates of
    the whole Manin quotient. Only T2 is available. check_descent=True in
    the verifiers is intentionally unsupported for this compact archive.
    """
    d, q = ZZ(d), ZZ(q)
    if d < 0 or d % 6 != 2 or q < 0 or R.characteristic() != 2187:
        raise ValueError("require modulus 2187, d=2 mod 6, and q>=0")
    prefix = "plus" if q % 2 == 0 else "minus"
    with np.load(path, allow_pickle=False) as archive:
        if tuple(archive["ideal_source_version"].tolist()) != (2,):
            raise ValueError("unsupported ideal-source archive version")
        if tuple(archive["parameters"].tolist()) != (3, 7, 9, 2, d):
            raise ValueError("ideal-source arithmetic or degree mismatch")
        orders = archive[prefix + "_order_exponents"]
        encoded = archive[prefix + "_T2"]
        if orders.ndim != 1 or orders.dtype.kind != "u" or encoded.dtype.kind != "u":
            raise ValueError("expected unsigned cyclic orders and action entries")
        exponents = tuple(ZZ(e) for e in orders)
        if any(e < 1 or e > 7 for e in exponents):
            raise ValueError("invalid cyclic exponent")
        rank = len(exponents)
        if encoded.shape != (rank, rank):
            raise ValueError("action matrix dimensions mismatch")
        moduli = tuple(3**e for e in exponents)
        for j, order in enumerate(moduli):
            if np.any(encoded[:, j] >= int(order)):
                raise ValueError("action entries are not reduced modulo coordinate orders")
        T = matrix(R, rank, rank, [int(x) for x in encoded.flat])
    if not mixed_endomorphism_is_well_defined(T, moduli):
        raise ValueError("T2 is not well-defined on the mixed ideal image")
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024*1024), b""):
            digest.update(chunk)
    return {
        "coefficient_ring": R, "modulus": ZZ(2187), "p": ZZ(3),
        "m": ZZ(7), "period": ZZ(1458), "d": d, "q": q,
        "sign": (-1)**q, "presentation": None,
        "source_scope": "ideal_image_(9,T2)_signed_Manin",
        "source_path": str(path), "source_sha256": digest.hexdigest(),
        "coordinates": {
            "surviving_indices": tuple(range(rank)),
            "surviving_exponents": exponents,
            "coordinate_moduli": moduli,
            "quotient_is_free": all(e == 7 for e in exponents),
        },
        "archived_hecke_matrices": {ZZ(2): {
            "matrix": T, "normalized_matrix": T,
            "coordinate_exponents": exponents, "coordinate_moduli": moduli,
            "base_ring": R,
        }},
    }

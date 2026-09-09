"""Load a prepared signed source from a sealed runner replay bundle."""

from __future__ import annotations

import hashlib
import json
from functools import lru_cache
from pathlib import Path
import re

import numpy as np

from sage.all import ZZ, factor, matrix

from mixed_endomorphisms import (
    mixed_matrix_is_zero,
    mixed_endomorphism_is_well_defined,
    normalize_mixed_matrix,
)


def _prime_power_data(R):
    """Recover the arithmetic data from ``R = Z/(p^m)``."""
    if not hasattr(R, "characteristic"):
        raise TypeError("the coefficient ring has no characteristic")

    modulus = ZZ(R.characteristic())
    factorization = list(factor(modulus))

    if len(factorization) != 1:
        raise ValueError("the coefficient ring must be Z/(p^m)")

    p, m = factorization[0]

    return {
        "coefficient_ring": R,
        "modulus": modulus,
        "p": p,
        "m": m,
        "period": p**(m - 1) * (p - 1),
    }


def _validate_degree_and_orientation(d, q):
    d = ZZ(d)
    q = ZZ(q)

    if d < 0 or d % 2:
        raise ValueError("d must be a nonnegative even degree")

    if q < 0:
        raise ValueError("q must be nonnegative")

    return d, q


@lru_cache(maxsize=16)
def _sha256(path):
    answer = hashlib.sha256()

    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            answer.update(block)

    return answer.hexdigest()


def _degree_recorded_by_path(path):
    """Read an optional degree marker from a path component or name."""
    patterns = (
        re.compile(r"^degree_(\d+)$"),
        re.compile(r"(?:^|_)degree_?(\d+)(?:_|\.|$)"),
    )

    for part in reversed(Path(path).parts):
        for pattern in patterns:
            match = pattern.search(part)

            if match:
                return ZZ(match.group(1))

    return None


def _load_arrays(path, d):
    """Load one degree from a single- or multiple-degree NPZ bundle."""
    try:
        with np.load(path, allow_pickle=False) as bundle:
            if "degrees" not in bundle.files:
                return {
                    "arrays": {
                        name: np.asarray(bundle[name]).copy()
                        for name in bundle.files
                    },
                    "available_degrees": None,
                    "original_bundle_sha256": None,
                    "archive_prime": None,
                    "archive_exponent": None,
                }

            if "schema" not in bundle.files or tuple(
                map(str, bundle["schema"])
            ) != ("hecke-congruences.source-data-archive.v1",):
                raise ValueError("unexpected source-data archive schema")

            if "prime" not in bundle.files or "exponent" not in bundle.files:
                raise ValueError(
                    "the source-data archive lacks its arithmetic metadata"
                )

            available_degrees = tuple(
                ZZ(value) for value in bundle["degrees"]
            )

            if d not in available_degrees:
                raise ValueError(
                    f"degree {d} is not present in the source archive"
                )

            prefix = f"degree_{d}__"
            arrays = {
                name[len(prefix):]: np.asarray(bundle[name]).copy()
                for name in bundle.files
                if name.startswith(prefix)
            }
            position = available_degrees.index(d)
            original_sha256 = None

            if "bundle_sha256" in bundle.files:
                original_sha256 = str(
                    bundle["bundle_sha256"][position]
                )

            return {
                "arrays": arrays,
                "available_degrees": available_degrees,
                "original_bundle_sha256": original_sha256,
                "archive_prime": ZZ(bundle["prime"][0]),
                "archive_exponent": ZZ(bundle["exponent"][0]),
            }
    except ValueError as error:
        if Path(path).read_bytes().startswith(
            b"version https://git-lfs.github.com/spec/v1"
        ):
            raise ValueError(
                "the requested source bundle is only a Git-LFS "
                "pointer; materialize the LFS object first"
            ) from error

        raise


def _coordinate_projection_indices(
    projection,
    scales,
    modulus,
):
    """Recover standard signed cyclic factors from a stored projection."""
    projection = np.asarray(projection, dtype=np.int64) % modulus
    dimension = len(scales)

    if projection.shape != (dimension, dimension):
        raise ValueError(
            "the signed projection has the wrong dimensions"
        )

    diagonal = np.diag(projection)
    off_diagonal = projection.copy()
    np.fill_diagonal(off_diagonal, 0)

    if np.any(off_diagonal):
        raise NotImplementedError(
            "this replay bundle has a non-coordinate signed "
            "projection; extracting its image requires an additional "
            "mixed-module basis calculation"
        )

    if np.any((diagonal != 0) & (diagonal != scales)):
        raise ArithmeticError(
            "the signed projection is incompatible with the stored "
            "cyclic order exponents"
        )

    return tuple(
        index
        for index, value in enumerate(diagonal)
        if value
    )


def _decode_signed_hecke_matrix(
    encoded,
    selected_indices,
    scales,
    coordinate_moduli,
    modulus,
):
    """Decode one stored Hecke action on a coordinate signed summand."""
    encoded = np.asarray(encoded, dtype=np.int64) % modulus
    dimension = len(scales)

    if encoded.shape != (dimension, dimension):
        raise ValueError("a stored Hecke matrix has wrong dimensions")

    selected = tuple(selected_indices)
    selected_set = set(selected)
    complement = tuple(
        index
        for index in range(dimension)
        if index not in selected_set
    )

    if selected and complement and np.any(
        encoded[np.ix_(selected, complement)]
    ):
        raise ArithmeticError(
            "the stored Hecke action does not preserve the selected "
            "signed coordinate summand"
        )

    entries = []

    for source in selected:
        for target in selected:
            value = int(encoded[source, target])
            target_scale = int(scales[target])

            if value % target_scale:
                raise ArithmeticError(
                    "a stored Hecke entry is not in mixed cyclic "
                    "normal form"
                )

            entries.append(value // target_scale)

    rank = len(selected)
    decoded = matrix(ZZ, rank, rank, entries)
    decoded = normalize_mixed_matrix(
        decoded,
        coordinate_moduli,
    )

    if not mixed_endomorphism_is_well_defined(
        decoded,
        coordinate_moduli,
    ):
        raise ArithmeticError(
            "the decoded Hecke matrix is not a mixed endomorphism"
        )

    return decoded


def load_source_data(
    R,
    d,
    q,
    path,
    projection_mode="coordinates",
):
    """
    Load source data compatible with the identity verifiers.

    The input ``path`` must be a runner ``replay_bundle.npz`` containing

        order_exponents,
        T*_rows,
        plus_projection,
        minus_projection.

    The bundle represents the complete mixed cyclic Manin source.  For
    odd ``p``, orientation ``q`` selects the plus projection when ``q``
    is even and the minus projection when ``q`` is odd.

    With ``projection_mode="coordinates"`` (the default), the selected
    projection must be a coordinate summand in the stored mixed cyclic
    basis.  With ``projection_mode="generators"``, the complete mixed
    source and Hecke matrices are retained and the rows of the stored
    idempotent are recorded as generators of the signed direct summand.
    The latter mode also supports non-coordinate signed projections.

    The returned dictionary has the same public arithmetic fields as
    ``prepare_source_data`` and may be passed to
    ``verify_ordinary_identities``, ``verify_divided_identities``,
    ``verify_ordinary_joint_identities``, and
    ``verify_divided_joint_identities``.  Hecke matrices are loaded from
    the bundle rather than recomputed from Heilbronn--Merel matrices.

    Since the replay bundle does not contain the original Manin relation
    matrix, calls using ``check_descent=True`` are not supported.
    """
    arithmetic = _prime_power_data(R)
    p = arithmetic["p"]
    m = arithmetic["m"]
    modulus = int(arithmetic["modulus"])
    d, q = _validate_degree_and_orientation(d, q)
    path = Path(path).expanduser().resolve()

    if projection_mode not in {"coordinates", "generators"}:
        raise ValueError(
            "projection_mode must be 'coordinates' or 'generators'"
        )

    if not path.is_file():
        raise FileNotFoundError(path)

    if p == 2:
        if q != 0:
            raise ValueError(
                "for p=2 the unsplit source has only orientation q=0"
            )

        sign = None
        projection_name = None
    else:
        sign = (-1)**q
        projection_name = (
            "plus_projection"
            if q % 2 == 0
            else "minus_projection"
        )

    loaded = _load_arrays(path, d)
    arrays = loaded["arrays"]
    if "source_data_version" in arrays:
        data = _load_compact_source(R,d,q,path,arrays)
        if data["source_scope"] != "manin":
            raise ValueError("this is an ideal image; use load_ideal_source_data")
        return data

    if (
        loaded["archive_prime"] is not None
        and (
            loaded["archive_prime"] != p
            or loaded["archive_exponent"] != m
        )
    ):
        raise ValueError(
            "the source-data archive precision does not match the "
            "coefficient ring"
        )
    recorded_degree = _degree_recorded_by_path(path)

    if (
        loaded["available_degrees"] is None
        and recorded_degree is not None
        and recorded_degree != d
    ):
        raise ValueError(
            f"the path records degree {recorded_degree}, not degree {d}"
        )

    required = {"order_exponents"}

    if projection_name is not None:
        required.add(projection_name)

    missing = sorted(required - arrays.keys())

    if missing:
        raise ValueError(
            "the source bundle is missing: " + ", ".join(missing)
        )

    order_exponents = tuple(
        ZZ(value) for value in arrays["order_exponents"]
    )

    if any(order < 1 or order > m for order in order_exponents):
        raise ValueError(
            "the stored cyclic orders are incompatible with the "
            "coefficient-ring precision"
        )

    scales = np.asarray(
        [int(p**(m - order)) for order in order_exponents],
        dtype=np.int64,
    )

    verification_projection = None

    if projection_name is None:
        selected_indices = tuple(range(len(order_exponents)))
    elif projection_mode == "coordinates":
        selected_indices = _coordinate_projection_indices(
            arrays[projection_name],
            scales,
            modulus,
        )
    else:
        selected_indices = tuple(range(len(order_exponents)))
        full_moduli = tuple(
            p**order for order in order_exponents
        )
        verification_projection = _decode_signed_hecke_matrix(
            arrays[projection_name],
            selected_indices,
            scales,
            full_moduli,
            modulus,
        )

        if not mixed_matrix_is_zero(
            verification_projection**2
            - verification_projection,
            full_moduli,
        ):
            raise ArithmeticError(
                "the stored signed projection is not idempotent"
            )

    selected_exponents = tuple(
        order_exponents[index]
        for index in selected_indices
    )
    coordinate_moduli = tuple(
        p**order for order in selected_exponents
    )
    hecke_matrices = {}

    for name, encoded in arrays.items():
        match = re.fullmatch(r"T(\d+)_rows", name)

        if not match:
            continue

        n = ZZ(match.group(1))
        decoded = _decode_signed_hecke_matrix(
            encoded,
            selected_indices,
            scales,
            coordinate_moduli,
            modulus,
        )
        hecke_matrices[n] = {
            "matrix": decoded,
            "normalized_matrix": decoded,
            "coordinate_exponents": selected_exponents,
            "coordinate_moduli": coordinate_moduli,
            "base_ring": R,
            "source": "runner_replay_bundle",
        }

    if not hecke_matrices:
        raise ValueError("the source bundle contains no Hecke matrices")

    if verification_projection is not None:
        for n, hecke_data in hecke_matrices.items():
            Tn = hecke_data["normalized_matrix"]

            if not mixed_matrix_is_zero(
                verification_projection*Tn
                - Tn*verification_projection,
                coordinate_moduli,
            ):
                raise ArithmeticError(
                    f"the stored signed projection does not commute "
                    f"with T_{n}"
                )

    rank = len(selected_indices)

    answer = {
        **arithmetic,
        "d": d,
        "q": q,
        "sign": sign,
        "presentation": None,
        "coordinates": {
            "surviving_indices": tuple(range(rank)),
            "surviving_exponents": selected_exponents,
            "coordinate_moduli": coordinate_moduli,
            "quotient_is_free": all(order == m for order in selected_exponents),
        },
        "source_backend": "runner_replay_bundle",
        "source_path": str(path),
        "source_sha256": _sha256(path),
        "original_bundle_sha256": loaded[
            "original_bundle_sha256"
        ],
        "available_degrees": loaded["available_degrees"],
        "ambient_order_exponents": order_exponents,
        "selected_ambient_indices": selected_indices,
        "archived_hecke_matrices": hecke_matrices,
    }

    if verification_projection is not None:
        answer.update({
            "source_scope": "image_of_archived_signed_projection",
            "verification_projection": verification_projection,
            "verification_generators": verification_projection,
        })

    return answer


# Legacy compact (9,T2) sources. Decoding checks the finite module/action
# encoding, not its identification with a Manin ideal image.


def _load_legacy_ideal_source_data(R, d, q, path, archive):
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


def _load_compact_source(R, d, q, path, arrays):
    """Validate v3 full/ideal sources. Structural decoding is not a Manin replay."""
    arithmetic = _prime_power_data(R)
    p, m = arithmetic["p"], arithmetic["m"]
    if p == 2 and q != 0:
        raise ValueError("p=2 requires the unsplit source and q=0")
    if np.asarray(arrays["source_data_version"]).tolist() != [3]:
        raise ValueError("unsupported compact source version")
    encoded = arrays["metadata_json"]
    if encoded.ndim != 1 or encoded.dtype != np.dtype('uint8'):
        raise ValueError("metadata_json must be an unsigned byte vector")
    meta = json.loads(encoded.tobytes().decode('utf-8'))
    if (meta["prime"],meta["exponent"],meta["degree"]) != (p,m,d):
        raise ValueError("source arithmetic or degree mismatch")
    scope = meta["source_scope"]
    if scope not in ("manin","ideal_image") or (scope == "ideal_image") != isinstance(meta["ideal"],dict):
        raise ValueError("invalid source scope or ideal metadata")
    indices = tuple(ZZ(n) for n in meta["hecke_indices"])
    if not indices or len(set(indices)) != len(indices) or any(n<=0 or n%p==0 for n in indices):
        raise ValueError("invalid Hecke indices")
    orientations = meta["orientations"]
    if len(set(orientations)) != len(orientations) or any(
        not isinstance(t,int) or t<0 or t>=p-1 for t in orientations
    ):
        raise ValueError("invalid orientations")
    orientation = int(q % (p-1))
    # Full modules depend only on the sign. General ideal images need the
    # actual twist, not merely its parity; never substitute the wrong image.
    if orientation not in orientations and scope == "manin":
        orientation = next((t for t in orientations if t%2==orientation%2), -1)
    if orientation not in orientations:
        raise ValueError("the requested ideal orientation is not stored")
    prefix = f"q{orientation}"
    orders = arrays[prefix+"_order_exponents"]
    if orders.ndim != 1 or orders.dtype.kind != 'u':
        raise ValueError("invalid cyclic exponent encoding")
    exponents = tuple(ZZ(e) for e in orders)
    if any(e<1 or e>m for e in exponents):
        raise ValueError("invalid cyclic order")
    rank = len(exponents)
    moduli = tuple(p**e for e in exponents)
    actions = {}
    for n in indices:
        values = arrays[prefix+f"_T{n}"]
        if values.dtype.kind != 'u' or values.shape != (rank,rank):
            raise ValueError("invalid action encoding/shape")
        for j,order in enumerate(moduli):
            if np.any(values[:,j] >= int(order)):
                raise ValueError("action not reduced modulo target cyclic orders")
        T = matrix(R,rank,rank,[int(v) for v in values.flat])
        if not mixed_endomorphism_is_well_defined(T,moduli):
            raise ValueError("action is not a mixed endomorphism")
        actions[n] = {"matrix":T,"normalized_matrix":T,"coordinate_exponents":exponents,
                      "coordinate_moduli":moduli,"base_ring":R}
    return {**arithmetic,"d":ZZ(d),"q":ZZ(q),"sign":None if p==2 else (-1)**q,
            "source_scope":scope,"ideal":meta["ideal"],"source_metadata":meta,
            "source_path":str(path),"source_sha256":_sha256(str(path)),"presentation":None,
            "coordinates":{"surviving_indices":tuple(range(rank)),"surviving_exponents":exponents,
                           "coordinate_moduli":moduli,"quotient_is_free":all(e==m for e in exponents)},
            "archived_hecke_matrices":actions}


def load_ideal_source_data(R,d,q,path):
    """Load a generic v3 ideal source or an unchanged legacy (9,T2)/2187 archive.

    Ideal generators are evaluated in orientation q. Their stored Hecke
    matrices are untwisted; the notebook verifier supplies the twist once.
    Terminal divisibility and all witnesses are interpreted inside IM.
    """
    d,q = _validate_degree_and_orientation(d,q)
    arrays = _load_arrays(Path(path),d)["arrays"]
    if "ideal_source_version" in arrays:
        return _load_legacy_ideal_source_data(R,d,q,path,arrays)
    if "source_data_version" not in arrays:
        raise ValueError("expected an ideal-image archive, not a full-source bundle")
    data = _load_compact_source(R,d,q,Path(path),arrays)
    if data["source_scope"] != "ideal_image":
        raise ValueError("the archive describes the full module, not an ideal image")
    return data

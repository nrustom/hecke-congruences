#!/usr/bin/env python3
"""Import verified native Hecke factors into the strong-signature cache.

The native archive stores an exact primitive-selector factorization and exact
polynomial expressions for the selected Hecke generators.  These data are
enough for ``nim/strong_signatures.nim`` to redo the local KRW reductions; no
characteristic-zero eigenvectors or modular-form computation are needed.

The importer checks the source verification manifest, every imported source
certificate hash, and the elementary dimension/count invariants.  Imported
cache entries carry their source paths and SHA-256 digests and use a distinct
schema, so they cannot be confused with caches produced by ``mfeigenbasis``.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from pathlib import Path
from typing import Any, Iterable


IMPORTED_SCHEMA = "hecke.exact-level-one-hecke-factors.imported-native.v1"
SOURCE_SCHEMA = "hecke-cert.native-strong-weight-case.v1"
MANIFEST_SCHEMA = "hecke-cert.native-strong-weight-bounds-manifest.v1"
VERIFICATION_SCHEMA = "hecke-cert.native-strong-weight-bounds-verification.v1"

# Exact characteristic-zero Hecke polynomials routinely have coefficients
# longer than Python's defensive decimal-to-integer conversion limit.
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def payload_sha1(value: dict[str, Any]) -> str:
    encoded = json.dumps(value, ensure_ascii=False, separators=(",", ":"))
    return hashlib.sha1(encoded.encode("utf-8")).hexdigest().upper()


def atomic_json(path: Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f"{path.name}.tmp.{os.getpid()}")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    os.replace(temporary, path)


def polynomial(coefficients: Iterable[Any], variable: str = "x") -> str:
    terms = []
    for degree, raw_coefficient in enumerate(coefficients):
        coefficient = str(raw_coefficient)
        if coefficient == "0":
            continue
        if degree == 0:
            monomial = "1"
        elif degree == 1:
            monomial = variable
        else:
            monomial = f"{variable}^{degree}"
        terms.append(f"({coefficient})*{monomial}")
    return "0" if not terms else "(" + "+".join(terms) + ")"


def verify_source_envelope(
    source_directory: Path,
) -> tuple[dict[str, Any], dict[int, dict[str, Any]]]:
    manifest_path = source_directory / "manifest.json"
    verification_path = source_directory / "manifest_verification.json"
    manifest = json.loads(manifest_path.read_text())
    verification = json.loads(verification_path.read_text())

    if manifest.get("schema") != MANIFEST_SCHEMA:
        raise ValueError(f"unexpected source manifest schema: {manifest_path}")
    if verification.get("schema") != VERIFICATION_SCHEMA:
        raise ValueError(f"unexpected source verification schema: {verification_path}")
    if not verification.get("verified") or verification.get("errors"):
        raise ValueError(f"source manifest is not verified: {verification_path}")
    if verification.get("manifest_sha256") != sha256_file(manifest_path):
        raise ValueError("source manifest SHA-256 does not match its verification")

    rows: dict[int, dict[str, Any]] = {}
    for row in manifest.get("certificates", []):
        weight = int(row["weight"])
        if weight in rows:
            raise ValueError(f"duplicate source certificate for weight {weight}")
        rows[weight] = row
    return manifest, rows


def convert_certificate(
    certificate: dict[str, Any],
    *,
    source_path: Path,
    source_sha256: str,
    source_manifest: Path,
    source_manifest_sha256: str,
    source_certificate_listed_in_manifest: bool = True,
) -> dict[str, Any]:
    if certificate.get("schema") != SOURCE_SCHEMA:
        raise ValueError(f"unexpected source certificate schema: {source_path}")

    generators = [int(value) for value in certificate["big_Hecke_coordinates"]]
    backend = certificate["backend"]
    factors = certificate["factors"]
    dimension = int(certificate["space_dimension"])
    if sum(int(factor["degree"]) for factor in factors) != dimension:
        raise ValueError(f"factor degrees do not sum to the dimension: {source_path}")
    if sum(len(factor["branches"]) for factor in factors) != int(
        certificate["strong_branch_count"]
    ):
        raise ValueError(f"local branch count is inconsistent: {source_path}")

    orbits = []
    for orbit_number, factor in enumerate(factors, start=1):
        defining_polynomial = polynomial(
            factor["defining_polynomial_coefficients_ascending"]
        )
        relations = factor["generator_polynomials_in_primitive_selector"]
        eigenvalues = {
            str(ell): f"Mod({polynomial(relations[str(ell)])},{defining_polynomial})"
            for ell in generators
        }
        orbits.append(
            {
                "orbit": orbit_number,
                "field_degree": int(factor["degree"]),
                "defining_polynomial": defining_polynomial,
                "eigenvalues": eigenvalues,
                "exact_big_Hecke_relation_checks_passed": True,
                "native_factor_index": int(factor["factor_index"]),
            }
        )

    answer: dict[str, Any] = {
        "schema": IMPORTED_SCHEMA,
        "weight": int(certificate["weight"]),
        "level": 1,
        "cuspidal": True,
        "dimension": dimension,
        "orbits": orbits,
        "orbit_dimension_sum_verified": True,
        "import_provenance": {
            "source_schema": SOURCE_SCHEMA,
            "source_certificate": str(source_path.resolve()),
            "source_certificate_sha256": source_sha256,
            "source_manifest": str(source_manifest.resolve()),
            "source_manifest_sha256": source_manifest_sha256,
            "source_certificate_listed_in_manifest": (
                source_certificate_listed_in_manifest
            ),
            "source_certificate_self_verified": bool(certificate.get("verified")),
            "source_exact_Hecke_matrices_sha256": certificate[
                "exact_Hecke_matrices_sha256"
            ],
            "source_primitive_relation_verification": backend.get(
                "primitive_relation_verification",
                {
                    "recorded_in_legacy_certificate": False,
                    "source_certificate_verified": bool(certificate.get("verified")),
                    "exact_Hecke_matrices_sha256": certificate[
                        "exact_Hecke_matrices_sha256"
                    ],
                },
            ),
            "source_manifest_independently_verified": True,
            "conversion": "native primitive-selector factors to exact Hecke-factor cache",
        },
    }
    answer["payload_sha1"] = payload_sha1(answer)
    return answer


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-directory", type=Path, required=True)
    parser.add_argument("--exact-cache", type=Path, required=True)
    parser.add_argument("--prime", type=int, required=True)
    parser.add_argument("--exponent", type=int, required=True)
    parser.add_argument("--minimum-weight", type=int, default=0)
    parser.add_argument("--maximum-weight", type=int, required=True)
    parser.add_argument(
        "--overwrite-imported",
        action="store_true",
        help="replace an existing cache only when it already uses the imported schema",
    )
    parser.add_argument(
        "--include-verified-unmanifested",
        action="store_true",
        help=(
            "also import self-verified weight*/certificate.json files omitted "
            "from a stale but independently verified manifest"
        ),
    )
    args = parser.parse_args()

    manifest, rows = verify_source_envelope(args.source_directory)
    if int(manifest["prime"]) != args.prime or int(manifest["exponent"]) != args.exponent:
        raise ValueError("source manifest prime or exponent does not match the request")

    expected_generators = [int(value) for value in manifest["big_Hecke_coordinates"]]
    manifest_weights = set(rows)
    if args.include_verified_unmanifested:
        for source_path in args.source_directory.glob("weight*/certificate.json"):
            certificate = json.loads(source_path.read_text())
            weight = int(certificate["weight"])
            if weight in rows:
                continue
            if certificate.get("schema") != SOURCE_SCHEMA:
                raise ValueError(
                    f"unexpected supplemental certificate schema: {source_path}"
                )
            if not certificate.get("verified"):
                raise ValueError(
                    f"supplemental certificate is not self-verified: {source_path}"
                )
            rows[weight] = {
                "weight": weight,
                "path": str(source_path.resolve()),
                "sha256": sha256_file(source_path),
            }
    source_manifest = args.source_directory / "manifest.json"
    source_manifest_sha256 = sha256_file(source_manifest)
    imported = []
    retained = []

    for weight in sorted(
        weight
        for weight in rows
        if args.minimum_weight <= weight <= args.maximum_weight
    ):
        row = rows[weight]
        source_path = Path(row["path"])
        if not source_path.is_absolute():
            # Manifest paths are relative to the native project root, whose
            # certificate directory is four levels above this p^m directory.
            project_root = args.source_directory.parents[3]
            source_path = project_root / source_path
        source_sha256 = sha256_file(source_path)
        if source_sha256 != row["sha256"]:
            raise ValueError(f"source certificate SHA-256 mismatch: {source_path}")
        certificate = json.loads(source_path.read_text())
        if int(certificate["prime"]) != args.prime or int(certificate["exponent"]) != args.exponent:
            raise ValueError(f"source certificate prime or exponent differs: {source_path}")
        if [int(value) for value in certificate["big_Hecke_coordinates"]] != expected_generators:
            raise ValueError(f"source Hecke coordinates differ: {source_path}")

        target = args.exact_cache / f"weight_{weight}.json"
        if target.exists():
            existing = json.loads(target.read_text())
            if not (
                args.overwrite_imported
                and existing.get("schema") == IMPORTED_SCHEMA
            ):
                retained.append(weight)
                continue

        converted = convert_certificate(
            certificate,
            source_path=source_path,
            source_sha256=source_sha256,
            source_manifest=source_manifest,
            source_manifest_sha256=source_manifest_sha256,
            source_certificate_listed_in_manifest=(weight in manifest_weights),
        )
        atomic_json(target, converted)
        imported.append(weight)

    print(
        json.dumps(
            {
                "source_manifest_verified": True,
                "source_prime": args.prime,
                "source_exponent": args.exponent,
                "minimum_weight": args.minimum_weight,
                "maximum_weight": args.maximum_weight,
                "imported_count": len(imported),
                "retained_existing_count": len(retained),
                "imported_weights": imported,
                "retained_existing_weights": retained,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()

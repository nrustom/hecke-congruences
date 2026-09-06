#!/usr/bin/env python3
"""Generate the Lean transcription of the exact p=7 certificate polynomials."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent
SOURCE = ROOT.parent / "p7_mod49_relation_data.json"
TARGET = ROOT / "HeckeCongruences" / "PrimeSevenData.lean"


def family_name(relation: dict) -> str:
    family = relation["family"]
    if family == "compact_W_coordinate":
        return ".coordinate"
    if family == "projected_raw_digit_graph":
        return ".graphU" if relation["raw_digit"] == "U" else ".graphV"
    raise ValueError(f"unknown relation family: {family}")


def term_text(term: dict) -> str:
    return (
        f"⟨{term['coefficient']}, {term['W3_power']}, "
        f"{term['W29_power']}, {term['J_power']}⟩"
    )


def main() -> None:
    raw = SOURCE.read_bytes()
    data = json.loads(raw)
    digest = hashlib.sha256(raw).hexdigest()

    lines = [
        "/-!",
        "# Exact `p = 7` relation data",
        "",
        "This file is generated from `p7_mod49_relation_data.json` by",
        "`generate_prime_seven_data.py`.  It transcribes every one of the",
        "210 polynomials used in the manuscript: 126 coordinate relations and",
        "84 raw-digit graph relations.",
        "The archived `weightResidueMod42` is the modular-form weight residue",
        "`k`; the manuscript's coefficient-degree residue is `r=k-2`.",
        "In each term, `QPower`, `GPower`, and `JPower` are respectively the",
        "powers of `Q_j(T₃)`, `G_j(T₃,T₂₉)`, and the projected divided",
        "operator `E^6 U_c` or `E^6 V` (absent from coordinate relations).",
        "After reduction on the selected branch, the last variable is the raw digit.",
        "-/",
        "",
        "namespace HeckeCongruences.PrimeSevenData",
        "",
        "inductive RelationFamily where",
        "  | coordinate",
        "  | graphU",
        "  | graphV",
        "  deriving DecidableEq, Repr",
        "",
        "structure RelationTerm where",
        "  coefficient : Nat",
        "  QPower : Nat",
        "  GPower : Nat",
        "  JPower : Nat",
        "  deriving DecidableEq, Repr",
        "",
        "structure Relation where",
        "  weightResidueMod42 : Nat",
        "  centre : Nat",
        "  family : RelationFamily",
        "  label : String",
        "  selectorPower : Nat",
        "  relationPower : Nat",
        "  terms : List RelationTerm",
        "  deriving DecidableEq, Repr",
        "",
        "structure RawPoint where",
        "  Q : Nat",
        "  G : Nat",
        "  U : Nat",
        "  V : Nat",
        "  deriving DecidableEq, Repr",
        "",
        "structure BranchData where",
        "  weightResidueMod42 : Nat",
        "  centre : Nat",
        "  allowedRawPoints : List RawPoint",
        "  deriving DecidableEq, Repr",
        "",
        f'def sourceSHA256 : String := "{digest}"',
        "",
        "def relations : List Relation := [",
    ]

    for relation in data["relations"]:
        selector_power = relation.get(
            "selector_power", data["fixed_selector_power_for_W_relations"]
        )
        terms = ", ".join(term_text(term) for term in relation["terms"])
        label = json.dumps(relation["label"])
        lines.extend(
            [
                "  { weightResidueMod42 := "
                f"{relation['weight_residue_mod42']}, centre := {relation['centre']},",
                f"    family := {family_name(relation)}, label := {label},",
                f"    selectorPower := {selector_power}, relationPower := "
                f"{data['fixed_relation_power']},",
                f"    terms := [{terms}] }},",
            ]
        )
    lines.extend(["]", "", "def branches : List BranchData := ["])

    def branch_key(item: tuple[str, dict]) -> tuple[int, int]:
        residue, centre = item[0].split(":")
        return int(residue), int(centre)

    for key, branch in sorted(data["branches"].items(), key=branch_key):
        residue, centre = map(int, key.split(":"))
        points = ", ".join("⟨" + ", ".join(map(str, point)) + "⟩"
                           for point in branch["allowed_raw_points"])
        lines.append(
            f"  ⟨{residue}, {centre}, [{points}]⟩,"
        )
    lines.extend(
        [
            "]",
            "",
            "set_option maxRecDepth 4096",
            "",
            "theorem relation_count : relations.length = 210 := by decide",
            "",
            "theorem relation_powers : ∀ relation ∈ relations, relation.relationPower = 3 := by",
            "  decide",
            "",
            "theorem selector_powers : ∀ relation ∈ relations, relation.selectorPower = 6 := by",
            "  decide",
            "",
            "theorem branch_count : branches.length = 63 := by decide",
            "",
            "end HeckeCongruences.PrimeSevenData",
            "",
        ]
    )
    TARGET.write_text("\n".join(lines))


if __name__ == "__main__":
    main()

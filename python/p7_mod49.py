"""Direct Sage replay of the modulo-49 selector relations."""

from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path

import numpy as np

from identity_verification import _hecke_matrix_on_source
from sage.all import GF, PolynomialRing


P = 7
EXPONENT = 3
MODULUS = P**EXPONENT
TWIST_EXPONENT = P**(EXPONENT - 1)
DEGREE_SHIFT = 2 * P
CENTRES = {
    0: (0, 3, 4),
    2: (0, 2, 5),
    4: (0, 1, 6),
}
SELECTOR_ROOTS = {
    0: (3, 4),
    2: (2, 5),
    4: (1, 6),
}
TANGENT_POLYNOMIALS = {
    0: (0, 7, 4, 7, 45, 7, 1),
    2: (0, 14, 9, 0, 6, 42, 1),
    4: (0, 28, 1, 14, 47, 7, 1),
}
SOURCE_MATHEMATICS_SHA256 = (
    "8bc8a70a04c22926fcca77a7336d122c"
    "bd3a841142ffd9538edea25740a6967a"
)


def load_p7_mod49_relations(path=None):
    """Load the fixed selector and raw-digit graph polynomials."""
    if path is None:
        path = Path(__file__).resolve().parent.parent / "p7_mod49_relation_data.json"

    with Path(path).open() as stream:
        value = json.load(stream)

    if value.get("schema") != "hecke-congruences.p7-mod49-relations.v1":
        raise ValueError("unexpected modulo-49 relation-data schema")

    if value.get("relation_count") != 210:
        raise ValueError("the modulo-49 relation inventory is incomplete")

    if (
        value.get("source_mathematics_sha256")
        != SOURCE_MATHEMATICS_SHA256
    ):
        raise ValueError("the modulo-49 relation inventory has changed")

    return value


def _p7_mod49_polynomial_bundle(raw_data):
    """Convert the sparse archive data to the manuscript polynomials."""
    field = GF(P)
    coordinate_ring = PolynomialRing(
        field,
        2,
        names=("X", "Y"),
    )
    X, Y = coordinate_ring.gens()
    u_graph_ring = PolynomialRing(
        field,
        3,
        names=("X", "Y", "U"),
    )
    v_graph_ring = PolynomialRing(
        field,
        3,
        names=("X", "Y", "V"),
    )
    X_U, Y_U, U = u_graph_ring.gens()
    X_V, Y_V, V = v_graph_ring.gens()
    records = []
    by_label = {}
    by_branch = {}
    coordinate_relations = {}
    u_graph_relations = {}
    v_graph_relations = {}
    phi = {}
    psi = {}
    coordinate_numbers = {}

    for relation in raw_data["relations"]:
        family = relation["family"]
        raw_digit = relation.get("raw_digit")

        if family == "compact_W_coordinate":
            polynomial_ring = coordinate_ring
            first_variable, second_variable = X, Y
            third_variable = None
        elif raw_digit == "U":
            polynomial_ring = u_graph_ring
            first_variable, second_variable = X_U, Y_U
            third_variable = U
        elif raw_digit == "V":
            polynomial_ring = v_graph_ring
            first_variable, second_variable = X_V, Y_V
            third_variable = V
        else:
            raise ValueError("unknown modulo-49 relation family")

        polynomial = polynomial_ring.zero()

        for term in relation["terms"]:
            monomial = (
                field(term["coefficient"])
                * first_variable**int(term["W3_power"])
                * second_variable**int(term["W29_power"])
            )

            if third_variable is not None:
                monomial *= third_variable**int(
                    term["J_power"]
                )
            elif int(term["J_power"]):
                raise ValueError(
                    "a coordinate relation contains a raw digit"
                )

            polynomial += monomial

        degree_residue = (
            int(relation["weight_residue_mod42"]) - 2
        ) % 42
        centre = int(relation["centre"])

        record = {
            key: value
            for key, value in relation.items()
            if key not in {"terms", "weight_residue_mod42"}
        }
        record["degree_residue_mod42"] = degree_residue
        record["polynomial"] = polynomial
        records.append(record)
        by_label[record["label"]] = polynomial
        branch = (degree_residue, centre)
        by_branch.setdefault(branch, []).append(record)

        if family == "compact_W_coordinate":
            number = coordinate_numbers.get(branch, 0) + 1
            coordinate_numbers[branch] = number
            record["nu"] = number
            coordinate_relations[
                (degree_residue, centre, number)
            ] = polynomial
        elif raw_digit == "U":
            u_graph_relations[branch] = polynomial
            phi[branch] = -coordinate_ring(
                polynomial(X, Y, 0)
            )
        elif raw_digit == "V":
            v_graph_relations[branch] = polynomial
            psi[branch] = -coordinate_ring(
                polynomial(X, Y, 0)
            )

    if any(number != 2 for number in coordinate_numbers.values()):
        raise ValueError(
            "each modulo-49 branch must have exactly two "
            "coordinate relations"
        )

    return {
        "schema": "hecke-congruences.p7-mod49-sage-polynomials.v1",
        "source_mathematics_sha256": raw_data[
            "source_mathematics_sha256"
        ],
        "coefficient_field": field,
        "coordinate_ring": coordinate_ring,
        "coordinate_generators": (X, Y),
        "U_graph_ring": u_graph_ring,
        "U_graph_generators": (X_U, Y_U, U),
        "V_graph_ring": v_graph_ring,
        "V_graph_generators": (X_V, Y_V, V),
        "fixed_relation_power": int(
            raw_data["fixed_relation_power"]
        ),
        "fixed_selector_power_for_W_relations": int(
            raw_data["fixed_selector_power_for_W_relations"]
        ),
        "fixed_selector_power_for_J_graph_relations": int(
            raw_data[
                "fixed_selector_power_for_J_graph_relations"
            ]
        ),
        "relation_count": len(records),
        "coordinate_relation_count": int(
            raw_data["coordinate_relation_count"]
        ),
        "joint_relation_count": int(
            raw_data["joint_relation_count"]
        ),
        "relations": records,
        "by_label": by_label,
        "R": coordinate_relations,
        "U_minus_phi": u_graph_relations,
        "V_minus_psi": v_graph_relations,
        "phi": phi,
        "psi": psi,
        "by_branch": {
            branch: tuple(branch_records)
            for branch, branch_records in by_branch.items()
        },
    }


def p7_mod49_relation_polynomials(path=None):
    """
    Return the 210 classification relations as Sage polynomials.

    This follows the notation of the modulo-49 chapter.  The dictionary
    ``R`` contains the coordinate polynomials

        R[r,c,nu] = R_{r,c}^{(nu)}(X,Y) in F_7[X,Y],

    where ``r`` is the coefficient-degree residue modulo 42 and
    ``nu`` is 1 or 2.  The dictionaries ``phi`` and ``psi`` contain
    the affine polynomials phi_{r,c}(X,Y) and psi_{r,c}(X,Y).
    Equivalently, ``U_minus_phi`` and ``V_minus_psi`` contain the
    explicit graph polynomials

        U - phi_{r,c}(X,Y),    V - psi_{r,c}(X,Y).

    The original archive label is retained in each record solely for
    binding the Sage polynomial to the stored certificate data.
    """
    return _p7_mod49_polynomial_bundle(
        load_p7_mod49_relations(path)
    )


@dataclass(frozen=True)
class _Source:
    order_exponents: tuple[int, ...]

    @property
    def dimension(self):
        return len(self.order_exponents)

    @property
    def scales(self):
        return np.asarray(
            [
                P ** (EXPONENT - order)
                for order in self.order_exponents
            ],
            dtype=np.int64,
        )

    @property
    def orders(self):
        return np.asarray(
            [P**order for order in self.order_exponents],
            dtype=np.int64,
        )


def _order_exponent(modulus):
    modulus = int(modulus)
    exponent = 0

    while modulus > 1 and modulus % P == 0:
        modulus //= P
        exponent += 1

    if modulus != 1 or not 1 <= exponent <= EXPONENT:
        raise ValueError("unexpected mixed cyclic modulus")

    return exponent


def _generators(source):
    return np.diag(source.scales).astype(np.int64)


def _encode_operator(source, operator):
    if operator.nrows() != source.dimension:
        raise ValueError("operator dimension does not match the source")

    return np.asarray(
        [
            [
                int(operator[row, column])
                * int(source.scales[column])
                % MODULUS
                for column in range(source.dimension)
            ]
            for row in range(source.dimension)
        ],
        dtype=np.int64,
    )


def _add(*vectors):
    answer = np.zeros_like(
        np.asarray(vectors[0], dtype=np.int64)
    )

    for value in vectors:
        answer = (
            answer
            + np.asarray(value, dtype=np.int64)
        ) % MODULUS

    return answer


def _scale(vectors, scalar):
    return (
        np.asarray(vectors, dtype=np.int64)
        * int(scalar)
        % MODULUS
    )


def _apply(source, vectors, operator):
    vectors = np.asarray(vectors, dtype=np.int64)

    if len(vectors) == 0:
        return vectors.copy()

    if np.any(vectors % source.scales):
        raise ArithmeticError("invalid mixed cyclic encoding")

    coefficients = (
        vectors // source.scales
    ) % source.orders

    return (
        coefficients
        @ np.asarray(operator, dtype=np.int64)
        % MODULUS
    )


def _divide(source, vectors, exponent):
    vectors = np.asarray(vectors, dtype=np.int64)

    if len(vectors) == 0:
        return vectors.copy()

    coefficients = (
        vectors // source.scales
    ) % source.orders
    divisors = np.asarray(
        [
            P ** min(exponent, order)
            for order in source.order_exponents
        ],
        dtype=np.int64,
    )

    if np.any(coefficients % divisors):
        return None

    quotient = coefficients // (P**exponent)

    for column, order in enumerate(source.order_exponents):
        if exponent >= order:
            quotient[:, column] = 0

    return quotient * source.scales % MODULUS


def _polynomial_operator(source, operator, coefficients):
    identity = _generators(source)
    result = np.zeros_like(identity)
    operator_power = identity

    for index, coefficient in enumerate(coefficients):
        if coefficient:
            result = _add(
                result,
                _scale(operator_power, coefficient),
            )

        if index + 1 < len(coefficients):
            operator_power = _apply(
                source,
                operator_power,
                operator,
            )

    return result


def _t29_difference(source, t3, t29, alpha, beta):
    identity = _generators(source)
    first = _add(t3, _scale(identity, -beta))
    second = _add(t3, _scale(identity, -alpha))
    cubic = _apply(source, first, second)
    cubic = _apply(source, cubic, t3)

    return _add(
        t29,
        _scale(identity, -2),
        _scale(cubic, -1),
    )


def _multiply_polynomials(left, right):
    result = [0] * (len(left) + len(right) - 1)

    for i, first in enumerate(left):
        for j, second in enumerate(right):
            result[i + j] = (
                result[i + j]
                + first * second
            ) % P

    return result


def _lagrange(centre, centres):
    numerator = [1]
    denominator = 1

    for other in centres:
        if other == centre:
            continue

        numerator = _multiply_polynomials(
            numerator,
            [(-other) % P, 1],
        )
        denominator = denominator * (centre - other) % P

    inverse = pow(denominator, -1, P)

    return [
        inverse * coefficient % P
        for coefficient in numerator
    ]


def _multiply_terms(left, right):
    result = {}

    for first in left:
        for second in right:
            powers = tuple(
                int(first[key]) + int(second[key])
                for key in (
                    "W3_power",
                    "W29_power",
                    "J_power",
                )
            )
            result[powers] = (
                result.get(powers, 0)
                + int(first["coefficient"])
                * int(second["coefficient"])
            ) % P

    return [
        {
            "W3_power": powers[0],
            "W29_power": powers[1],
            "J_power": powers[2],
            "coefficient": coefficient,
        }
        for powers, coefficient in sorted(result.items())
        if coefficient
    ]


def _power_terms(terms, exponent):
    answer = terms

    for _ in range(exponent - 1):
        answer = _multiply_terms(answer, terms)

    return answer


def _terms_from_sage_polynomial(polynomial):
    """Return the private three-coordinate monomial encoding."""
    number_of_variables = polynomial.parent().ngens()

    if number_of_variables not in {2, 3}:
        raise ValueError(
            "a modulo-49 relation must have two or three variables"
        )

    return [
        {
            "W3_power": int(exponents[0]),
            "W29_power": int(exponents[1]),
            "J_power": (
                int(exponents[2])
                if number_of_variables == 3
                else 0
            ),
            "coefficient": int(coefficient) % P,
        }
        for exponents, coefficient in sorted(
            polynomial.dict().items()
        )
        if coefficient
    ]


def _solve_mod7(matrix, target):
    matrix = np.asarray(matrix, dtype=np.int64) % P
    target = (
        np.asarray(target, dtype=np.int64)
        .reshape((-1, 1))
        % P
    )
    augmented = np.concatenate((matrix, target), axis=1)
    cursor = 0
    pivots = []

    for column in range(matrix.shape[1]):
        pivot = next(
            (
                row
                for row in range(cursor, matrix.shape[0])
                if augmented[row, column]
            ),
            None,
        )

        if pivot is None:
            continue

        augmented[[cursor, pivot]] = augmented[[pivot, cursor]]
        augmented[cursor] = (
            augmented[cursor]
            * pow(
                int(augmented[cursor, column]),
                -1,
                P,
            )
            % P
        )

        for row in range(matrix.shape[0]):
            if row != cursor and augmented[row, column]:
                augmented[row] = (
                    augmented[row]
                    - augmented[row, column]
                    * augmented[cursor]
                ) % P

        pivots.append(column)
        cursor += 1

    if any(
        not np.any(row[:-1]) and row[-1]
        for row in augmented
    ):
        return None

    solution = np.zeros(matrix.shape[1], dtype=np.int64)

    for row, column in enumerate(pivots):
        solution[column] = augmented[row, -1]

    return solution


def _divided_action(source, current, numerator, exponent, previous_division=0):
    product = _apply(source, current, numerator)
    quotient = _divide(source, product, exponent)

    if quotient is not None:
        return quotient

    # Adding 7-torsion preserves a preceding positive-power division,
    # but the prescribed starting vector must remain fixed.
    if exponent != 1 or previous_division < 1:
        return None

    torsion = (
        np.eye(source.dimension, dtype=np.int64)
        * P ** (EXPONENT - 1)
    )
    effect = _apply(source, torsion, numerator)
    effect_obstruction = (
        effect // source.scales
    ) % source.orders % P
    product_obstruction = (
        product // source.scales
    ) % source.orders % P
    corrected = np.asarray(current, dtype=np.int64).copy()

    for row, obstruction in enumerate(product_obstruction):
        if not np.any(obstruction):
            continue

        solution = _solve_mod7(
            effect_obstruction.T,
            -obstruction,
        )

        if solution is None:
            return None

        corrected[row] = (
            corrected[row]
            + solution @ torsion
        ) % MODULUS

    return _divide(
        source,
        _apply(source, corrected, numerator),
        exponent,
    )


def _monomial(source, selected, numerators, divisions, powers):
    current = selected
    previous_division = 0

    for index in (2, 1, 0):
        for _ in range(powers[index]):
            current = _divided_action(
                source,
                current,
                numerators[index],
                divisions[index],
                previous_division=previous_division,
            )

            if current is None:
                return None

            previous_division = divisions[index]

    return current


def _terminal_ambiguity_suffices(source, value, terms, divisions):
    obstruction = (value // source.scales) % P
    bad = np.argwhere(obstruction)

    if not len(bad):
        return True

    maximum_order = max(
        source.order_exponents[int(column)]
        for _, column in bad
    )

    # Monomials are applied in order J, W29, W3. Only the kernel of
    # the last division can be added freely to the terminal witness.
    for term in terms:
        if not int(term["coefficient"]) % P:
            continue
        for key, exponent in zip(
            ("W3_power", "W29_power", "J_power"), divisions
        ):
            if int(term[key]):
                if exponent >= maximum_order:
                    return True
                break

    return False


def _relation_holds(source, selected, numerators, divisions, terms):
    result = np.zeros_like(selected)
    cache = {}

    for term in terms:
        powers = tuple(
            int(term[key])
            for key in (
                "W3_power",
                "W29_power",
                "J_power",
            )
        )

        if powers not in cache:
            cache[powers] = _monomial(
                source,
                selected,
                numerators,
                divisions,
                powers,
            )

        if cache[powers] is None:
            return False

        result = _add(
            result,
            _scale(
                cache[powers],
                term["coefficient"],
            ),
        )

    if _divide(source, result, 1) is not None:
        return True

    return _terminal_ambiguity_suffices(
        source,
        result,
        terms,
        divisions,
    )


def verify_p7_mod49_selector_identities(
    data,
    relation_data=None,
    check_descent=False,
):
    """
    Verify all selector and raw-digit graph identities in one case.

    The prepared source must be M_d^((-1)^q) over Z/343Z.  In the
    notation of the manuscript, the relation residue is the twisted
    coefficient-degree residue

        r = d + 14*q modulo 42.

    For each of the three residual T_3 centres, this replays the fixed
    selector-sixth-power and relation-cube staged monomial tree from
    the modulo-49 classification certificate.

    The archived graph variable is the projected raw digit
    E(T_3)**6 * (T_3-c)/7 or E(T_3)**6 * (T_29-2)/7.  The starting
    vectors also carry E(T_3)**6.  Thus the U graph checks
    E**6 * (E**6*U - phi(Q,G))**3, and similarly for V.
    """
    if data["p"] != P or data["m"] != EXPONENT:
        raise ValueError(
            "the selector identities require a source over Z/343Z"
        )

    if relation_data is None:
        relation_data = p7_mod49_relation_polynomials()

    if relation_data.get("schema") == (
        "hecke-congruences.p7-mod49-relations.v1"
    ):
        relation_data = _p7_mod49_polynomial_bundle(
            relation_data
        )

    if relation_data.get("schema") != (
        "hecke-congruences.p7-mod49-sage-polynomials.v1"
    ):
        raise ValueError(
            "expected the modulo-49 Sage polynomial bundle"
        )

    coordinates = data["coordinates"]
    degree_residue = (
        data["d"]
        + DEGREE_SHIFT * data["q"]
    ) % 42
    residue_mod6 = degree_residue % 6

    if not coordinates["surviving_indices"]:
        return {
            "degree": data["d"],
            "orientation": data["q"],
            "sign": data["sign"],
            "degree_residue_mod42": degree_residue,
            "rank": 0,
            "branches": [],
            "passed": True,
            "vacuous": True,
        }

    T3_data = _hecke_matrix_on_source(
        3,
        data,
        check_descent,
    )
    T29_data = _hecke_matrix_on_source(
        29,
        data,
        check_descent,
    )
    moduli = tuple(T3_data["coordinate_moduli"])

    if tuple(T29_data["coordinate_moduli"]) != moduli:
        raise ArithmeticError(
            "T_3 and T_29 use incompatible mixed coordinates"
        )

    source = _Source(
        tuple(_order_exponent(value) for value in moduli)
    )
    twist3 = pow(
        3,
        TWIST_EXPONENT * data["q"],
        MODULUS,
    )
    twist29 = pow(
        29,
        TWIST_EXPONENT * data["q"],
        MODULUS,
    )
    t3 = _encode_operator(
        source,
        twist3 * T3_data["normalized_matrix"],
    )
    t29 = _encode_operator(
        source,
        twist29 * T29_data["normalized_matrix"],
    )
    identity = _generators(source)
    projection = data.get("verification_projection")

    if projection is None:
        roots = identity
    else:
        roots = _encode_operator(source, projection)
        roots = roots[np.any(roots != 0, axis=1)]

    w3 = _polynomial_operator(
        source,
        t3,
        TANGENT_POLYNOMIALS[residue_mod6],
    )
    alpha, beta = SELECTOR_ROOTS[residue_mod6]
    w29 = _t29_difference(
        source,
        t3,
        t29,
        alpha,
        beta,
    )
    relation_power = int(
        relation_data["fixed_relation_power"]
    )
    branch_records = []

    for centre in CENTRES[residue_mod6]:
        selector = _polynomial_operator(
            source,
            t3,
            _lagrange(
                centre,
                CENTRES[residue_mod6],
            ),
        )
        selected = roots
        selector_operator = identity

        for _ in range(6):
            selected = _apply(
                source,
                selected,
                selector,
            )
            selector_operator = _apply(
                source,
                selector_operator,
                selector,
            )

        relations = [
            relation
            for relation in relation_data["relations"]
            if int(relation["degree_residue_mod42"])
            == degree_residue
            and int(relation["centre"]) == centre
        ]
        relation_records = []

        for relation in relations:
            if relation["family"] == "projected_raw_digit_graph":
                if relation["raw_digit"] == "U":
                    raw = _add(
                        t3,
                        _scale(identity, -centre),
                    )
                elif relation["raw_digit"] == "V":
                    raw = _add(
                        t29,
                        _scale(identity, -2),
                    )
                else:
                    raise ValueError("unknown raw-digit label")

                joint = _apply(
                    source,
                    selector_operator,
                    raw,
                )
            else:
                joint = np.zeros_like(identity)

            terms = _terms_from_sage_polynomial(
                relation["polynomial"]**relation_power
            )
            passed = _relation_holds(
                source,
                selected,
                (w3, w29, joint),
                (2, 1, 1),
                terms,
            )
            relation_records.append({
                "label": relation["label"],
                "family": relation["family"],
                "passed": bool(passed),
            })

        branch_records.append({
            "centre": centre,
            "relations": relation_records,
            "passed": all(
                relation["passed"]
                for relation in relation_records
            ),
        })

    return {
        "degree": data["d"],
        "orientation": data["q"],
        "sign": data["sign"],
        "degree_residue_mod42": degree_residue,
        "rank": source.dimension,
        "branches": branch_records,
        "passed": all(
            branch["passed"]
            for branch in branch_records
        ),
        "vacuous": False,
    }

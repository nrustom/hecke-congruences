from sage.all import (
    ZZ,
    PolynomialRing,
    diagonal_matrix,
    factor,
    gcd,
    identity_matrix,
    matrix,
    pari,
    vector,
)

from pari_howell import pari_howell_row_span


def symmetric_power_action(
    gamma,
    degree,
    coefficient_ring,
    input_indices=None,
    output_indices=None,
):
    """
    Matrix of the right action on the ordered basis

        X^i * Y^(degree-i),  i = 0, ..., degree.

    If input_indices or output_indices are supplied, return only the
    indicated input rows or output columns.
    """
    degree = ZZ(degree)
    R = coefficient_ring

    if degree < 0:
        raise ValueError("degree must be nonnegative")

    def validated_indices(indices, label):
        if indices is None:
            return tuple(range(degree + 1))

        indices = tuple(ZZ(j) for j in indices)

        if len(set(indices)) != len(indices):
            raise ValueError(f"{label} indices must be distinct")

        if any(j < 0 or j > degree for j in indices):
            raise ValueError(
                f"a {label} index lies outside 0,...,degree"
            )

        return indices

    input_indices = validated_indices(input_indices, "input")
    output_indices = validated_indices(output_indices, "output")

    polynomial_ring = PolynomialRing(
        R,
        names=("X", "Y")
    )
    X, Y = polynomial_ring.gens()

    gamma = matrix(R, gamma)
    a, b, c, e = gamma.list()

    rows = []

    for i in input_indices:
        image = (
            (a*X + b*Y)**i
            * (c*X + e*Y)**(degree-i)
        )
        rows.append([
            image.monomial_coefficient(
                X**j * Y**(degree-j)
            )
            for j in output_indices
        ])

    return matrix(R, rows)

def direct_manin_presentation(degree, coefficient_ring):
    """
    Construct the Manin presentation

        M_d(R) =
        V_d(R) /
        (V_d(R)(1+S) + V_d(R)(1+U+U^2))

    for an even nonnegative degree d over the supplied coefficient
    ring R = Z/(p^m). The matrices S and U agree with the manuscript.
    """
    degree = ZZ(degree)
    R = coefficient_ring

    if degree < 0:
        raise ValueError("degree must be nonnegative")

    if degree % 2 != 0:
        raise ValueError("the manuscript uses even degrees")

    S = matrix(R, [
        [0, -1],
        [1,  0],
    ])

    U = matrix(R, [
        [1, -1],
        [1,  0],
    ])

    identity = identity_matrix(R, degree + 1)

    AS = symmetric_power_action(S, degree, R)
    AU = symmetric_power_action(U, degree, R)

    # Rows of B_mod are the Manin relations.
    B_mod = (identity + AS).stack(identity + AU + AU**2)

    # Compute the canonical Howell generators of the relation module.
    howell = pari_howell_row_span(B_mod)
    H_R = howell["H_R"]

    return {
        "degree": degree,
        "sign": None,
        "coefficient_ring": R,
        "modulus": howell["modulus"],
        "ambient_dimension": degree + 1,
        "ambient_indices": tuple(range(degree + 1)),
        "B_mod": B_mod,
        "A_Z": howell["A_Z"],
        "H_pari": howell["H_pari"],
        "H_R": H_R,
    }


def direct_signed_manin_presentation(
    degree,
    coefficient_ring,
    sign,
):
    """
    Construct the plus or minus Manin presentation directly.

    For iota = diag(-1, 1), the monomial X^i Y^(d-i) has sign
    (-1)^i.  This constructor forms only the even output columns for
    sign +1 or the odd output columns for sign -1.  It does not build
    the full Manin quotient or compute its Howell basis.

    The construction requires 2 to be invertible in the coefficient
    ring, so that the Manin relation module decomposes into its signed
    summands.
    """
    degree = ZZ(degree)
    sign = ZZ(sign)
    R = coefficient_ring

    if degree < 0:
        raise ValueError("degree must be nonnegative")

    if degree % 2 != 0:
        raise ValueError("the manuscript uses even degrees")

    if sign not in (-1, 1):
        raise ValueError("sign must be +1 or -1")

    modulus = ZZ(R.characteristic())
    if gcd(2, modulus) != 1:
        raise ValueError(
            "the projector decomposition requires 2 to be invertible"
        )

    parity = 0 if sign == 1 else 1
    ambient_indices = tuple(
        i for i in range(degree + 1) if i % 2 == parity
    )

    S = matrix(R, [
        [0, -1],
        [1, 0],
    ])
    U = matrix(R, [
        [1, -1],
        [1, 0],
    ])

    identity_columns = identity_matrix(
        R,
        degree + 1,
    ).matrix_from_columns(ambient_indices)

    AS_signed = symmetric_power_action(
        S,
        degree,
        R,
        output_indices=ambient_indices,
    )
    AU_signed = symmetric_power_action(
        U,
        degree,
        R,
        output_indices=ambient_indices,
    )
    AU2_signed = symmetric_power_action(
        U**2,
        degree,
        R,
        output_indices=ambient_indices,
    )

    signed_relations = (
        identity_columns + AS_signed
    ).stack(
        identity_columns + AU_signed + AU2_signed
    )

    howell = pari_howell_row_span(signed_relations)

    return {
        "degree": degree,
        "sign": sign,
        "coefficient_ring": R,
        "modulus": howell["modulus"],
        "ambient_dimension": len(ambient_indices),
        "ambient_indices": ambient_indices,
        "B_mod": signed_relations,
        "A_Z": howell["A_Z"],
        "H_pari": howell["H_pari"],
        "H_R": howell["H_R"],
    }

def is_zero_in_manin_quotient(v, presentation):
    """
    Return True exactly when v represents zero in the
    Manin quotient described by `presentation`.
    """
    ambient_dimension = presentation.get(
        "ambient_dimension",
        presentation["degree"] + 1,
    )
    R = presentation["coefficient_ring"]
    modulus = presentation["modulus"]

    v = vector(R, v)

    if len(v) != ambient_dimension:
        raise ValueError(
            f"expected a vector of length {ambient_dimension}"
        )

    v_Z = matrix(
        ZZ,
        ambient_dimension,
        1,
        [ZZ(x) for x in v]
    )

    enlarged_generators = presentation["A_Z"].augment(v_Z)

    enlarged_howell = pari(enlarged_generators).matimagemod(modulus)

    return enlarged_howell == presentation["H_pari"]

def same_manin_class(v, w, presentation):
    R = presentation["coefficient_ring"]
    v = vector(R, v)
    w = vector(R, w)

    return is_zero_in_manin_quotient(
        v - w,
        presentation
    )

def manin_class_exponent(v, presentation):
    """
    Return the smallest a >= 0 such that p^a*v is zero
    in the Manin quotient.
    """
    modulus = ZZ(presentation["modulus"])
    factorization = list(factor(modulus))

    if len(factorization) != 1:
        raise ValueError("the modulus must be a prime power")

    p, m = factorization[0]

    for a in range(m + 1):
        if is_zero_in_manin_quotient(
            p**a * v,
            presentation
        ):
            return a

    raise ArithmeticError("no exponent found")

def rows_zero_in_manin_quotient(rows, presentation):
    """
    Test whether every row of `rows` represents zero in the
    given Manin quotient.
    """
    R = presentation["coefficient_ring"]
    modulus = presentation["modulus"]
    ambient_dimension = presentation.get(
        "ambient_dimension",
        presentation["degree"] + 1,
    )

    rows = matrix(R, rows)

    if rows.ncols() != ambient_dimension:
        raise ValueError(
            f"expected {ambient_dimension} columns"
        )

    row_representatives = matrix(
        ZZ,
        rows.nrows(),
        rows.ncols(),
        [ZZ(x) for x in rows.list()]
    )

    enlarged = presentation["A_Z"].augment(
        row_representatives.transpose()
    )

    enlarged_howell = pari(enlarged).matimagemod(modulus)

    return enlarged_howell == presentation["H_pari"]

def annihilates_manin_quotient(F, presentation):
    return rows_zero_in_manin_quotient(F, presentation)


def signed_manin_quotient(presentation, sign):
    """
    Construct the plus or minus Manin presentation for odd modulus.

    The involution iota = diag(-1, 1) acts on X^i Y^(d-i) by
    (-1)^i.  For sign +1 (respectively -1), project the Manin
    relations onto the even (respectively odd) monomial coordinates.

    Because 2 is invertible in the coefficient ring and the relation
    module is iota-stable, this presents the corresponding signed
    direct summand of the Manin quotient.
    """
    sign = ZZ(sign)

    if sign not in (-1, 1):
        raise ValueError("sign must be +1 or -1")

    if presentation.get("sign") is not None:
        raise ValueError("the input presentation is already signed")

    degree = ZZ(presentation["degree"])
    R = presentation["coefficient_ring"]
    modulus = ZZ(presentation["modulus"])

    if gcd(2, modulus) != 1:
        raise ValueError(
            "the projector decomposition requires 2 to be invertible"
        )

    iota = diagonal_matrix(
        R,
        [(-1)**i for i in range(degree + 1)],
    )

    relation_images = presentation["B_mod"] * iota
    if not rows_zero_in_manin_quotient(
        relation_images,
        presentation,
    ):
        raise ArithmeticError(
            "the Manin relation module is not stable under iota"
        )

    parity = 0 if sign == 1 else 1
    ambient_indices = tuple(
        i for i in range(degree + 1) if i % 2 == parity
    )

    signed_relations = presentation["B_mod"].matrix_from_columns(
        ambient_indices
    )
    howell = pari_howell_row_span(signed_relations)

    return {
        "degree": degree,
        "sign": sign,
        "coefficient_ring": R,
        "modulus": howell["modulus"],
        "ambient_dimension": len(ambient_indices),
        "ambient_indices": ambient_indices,
        "B_mod": signed_relations,
        "A_Z": howell["A_Z"],
        "H_pari": howell["H_pari"],
        "H_R": howell["H_R"],
    }

def manin_quotient_coordinates(presentation):
    """
    Put a Manin quotient over Z/(p^m) into Smith cyclic coordinates.

    INPUT:

    ``presentation``
        A dictionary describing a Manin presentation

            M = R^n / rowspan_R(B),

        where R = Z/(p^m) and ``B = presentation["B_mod"]`` has
        the Manin relations as its rows.  The ambient coordinates are
        the monomial coordinates of the presentation.  For a signed
        presentation, these are only the monomials of the appropriate
        parity.

    OUTPUT:

    A dictionary containing:

    ``p``
        The prime p.

    ``m``
        The exponent in the coefficient modulus p^m.

    ``U_Z``, ``V_Z``, ``D_Z``
        The integral Smith-normal-form data satisfying

            U_Z * B_Z * V_Z = D_Z.

    ``U_R``, ``V_R``, ``D_R``
        The corresponding matrices over R.

    ``cyclic_exponents``
        One exponent for every full Smith coordinate.  Exponent zero
        means that the coordinate is killed.

    ``surviving_indices``
        The indices of the Smith coordinates that survive in M.

    ``surviving_exponents``
        The positive exponents e_i of the surviving cyclic factors.
        Their coordinate moduli are p^e_i.

    ``quotient_is_free``
        True precisely when every surviving factor has order p^m,
        equivalently when M is free over R in these coordinates.

    NOTES:

    To obtain monomial representatives of the surviving cyclic
    generators, use

        indices = data["surviving_indices"]
        V_inverse = data["V_R"].inverse()
        representatives = matrix(
            R,
            [V_inverse.row(i) for i in indices],
        )

    An endomorphism in Smith coordinates is generally a mixed matrix:
    its target column i must be interpreted modulo
    p^surviving_exponents[i].
    """
    B_mod = presentation["B_mod"]
    R = presentation["coefficient_ring"]
    modulus = ZZ(presentation["modulus"])

    factorization = list(factor(modulus))

    if len(factorization) != 1:
        raise ValueError("the modulus must be a prime power")

    p, m = factorization[0]

    B_representatives = matrix(
        ZZ,
        B_mod.nrows(),
        B_mod.ncols(),
        [ZZ(x) for x in B_mod.list()]
    )

    snf = pari(B_representatives).matsnf(1)

    U_Z = matrix(ZZ, snf[0].sage())
    V_Z = matrix(ZZ, snf[1].sage())
    D_Z = matrix(ZZ, snf[2].sage())

    assert U_Z * B_representatives * V_Z == D_Z

    U_R = U_Z.change_ring(R)
    V_R = V_Z.change_ring(R)
    D_R = D_Z.change_ring(R)

    assert U_R * B_mod * V_R == D_R
    assert U_R.det().is_unit()
    assert V_R.det().is_unit()

    # PARI may shift the diagonal in a rectangular matrix.
    pivot_by_column = {}

    for i in range(D_Z.nrows()):
        for j in range(D_Z.ncols()):
            if D_Z[i, j] != 0:
                if j in pivot_by_column:
                    raise ValueError(
                        "more than one Smith pivot in a column"
                    )

                pivot_by_column[j] = abs(ZZ(D_Z[i, j]))

    cyclic_exponents = []

    for j in range(D_Z.ncols()):
        if j not in pivot_by_column:
            # No relation: a free Z/(p^m) coordinate.
            exponent = m
        else:
            pivot = pivot_by_column[j]
            exponent = min(pivot.valuation(p), m)

        cyclic_exponents.append(exponent)

    # Exponent zero means that a unit kills the coordinate.
    surviving_indices = [
        j
        for j, exponent in enumerate(cyclic_exponents)
        if exponent > 0
    ]

    surviving_exponents = [
        cyclic_exponents[j]
        for j in surviving_indices
    ]

    quotient_is_free = all(
        exponent == m
        for exponent in surviving_exponents
    )

    return {
        "p": p,
        "m": m,
        "U_Z": U_Z,
        "V_Z": V_Z,
        "D_Z": D_Z,
        "U_R": U_R,
        "V_R": V_R,
        "D_R": D_R,
        "cyclic_exponents": cyclic_exponents,
        "surviving_indices": surviving_indices,
        "surviving_exponents": surviving_exponents,
        "quotient_is_free": quotient_is_free,
    }


def _p_valuation_bounded(value, p, maximum):
    """Return min(v_p(value), maximum) for a residue representative."""
    value = ZZ(value)

    if value == 0:
        return ZZ(maximum)

    valuation = ZZ(0)
    while valuation < maximum and value % p == 0:
        value //= p
        valuation += 1

    return valuation


def chain_ring_manin_quotient_coordinates(presentation):
    """
    Put a Manin quotient into cyclic coordinates directly over Z/(p^m).

    This is an alternative to :func:`manin_quotient_coordinates`.  It diagonalizes the relation
    module over the finite ring R = Z/(p^m), while recording only
    the right change-of-basis matrix ``V_R``.  It therefore avoids the
    integral Smith transformation matrix ``U_Z`` and the accompanying
    integer coefficient growth.

    The returned dictionary has the same fields used by the Hecke
    routines: ``V_R``, ``surviving_indices``,
    ``surviving_exponents``, and ``quotient_is_free``.  Thus it may be
    passed directly to ``hecke_matrix_on_signed_manin_quotient``.

    Row-vector convention is used.  If ``D_R`` is the resulting
    diagonal relation matrix, then row operations and the recorded
    column operations give

        rowspan_R(B_mod * V_R) = rowspan_R(D_R).

    Consequently a surviving cyclic generator in the new coordinates
    is represented in the original monomial coordinates by the
    corresponding row of ``V_R.inverse()``.

    The Howell basis already stored in the presentation is used as a
    compact generating matrix for the relation module.  All arithmetic
    during diagonalization remains in R.
    """
    R = presentation["coefficient_ring"]
    modulus = ZZ(presentation["modulus"])
    factorization = list(factor(modulus))

    if len(factorization) != 1:
        raise ValueError("the modulus must be a prime power")

    p, m = factorization[0]
    ambient_dimension = presentation.get(
        "ambient_dimension",
        presentation["degree"] + 1,
    )

    # PARI's Howell matrix stores relation generators as columns.
    # Transposition therefore gives a compact row-generating matrix.
    relations = matrix(R, presentation["H_R"].transpose())

    if relations.ncols() != ambient_dimension:
        raise ArithmeticError(
            "the Howell relation generators have the wrong ambient dimension"
        )

    A = matrix(R, relations)
    V_R = identity_matrix(R, ambient_dimension)
    diagonal_valuations = []
    pivot = 0
    maximum_pivots = min(A.nrows(), A.ncols())

    while pivot < maximum_pivots:
        best_position = None
        best_valuation = m

        for i in range(pivot, A.nrows()):
            for j in range(pivot, A.ncols()):
                value = ZZ(A[i, j])
                if value == 0:
                    continue

                valuation = _p_valuation_bounded(value, p, m)
                if valuation < best_valuation:
                    best_position = (i, j)
                    best_valuation = valuation

                    # A unit is the smallest possible pivot.
                    if valuation == 0:
                        break

            if best_valuation == 0:
                break

        if best_position is None:
            break

        pivot_row, pivot_column = best_position

        if pivot_row != pivot:
            A.swap_rows(pivot_row, pivot)

        if pivot_column != pivot:
            A.swap_columns(pivot_column, pivot)
            V_R.swap_columns(pivot_column, pivot)

        pivot_power = p**best_valuation
        pivot_value = ZZ(A[pivot, pivot])
        pivot_unit = R(pivot_value // pivot_power)

        if not pivot_unit.is_unit():
            raise ArithmeticError("the selected pivot has nonunit part")

        # Normalize the pivot to p^best_valuation.  This is a row
        # operation, so it does not alter V_R.
        inverse_unit = pivot_unit.inverse_of_unit()
        A.rescale_row(pivot, inverse_unit)

        if A[pivot, pivot] != R(pivot_power):
            raise ArithmeticError("failed to normalize a chain-ring pivot")

        # Clear the pivot column by row operations.
        for i in range(A.nrows()):
            if i == pivot or A[i, pivot] == 0:
                continue

            value = ZZ(A[i, pivot])
            if value % pivot_power != 0:
                raise ArithmeticError(
                    "a pivot does not divide an entry in its column"
                )

            quotient = R(value // pivot_power)
            A.add_multiple_of_row(i, pivot, -quotient)

        # Clear the pivot row by column operations, recording exactly
        # the same operations on V_R.
        for j in range(A.ncols()):
            if j == pivot or A[pivot, j] == 0:
                continue

            value = ZZ(A[pivot, j])
            if value % pivot_power != 0:
                raise ArithmeticError(
                    "a pivot does not divide an entry in its row"
                )

            quotient = R(value // pivot_power)
            A.add_multiple_of_column(j, pivot, -quotient)
            V_R.add_multiple_of_column(j, pivot, -quotient)

        if any(A[i, pivot] != 0 for i in range(A.nrows()) if i != pivot):
            raise ArithmeticError("failed to clear a pivot column")

        if any(A[pivot, j] != 0 for j in range(A.ncols()) if j != pivot):
            raise ArithmeticError("failed to clear a pivot row")

        diagonal_valuations.append(best_valuation)
        pivot += 1

    if not V_R.det().is_unit():
        raise ArithmeticError("the right transformation is singular")

    # A zero diagonal coordinate is free over R.  A diagonal p^v
    # relation leaves a cyclic factor of order p^v; v=0 kills it.
    cyclic_exponents = []
    for j in range(ambient_dimension):
        if j < len(diagonal_valuations):
            exponent = diagonal_valuations[j]
        else:
            exponent = m
        cyclic_exponents.append(exponent)

    surviving_indices = [
        j
        for j, exponent in enumerate(cyclic_exponents)
        if exponent > 0
    ]
    surviving_exponents = [
        cyclic_exponents[j]
        for j in surviving_indices
    ]

    return {
        "backend": "finite_chain_ring",
        "p": p,
        "m": m,
        "V_R": V_R,
        "D_R": A,
        "cyclic_exponents": cyclic_exponents,
        "surviving_indices": surviving_indices,
        "surviving_exponents": surviving_exponents,
        "quotient_is_free": all(
            exponent == m
            for exponent in surviving_exponents
        ),
    }

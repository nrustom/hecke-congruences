from sage.all import (
    ZZ,
    gcd,
    matrix,
    zero_matrix,
)

from sage.modular.modsym.heilbronn import HeilbronnMerel

from manin_quotient import (
    rows_zero_in_manin_quotient,
    symmetric_power_action,
)
from mixed_endomorphisms import (
    mixed_endomorphism_is_well_defined,
    normalize_mixed_matrix,
)


def heilbronn_merel_matrices(n):
    """
    Return Sage matrices in the Heilbronn--Merel family H_n.
    """
    family = HeilbronnMerel(ZZ(n))

    return [
        matrix(ZZ, 2, 2, entries)
        for entries in family.to_list()
    ]

def ambient_hecke_matrix(n, degree, coefficient_ring):
    """
    Return the ambient Heilbronn--Merel matrix for T_n on V_d(R).

    This does not yet assert that the operator descends to the
    Manin quotient.
    """
    n = ZZ(n)
    degree = ZZ(degree)
    R = coefficient_ring

    if n <= 0:
        raise ValueError("n must be positive")

    if degree < 0:
        raise ValueError("degree must be nonnegative")

    if gcd(n, R.characteristic()) != 1:
        raise ValueError(
            "the manuscript currently defines this formula for (n,p)=1"
        )

    T = zero_matrix(R, degree + 1, degree + 1)

    for gamma in heilbronn_merel_matrices(n):
        T += symmetric_power_action(gamma, degree, R)

    return T

def ambient_operator_descends(
    ambient_operator,
    presentation
):
    R = presentation["coefficient_ring"]
    ambient_dimension = presentation.get(
        "ambient_dimension",
        presentation["degree"] + 1,
    )

    ambient_operator = matrix(R, ambient_operator)

    if ambient_operator.dimensions() != (
        ambient_dimension,
        ambient_dimension,
    ):
        return False

    relation_images = (
        presentation["B_mod"] * ambient_operator
    )

    return rows_zero_in_manin_quotient(
        relation_images,
        presentation
    )


def hecke_matrix_from_ambient_on_manin_quotient(
    ambient_T,
    presentation,
    quotient_coordinates
):
    """
    Compute the smaller matrix induced by ambient_T on a possibly
    nonfree Manin quotient.

    The returned matrix acts on the direct sum

        direct_sum_j Z/(p^e_j),

    where e_j are recorded in `coordinate_exponents`.
    """

    R = presentation["coefficient_ring"]
    ambient_dimension = presentation.get(
        "ambient_dimension",
        presentation["degree"] + 1,
    )
    ambient_T = matrix(R, ambient_T)

    if ambient_T.dimensions() != (
        ambient_dimension,
        ambient_dimension,
    ):
        raise ValueError(
            "ambient_T has dimensions incompatible with "
            "the Manin presentation"
        )

    if not ambient_operator_descends(ambient_T, presentation):
        raise ValueError(
            "ambient_T does not preserve the Manin relation module"
        )

    V_R = quotient_coordinates["V_R"]

    T_smith = (
        V_R.inverse()
        * ambient_T
        * V_R
    )

    indices = quotient_coordinates["surviving_indices"]

    T_quotient = T_smith.matrix_from_rows_and_columns(
        indices,
        indices
    )

    p = quotient_coordinates["p"]
    exponents = quotient_coordinates["surviving_exponents"]

    coordinate_moduli = [
        p**e for e in exponents
    ]

    normalized = normalize_mixed_matrix(
        T_quotient,
        coordinate_moduli,
    )

    # Check that the matrix defines a well-defined map between
    # the cyclic coordinate factors.
    #
    # If the source coordinate has modulus p^e_i, then p^e_i
    # times its image must vanish in every target coordinate.
    for i in range(T_quotient.nrows()):
        for j in range(T_quotient.ncols()):
            source_modulus = coordinate_moduli[i]
            target_modulus = coordinate_moduli[j]

            if (
                source_modulus * ZZ(normalized[i, j])
            ) % target_modulus != 0:
                raise ArithmeticError(
                    "the induced matrix is incompatible "
                    "with the cyclic coordinate moduli"
                )

    return {
        "matrix": T_quotient,
        "normalized_matrix": normalized,
        "coordinate_exponents": exponents,
        "coordinate_moduli": coordinate_moduli,
        "base_ring": R,
    }

def hecke_matrix_on_manin_quotient(
    n,
    presentation,
    quotient_coordinates
):
    """
    Compute T_n on the mixed Manin quotient without first constructing
    the full ambient Hecke matrix.

    This gives a mixed matrix acting on direct_sum_j Z/(p^e_j).

    Row-vector convention is used throughout.
    """
    n = ZZ(n)
    degree = presentation["degree"]
    R = presentation["coefficient_ring"]

    if gcd(n, R.characteristic()) != 1:
        raise ValueError("this routine currently requires gcd(n,p)=1")

    V = quotient_coordinates["V_R"]
    V_inverse = V.inverse()

    indices = quotient_coordinates["surviving_indices"]
    exponents = quotient_coordinates["surviving_exponents"]
    p = quotient_coordinates["p"]

    coordinate_moduli = [p**e for e in exponents]
    number_of_generators = len(indices)

    # The Smith-coordinate generator e_i corresponds in the original
    # monomial coordinates to e_i V^(-1), namely row i of V^(-1).
    representatives = matrix(
        R,
        [V_inverse.row(i) for i in indices]
    )

    if representatives.dimensions() != (
        number_of_generators,
        degree + 1,
    ):
        raise ArithmeticError(
            "the Smith-coordinate representatives have "
            "unexpected dimensions"
        )

    # Apply the Heilbronn--Merel sum directly to these representatives.
    images = zero_matrix(
        R,
        number_of_generators,
        degree + 1
    )

    for gamma in heilbronn_merel_matrices(n):
        A_gamma = symmetric_power_action(gamma, degree, R)
        images += representatives * A_gamma

    # Return the images to Smith coordinates.
    images_in_smith_coordinates = images * V

    # Retain only the surviving quotient coordinates.
    quotient_matrix = matrix(
        R,
        [
            [
                images_in_smith_coordinates[i,j]
                for j in indices
            ]
            for i in range(number_of_generators)
        ]
    )

    normalized = normalize_mixed_matrix(
        quotient_matrix,
        coordinate_moduli
    )

    if not mixed_endomorphism_is_well_defined(
        normalized,
        coordinate_moduli
    ):
        raise ArithmeticError(
            "the computed matrix is not a well-defined endomorphism "
            "of the mixed cyclic quotient"
        )

    return {
        "matrix": quotient_matrix,
        "normalized_matrix": normalized,
        "coordinate_exponents": exponents,
        "coordinate_moduli": coordinate_moduli,
        "base_ring": R,
    }


def hecke_matrix_on_signed_manin_quotient(
    n,
    signed_presentation,
    quotient_coordinates,
    check_descent=True,
):
    """
    Compute T_n directly on a signed Manin quotient.

    Only the even-even block for sign +1 or the odd-odd block for
    sign -1 of each Heilbronn--Merel action is constructed.  The full
    Manin quotient and the full ambient Hecke matrix are not built.

    Matrices act on row vectors.
    """
    n = ZZ(n)
    degree = ZZ(signed_presentation["degree"])
    sign = signed_presentation.get("sign")
    R = signed_presentation["coefficient_ring"]

    if sign not in (-1, 1):
        raise ValueError("the presentation must have sign +1 or -1")

    if gcd(n, R.characteristic()) != 1:
        raise ValueError("this routine requires gcd(n,p)=1")

    signed_indices = tuple(
        ZZ(i) for i in signed_presentation["ambient_indices"]
    )
    signed_dimension = len(signed_indices)

    if signed_presentation["ambient_dimension"] != signed_dimension:
        raise ValueError("the signed presentation has inconsistent data")

    V = quotient_coordinates["V_R"]
    V_inverse = V.inverse()
    surviving_indices = quotient_coordinates["surviving_indices"]
    exponents = quotient_coordinates["surviving_exponents"]
    p = quotient_coordinates["p"]
    coordinate_moduli = [p**e for e in exponents]
    number_of_generators = len(surviving_indices)

    representatives = matrix(
        R,
        [V_inverse.row(i) for i in surviving_indices],
    )

    if representatives.dimensions() != (
        number_of_generators,
        signed_dimension,
    ):
        raise ArithmeticError(
            "the signed Smith representatives have unexpected dimensions"
        )

    images = zero_matrix(
        R,
        number_of_generators,
        signed_dimension,
    )

    if check_descent:
        signed_ambient_sum = zero_matrix(
            R,
            signed_dimension,
            signed_dimension,
        )

    for gamma in heilbronn_merel_matrices(n):
        signed_block = symmetric_power_action(
            gamma,
            degree,
            R,
            input_indices=signed_indices,
            output_indices=signed_indices,
        )
        images += representatives * signed_block

        if check_descent:
            signed_ambient_sum += signed_block

    if check_descent and not ambient_operator_descends(
        signed_ambient_sum,
        signed_presentation,
    ):
        raise ArithmeticError(
            "the signed Heilbronn--Merel sum does not preserve "
            "the signed Manin relation module"
        )

    images_in_smith_coordinates = images * V
    quotient_matrix = matrix(
        R,
        [
            [
                images_in_smith_coordinates[i, j]
                for j in surviving_indices
            ]
            for i in range(number_of_generators)
        ],
    )

    normalized = normalize_mixed_matrix(
        quotient_matrix,
        coordinate_moduli,
    )

    if not mixed_endomorphism_is_well_defined(
        normalized,
        coordinate_moduli,
    ):
        raise ArithmeticError(
            "the signed Hecke matrix is incompatible with "
            "the cyclic coordinate moduli"
        )

    return {
        "matrix": quotient_matrix,
        "normalized_matrix": normalized,
        "coordinate_exponents": exponents,
        "coordinate_moduli": coordinate_moduli,
        "base_ring": R,
        "sign": sign,
        "descent_checked": bool(check_descent),
    }

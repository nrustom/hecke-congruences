from sage.all import (
    ZZ,
    gcd,
    matrix,
    zero_matrix,
)


def _coerce_coordinate_moduli(coordinate_moduli):
    moduli = tuple(ZZ(q) for q in coordinate_moduli)

    if any(q <= 1 for q in moduli):
        raise ValueError("coordinate moduli must be greater than one")

    return moduli


def normalize_mixed_matrix(A, coordinate_moduli):
    """
    Normalize column j modulo the modulus of its target coordinate.
    """
    coordinate_moduli = _coerce_coordinate_moduli(coordinate_moduli)
    A = matrix(A)

    if A.ncols() != len(coordinate_moduli):
        raise ValueError(
            "the number of matrix columns must equal the number "
            "of target coordinate moduli"
        )

    return matrix(
        ZZ,
        A.nrows(),
        A.ncols(),
        [
            ZZ(A[i,j]) % coordinate_moduli[j]
            for i in range(A.nrows())
            for j in range(A.ncols())
        ]
    )


def mixed_endomorphism_is_well_defined(A, coordinate_moduli):
    """
    Check that A defines an endomorphism of

        direct_sum_i Z/(coordinate_moduli[i]).

    Matrices act on row vectors.
    """
    coordinate_moduli = _coerce_coordinate_moduli(coordinate_moduli)
    A = matrix(A)

    if A.nrows() != len(coordinate_moduli):
        return False

    if A.ncols() != len(coordinate_moduli):
        return False

    return all(
        (
            coordinate_moduli[i] * ZZ(A[i,j])
        ) % coordinate_moduli[j] == 0
        for i in range(A.nrows())
        for j in range(A.ncols())
    )

def mixed_matrix_is_zero(A, coordinate_moduli):
    coordinate_moduli = _coerce_coordinate_moduli(coordinate_moduli)
    A = matrix(A)

    if A.ncols() != len(coordinate_moduli):
        raise ValueError(
            "the number of matrix columns must equal the number "
            "of target coordinate moduli"
        )

    return all(
        ZZ(A[i,j]) % coordinate_moduli[j] == 0
        for i in range(A.nrows())
        for j in range(A.ncols())
    )

def reduce_mixed_matrix(
    A,
    coordinate_moduli,
    p,
    a
):
    """
    Reduce an endomorphism of

        direct_sum_j Z/(coordinate_moduli[j])

    modulo p^a.

    Returns its matrix on M/p^a M together with the reduced
    coordinate moduli.
    """

    p = ZZ(p)
    a = ZZ(a)
    coordinate_moduli = _coerce_coordinate_moduli(coordinate_moduli)
    A = normalize_mixed_matrix(A, coordinate_moduli)

    if not p.is_prime():
        raise ValueError("p must be prime")

    if a < 1:
        raise ValueError("a must be positive")

    reduction_modulus = p**a

    reduced_moduli = [
        gcd(q, reduction_modulus)
        for q in coordinate_moduli
    ]

    if any(q == 1 for q in reduced_moduli):
        raise NotImplementedError(
            "a coordinate disappears completely after reduction"
        )

    reduced_matrix = matrix(
        ZZ,
        A.nrows(),
        A.ncols(),
        [
            ZZ(A[i,j]) % reduced_moduli[j]
            for i in range(A.nrows())
            for j in range(A.ncols())
        ]
    )

    if not mixed_endomorphism_is_well_defined(
        reduced_matrix,
        reduced_moduli
    ):
        raise ArithmeticError(
            "the reduced matrix is not a well-defined "
            "endomorphism of the reduced mixed module"
        )

    return {
        "matrix": reduced_matrix,
        "coordinate_moduli": reduced_moduli,
        "modulus": reduction_modulus,
    }

def is_power_of_prime(q, p):
    q = ZZ(q)
    p = ZZ(p)

    if q < 1:
        return False

    while q % p == 0:
        q //= p

    return q == 1


def divide_mixed_endomorphism_by_p_power(
    A,
    coordinate_moduli,
    p,
    a
):
    """
    Construct an endomorphism Z satisfying

        p^a Z = A

    on a mixed direct sum of cyclic p-power modules.

    Matrices act on row vectors.
    """
    p = ZZ(p)
    a = ZZ(a)
    coordinate_moduli = _coerce_coordinate_moduli(coordinate_moduli)

    if not p.is_prime():
        raise ValueError("p must be prime")

    if a < 0:
        raise ValueError("a must be nonnegative")

    if not all(
        is_power_of_prime(q, p)
        for q in coordinate_moduli
    ):
        raise ValueError(
            "all coordinate moduli must be powers of p"
        )

    A = normalize_mixed_matrix(
        A,
        coordinate_moduli
    )

    if not mixed_endomorphism_is_well_defined(
        A,
        coordinate_moduli
    ):
        raise ArithmeticError(
            "A is not a well-defined mixed endomorphism"
        )

    scale = p**a

    Z = zero_matrix(ZZ, A.nrows(), A.ncols())

    for i in range(A.nrows()):
        for j in range(A.ncols()):
            target_modulus = ZZ(coordinate_moduli[j])
            value = ZZ(A[i,j])

            obstruction = gcd(scale, target_modulus)

            if value % obstruction != 0:
                raise ArithmeticError(
                    "entry ({},{}) is not divisible by p^{} "
                    "at the required target precision".format(
                        i, j, a
                    )
                )

            if scale >= target_modulus:
                # Multiplication by scale is zero in this target.
                # Divisibility therefore requires value = 0.
                if value != 0:
                    raise ArithmeticError(
                        "entry ({},{}) cannot be divided at this "
                        "short target coordinate".format(i, j)
                    )

                quotient_value = 0
            else:
                quotient_value = value // scale

            Z[i,j] = quotient_value

    if not mixed_endomorphism_is_well_defined(
        Z,
        coordinate_moduli
    ):
        raise ArithmeticError(
            "entrywise division exists, but the resulting matrix "
            "does not define an endomorphism of the mixed module"
        )

    if not mixed_matrix_is_zero(
        scale*Z - A,
        coordinate_moduli
    ):
        raise ArithmeticError(
            "internal verification of p-power division failed"
        )

    return Z


def mixed_matrix_is_zero_mod_p_power(
    A,
    coordinate_moduli,
    p,
    a
):
    reduced = reduce_mixed_matrix(
        A,
        coordinate_moduli,
        p,
        a
    )

    return mixed_matrix_is_zero(
        reduced["matrix"],
        reduced["coordinate_moduli"]
    )

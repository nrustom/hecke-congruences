"""Linear algebra on finite direct sums of cyclic p-power modules.

Matrices act on row vectors, with column j reduced modulo its target
cyclic order. Image membership, vanishing after reduction, and division
as an endomorphism are distinct conditions when torsion is present.
Ideal-image construction keeps this torsion and can work from a
presentation without first diagonalizing the full ambient quotient.
"""

from sage.all import (
    ZZ,
    gcd,
    identity_matrix,
    matrix,
    zero_matrix,
)


def _coerce_coordinate_moduli(coordinate_moduli):
    """Return the cyclic orders as integers, rejecting orders at most one."""
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
    """Test whether all row images vanish in the mixed cyclic module.

    Column j is reduced modulo its own target order, not merely the ambient modulus.
    """
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
    """Test whether q is a nonnegative integral power of the given prime p.

    The caller supplies a prime p greater than one; q=1 is included.
    """
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
    """Test whether the induced endomorphism on M/p^a M is zero, retaining the reduced cyclic orders."""
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


# Ideal images in presented modules. Relations present M=R^n/rowspan(B);
# no saturation or torsion-free quotient is taken.


def _basis(rows):
    """Compute a Howell row basis over the coefficient ring without discarding torsion."""
    from modular_matrix import row_basis
    return row_basis(rows)


class PresentedSubmodule:
    """The submodule (J + rowspan(G) + scalar*R^n)/J inside M = R^n/J.

    Construction only stores generators. Howell reduction is lazy; no
    Smith form or basis of M is computed. ``generators`` are ambient
    representatives, not an independent basis of this submodule.
    """

    def __init__(self, relations, generators, scalar=0):
        """Store the ambient relations and image generators as immutable matrices.

        The row bases are computed only when needed; the ambient quotient is not first diagonalized.
        """
        if (relations.base_ring() != generators.base_ring()
                or relations.ncols() != generators.ncols()):
            raise ValueError("relations and generators must have the same ring and width")
        self.relations = matrix(relations)
        self.generators = matrix(generators)
        self.relations.set_immutable()
        self.generators.set_immutable()
        self._relation_basis = None
        self._preimage_basis = None
        self.scalar = scalar

    @property
    def relation_basis(self):
        """Howell generators of J, computed on first access."""
        if self._relation_basis is None:
            self._relation_basis = _basis(self.relations)
            self._relation_basis.set_immutable()
        return self._relation_basis

    @property
    def preimage_basis(self):
        """Howell generators of J + rowspan(G), NOT a basis of IM."""
        if self._preimage_basis is None:
            from modular_matrix import howell_preimage_with_scalar
            self._preimage_basis = howell_preimage_with_scalar(
                self.relation_basis.stack(self.generators), self.scalar)
            self._preimage_basis.set_immutable()
        return self._preimage_basis

    def contains(self, representative):
        """Test membership of an ambient row representative modulo J."""
        row = matrix(self.relations.base_ring(), 1, self.relations.ncols(),
                     list(representative))
        return _basis(self.preimage_basis.stack(row)) == self.preimage_basis

    def __contains__(self, representative):
        """Test membership of the represented class in this image submodule."""
        return self.contains(representative)

    def is_zero(self):
        """Test IM = 0, equivalently every generator belongs to J."""
        return self.preimage_basis == self.relation_basis

    def is_full(self):
        """Test IM = M."""
        return self.preimage_basis == _basis(identity_matrix(
            self.relations.base_ring(), self.relations.ncols()))


def image_submodule(relations, image_generators, scalar=0):
    """Return scalar*M + images from ambient rows, without constructing M.

    ``image_generators`` may be a rectangular matrix of streamed operator
    images. Supply enough rows to generate the desired images. This low-level
    routine does not assert that those rows come from well-defined operators.
    """
    R = relations.base_ring()
    n = relations.ncols()
    generators = matrix(R, image_generators)
    if generators.ncols() != n:
        raise ValueError("image rows must have the ambient presentation width")
    if R(scalar):
        generators = generators.stack(R(scalar) * identity_matrix(R, n))
    return PresentedSubmodule(relations, generators, scalar)


def ideal_image(relations, operators, p, a=None, check_descent=True):
    """Compute IM for I=(p^a,F_1(T),...,F_s(T)), without Smith reduction.

    Pass the already evaluated matrices F_j(T) as ``operators``. Sage
    polynomial substitution may be used, including joint polynomials.
    Their rows must use the same ambient coordinates as ``relations``.
    For mixed cyclic coordinates use diag(coordinate_moduli) as relations.
    Omit ``a`` for I=(F_1,...,F_s) with no scalar generator.

    By default verify each operator preserves J. With commuting Hecke
    actions their images are already Hecke-stable: no Hecke hull is needed.
    For noncommuting actions this computes only the indicated sum of images.
    Use image_submodule for streamed image rows instead of full matrices.
    """
    p = ZZ(p)
    a = None if a is None else ZZ(a)
    modulus = ZZ(relations.base_ring().characteristic())
    if not p.is_prime() or (a is not None and a < 0) or modulus < 2:
        raise ValueError("require prime p, nonnegative a, and R=Z/p^m")
    remaining = modulus
    while remaining % p == 0:
        remaining //= p
    if remaining != 1:
        raise ValueError("coefficient characteristic must be a power of p")
    R, n = relations.base_ring(), relations.ncols()
    generators = matrix(R, 0, n)
    relation_basis = _basis(relations) if check_descent else None
    if relation_basis is not None:
        relation_basis.set_immutable()
    for operator in operators:
        operator = matrix(R, operator)
        if operator.dimensions() != (n, n):
            raise ValueError("each operator must be an ambient square matrix")
        if check_descent and _basis(relation_basis.stack(relations * operator)) != relation_basis:
            raise ValueError("an operator does not preserve the relation module")
        generators = generators.stack(operator)
    result = image_submodule(relations, generators, scalar=0 if a is None else pow(p, a, modulus))
    result._relation_basis = relation_basis
    return result


def lift_rows(images, K):
    """Solve C*K=images in an upper Howell basis; no division by nonunits in R."""
    R = K.base_ring()
    if images.base_ring() != R or images.ncols() != K.ncols():
        raise ValueError("preimage ring/width mismatch")
    work = matrix(images)
    coefficients = matrix(R, images.nrows(), K.nrows())
    for j in range(K.nrows()):
        column = next(i for i in range(K.ncols()) if K[j,i])
        pivot = ZZ(K[j,column])
        for i in range(images.nrows()):
            value = ZZ(work[i,column])
            if value % pivot:
                raise ArithmeticError("image outside the ideal preimage")
            c = R(value // pivot)
            coefficients[i,j] = c
            work.set_row(i, work.row(i)-c*K.row(j))
    if work:
        raise ArithmeticError("image outside the ideal preimage")
    return coefficients


def image_coordinates(B, generators, actions, scalar=0, audit=True):
    """Cyclic presentation and restricted actions on (J+rowspan(G)+scalar*R^n)/J.

    Only the image is Smith-reduced. All kernel relations of its Howell
    generators are retained, even with no scalar generator or zero image.
    ``actions`` maps operator indices to matrices on the ambient presentation.
    """
    from modular_matrix import howell_preimage_with_scalar, chain_ring_coordinates
    R, n = B.base_ring(), B.ncols()
    N = ZZ(R.characteristic())
    J = _basis(B)
    K = howell_preimage_with_scalar(J.stack(matrix(R, generators)), scalar)
    k = K.nrows()
    pivots = [next(j for j in range(n) if K[i,j]) for i in range(k)]
    annihilators = matrix(R, k, k)
    for i, j in enumerate(pivots):
        annihilators[i,i] = N // ZZ(K[i,j])
    kernel = annihilators-lift_rows(annihilators*K, K)
    relations = _basis(lift_rows(J,K).stack(kernel))
    C = chain_ring_coordinates(relations)
    inclusion = C["V_R_inverse"].matrix_from_rows(C["surviving_indices"])*K
    projection = C["V_R"].matrix_from_columns(C["surviving_indices"])
    p, m = C["p"], C["m"]
    moduli = tuple(p**e for e in C["surviving_exponents"])
    def log_order(H):
        """Return the base-p logarithm of the order of a Howell row submodule."""
        return sum(m-ZZ(next(value for value in row if value)).valuation(p) for row in H.rows())
    if sum(C["surviving_exponents"]) != log_order(K)-log_order(J):
        raise ArithmeticError("ideal cardinality replay failed")
    if audit:
        annihilated = matrix(inclusion)
        for i, order in enumerate(moduli):
            annihilated.rescale_row(i, R(order))
        if _basis(J.stack(annihilated)) != J:
            raise ArithmeticError("ideal inclusion replay failed")
    restricted = {}
    for index, T in actions.items():
        if T.base_ring() != R or T.dimensions() != (n,n):
            raise ValueError("operator and presentation mismatch")
        if audit and _basis(J.stack(J*T)) != J:
            raise ArithmeticError("operator does not descend to M")
        images = inclusion*T
        action = normalize_mixed_matrix(lift_rows(images,K)*projection, moduli)
        action = matrix(R, action)
        if not mixed_endomorphism_is_well_defined(action, moduli):
            raise ArithmeticError("operator does not respect ideal cyclic orders")
        if audit and _basis(J.stack(images-action*inclusion)) != J:
            raise ArithmeticError("ideal action replay failed")
        restricted[index] = action
    return {"coordinates":C, "inclusion":inclusion, "actions":restricted,
            "preimage_basis":K, "ambient_relations":J}

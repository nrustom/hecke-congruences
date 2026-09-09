"""Ideal images in presented modules, without Smith coordinates.

All matrices use row vectors. Relations present M = R^n / rowspan(B).
No saturation or torsion-free quotient is taken.
"""

from sage.all import ZZ, matrix, identity_matrix
from pari_howell import pari_howell_row_span


def _basis(rows):
    if rows.ncols() == 0:
        return matrix(rows.base_ring(), 0, 0)
    return pari_howell_row_span(rows)["H_R"].transpose()


class PresentedSubmodule:
    """The submodule (J + rowspan(G))/J inside M = R^n/J.

    Construction only stores generators. Howell reduction is lazy; no
    Smith form or basis of M is computed. ``generators`` are ambient
    representatives, not an independent basis of this submodule.
    """

    def __init__(self, relations, generators):
        if (relations.base_ring() != generators.base_ring()
                or relations.ncols() != generators.ncols()):
            raise ValueError("relations and generators must have the same ring and width")
        self.relations = matrix(relations)
        self.generators = matrix(generators)
        self.relations.set_immutable()
        self.generators.set_immutable()
        self._relation_basis = None
        self._preimage_basis = None

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
            self._preimage_basis = _basis(self.relation_basis.stack(self.generators))
            self._preimage_basis.set_immutable()
        return self._preimage_basis

    def contains(self, representative):
        """Test membership of an ambient row representative modulo J."""
        row = matrix(self.relations.base_ring(), 1, self.relations.ncols(),
                     list(representative))
        return _basis(self.preimage_basis.stack(row)) == self.preimage_basis

    def __contains__(self, representative):
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
    return PresentedSubmodule(relations, generators)


def ideal_image(relations, operators, p, a, check_descent=True):
    """Compute IM for I=(p^a,F_1(T),...,F_s(T)), without Smith reduction.

    Pass the already evaluated matrices F_j(T) as ``operators``. Sage
    polynomial substitution may be used, including joint polynomials.
    Their rows must use the same ambient coordinates as ``relations``.
    For mixed cyclic coordinates use diag(coordinate_moduli) as relations.

    By default verify each operator preserves J. With commuting Hecke
    actions their images are already Hecke-stable: no Hecke hull is needed.
    For noncommuting actions this computes only the indicated sum of images.
    Use image_submodule for streamed image rows instead of full matrices.
    """
    p, a = ZZ(p), ZZ(a)
    modulus = ZZ(relations.base_ring().characteristic())
    if not p.is_prime() or a < 0 or modulus < 2:
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
    result = image_submodule(relations, generators, scalar=pow(p, a, modulus))
    result._relation_basis = relation_basis
    return result

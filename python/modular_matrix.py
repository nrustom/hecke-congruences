"""Exact finite-ring row arithmetic shared by the Sage source constructors.

Matches the Nim conventions: upper row Howell bases, unit compression,
and Smith elimination over Z/p^m with both coordinate maps retained.
"""
from sage.all import ZZ, Integers, matrix, identity_matrix
from pari_kernel import pari_howell_row_span


def inverse_unit_prime_power(A, p, m):
    """Invert a unit minor modulo p, then Newton-lift its inverse to full precision."""
    from sage.all import GF
    R = A.base_ring()
    if A.nrows() != A.ncols():
        raise ValueError("inverse requires a square matrix")
    inverse = A.change_ring(GF(p)).inverse().change_ring(R)
    precision = 1
    identity = identity_matrix(R,A.nrows())
    while precision < m:
        inverse = inverse*(2*identity-A*inverse)
        precision *= 2
    if A*inverse != identity:
        raise ArithmeticError("unit-minor inverse replay failed")
    return inverse


def row_basis(rows):
    """Canonical upper row Howell basis, omitting zero rows (also for rank 0)."""
    R, n = rows.base_ring(), rows.ncols()
    if n == 0 or rows.nrows() == 0:
        return matrix(R, 0, n)
    reverse = tuple(reversed(range(n)))
    H = pari_howell_row_span(rows.matrix_from_columns(reverse))["H_R"].transpose()
    H = H.matrix_from_columns(reverse)
    selected = [i for i in reversed(range(H.nrows())) if H.row(i)]
    return H.matrix_from_rows(selected)


def howell_preimage_with_scalar(generators, scalar=0):
    """Howell basis of rowspan(generators)+scalar*R^n; reduce first modulo gcd(s,N).

    Only the preliminary image calculation uses this smaller modulus. The
    returned rows and all subsequent kernel/action calculations use R.
    """
    R, n = generators.base_ring(), generators.ncols()
    N = ZZ(R.characteristic())
    s = ZZ(scalar).gcd(N)
    if s == N:
        return row_basis(generators)
    if s == 1:
        return identity_matrix(R, n)
    low = row_basis(generators.change_ring(Integers(s)))
    K = s * identity_matrix(R, n)
    for row in low.rows():
        pivot = next(j for j, value in enumerate(row) if value)
        K.set_row(pivot, [R(ZZ(value)) for value in row])
    return K


def unit_compression(relations, inherited=0):
    """Eliminate unit pivots outside the inherited block, preserving all torsion."""
    R = relations.base_ring()
    E = matrix(relations)
    pivots = []
    row = 0
    for column in range(inherited, E.ncols()):
        found = next((i for i in range(row, E.nrows()) if E[i, column].is_unit()), None)
        if found is None:
            continue
        E.swap_rows(row, found)
        E.rescale_row(row, E[row, column].inverse_of_unit())
        for i in range(E.nrows()):
            if i != row and E[i, column]:
                E.add_multiple_of_row(i, row, -E[i, column])
        pivots.append(column)
        row += 1
    free = [j for j in range(E.ncols()) if j not in pivots]
    projection = matrix(R, E.ncols(), len(free))
    section = matrix(R, len(free), E.ncols())
    for j, k in enumerate(free):
        projection[k, j] = section[j, k] = 1
    for i, k in enumerate(pivots):
        for j, column in enumerate(free):
            projection[k, j] = -E[i, column]
    return projection, section, free


def chain_ring_coordinates(relations):
    """Smith cyclic coordinates without an integral Smith calculation or final inverse.

    V and V_inverse are updated by inverse elementary operations. Columns of
    V are stored as rows during elimination, as in the Nim contiguous kernels.
    """
    R = relations.base_ring()
    factors = list(ZZ(R.characteristic()).factor())
    if len(factors) != 1:
        raise ValueError("require R=Z/p^m")
    p, m = factors[0]
    A = row_basis(relations)
    n = A.ncols()
    Vt = identity_matrix(R, n)
    inverse = identity_matrix(R, n)
    valuations = []
    N = int(R.characteristic())
    lookup = [m] * N if N <= 65536 else None
    if lookup is not None:
        for value in range(1, N):
            lookup[value] = 0 if value % p else 1 + lookup[value // p]
    floor = 0
    for pivot in range(min(A.dimensions())):
        best, position = m, None
        for i in range(pivot, A.nrows()):
            for j in range(pivot, n):
                value = ZZ(A[i, j])
                v = lookup[int(value)] if lookup is not None else min(value.valuation(p), m)
                if v < best:
                    best, position = v, (i, j)
                if best == floor:
                    break
            if best == floor:
                break
        if position is None:
            break
        i, j = position
        A.swap_rows(i, pivot)
        A.swap_columns(j, pivot)
        Vt.swap_rows(j, pivot)
        inverse.swap_rows(j, pivot)
        divisor = p**best
        A.rescale_row(pivot, R(ZZ(A[pivot, pivot]) // divisor).inverse_of_unit())
        for i in range(pivot + 1, A.nrows()):
            A.add_multiple_of_row(i, pivot, -R(ZZ(A[i, pivot]) // divisor))
        for j in range(pivot + 1, n):
            c = R(ZZ(A[pivot, j]) // divisor)
            if c:
                A[pivot, j] = 0  # The pivot column has already been cleared.
                Vt.add_multiple_of_row(j, pivot, -c)
                inverse.add_multiple_of_row(pivot, j, c)
        valuations.append(best)
        floor = best
    exponents = valuations + [m] * (n - len(valuations))
    indices = [i for i, e in enumerate(exponents) if e]
    surviving = [exponents[i] for i in indices]
    return {"backend": "finite_chain_ring", "p": p, "m": m,
            "V_R": Vt.transpose(), "V_R_inverse": inverse, "D_R": A,
            "cyclic_exponents": exponents, "surviving_indices": indices,
            "surviving_exponents": surviving,
            "quotient_is_free": all(e == m for e in surviving)}

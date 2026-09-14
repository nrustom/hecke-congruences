"""Full Dickson multipliers and sparse polynomial interchange with Nim."""
from sage.all import ZZ, PolynomialRing, identity_matrix, matrix


def dickson_polynomials(p, m, R):
    """Return (A_m(X,1), B_m(X,1)); do not truncate the multipliers modulo p."""
    X = PolynomialRing(R, "X").gen()
    t = p**(m-1)
    return sum(X**(j*(p-1)) for j in range(p+1))**t, (X**p-X)**t


def evaluate_polynomial(terms, operators):
    """Evaluate [[coefficient,[e_1,...,e_s]],...] in the specified variable order."""
    if not operators:
        raise ValueError("at least one operator is required")
    R, n = operators[0].base_ring(), operators[0].nrows()
    if any(T.base_ring() != R or T.dimensions() != (n, n) for T in operators):
        raise ValueError("polynomial operator ring/shape mismatch")
    result = matrix(R, n, n)
    powers = {}
    for coefficient, exponents in terms:
        if len(exponents) != len(operators):
            raise ValueError("one exponent is required per operator")
        term = identity_matrix(R, n)
        for i, e in enumerate(exponents):
            e = ZZ(e)
            if e < 0:
                raise ValueError("negative polynomial exponent")
            if e:
                if (i, e) not in powers:
                    powers[i, e] = operators[i]**e
                term *= powers[i, e]
        result += R(ZZ(coefficient))*term
    return result


def polynomial_terms(F):
    """Convert a Sage polynomial to the same sparse JSON-compatible term list."""
    terms = []
    for exponent, coefficient in F.dict().items():
        powers = [int(exponent)] if F.parent().ngens() == 1 else list(map(int, exponent))
        terms.append([str(ZZ(coefficient)), powers])
    return sorted(terms, key=lambda term: term[1])

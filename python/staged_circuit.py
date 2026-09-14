"""Common-chain presentations of nested linear relations on a mixed module.

All auxiliary elements, including terminal rho, belong to the supplied module.
In particular, supplying ideal-image coordinates imposes membership in the
ideal, not merely in the ambient Manin module. No global divided operator
or all-weight transfer theorem is assumed. The module and function names
retain 'staged' for compatibility; they test a fixed common-chain
presentation, not the full independent-monomial polynomial relation.
"""

from sage.all import ZZ, matrix, identity_matrix, zero_matrix
from mixed_endomorphisms import (
    mixed_matrix_is_zero, mixed_endomorphism_is_well_defined,
)
from pari_kernel import pari_howell_row_span


def verify_staged_polynomial(F, operators, divisions, coordinate_moduli,
                             p, b=1, howell_fallback=True,
                             max_howell_dimension=4096):
    """Test full domain of a fixed nested common-chain presentation.

    ``F`` is a multivariate polynomial over Z/p^m. ``operators`` maps
    variable names to ordinary, already oriented matrices. ``divisions``
    maps each subsequent variable to (numerator polynomial, exponent).
    Numerators may involve only earlier variables, in polynomial-ring
    order. For example T, A, D with A=T/9 and D=Q(A)/9.

    Monomials are evaluated rightmost-variable first: A^i D^j x is formed
    by j successive D circuits followed by i A circuits. Repeated calls
    to the same variable on the same input share intermediate elements. This fixes
    the precise finite circuit being tested; failure is not a claim that
    the manuscript's larger independent-monomial relation has failed.

    First try explicit coordinatewise preimages and replay every equation.
    On failure, Howell image membership solves the entire simultaneous
    linear system, without fixing those preimages. The latter proves
    full domain, but does not extract the auxiliary elements. Resource errors propagate;
    they are not mathematical failures. No scalar cancellation in a
    torsion module is used. ``b`` specifies output = p^b rho inside M.
    ``max_howell_dimension`` limits the dense fallback to avoid exhausting
    notebook memory (None disables the guard). Hitting it is inconclusive.
    """
    R = F.base_ring()
    p, b = ZZ(p), ZZ(b)
    modulus = ZZ(R.characteristic())
    if not p.is_prime() or modulus <= 1 or modulus != p**modulus.valuation(p):
        raise ValueError("the coefficient ring must have prime-power characteristic")
    m = modulus.valuation(p)
    if b < 0 or b > m:
        raise ValueError("terminal exponent must lie between 0 and m")
    names = F.parent().variable_names()
    mods = tuple(ZZ(t) for t in coordinate_moduli)
    rank = len(mods)
    if any(t <= 1 or modulus % t or t != p**t.valuation(p) for t in mods):
        raise ValueError("cyclic moduli must be nontrivial powers of p dividing p^m")
    if set(operators) & set(divisions) or set(operators) | set(divisions) != set(names):
        raise ValueError("define every polynomial variable exactly once")
    Id = identity_matrix(R, rank)
    ordinary = {}
    for name, value in operators.items():
        value = matrix(R, value)
        if value.dimensions() != (rank, rank) or not mixed_endomorphism_is_well_defined(value, mods):
            raise ValueError("ordinary operator is not an endomorphism of the supplied module")
        ordinary[name] = value
    for name, (Q, a) in divisions.items():
        if Q.parent() != F.parent() or ZZ(a) <= 0 or ZZ(a) > m:
            raise ValueError("invalid numerator ring or division exponent")
        if any(names.index(str(v)) >= names.index(name) for v in Q.variables()):
            raise ValueError("a numerator may use only earlier variables")

    # Node 0 is x. Each subsequent node y has equation p^a y = sum x_j B_j.
    steps, cache = [], {}

    def apply(name, node):
        """Append one operator or division equation and return its intermediate-element index.

        Reuse the same output when this common-chain presentation repeats an application.
        """
        key = (name, node)
        if key in cache:
            return cache[key]
        if name in ordinary:
            exponent, terms = 0, {node: ordinary[name]}
        else:
            Q, exponent = divisions[name]
            # Keep scalar coefficients scalar: multiplying by a dense c*Id
            # would turn a row scaling into an unnecessary matrix product.
            terms = polynomial(Q, node)
        steps.append((ZZ(exponent), terms))
        result = len(steps)
        cache[key] = result
        return result

    def polynomial(Q, node):
        """Expand the polynomial at the given input, applying rightmost relations first and collecting equal outputs."""
        terms = {}
        for powers, coefficient in Q.dict().items():
            current = node
            for name, power in reversed(list(zip(names, powers))):
                for _ in range(power):
                    current = apply(name, current)
            terms[current] = terms.get(current, R(0)) + coefficient
        return {j: c for j, c in terms.items() if c}

    terminal = polynomial(F, 0)

    def preimage(value, exponent):
        """Choose coordinatewise outputs for p^a y=u, or return None if division is impossible.

        These are elementwise choices, not necessarily a divided endomorphism.
        """
        answer = zero_matrix(R, rank, rank)
        divisor = p**exponent
        for i in range(rank):
            for j, target in enumerate(mods):
                entry = ZZ(value[i, j]) % target
                if entry % divisor.gcd(target):
                    return None
                answer[i, j] = entry // divisor
        return answer

    values = [Id]
    greedy = True
    for exponent, terms in steps:
        rhs = sum((values[j]*B for j, B in terms.items()), zero_matrix(R, rank, rank))
        y = preimage(rhs, exponent)
        if y is None:
            greedy = False
            break
        if not mixed_matrix_is_zero(p**exponent*y-rhs, mods):
            raise ArithmeticError("division witness replay failed")
        values.append(y)
    if greedy:
        output = sum((c*values[j] for j, c in terminal.items()), zero_matrix(R, rank, rank))
        rho = preimage(output, b)
        greedy = rho is not None
        if greedy and not mixed_matrix_is_zero(output-p**b*rho, mods):
            raise ArithmeticError("terminal witness replay failed")
    report = {"passed": bool(greedy), "relation": F,
              "rank": rank, "coordinate_moduli": mods,
              "staged_nodes": len(steps), "terminal_power": b,
              "verification_route": "explicit_witness_replay" if greedy else None,
              "witnesses_replayed": bool(greedy), "howell_attempted": False}
    if greedy:
        return report
    if not howell_fallback:
        report.update(passed=None, verification_route="inconclusive_greedy_choices")
        return report

    # Unknowns are nodes 1,...,N and rho. Columns are the N equations
    # and the terminal equation, each interpreted with its own cyclic moduli.
    count = len(steps) + 1
    size = rank*count
    if max_howell_dimension is not None and size > max_howell_dimension:
        raise MemoryError(
            f"common-chain Howell system has dimension {size}, exceeding "
            f"max_howell_dimension={max_howell_dimension}; the greedy "
            "choices failed, but full domain of the presentation is still untested"
        )
    system = zero_matrix(R, size, size)
    rhs = zero_matrix(R, rank, size)
    for column, (exponent, terms) in enumerate(steps):
        system.set_block(column*rank, column*rank, p**exponent*Id)
        for node, B in terms.items():
            B = B if hasattr(B, 'nrows') else B*Id
            if node == 0:
                rhs.set_block(0, column*rank, B)
            else:
                system.set_block((node-1)*rank, column*rank, -B)
    last = (count-1)*rank
    for node, coefficient in terminal.items():
        if node == 0:
            rhs.set_block(0, last, -coefficient*Id)
        else:
            system.set_block((node-1)*rank, last, coefficient*Id)
    system.set_block(last, last, -p**b*Id)
    relations = zero_matrix(R, size, size)
    for j, target in enumerate(mods*count):
        relations[j, j] = R(target)
    image = system.stack(relations)
    base = pari_howell_row_span(image)["H_pari"]
    enlarged = pari_howell_row_span(image.stack(rhs))["H_pari"]
    report.update(passed=bool(base == enlarged), howell_attempted=True,
                  verification_route="simultaneous_howell")
    return report

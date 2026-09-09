"""High-level verification of ordinary and divided Hecke identities."""

from sage.all import (
    ZZ,
    block_matrix,
    diagonal_matrix,
    identity_matrix,
    matrix,
    vector,
    zero_matrix,
)

from pari_kernel import pari_howell_row_span

from hecke_action import (
    ambient_hecke_matrix,
    hecke_matrix_from_ambient_on_manin_quotient,
    hecke_matrix_on_manin_quotient,
    hecke_matrix_on_signed_manin_quotient,
)
from mixed_endomorphisms import (
    mixed_matrix_is_zero,
    mixed_matrix_is_zero_mod_p_power,
    mixed_endomorphism_is_well_defined,
    divide_mixed_endomorphism_by_p_power,
    normalize_mixed_matrix,
)


from compute_source_data import prepare_source_data


def _hecke_matrix_on_source(n, data, check_descent):
    archived = data.get("archived_hecke_matrices")

    if archived is not None:
        if check_descent:
            raise NotImplementedError(
                "an archived replay bundle does not contain the "
                "ambient Manin relations needed to recheck descent"
            )

        n = ZZ(n)

        if n not in archived:
            available = ", ".join(
                f"T_{index}" for index in sorted(archived)
            )
            raise KeyError(
                f"T_{n} is not stored in the source bundle; "
                f"available operators: {available}"
            )

        return archived[n]

    if data["p"] == 2:
        if check_descent:
            ambient_T = ambient_hecke_matrix(
                n,
                data["d"],
                data["coefficient_ring"],
            )

            return hecke_matrix_from_ambient_on_manin_quotient(
                ambient_T,
                data["presentation"],
                data["coordinates"],
            )

        return hecke_matrix_on_manin_quotient(
            n,
            data["presentation"],
            data["coordinates"],
        )

    return hecke_matrix_on_signed_manin_quotient(
        n,
        data["presentation"],
        data["coordinates"],
        check_descent=check_descent,
    )


def _vacuous_result(data, F, n, reason):
    return {
        "degree": data["d"],
        "source_scope": data.get("source_scope", "manin"),
        "operator": f"T_{n}",
        "residue": data["d"] % data["period"],
        "relation": F,
        "orientation": data["q"],
        "sign": data["sign"],
        "rank": 0,
        "coordinate_moduli": tuple(),
        "passed": True,
        "vacuous": True,
        "reason": reason,
    }


def _rows_lie_in_p_power(
    rows,
    coordinate_moduli,
    p,
    a,
):
    """Test whether the represented elements lie in ``p^a M``."""
    p = ZZ(p)
    a = ZZ(a)
    coordinate_moduli = tuple(
        ZZ(value) for value in coordinate_moduli
    )
    rows = normalize_mixed_matrix(
        rows,
        coordinate_moduli,
    )

    return all(
        ZZ(rows[i, j]) % p**min(
            a,
            coordinate_moduli[j].valuation(p),
        ) == 0
        for i in range(rows.nrows())
        for j in range(rows.ncols())
    )


def _divide_rows_by_p_power(
    rows,
    coordinate_moduli,
    p,
    a,
):
    """Return one canonical elementwise quotient, or ``None``."""
    p = ZZ(p)
    a = ZZ(a)
    coordinate_moduli = tuple(
        ZZ(value) for value in coordinate_moduli
    )
    rows = normalize_mixed_matrix(
        rows,
        coordinate_moduli,
    )
    quotient = zero_matrix(
        ZZ,
        rows.nrows(),
        rows.ncols(),
    )

    for i in range(rows.nrows()):
        for j, target_modulus in enumerate(coordinate_moduli):
            exponent = target_modulus.valuation(p)
            divisor = p**min(a, exponent)
            value = ZZ(rows[i, j])

            if value % divisor:
                return None

            quotient[i, j] = (
                0
                if a >= exponent
                else value // p**a
            )

    return normalize_mixed_matrix(
        quotient,
        coordinate_moduli,
    )


def _canonical_staged_witnesses_exist(
    A,
    F,
    coordinate_moduli,
    p,
    a,
    b,
    source_generators=None,
    source_projection=None,
):
    """Try the canonical elementwise staged-division chain."""
    R = F.base_ring()
    coordinate_moduli = tuple(
        ZZ(value) for value in coordinate_moduli
    )
    rank = len(coordinate_moduli)
    identity = identity_matrix(R, rank)
    A = matrix(R, A)
    projection = (
        identity
        if source_projection is None
        else matrix(R, source_projection)
    )
    generators = matrix(
        R,
        projection
        if source_generators is None
        else source_generators,
    )

    if not mixed_endomorphism_is_well_defined(
        projection,
        coordinate_moduli,
    ):
        raise ArithmeticError(
            "the source projection is not a mixed endomorphism"
        )

    if not mixed_matrix_is_zero(
        projection**2 - projection,
        coordinate_moduli,
    ):
        raise ArithmeticError(
            "the source projection is not idempotent"
        )

    if not mixed_matrix_is_zero(
        projection*A - A*projection,
        coordinate_moduli,
    ):
        raise ArithmeticError(
            "the staged numerator does not commute with the "
            "source projection"
        )

    if not mixed_matrix_is_zero(
        generators*projection - generators,
        coordinate_moduli,
    ):
        raise ArithmeticError(
            "a supplied source generator is outside the "
            "projected summand"
        )

    witnesses = [
        normalize_mixed_matrix(
            generators,
            coordinate_moduli,
        )
    ]
    current = witnesses[0]

    for _ in range(F.degree()):
        quotient = _divide_rows_by_p_power(
            current*A,
            coordinate_moduli,
            p=p,
            a=a,
        )

        if quotient is None:
            return False

        current = normalize_mixed_matrix(
            matrix(R, quotient)*projection,
            coordinate_moduli,
        )
        witnesses.append(current)

    terminal = zero_matrix(
        ZZ,
        generators.nrows(),
        rank,
    )

    for j, witness in enumerate(witnesses):
        terminal += ZZ(F[j]) * witness

    return _rows_lie_in_p_power(
        terminal,
        coordinate_moduli,
        p=p,
        a=b,
    )
def verify_ordinary_identities(
    F,
    n,
    data,
    check_descent=False,
):
    """
    Test the ordinary identity F(chi_m(n)^q T_n) on a prepared source.

    Here F is a polynomial over R = Z/(p^m), and

        chi_m(n)^q = n^(q*p^(m-1)).

    The dictionary ``data`` is constructed once by
    ``prepare_source_data(R,d,q)`` and may be reused for several Hecke
    operators.  For odd p, the identity is tested on M_d^+ when q is
    even and on M_d^- when q is odd.  For p=2, one has q=0 and the
    identity is tested on the unsplit source M_d.

    The prepared data contain the Manin presentation and its
    finite-chain-ring quotient coordinates.  This function reuses
    those objects and computes only the operator-dependent twist and
    Hecke matrix.

    INPUT:

    ``F``
        A polynomial in one variable over Z/(p^m).

    ``n``
        The index of the prime-to-p Hecke operator T_n.

    ``data``
        The dictionary returned by ``prepare_source_data(R,d,q)``.
        Its coefficient ring must equal the base ring of F.

    ``check_descent``
        If true, verify directly that the Heilbronn--Merel operator
        preserves the relevant Manin relation module.
    """
    if not hasattr(F, "base_ring"):
        raise TypeError(
            "F must be a Sage polynomial"
        )

    if (
        F.base_ring()
        != data["coefficient_ring"]
    ):
        raise ValueError(
            "F and the prepared source must use "
            "the same coefficient ring"
        )

    n = ZZ(n)

    if n <= 0:
        raise ValueError("n must be positive")

    if n.gcd(data["p"]) != 1:
        raise ValueError(
            "the Hecke index n must be prime to p"
        )

    R = data["coefficient_ring"]
    q = data["q"]

    twist_scalar = R(n)**(
        q * data["p"]**(data["m"] - 1)
    )

    coordinates = data["coordinates"]

    if not coordinates["surviving_indices"]:
        return _vacuous_result(
            data,
            F,
            n,
            "the selected source module is zero",
        )

    Tn_data = _hecke_matrix_on_source(
        n,
        data,
        check_descent,
    )
    Tn = Tn_data["normalized_matrix"]
    moduli = tuple(Tn_data["coordinate_moduli"])
    passed = mixed_matrix_is_zero(
        F(twist_scalar* Tn),
        moduli,
    )

    return {
        "degree": data["d"],
        "source_scope": data.get("source_scope", "manin"),
        "operator": f"T_{n}",
        "residue": data["d"] % data["period"],
        "relation": F,
        "orientation": data["q"],
        "sign": data["sign"],
        "twist_scalar": twist_scalar,
        "rank": len(moduli),
        "coordinate_moduli": moduli,
        "passed": bool(passed),
        "vacuous": False,
        "reason": None,
    }

def verify_ordinary_joint_identities(
    F,
    hecke_indices,
    data,
    check_descent=False,
):
    """
    Test a joint ordinary Hecke identity on a prepared source.

    If

        F = F(X_1, ..., X_s)

    and

        hecke_indices = (n_1, ..., n_s),

    this tests

        F(
            chi_m(n_1)^q T_{n_1},
            ...,
            chi_m(n_s)^q T_{n_s}
        ) = 0

    on the source represented by ``data``, where

        chi_m(n)^q = n^(q*p^(m-1)).

    Sage's direct multivariable polynomial substitution is used. Thus
    the order of ``hecke_indices`` must agree with the order of the
    generators of the parent polynomial ring of F.

    INPUT:

    ``F``
        A multivariable Sage polynomial over Z/(p^m).

    ``hecke_indices``
        A tuple or list (n_1,...,n_s) of positive Hecke indices prime
        to p. The index n_i corresponds to the i-th generator of the
        parent polynomial ring of F.

    ``data``
        The dictionary returned by ``prepare_source_data(R,d,q)``.

    ``check_descent``
        If true, verify directly that every Heilbronn--Merel Hecke
        operator preserves the relevant Manin relation module.
    """
    if not hasattr(F, "base_ring"):
        raise TypeError(
            "F must be a Sage polynomial"
        )

    if F.base_ring() != data["coefficient_ring"]:
        raise ValueError(
            "F and the prepared source must use "
            "the same coefficient ring"
        )

    hecke_indices = tuple(
        ZZ(n) for n in hecke_indices
    )

    if not hecke_indices:
        raise ValueError(
            "at least one Hecke index is required"
        )

    if len(hecke_indices) != F.parent().ngens():
        raise ValueError(
            "the number of Hecke indices must equal "
            "the number of polynomial variables"
        )

    for n in hecke_indices:
        if n <= 0:
            raise ValueError(
                "every Hecke index must be positive"
            )

        if n.gcd(data["p"]) != 1:
            raise ValueError(
                "every Hecke index must be prime to p"
            )

    R = data["coefficient_ring"]
    q = data["q"]
    coordinates = data["coordinates"]

    operator_label = tuple(
        f"T_{n}" for n in hecke_indices
    )

    if not coordinates["surviving_indices"]:
        return {
            "degree": data["d"],
            "source_scope": data.get("source_scope", "manin"),
            "operators": operator_label,
            "hecke_indices": hecke_indices,
            "residue": data["d"] % data["period"],
            "relation": F,
            "orientation": data["q"],
            "sign": data["sign"],
            "twist_scalars": tuple(),
            "rank": 0,
            "coordinate_moduli": tuple(),
            "passed": True,
            "vacuous": True,
            "reason": "the selected source module is zero",
        }

    twist_scalars = []
    twisted_hecke_matrices = []
    moduli = None

    for n in hecke_indices:
        twist_scalar = R(n)**(
            q * data["p"]**(data["m"] - 1)
        )

        Tn_data = _hecke_matrix_on_source(
            n,
            data,
            check_descent,
        )

        current_moduli = tuple(
            Tn_data["coordinate_moduli"]
        )

        if moduli is None:
            moduli = current_moduli
        elif current_moduli != moduli:
            raise ArithmeticError(
                "the Hecke matrices use incompatible "
                "mixed quotient coordinates"
            )

        twist_scalars.append(twist_scalar)
        twisted_hecke_matrices.append(
            twist_scalar
            * Tn_data["normalized_matrix"]
        )

    # Sage directly substitutes the matrices for the generators
    # of the multivariable polynomial ring.
    relation_matrix = F(
        *twisted_hecke_matrices
    )

    passed = mixed_matrix_is_zero(
        relation_matrix,
        moduli,
    )

    return {
        "degree": data["d"],
        "source_scope": data.get("source_scope", "manin"),
        "operators": operator_label,
        "hecke_indices": hecke_indices,
        "residue": data["d"] % data["period"],
        "relation": F,
        "orientation": data["q"],
        "sign": data["sign"],
        "twist_scalars": tuple(twist_scalars),
        "rank": len(moduli),
        "coordinate_moduli": moduli,
        "passed": bool(passed),
        "vacuous": False,
        "reason": None,
    }

def _staged_witnesses_exist(
    A,
    F,
    coordinate_moduli,
    p,
    a,
    b,
    source_generators=None,
    source_projection=None,
):
    """
    Test whether every element of a mixed cyclic module admits staged
    p^a-division witnesses of terminal depth b for the pair (A,F).

    The module is

        M = direct_sum_i Z/(coordinate_moduli[i]),

    and matrices act on row vectors. If

        F(X) = c_0 + c_1*X + ... + c_nu*X^nu,

    the function tests, for every x_0 in M, whether there exist

        x_1, ..., x_nu, rho in M

    satisfying

        A*x_(j-1) = p^a*x_j

    for 1 <= j <= nu, and

        c_0*x_0 + ... + c_nu*x_nu = p^b*rho.

    By default, the standard cyclic generators of ``M`` are tested. If
    ``source_projection`` is supplied, the calculation is instead made
    on its image: ``source_generators`` must generate that image, and
    every unknown witness is constrained to lie in the image.
    """
    p = ZZ(p)
    a = ZZ(a)
    b = ZZ(b)

    if not p.is_prime():
        raise ValueError("p must be prime")

    if a <= 0:
        raise ValueError("a must be positive")

    if b < 0:
        raise ValueError("b must be nonnegative")

    if not hasattr(F, "base_ring"):
        raise TypeError("F must be a Sage polynomial")

    if F.degree() < 1:
        raise ValueError("F must have positive degree")

    R = F.base_ring()
    coordinate_moduli = tuple(
        ZZ(q) for q in coordinate_moduli
    )

    rank = len(coordinate_moduli)
    nu = ZZ(F.degree())

    if rank == 0:
        return True

    A = matrix(R, A)

    if A.dimensions() != (rank, rank):
        raise ValueError(
            "A must be a square matrix of size equal to "
            "the number of cyclic coordinates"
        )

    if not mixed_endomorphism_is_well_defined(
        A,
        coordinate_moduli,
    ):
        raise ArithmeticError(
            "A is not a well-defined endomorphism "
            "of the mixed cyclic module"
        )

    identity = identity_matrix(R, rank)

    if source_projection is None:
        projection = identity

        if source_generators is None:
            generators = identity
        else:
            generators = matrix(R, source_generators)
    else:
        projection = matrix(R, source_projection)

        if not mixed_endomorphism_is_well_defined(
            projection,
            coordinate_moduli,
        ):
            raise ArithmeticError(
                "the source projection is not a mixed endomorphism"
            )

        if not mixed_matrix_is_zero(
            projection**2 - projection,
            coordinate_moduli,
        ):
            raise ArithmeticError(
                "the source projection is not idempotent"
            )

        if not mixed_matrix_is_zero(
            projection*A - A*projection,
            coordinate_moduli,
        ):
            raise ArithmeticError(
                "the staged numerator does not commute with the "
                "source projection"
            )

        generators = matrix(
            R,
            projection
            if source_generators is None
            else source_generators,
        )

        if not mixed_matrix_is_zero(
            generators*projection - generators,
            coordinate_moduli,
        ):
            raise ArithmeticError(
                "a supplied source generator is outside the "
                "projected summand"
            )

    if generators.ncols() != rank:
        raise ValueError(
            "the source generators have the wrong number of columns"
        )

    # This is the first staged equation for every selected x_0.
    if not _rows_lie_in_p_power(
        generators*A,
        coordinate_moduli,
        p=p,
        a=a,
    ):
        return False

    blocks = [
        [
            zero_matrix(R, rank, rank)
            for _ in range(nu + 1)
        ]
        for _ in range(nu + 1)
    ]

    # Unknown block j represents x_(j+1).
    for j in range(nu):
        # Output block j:
        #     p^a*x_(j+1)
        blocks[j][j] = R(p**a) * projection

        # Output block j+1:
        #     p^a*x_(j+2) - A*x_(j+1)
        if j < nu - 1:
            blocks[j][j + 1] = -projection*A

        # Final output block:
        #     sum c_j*x_j - p^b*rho
        blocks[j][nu] = F[j + 1] * projection

    # The last unknown block is rho.
    blocks[nu][nu] = -R(p**b) * projection

    witness_matrix = block_matrix(
        R,
        blocks,
    )

    repeated_moduli = (
        coordinate_moduli * (nu + 1)
    )

    if not mixed_endomorphism_is_well_defined(
        witness_matrix,
        repeated_moduli,
    ):
        raise ArithmeticError(
            "the staged witness matrix is not a well-defined "
            "endomorphism of the repeated mixed module"
        )

    # These rows impose the cyclic relations in the target
    # M^(nu+1).
    target_relations = diagonal_matrix(
        R,
        [
            R(q)
            for q in repeated_moduli
        ],
    )

    image_generators = witness_matrix.stack(
        target_relations
    )

    # Construct the required right-hand side for every selected
    # generator x_0:
    #
    #     (A*x_0, 0, ..., 0, -c_0*x_0).
    right_hand_side_rows = []

    for i in range(generators.nrows()):
        x_0 = vector(R, generators.row(i))

        row_entries = list(x_0 * A)

        for _ in range(nu - 1):
            row_entries.extend(
                [R(0)] * rank
            )

        row_entries.extend(
            list(-F[0] * x_0)
        )

        right_hand_side_rows.append(
            row_entries
        )

    right_hand_sides = matrix(
        R,
        right_hand_side_rows,
    )

    base_howell = pari_howell_row_span(
        image_generators
    )["H_pari"]

    enlarged_howell = pari_howell_row_span(
        image_generators.stack(
            right_hand_sides
        )
    )["H_pari"]

    return enlarged_howell == base_howell


def verify_divided_identities(
    F,
    Q,
    n,
    a,
    b,
    data,
    check_descent=False,
):
    """
    Test staged p^a-division witnesses on a prepared source.

    Put

        A = Q(chi_m(n)^q*T_n).

    The function first tests

        A*M contained in p^a*M.

    It then solves the complete simultaneous witness system for the
    standard cyclic generators of M. Thus it tests whether every x_0
    admits elements x_1, ..., x_nu, rho satisfying

        A*x_(j-1) = p^a*x_j

    and

        c_0*x_0 + ... + c_nu*x_nu = p^b*rho,

    where F(X) = c_0 + ... + c_nu*X^nu.

    Because the elements admitting witnesses form a submodule, checking
    the standard cyclic generators is sufficient.

    When F is monic, the function first attempts the faster sufficient
    construction of a global endomorphism Z satisfying

        p^a*Z = A

    and tests

        p^a*F(Z) = 0.

    If this succeeds, monicity supplies staged witnesses directly. If
    the global division cannot be constructed, or if the scaled
    polynomial identity fails, the function falls back to the complete
    Howell staged-witness solver.
    """
    if not hasattr(F, "base_ring"):
        raise TypeError(
            "F must be a Sage polynomial"
        )

    if not hasattr(Q, "base_ring"):
        raise TypeError(
            "Q must be a Sage polynomial"
        )

    if (
        F.base_ring()
        != data["coefficient_ring"]
    ):
        raise ValueError(
            "F and the prepared source must use "
            "the same coefficient ring"
        )

    if (
        Q.base_ring()
        != data["coefficient_ring"]
    ):
        raise ValueError(
            "Q and the prepared source must use "
            "the same coefficient ring"
        )

    if F.degree() < 1:
        raise ValueError("F must have positive degree")

    n = ZZ(n)
    a = ZZ(a)
    b = ZZ(b)

    p = data["p"]
    m = data["m"]
    R = data["coefficient_ring"]
    q = data["q"]

    if n <= 0:
        raise ValueError("n must be positive")

    if n.gcd(p) != 1:
        raise ValueError(
            "the Hecke index n must be prime to p"
        )

    if a <= 0:
        raise ValueError("a must be positive")

    if b < 0 or b > m - a:
        raise ValueError(
            "the terminal depth must satisfy "
            "0 <= b <= m-a"
        )

    twist_scalar = R(n)**(
        q * p**(m - 1)
    )

    coordinates = data["coordinates"]

    if not coordinates["surviving_indices"]:
        result = _vacuous_result(
            data,
            F,
            n,
            "the selected source module is zero",
        )

        result.update({
            "numerator_polynomial": Q,
            "division_power": a,
            "terminal_power": b,
            "twist_scalar": twist_scalar,
            "division_passed": True,
            "terminal_passed": True,
            "global_fast_path_attempted": False,
            "global_division_constructed": False,
            "global_scaled_annihilation_passed": False,
            "verification_route": "vacuous",
        })

        return result

    Tn_data = _hecke_matrix_on_source(
        n,
        data,
        check_descent,
    )

    Tn = Tn_data["normalized_matrix"]
    moduli = tuple(
        Tn_data["coordinate_moduli"]
    )

    numerator = Q(
        twist_scalar * Tn
    )

    source_projection = data.get(
        "verification_projection"
    )
    source_generators = data.get(
        "verification_generators"
    )

    if source_projection is None:
        first_division_rows = numerator
    else:
        first_division_rows = (
            matrix(R, source_generators)
            * numerator
        )

    division_passed = _rows_lie_in_p_power(
        first_division_rows,
        moduli,
        p=p,
        a=a,
    )

    if not division_passed:
        return {
            "degree": data["d"],
            "source_scope": data.get("source_scope", "manin"),
            "operator": f"T_{n}",
            "numerator_polynomial": Q,
            "division_power": a,
            "relation": F,
            "terminal_power": b,
            "residue": data["d"] % data["period"],
            "orientation": data["q"],
            "sign": data["sign"],
            "twist_scalar": twist_scalar,
            "rank": len(moduli),
            "coordinate_moduli": moduli,
            "division_passed": False,
            "terminal_passed": False,
            "passed": False,
            "global_fast_path_attempted": False,
            "global_division_constructed": False,
            "global_scaled_annihilation_passed": False,
            "verification_route": "first_division_failure",
            "vacuous": False,
            "reason": (
                "Q(chi_m(n)^q*T_n) does not map the source "
                f"into p^{a} times the source"
            ),
        }

    global_fast_path_attempted = bool(
        F.is_monic()
    )

    global_division_constructed = False
    global_scaled_annihilation_passed = False
    canonical_staged_chain_passed = False

    if global_fast_path_attempted:
        try:
            Z = divide_mixed_endomorphism_by_p_power(
                numerator,
                moduli,
                p=p,
                a=a,
            )

        except ArithmeticError:
            Z = None

        else:
            global_division_constructed = True

            scaled_relation = p**a * F(Z)

            if source_projection is not None:
                scaled_relation = (
                    matrix(R, source_generators)
                    * scaled_relation
                )

            global_scaled_annihilation_passed = mixed_matrix_is_zero(
                scaled_relation,
                moduli,
            )

    if global_scaled_annihilation_passed:
        terminal_passed = True
        verification_route = (
            "global_scaled_annihilation"
        )

    else:
        canonical_staged_chain_passed = (
            _canonical_staged_witnesses_exist(
                numerator,
                F,
                moduli,
                p=p,
                a=a,
                b=b,
                source_generators=source_generators,
                source_projection=source_projection,
            )
        )

        if canonical_staged_chain_passed:
            terminal_passed = True
            verification_route = "canonical_staged_chain"
        else:
            terminal_passed = _staged_witnesses_exist(
                numerator,
                F,
                moduli,
                p=p,
                a=a,
                b=b,
                source_generators=source_generators,
                source_projection=source_projection,
            )

            verification_route = (
                "howell_staged_witness_fallback"
            )

    return {
        "degree": data["d"],
        "source_scope": data.get("source_scope", "manin"),
        "operator": f"T_{n}",
        "numerator_polynomial": Q,
        "division_power": a,
        "relation": F,
        "terminal_power": b,
        "residue": data["d"] % data["period"],
        "orientation": data["q"],
        "sign": data["sign"],
        "twist_scalar": twist_scalar,
        "rank": len(moduli),
        "coordinate_moduli": moduli,
        "division_passed": True,
        "terminal_passed": bool(terminal_passed),
        "passed": bool(terminal_passed),
        "global_fast_path_attempted": (
            global_fast_path_attempted
        ),
        "global_division_constructed": (
            global_division_constructed
        ),
        "global_scaled_annihilation_passed": (
            global_scaled_annihilation_passed
        ),
        "canonical_staged_chain_passed": (
            canonical_staged_chain_passed
        ),
        "verification_route": verification_route,
        "vacuous": False,
        "reason": (
            None
            if terminal_passed
            else (
                "the first staged division holds, but the complete "
                "terminal witness system is not solvable for every "
                "source generator"
            )
        ),
    }


def verify_divided_joint_identities(
    F,
    Q,
    hecke_indices,
    a,
    b,
    data,
    check_descent=False,
):
    """
    Test a staged division relation with a joint Hecke numerator.

    If

        Q = Q(X_1, ..., X_s)

    and ``hecke_indices = (n_1, ..., n_s)``, put

        A = Q(
            chi_m(n_1)^q*T_{n_1},
            ...,
            chi_m(n_s)^q*T_{n_s}
        ).

    The function tests whether every element of the prepared signed
    source admits staged ``p^a``-division witnesses of terminal depth
    ``b`` for the pair ``(A,F)``.  Equivalently, it first tests

        A*M contained in p^a*M

    and then solves the complete simultaneous staged-witness system
    for the standard cyclic generators of ``M``.  Sage's direct
    multivariable substitution is used, so the order of
    ``hecke_indices`` must agree with the order of the generators of
    the parent polynomial ring of ``Q``.

    When ``F`` is monic, the same global-division fast path as in
    ``verify_divided_identities`` is attempted before the complete
    Howell solver.

    INPUT:

    ``F``
        A positive-degree polynomial in one variable over Z/(p^m).

    ``Q``
        A multivariable polynomial over Z/(p^m), giving the numerator
        of the divided operator.

    ``hecke_indices``
        A tuple ``(n_1,...,n_s)`` of positive Hecke indices prime to p.

    ``a``
        The positive division exponent.

    ``b``
        The terminal depth, satisfying ``0 <= b <= m-a``.

    ``data``
        The dictionary returned by ``prepare_source_data(R,d,q)``.

    ``check_descent``
        If true, verify directly that every Heilbronn--Merel operator
        descends to the prepared Manin quotient.
    """
    if not hasattr(F, "base_ring"):
        raise TypeError("F must be a Sage polynomial")

    if not hasattr(Q, "base_ring"):
        raise TypeError("Q must be a Sage polynomial")

    R = data["coefficient_ring"]

    if F.base_ring() != R:
        raise ValueError(
            "F and the prepared source must use "
            "the same coefficient ring"
        )

    if Q.base_ring() != R:
        raise ValueError(
            "Q and the prepared source must use "
            "the same coefficient ring"
        )

    if F.degree() < 1:
        raise ValueError("F must have positive degree")

    hecke_indices = tuple(
        ZZ(n) for n in hecke_indices
    )

    if not hecke_indices:
        raise ValueError(
            "at least one Hecke index is required"
        )

    if len(hecke_indices) != Q.parent().ngens():
        raise ValueError(
            "the number of Hecke indices must equal "
            "the number of numerator variables"
        )

    p = data["p"]
    m = data["m"]
    q = data["q"]
    a = ZZ(a)
    b = ZZ(b)

    for n in hecke_indices:
        if n <= 0:
            raise ValueError(
                "every Hecke index must be positive"
            )

        if n.gcd(p) != 1:
            raise ValueError(
                "every Hecke index must be prime to p"
            )

    if a <= 0:
        raise ValueError("a must be positive")

    if b < 0 or b > m - a:
        raise ValueError(
            "the terminal depth must satisfy "
            "0 <= b <= m-a"
        )

    operator_label = tuple(
        f"T_{n}" for n in hecke_indices
    )
    twist_scalars = tuple(
        R(n)**(q * p**(m - 1))
        for n in hecke_indices
    )
    coordinates = data["coordinates"]

    if not coordinates["surviving_indices"]:
        return {
            "degree": data["d"],
            "source_scope": data.get("source_scope", "manin"),
            "operators": operator_label,
            "hecke_indices": hecke_indices,
            "numerator_polynomial": Q,
            "division_power": a,
            "relation": F,
            "terminal_power": b,
            "residue": data["d"] % data["period"],
            "orientation": data["q"],
            "sign": data["sign"],
            "twist_scalars": twist_scalars,
            "rank": 0,
            "coordinate_moduli": tuple(),
            "division_passed": True,
            "terminal_passed": True,
            "passed": True,
            "global_fast_path_attempted": False,
            "global_division_constructed": False,
            "global_scaled_annihilation_passed": False,
            "verification_route": "vacuous",
            "vacuous": True,
            "reason": "the selected source module is zero",
        }

    twisted_hecke_matrices = []
    moduli = None

    for n, twist_scalar in zip(
        hecke_indices,
        twist_scalars,
    ):
        Tn_data = _hecke_matrix_on_source(
            n,
            data,
            check_descent,
        )
        current_moduli = tuple(
            Tn_data["coordinate_moduli"]
        )

        if moduli is None:
            moduli = current_moduli
        elif current_moduli != moduli:
            raise ArithmeticError(
                "the Hecke matrices use incompatible "
                "mixed quotient coordinates"
            )

        twisted_hecke_matrices.append(
            twist_scalar
            * Tn_data["normalized_matrix"]
        )

    numerator = Q(*twisted_hecke_matrices)
    division_passed = mixed_matrix_is_zero_mod_p_power(
        numerator,
        moduli,
        p=p,
        a=a,
    )

    common = {
        "degree": data["d"],
        "source_scope": data.get("source_scope", "manin"),
        "operators": operator_label,
        "hecke_indices": hecke_indices,
        "numerator_polynomial": Q,
        "division_power": a,
        "relation": F,
        "terminal_power": b,
        "residue": data["d"] % data["period"],
        "orientation": data["q"],
        "sign": data["sign"],
        "twist_scalars": twist_scalars,
        "rank": len(moduli),
        "coordinate_moduli": moduli,
    }

    if not division_passed:
        return {
            **common,
            "division_passed": False,
            "terminal_passed": False,
            "passed": False,
            "global_fast_path_attempted": False,
            "global_division_constructed": False,
            "global_scaled_annihilation_passed": False,
            "verification_route": "first_division_failure",
            "vacuous": False,
            "reason": (
                "the joint numerator does not map the source "
                f"into p^{a} times the source"
            ),
        }

    global_fast_path_attempted = bool(F.is_monic())
    global_division_constructed = False
    global_scaled_annihilation_passed = False

    if global_fast_path_attempted:
        try:
            Z = divide_mixed_endomorphism_by_p_power(
                numerator,
                moduli,
                p=p,
                a=a,
            )
        except ArithmeticError:
            Z = None
        else:
            global_division_constructed = True
            global_scaled_annihilation_passed = (
                mixed_matrix_is_zero(
                    p**a * F(Z),
                    moduli,
                )
            )

    if global_scaled_annihilation_passed:
        terminal_passed = True
        verification_route = "global_scaled_annihilation"
    else:
        terminal_passed = _staged_witnesses_exist(
            numerator,
            F,
            moduli,
            p=p,
            a=a,
            b=b,
        )
        verification_route = "howell_staged_witness_fallback"

    return {
        **common,
        "division_passed": True,
        "terminal_passed": bool(terminal_passed),
        "passed": bool(terminal_passed),
        "global_fast_path_attempted": global_fast_path_attempted,
        "global_division_constructed": global_division_constructed,
        "global_scaled_annihilation_passed": (
            global_scaled_annihilation_passed
        ),
        "verification_route": verification_route,
        "vacuous": False,
        "reason": (
            None
            if terminal_passed
            else (
                "the first staged division holds, but the complete "
                "terminal witness system is not solvable for every "
                "source generator"
            )
        ),
    }

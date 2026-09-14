"""Compute Heilbronn--Merel actions on direct sources and their ideal images.

Matrices act on row vectors; column j is interpreted modulo the order of
the j-th cyclic coordinate. The recursive construction retains Dickson
transfer maps and complementary generators, without replacing the direct
Manin module by its torsion-free quotient. Descent checks, when requested,
test preservation of the defining relation submodule.
"""

from sage.all import (
    ZZ,
    gcd,
    matrix,
    zero_matrix,
)

from sage.modular.modsym.heilbronn import HeilbronnMerel
from types import SimpleNamespace

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
    """Check that the ambient operator preserves the Manin relation submodule.

    Return False for a dimension mismatch or a relation image that is nonzero in the quotient.
    """
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
        (quotient_coordinates["V_R_inverse"] if "V_R_inverse" in quotient_coordinates else V_R.inverse())
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
    V_inverse = quotient_coordinates["V_R_inverse"] if "V_R_inverse" in quotient_coordinates else V.inverse()

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
    V_inverse = quotient_coordinates["V_R_inverse"] if "V_R_inverse" in quotient_coordinates else V.inverse()
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


class RecursiveContext:
    """Section 3.10 exact complementary Manin presentations below a_m+b_m.

    This is the Sage counterpart of Nim's RecursiveContext. Lower modules
    and coefficient splittings are reused; only new complement Hecke images
    are computed. Both signs supply U-relations. No torsion is discarded.
    """

    def __init__(self, R, hecke_indices, retain_lifts=True):
        """Initialize recursive source construction over R=Z/p^m Z for the selected prime-to-p Hecke indices.

        Store the Dickson degree shifts and empty caches; no source is constructed here.
        """
        factors = list(ZZ(R.characteristic()).factor())
        if len(factors) != 1:
            raise ValueError("require R=Z/p^m")
        self.p, self.m = factors[0]
        self.R = R
        self.t = self.p**(self.m-1)
        self.a = self.p*(self.p-1)*self.t
        self.b = (self.p+1)*self.t
        self.hecke_indices = tuple(ZZ(n) for n in hecke_indices)
        if len(set(self.hecke_indices)) != len(self.hecke_indices) or any(
            n <= 0 or n % self.p == 0 for n in self.hecke_indices
        ):
            raise ValueError("require distinct positive prime-to-p Hecke indices")
        self.A, self.B = None, None
        self.retain_lifts = retain_lifts
        self.modules, self.splits = {}, {}
        self.presented_sources = {}

    @staticmethod
    def indices(d, sign):
        """Return the monomial indices of the requested sign, or every index for the unsplit source."""
        return tuple(i for i in range(d+1) if sign == 0 or (-1)**i == sign)

    def coefficient_split(self, d, sign):
        """B-first monic division, followed by a full-precision unit-minor solve."""
        from sage.all import GF
        if d < self.b or d >= self.a+self.b:
            raise ValueError("coefficient split outside its injection range")
        if (d,sign) in self.splits:
            return self.splits[d,sign]
        if self.A is None:
            from modular_polynomial import dickson_polynomials
            self.A,self.B = dickson_polynomials(self.p,self.m,self.R)
        indices = self.indices(d,sign)
        ia, ib = self.indices(d-self.a,sign), self.indices(d-self.b,-sign)
        bc = tuple(i for i in indices if i < self.p*self.t or i > d-self.t)
        bq, br = matrix(self.R,len(indices),len(ib)), matrix(self.R,len(indices),len(bc))
        aq, ar = matrix(self.R,len(ia),len(ib)), matrix(self.R,len(ia),len(bc))
        x = self.B.parent().gen()
        for row,i in enumerate(indices):
            if i in bc:
                br[row,bc.index(i)] = 1
            else:
                q,r = (x**i).quo_rem(self.B)
                bq.set_row(row,[q[k] for k in ib])
                br.set_row(row,[r[k] for k in bc])
        for row,i in enumerate(ia):
            full = self.A*x**i
            truncated = full.truncate(d-self.t+1)
            q,r = truncated.quo_rem(self.B)
            aq.set_row(row,[q[k] for k in ib])
            ar.set_row(row,[full[k] if k > d-self.t else r[k] for k in bc])
        E = ar.change_ring(GF(self.p))
        pivots = []
        for i in range(E.nrows()):
            pivot = next((j for j in range(E.ncols()) if E[i,j]), None)
            if pivot is None:
                raise ArithmeticError("Dickson split is not injective modulo p")
            pivots.append(pivot)
            E.rescale_row(i,1/E[i,pivot])
            for k in range(i+1,E.nrows()):
                E.add_multiple_of_row(k,i,-E[k,pivot])
        remaining = [j for j in range(len(bc)) if j not in pivots]
        minor = ar.matrix_from_columns(pivots)
        from modular_matrix import inverse_unit_prime_power
        inverse = inverse_unit_prime_power(minor,self.p,self.m)
        split = SimpleNamespace(indices=indices,a_indices=ia,b_indices=ib,
            complement=tuple(bc[j] for j in remaining),pivots=pivots,remaining=remaining,
            b_quotients=bq,b_remainders=br,a_quotients=aq,a_remainders=ar,pivot_inverse=inverse)
        self.splits[d,sign] = split
        return split

    def direct_module(self, d, sign):
        """Unit-compressed direct source with selected Hecke images and cached inverse."""
        from manin_quotient import direct_manin_presentation, direct_signed_manin_presentation
        from modular_matrix import chain_ring_coordinates
        P = (direct_manin_presentation(d,self.R,True) if sign == 0 else
             direct_signed_manin_presentation(d,self.R,sign,True))
        C = chain_ring_coordinates(P["H_R"].transpose())
        projection = C["V_R"].matrix_from_columns(C["surviving_indices"])
        representatives = C["V_R_inverse"].matrix_from_rows(C["surviving_indices"])
        reduction = P["compression_projection"]*projection
        section = P["compression_section"]
        indices = P["ambient_indices"]
        inputs = [indices[next(j for j,v in enumerate(row) if v)] for row in section.rows()]
        exponents = tuple(C["surviving_exponents"])
        moduli = tuple(self.p**e for e in exponents)
        actions = {}
        for n in self.hecke_indices:
            images = matrix(self.R,len(inputs),len(exponents))
            for gamma in heilbronn_merel_matrices(n):
                images += symmetric_power_action(gamma,d,self.R,inputs,indices)*reduction
            actions[n] = matrix(self.R,normalize_mixed_matrix(representatives*images,moduli))
        return SimpleNamespace(degree=d,sign=sign,indices=indices,exponents=exponents,
            reduction=reduction,lifts=representatives*section if self.retain_lifts else None,
            actions=actions,recursive=False)

    def build_modular_symbols_recursive(self, d, sign=0):
        """Construct the exact full-torsion quotient; never assume Manin injectivity."""
        from modular_matrix import unit_compression, chain_ring_coordinates
        if d < 0 or d % 2 or d >= self.a+self.b or sign not in (-1,0,1):
            raise ValueError("unsupported recursive degree/sign")
        if self.p == 2 and sign != 0:
            raise ValueError("p=2 requires the unsplit module")
        if self.p == 2 and self.m == 1:
            return self.direct_module(d,sign)
        if (d,sign) in self.modules:
            return self.modules[d,sign]
        if d < self.b:
            M = self.direct_module(d,sign)
            self.modules[d,sign] = M
            return M
        C = self.coefficient_split(d,sign)
        lower_b = self.build_modular_symbols_recursive(d-self.b,-sign)
        lower_a = self.build_modular_symbols_recursive(d-self.a,sign) if d >= self.a else None
        ga = len(lower_a.exponents) if lower_a is not None else 0
        gb, nw = len(lower_b.exponents), len(C.complement)
        f = C.b_remainders.matrix_from_columns(C.pivots)*C.pivot_inverse
        g = C.b_quotients-f*C.a_quotients
        w = C.b_remainders.matrix_from_columns(C.remaining)-f*C.a_remainders.matrix_from_columns(C.remaining)
        pre = matrix(self.R,len(C.indices),0)
        if lower_a is not None:
            pre = pre.augment(f*lower_a.reduction)
        pre = pre.augment(g*lower_b.reduction).augment(w)
        all_w = sorted(C.complement + (self.coefficient_split(d,-sign).complement if sign else ()))
        positions = {i:j for j,i in enumerate(C.indices)}
        S_rows = matrix(self.R,len(all_w),ga+gb+nw)
        for j,i in enumerate(all_w):
            if i in positions:
                S_rows.set_row(j,S_rows.row(j)+pre.row(positions[i]))
            if d-i in positions:
                S_rows.set_row(j,S_rows.row(j)+(-1)**i*pre.row(positions[d-i]))
        unit_projection, unit_section, _ = unit_compression(S_rows,ga+gb)
        small_pre = pre*unit_projection
        raw = matrix(self.R,ga+gb,unit_projection.ncols())
        orders = (() if lower_a is None else lower_a.exponents) + lower_b.exponents
        for i,e in enumerate(orders):
            raw.set_row(i,self.p**e*unit_projection.row(i))
        raw = raw.stack(S_rows*unit_projection)
        U_rows = matrix(self.R,len(all_w),unit_projection.ncols())
        for gamma in (matrix(self.R,[[1,-1],[1,0]]),matrix(self.R,[[0,-1],[1,-1]])):
            U_rows += symmetric_power_action(gamma,d,self.R,all_w,C.indices)*small_pre
        for j,i in enumerate(all_w):
            if i in positions:
                U_rows.set_row(j,U_rows.row(j)+small_pre.row(positions[i]))
        coordinates = chain_ring_coordinates(raw.stack(U_rows))
        projection = coordinates["V_R"].matrix_from_columns(coordinates["surviving_indices"])
        representatives = coordinates["V_R_inverse"].matrix_from_rows(coordinates["surviving_indices"])*unit_section
        reduction = small_pre*projection
        pre_projection = unit_projection*projection
        exponents = tuple(coordinates["surviving_exponents"])
        moduli = tuple(self.p**e for e in exponents)
        actions = {}
        for n in self.hecke_indices:
            images = matrix(self.R,0,len(exponents))
            if lower_a is not None:
                images = images.stack(lower_a.actions[n]*pre_projection.matrix_from_rows(range(ga)))
            images = images.stack(self.R(n)**self.t*lower_b.actions[n]*pre_projection.matrix_from_rows(range(ga,ga+gb)))
            fresh = matrix(self.R,nw,len(exponents))
            for gamma in heilbronn_merel_matrices(n):
                fresh += symmetric_power_action(gamma,d,self.R,C.complement,C.indices)*reduction
            action = matrix(self.R,normalize_mixed_matrix(representatives*images.stack(fresh),moduli))
            if not mixed_endomorphism_is_well_defined(action,moduli):
                raise ArithmeticError("recursive action violates cyclic orders")
            actions[n] = action
        lifts = None
        if self.retain_lifts:
            h_lifts = matrix(self.R,ga+gb+nw,len(C.indices))
            x = self.A.parent().gen()
            for lower,multiplier,offset in ((lower_a,self.A,0),(lower_b,self.B,ga)):
                if lower is None:
                    continue
                for i,row in enumerate(lower.lifts.rows()):
                    v = sum(row[j]*x**k for j,k in enumerate(lower.indices))
                    product = multiplier*v
                    h_lifts.set_row(offset+i,[product[k] for k in C.indices])
            for j,i in enumerate(C.complement):
                h_lifts[ga+gb+j,positions[i]] = 1
            lifts = representatives*h_lifts
        M = SimpleNamespace(degree=d,sign=sign,indices=C.indices,exponents=exponents,
            reduction=reduction,lifts=lifts,actions=actions,recursive=True)
        self.modules[d,sign] = M
        return M

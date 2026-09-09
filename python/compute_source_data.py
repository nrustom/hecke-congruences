"""Uniform Sage source construction, matching compute_source_data.nim.

Public source dictionaries can be passed unchanged to the ordinary/joint
and presented-linear-relation verifiers. An ideal-image source is always labelled.
"""
from sage.all import ZZ, matrix, diagonal_matrix
from manin_quotient import (direct_manin_presentation, direct_signed_manin_presentation,
                            chain_ring_manin_quotient_coordinates, symmetric_power_action)
from hecke_action import RecursiveContext, heilbronn_merel_matrices
from mixed_endomorphisms import image_coordinates
from modular_polynomial import evaluate_polynomial, polynomial_terms


def prepare_source_data(R, d, q, *, hecke_indices=None, ideal=None,
                        recursive=False, context=None, audit=False):
    """Prepare M_d or I M_d at orientation q over any Z/p^m.

    With only (R,d,q), preserve the notebook interface: prepare the direct
    Manin presentation and cyclic coordinates; compute Hecke actions lazily.
    Supply ``hecke_indices`` to share their construction. ``recursive=True``
    uses Section 3.10 below a_m+b_m, including all complement relations.

    ``ideal`` is {"scalar":s,"generators":[F1,...]} with Sage polynomials
    or sparse term lists (variables follow hecke_indices). Either entry may
    be omitted. No scalar generator is compulsory. The ideal is evaluated
    on chi_m(n)^q*T_n, whereas the returned actions are untwisted.
    With recursive=False an ideal is computed without Smith-reducing M.

    ``context`` may be a reusable RecursiveContext for the same ring/operators.
    This constructs sources only; it does not verify propagation hypotheses.
    """
    d, q = ZZ(d), ZZ(q)
    factors = list(ZZ(R.characteristic()).factor())
    if len(factors) != 1 or d < 0 or d % 2 or q < 0:
        raise ValueError("require R=Z/p^m, even d>=0 and q>=0")
    p, m = factors[0]
    if p == 2 and q != 0:
        raise ValueError("p=2 requires the unsplit source and q=0")
    sign = None if p == 2 else (-1)**q
    common = {"coefficient_ring":R,"modulus":p**m,"p":p,"m":m,
              "period":p**(m-1)*(p-1),"d":d,"q":q,"sign":sign,
              "source_scope":"manin" if ideal is None else "ideal_image"}
    if hecke_indices is None:
        if recursive or ideal is not None or context is not None:
            raise ValueError("supply hecke_indices for recursive/ideal sources")
        P = (direct_manin_presentation(d,R,True) if sign is None else
             direct_signed_manin_presentation(d,R,sign,True))
        return {**common,"presentation":P,"coordinates":chain_ring_manin_quotient_coordinates(P)}
    indices = tuple(ZZ(n) for n in hecke_indices)
    if not indices:
        raise ValueError("supply at least one Hecke index")
    ctx = context or RecursiveContext(R,indices,retain_lifts=False)
    if ctx.R != R or ctx.hecke_indices != indices:
        raise ValueError("source context ring or operator order mismatch")
    if ideal is not None and (not isinstance(ideal,dict) or set(ideal)-{"scalar","generators"}):
        raise ValueError("ideal fields are scalar and generators")
    if ideal is not None and not recursive:
        # Keep at most this degree's two sign presentations in a shared context.
        ctx.presented_sources = {key:value for key,value in ctx.presented_sources.items() if key[0]==d}
        key = (d,sign)
        if key in ctx.presented_sources:
            B,actions = ctx.presented_sources[key]
        else:
            P = (direct_manin_presentation(d,R,True) if sign is None else
                 direct_signed_manin_presentation(d,R,sign,True))
            B = P["H_R"].transpose()
            section = P["compression_section"]
            inputs = [P["ambient_indices"][next(j for j,v in enumerate(row) if v)] for row in section.rows()]
            actions = {}
            for n in indices:
                T = matrix(R,section.nrows(),section.nrows())
                for gamma in heilbronn_merel_matrices(n):
                    T += symmetric_power_action(gamma,d,R,inputs,P["ambient_indices"])*P["compression_projection"]
                actions[n] = T
            ctx.presented_sources[key] = (B,actions)
    else:
        M = (ctx.build_modular_symbols_recursive(d,sign or 0) if recursive else ctx.direct_module(d,sign or 0))
        B = diagonal_matrix(R,[p**e for e in M.exponents])
        actions, exponents = M.actions, M.exponents
    if ideal is not None:
        twisted = [R(n)**(q*ctx.t)*actions[n] for n in indices]
        generators = matrix(R,0,B.ncols())
        for F in ideal.get("generators",[]):
            terms = polynomial_terms(F) if hasattr(F,"dict") else F
            generators = generators.stack(evaluate_polynomial(terms,twisted))
        H = image_coordinates(B,generators,actions,scalar=ideal.get("scalar",0),audit=audit)
        actions, exponents = H["actions"], tuple(H["coordinates"]["surviving_exponents"])
        common["ideal"] = ideal
    moduli = tuple(p**e for e in exponents)
    return {**common,"presentation":None,
            "coordinates":{"surviving_indices":tuple(range(len(exponents))),
                           "surviving_exponents":exponents,"coordinate_moduli":moduli,
                           "quotient_is_free":all(e==m for e in exponents)},
            "archived_hecke_matrices":{
                n:{"matrix":T,"normalized_matrix":T,"coordinate_exponents":exponents,
                   "coordinate_moduli":moduli,"base_ring":R} for n,T in actions.items()}}

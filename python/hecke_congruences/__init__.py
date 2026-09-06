"""SageMath tools for explicit Manin-quotient and Hecke computations."""

from hecke_action import (
    ambient_hecke_matrix,
    ambient_operator_descends,
    hecke_matrix_from_ambient_on_manin_quotient,
    hecke_matrix_on_manin_quotient,
    hecke_matrix_on_signed_manin_quotient,
    heilbronn_merel_matrices,
)
from identity_verification import (
    prepare_source_data,
    verify_divided_identities,
    verify_divided_joint_identities,
    verify_ordinary_identities,
    verify_ordinary_joint_identities,
)
from load_source_data import load_source_data
from manin_quotient import (
    annihilates_manin_quotient,
    chain_ring_manin_quotient_coordinates,
    direct_manin_presentation,
    direct_signed_manin_presentation,
    is_zero_in_manin_quotient,
    manin_class_exponent,
    manin_quotient_coordinates,
    rows_zero_in_manin_quotient,
    same_manin_class,
    signed_manin_quotient,
    symmetric_power_action,
)
from mixed_endomorphisms import (
    divide_mixed_endomorphism_by_p_power,
    is_power_of_prime,
    mixed_endomorphism_is_well_defined,
    mixed_matrix_is_zero,
    mixed_matrix_is_zero_mod_p_power,
    normalize_mixed_matrix,
    reduce_mixed_matrix,
)
from pari_howell import pari_howell_row_span
from p7_mod49 import (
    load_p7_mod49_relations,
    p7_mod49_relation_polynomials,
    verify_p7_mod49_selector_identities,
)

__all__ = [
    "ambient_hecke_matrix",
    "ambient_operator_descends",
    "annihilates_manin_quotient",
    "chain_ring_manin_quotient_coordinates",
    "direct_manin_presentation",
    "direct_signed_manin_presentation",
    "divide_mixed_endomorphism_by_p_power",
    "hecke_matrix_from_ambient_on_manin_quotient",
    "hecke_matrix_on_manin_quotient",
    "hecke_matrix_on_signed_manin_quotient",
    "heilbronn_merel_matrices",
    "is_power_of_prime",
    "is_zero_in_manin_quotient",
    "manin_class_exponent",
    "manin_quotient_coordinates",
    "mixed_endomorphism_is_well_defined",
    "mixed_matrix_is_zero",
    "mixed_matrix_is_zero_mod_p_power",
    "normalize_mixed_matrix",
    "pari_howell_row_span",
    "load_p7_mod49_relations",
    "load_source_data",
    "p7_mod49_relation_polynomials",
    "reduce_mixed_matrix",
    "rows_zero_in_manin_quotient",
    "same_manin_class",
    "signed_manin_quotient",
    "symmetric_power_action",
    "verify_divided_identities",
    "verify_divided_joint_identities",
    "verify_ordinary_identities",
    "verify_ordinary_joint_identities",
    "verify_p7_mod49_selector_identities",
    "prepare_source_data",
]

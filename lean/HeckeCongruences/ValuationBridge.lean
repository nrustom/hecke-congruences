import HeckeCongruences.Basic
import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Integral digits in possibly ramified coefficient rings

The proofs use total divisibility in a valuation domain, rather than an
unramified valuation assumption. They apply to the integer ring of any
finite extension of Q_p.
-/

namespace HeckeCongruences

/-- A scalar whose residue has an explicit inverse is a unit. -/
theorem isUnit_of_residue_inverse {O : Type*} [CommRing O] [IsLocalRing O]
    {p c u v : O} (hp : p ∈ IsLocalRing.maximalIdeal O)
    (h : u*c + p*v = 1) : IsUnit c := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit c).mp
  have hp0 : IsLocalRing.residue O p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
  intro hc
  have hh := congrArg (IsLocalRing.residue O) h
  simpa [hp0, hc] using hh

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [ValuationRing O]

/-- The elementary quadratic valuation argument: an integral solution of
`a^2 + s*b*a + s^2*c = 0` is divisible by `s`. -/
theorem dvd_of_quadratic_scaled {a s b c : O}
    (h : a ^ 2 + s * b * a + s ^ 2 * c = 0) : s ∣ a := by
  by_contra hn
  have ha : a ≠ 0 := by intro ha; exact hn (ha ▸ dvd_zero s)
  obtain ⟨t, ht⟩ := (ValuationRing.dvd_total a s).resolve_right hn
  have htmax : t ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hn
    rw [ht]
    exact (hu.mul_right_dvd).mpr (dvd_refl a)
  have heq : a ^ 2 * (1 + t * b + t ^ 2 * c) = 0 := by
    rw [ht] at h
    linear_combination h
  have hzero : 1 + t * b + t ^ 2 * c = 0 :=
    (mul_eq_zero.mp heq).resolve_left (pow_ne_zero _ ha)
  have hm : t * b + t ^ 2 * c ∈ IsLocalRing.maximalIdeal O := by
    exact (IsLocalRing.maximalIdeal O).add_mem
      ((IsLocalRing.maximalIdeal O).mul_mem_right b htmax)
      ((IsLocalRing.maximalIdeal O).mul_mem_right c
        (by simpa [pow_two] using (IsLocalRing.maximalIdeal O).mul_mem_right t htmax))
  have hone : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    have he : (1 : O) = -(t * b + t ^ 2 * c) := by linear_combination hzero
    rw [he]
    exact (IsLocalRing.maximalIdeal O).neg_mem hm
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top
    (Ideal.eq_top_of_isUnit_mem _ hone isUnit_one)

/-- The double-root Taylor argument. The constant term is divisible by
`p^2`, the linear coefficient by `p`, and the quadratic coefficient is a
unit. A root modulo `p^2` lying in the selected residual branch has an
integral first base-p digit. -/
theorem dvd_of_double_root_expansion {p y A B C D : O}
    (hy : y ∈ IsLocalRing.maximalIdeal O) (hC : IsUnit C)
    (h : p ^ 2 ∣ p ^ 2 * A + p * B * y + C * y ^ 2 + y ^ 3 * D) :
    p ∣ y := by
  obtain ⟨z, hz⟩ := h
  by_contra hn
  have hy0 : y ≠ 0 := by intro he; exact hn (he ▸ dvd_zero p)
  obtain ⟨t, ht⟩ := (ValuationRing.dvd_total y p).resolve_right hn
  have htmax : t ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hn
    rw [ht]
    exact (hu.mul_right_dvd).mpr (dvd_refl y)
  have heq : y ^ 2 * (t ^ 2 * (A - z) + t * B + C + y * D) = 0 := by
    rw [ht] at hz
    linear_combination hz
  have he : t ^ 2 * (A - z) + t * B + C + y * D = 0 :=
    (mul_eq_zero.mp heq).resolve_left (pow_ne_zero _ hy0)
  have hCmax : C ∈ IsLocalRing.maximalIdeal O := by
    have hc : C = -(t ^ 2 * (A - z) + t * B + y * D) := by linear_combination he
    rw [hc]
    apply (IsLocalRing.maximalIdeal O).neg_mem
    exact (IsLocalRing.maximalIdeal O).add_mem
      ((IsLocalRing.maximalIdeal O).add_mem
        ((IsLocalRing.maximalIdeal O).mul_mem_right (A - z)
          (by simpa [pow_two] using (IsLocalRing.maximalIdeal O).mul_mem_right t htmax))
        ((IsLocalRing.maximalIdeal O).mul_mem_right B htmax))
      ((IsLocalRing.maximalIdeal O).mul_mem_right D hy)
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hCmax
  exact hCmax hC

end HeckeCongruences

import HeckeCongruences.Basic
import HeckeCongruences.ValuationBridge

/-!
# The selected eigenvalues for `p = 3`, modulo `3^3`

The definitions and theorem names in this file follow the two branches of
Section 5 of `prime_power_congruences_level_one_dickson_twisted.tex`.
The hypotheses are the exact propagated identities on `L_d^+`; the conclusions
are their consequences for the `T_2`- and `T_7`-eigenvalues.
-/

namespace HeckeCongruences.PrimeThree

open HeckeCongruences

variable {O M : Type*} [CommRing O] [IsLocalRing O]
  [AddCommGroup M] [Module O M]

/-- The nonzero-branch polynomial `F_r(Z_2) = Z_2^2-c_r`. -/
def nonzeroFr (Z2 : Module.End O M) (cr : O) : Module.End O M :=
  Z2 ^ 2 - cr • LinearMap.id

/-- The exact identity-to-eigenvalue step on the nonzero branch:
`T_2=3Z_2`, `(Z_2^2-c_r)L_d^+ ⊆ 9L_d^+`, and
`(T_7-t_r)L_d^+ ⊆ 27L_d^+` give the displayed scalar relations of the
manuscript. -/
theorem nonzero_branch_eigenvalue_relations
    {T2 T7 Z2 : Module.End O M}
    {v : PrimitiveEigenvector (O := O) (M := M)}
    {a2 a7 z2 cr tr : O}
    (ha2 : ActsBy T2 v a2)
    (ha7 : ActsBy T7 v a7)
    (hz2 : ActsBy Z2 v z2)
    (hT2division : T2 = (3 : O) • Z2)
    (hZ2 : MapsIntoMultiple (nonzeroFr Z2 cr) ((3 : O) ^ 2))
    (hT7 : MapsIntoMultiple (T7 - tr • LinearMap.id) ((3 : O) ^ 3)) :
    a2 = (3 : O) * z2 ∧
      LiterallyCongruent (3 : O) 2 (z2 ^ 2) cr ∧
      LiterallyCongruent (3 : O) 3 a7 tr := by
  have hscaled : ActsBy ((3 : O) • Z2) v ((3 : O) * z2) := hz2.smul
  have ha2scale : a2 = (3 : O) * z2 := by
    rw [hT2division] at ha2
    exact ha2.eigenvalue_eq hscaled
  have hpoly : ActsBy (nonzeroFr Z2 cr) v (z2 ^ 2 - cr) := by
    have hc : ActsBy (cr • LinearMap.id) v cr := by
      simpa using (ActsBy.id v).smul (s := cr)
    exact (hz2.pow 2).sub hc
  exact ⟨ha2scale, eigenvalue_dvd_of_mapsIntoMultiple hpoly hZ2,
    ordinary_identity_implies_literal_congruence ha7 hT7⟩

/-- The root-separation used after
`z_2^2 ≡ₗᵢₜ α^2 (mod 9)`.  The unit condition is the manuscript's
observation that `α` is nonzero modulo `3`. -/
theorem nonzero_branch_root_selector
    {z2 α : O}
    (hroot : LiterallyCongruent (3 : O) 2 (z2 ^ 2) (α ^ 2))
    (hseparated : IsUnit ((2 : O) * α)) :
    LiterallyCongruent (3 : O) 2 z2 α ∨
      LiterallyCongruent (3 : O) 2 z2 (-α) := by
  have hfactor : (3 : O) ^ 2 ∣ (z2 - α) * (z2 + α) := by
    obtain ⟨u, hu⟩ := hroot
    refine ⟨u, ?_⟩
    calc
      (z2 - α) * (z2 + α) = z2 ^ 2 - α ^ 2 := by ring
      _ = (3 : O) ^ 2 * u := hu
  have hdiff : IsUnit ((z2 - α) - (z2 + α)) := by
    have : (z2 - α) - (z2 + α) = -((2 : O) * α) := by ring
    rw [this]
    exact hseparated.neg
  rcases isUnit_or_isUnit_of_sub_isUnit hdiff with hleft | hright
  · right
    change (3 : O) ^ 2 ∣ z2 - (-α)
    simpa using dvd_right_of_unit_mul_dvd hleft hfactor
  · left
    apply dvd_right_of_unit_mul_dvd hright
    simpa [mul_comm] using hfactor

/-- Multiplying the selected root of `z_2` by `3` gives the corresponding
literal congruence for `a_2` modulo `27`. -/
theorem nonzero_branch_a2_selector
    {a2 z2 α : O} (ha2 : a2 = (3 : O) * z2)
    (hz2 : LiterallyCongruent (3 : O) 2 z2 α) :
    LiterallyCongruent (3 : O) 3 a2 ((3 : O) * α) := by
  obtain ⟨u, hu⟩ := hz2
  apply literallyCongruent_of_eq_mul
  calc
    a2 - (3 : O) * α = (3 : O) * (z2 - α) := by rw [ha2]; ring
    _ = (3 : O) ^ 3 * u := by rw [hu]; ring

/-- The zero-branch numerator `G_2=T_2(T_2-63)`. -/
def G2 (T2 : Module.End O M) : Module.End O M :=
  T2 * (T2 - (63 : O) • LinearMap.id)

/-- The zero-branch terminal relation
`Q(H_2)=(H_2(H_2+1))^2`. -/
def zeroQ (H2 : Module.End O M) : Module.End O M :=
  (H2 * (H2 + LinearMap.id)) ^ 2

/-- Evaluation of the exact zero-branch identities
`81H_2=T_2(T_2-63)`, `Q(H_2)L_d^+ ⊆ 3L_d^+`, and the ordinary
`T_7` relation. -/
theorem zero_branch_eigenvalue_relations
    {T2 T7 H2 : Module.End O M}
    {v : PrimitiveEigenvector (O := O) (M := M)}
    {a2 a7 h tr : O}
    (ha2 : ActsBy T2 v a2)
    (ha7 : ActsBy T7 v a7)
    (hh : ActsBy H2 v h)
    (hH2division : G2 T2 = (3 : O) ^ 4 • H2)
    (hQ : MapsIntoMultiple (zeroQ H2) (3 : O))
    (hT7 : MapsIntoMultiple (T7 - tr • LinearMap.id) ((3 : O) ^ 3)) :
    a2 * (a2 - 63) = (3 : O) ^ 4 * h ∧
      (3 : O) ∣ (h * (h + 1)) ^ 2 ∧
      LiterallyCongruent (3 : O) 3 a7 tr := by
  have h63 : ActsBy ((63 : O) • LinearMap.id) v (63 : O) := by
    simpa using (ActsBy.id v).smul (s := (63 : O))
  have hG : ActsBy (G2 T2) v (a2 * (a2 - 63)) :=
    ha2.mul (ha2.sub h63)
  have hscaled : ActsBy ((3 : O) ^ 4 • H2) v ((3 : O) ^ 4 * h) := hh.smul
  have hnumerator : a2 * (a2 - 63) = (3 : O) ^ 4 * h := by
    rw [hH2division] at hG
    exact hG.eigenvalue_eq hscaled
  have hplus : ActsBy (H2 + LinearMap.id) v (h + 1) := hh.add (ActsBy.id v)
  have hterminal : ActsBy (zeroQ H2) v ((h * (h + 1)) ^ 2) :=
    (hh.mul hplus).pow 2
  exact ⟨hnumerator, eigenvalue_dvd_of_mapsIntoMultiple hterminal hQ,
    ordinary_identity_implies_literal_congruence ha7 hT7⟩

/-- The final zero-branch root calculation.  Here `a_2=9x_f` and
`h_f=x_f(x_f-7)` are exactly the raw-digit substitutions in the manuscript.
The terminal identity forces `x_f` to reduce to `0`, `1`, or `-1`, hence
the three valuative classes for `a_2` modulo `27`. -/
theorem zero_branch_a2_selector
    {a2 x h : O}
    (h3max : (3 : O) ∈ IsLocalRing.maximalIdeal O)
    (ha2 : a2 = (3 : O) ^ 2 * x)
    (hh : h = x * (x - 7))
    (hterminal : (3 : O) ∣ (h * (h + 1)) ^ 2) :
    ValuativelyCongruent (3 : O) 3 a2 0 ∨
      ValuativelyCongruent (3 : O) 3 a2 ((3 : O) ^ 2) ∨
      ValuativelyCongruent (3 : O) 3 a2 (-((3 : O) ^ 2)) := by
  have hterminalMax : (h * (h + 1)) ^ 2 ∈ IsLocalRing.maximalIdeal O :=
    mem_maximalIdeal_of_dvd_by_nonunit h3max hterminal
  have hbaseMax : h * (h + 1) ∈ IsLocalRing.maximalIdeal O :=
    mem_maximalIdeal_of_pow_mem (by decide) hterminalMax
  let D : O := -5 * x ^ 3 + 17 * x ^ 2 - 2 * x
  have hcomparison : h * (h + 1) - x * (x - 1) * (x + 1) ^ 2 = (3 : O) * D := by
    dsimp [D]
    rw [hh]
    ring
  have hthreeD : (3 : O) * D ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.maximalIdeal O).mul_mem_right D h3max
  have hproduct : x * (x - 1) * (x + 1) ^ 2 ∈ IsLocalRing.maximalIdeal O := by
    have heq : x * (x - 1) * (x + 1) ^ 2 = h * (h + 1) - (3 : O) * D := by
      calc
        x * (x - 1) * (x + 1) ^ 2 =
            h * (h + 1) - (h * (h + 1) - x * (x - 1) * (x + 1) ^ 2) := by ring
        _ = h * (h + 1) - (3 : O) * D := by rw [hcomparison]
    rw [heq]
    exact (IsLocalRing.maximalIdeal O).sub_mem hbaseMax hthreeD
  rcases factor_mem_maximalIdeal_of_product_mem hproduct with hxprod | hxplusSq
  · rcases factor_mem_maximalIdeal_of_product_mem hxprod with hx | hxone
    · left
      apply valuativelyCongruent_of_scaled_maximal hx
      rw [ha2]
      ring
    · right; left
      apply valuativelyCongruent_of_scaled_maximal hxone
      rw [ha2]
      ring
  · have hxplus : x + 1 ∈ IsLocalRing.maximalIdeal O :=
      mem_maximalIdeal_of_pow_mem (by decide) hxplusSq
    right; right
    apply valuativelyCongruent_of_scaled_maximal hxplus
    rw [ha2]
    ring

section ValuationDomain

variable [IsDomain O] [ValuationRing O]

/-- The zero-branch integral digit follows from the numerator relation.
This is valid in ramified valuation rings as well as in Z_3. -/
theorem zero_branch_integral_digit {a2 h : O}
    (h3ne : (3 : O) ≠ 0)
    (hnumerator : a2 * (a2 - 63) = (3 : O) ^ 4 * h) :
    ∃ x : O, a2 = (3 : O) ^ 2 * x ∧ h = x * (x - 7) := by
  have hd : (3 : O) ^ 2 ∣ a2 :=
    dvd_of_quadratic_scaled (b := -7) (c := -h) (by linear_combination hnumerator)
  obtain ⟨x, hx⟩ := hd
  refine ⟨x, hx, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 4 h3ne)
  rw [hx] at hnumerator
  linear_combination -hnumerator

/-- Complete zero-branch implication from the lattice identities and the
original Hecke eigenvector equations. Integral divided eigenvalues and the
raw digit are derived, rather than assumed. -/
theorem zero_branch_congruences
    {T2 T7 H2 : Module.End O M}
    {v : PrimitiveEigenvector (O := O) (M := M)}
    {a2 a7 tr : O} (h3ne : (3 : O) ≠ 0)
    (h3max : (3 : O) ∈ IsLocalRing.maximalIdeal O)
    (hinj : Function.Injective (fun x : M => (3 : O)^4 • x))
    (ha2 : ActsBy T2 v a2) (ha7 : ActsBy T7 v a7)
    (hdivision : G2 T2 = (3 : O)^4 • H2)
    (hQ : MapsIntoMultiple (zeroQ H2) (3 : O))
    (hT7 : MapsIntoMultiple (T7 - tr • LinearMap.id) ((3 : O)^3)) :
    (ValuativelyCongruent (3 : O) 3 a2 0 ∨
      ValuativelyCongruent (3 : O) 3 a2 9 ∨
      ValuativelyCongruent (3 : O) 3 a2 (-9)) ∧
      LiterallyCongruent (3 : O) 3 a7 tr := by
  have hc : ActsBy ((63 : O) • LinearMap.id) v 63 := by
    simpa using (ActsBy.id v).smul (s := (63 : O))
  have hG : ActsBy (G2 T2) v (a2 * (a2 - 63)) := ha2.mul (ha2.sub hc)
  obtain ⟨h, hh, _⟩ := hG.of_division hdivision hinj
  obtain ⟨hnum, hterminal, h7⟩ :=
    zero_branch_eigenvalue_relations ha2 ha7 hh hdivision hQ hT7
  obtain ⟨x, hx, hhx⟩ := zero_branch_integral_digit h3ne hnum
  exact ⟨by simpa only [show (3 : O)^2 = 9 by norm_num] using
    zero_branch_a2_selector h3max hx hhx hterminal, h7⟩

end ValuationDomain

end HeckeCongruences.PrimeThree

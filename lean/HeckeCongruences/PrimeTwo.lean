import HeckeCongruences.Basic

/-!
# The selected eigenvalues for `p = 2`, modulo `2^8`

This file formalizes the subsection “Congruences for `a₃` and `a₅`”.
The assumptions named `hT5` and `hZ` are exactly the target-lattice
identities `eq:p2-T5-relation` and `eq:p2-divided-relation` in the manuscript.
The scalar `zr` denotes its z₃, the eigenvalue of Z_r.
-/

namespace HeckeCongruences.PrimeTwo

open HeckeCongruences

variable {O M : Type*} [CommRing O] [IsLocalRing O]
  [AddCommGroup M] [Module O M]

/-- The operator `X_r = T₃ - c_{3,r}` used in the manuscript. -/
def Xr (T3 : Module.End O M) (c3r : O) : Module.End O M :=
  T3 - c3r • LinearMap.id

/-- The terminal polynomial `F_r(Z) = Z² - ε_r Z`. -/
def Fr (Zr : Module.End O M) (εr : O) : Module.End O M :=
  Zr ^ 2 - εr • Zr

/-- Evaluation of `eq:p2-T5-relation`:
`(T₅-c_{5,r})L_d^+ ⊆ 256 L_d^+` implies
`a₅(f) ≡ₗᵢₜ c_{5,r} (mod 256)`. -/
theorem a5_literal_mod256
    {T5 : Module.End O M} {v : PrimitiveEigenvector (O := O) (M := M)}
    {a5 c5r : O}
    (ha5 : ActsBy T5 v a5)
    (hT5 : MapsIntoMultiple (T5 - c5r • LinearMap.id) ((2 : O) ^ 8)) :
    LiterallyCongruent (2 : O) 8 a5 c5r :=
  ordinary_identity_implies_literal_congruence ha5 hT5

/-- The zero-root case of the staged `T₃` relation.  The exact assumptions are
`X_r = 2^7 Z_r` and `(Z_r²)L_d^+ ⊆ 2L_d^+` (`ε_r=0`). -/
theorem a3_valuative_mod256_of_epsilon_zero
    {T3 Zr : Module.End O M}
    {v : PrimitiveEigenvector (O := O) (M := M)}
    {a3 c3r zr : O}
    (h2max : (2 : O) ∈ IsLocalRing.maximalIdeal O)
    (ha3 : ActsBy T3 v a3)
    (hzr : ActsBy Zr v zr)
    (hdivision : Xr T3 c3r = (2 : O) ^ 7 • Zr)
    (hZ : MapsIntoMultiple (Fr Zr 0) (2 : O)) :
    ValuativelyCongruent (2 : O) 8 a3 c3r := by
  have hX : ActsBy (Xr T3 c3r) v (a3 - c3r) := by
    have hc : ActsBy (c3r • LinearMap.id) v c3r := by
      simpa using (ActsBy.id v).smul (s := c3r)
    exact ha3.sub hc
  have hscaled : ActsBy ((2 : O) ^ 7 • Zr) v ((2 : O) ^ 7 * zr) := hzr.smul
  have hscale : a3 - c3r = (2 : O) ^ 7 * zr := by
    rw [hdivision] at hX
    exact hX.eigenvalue_eq hscaled
  have hpoly : ActsBy (Fr Zr 0) v (zr ^ 2) := by
    simpa [Fr] using (hzr.pow 2).sub (hzr.smul (s := (0 : O)))
  have hzsq_dvd : (2 : O) ∣ zr ^ 2 := eigenvalue_dvd_of_mapsIntoMultiple hpoly hZ
  have hzsq_max : zr ^ 2 ∈ IsLocalRing.maximalIdeal O :=
    mem_maximalIdeal_of_dvd_by_nonunit h2max hzsq_dvd
  have hzmax : zr ∈ IsLocalRing.maximalIdeal O :=
    mem_maximalIdeal_of_pow_mem (by decide) hzsq_max
  exact valuativelyCongruent_of_scaled_maximal hzmax hscale

/-- The two-root case of the staged `T₃` relation.  From
`(Z_r²-Z_r)L_d^+ ⊆ 2L_d^+` (`ε_r=1`) one obtains the two KRW possibilities
`a₃(f) ≡ᵥₐₗ c_{3,r}` or `c_{3,r}+128` modulo `256`. -/
theorem a3_valuative_mod256_of_epsilon_one
    {T3 Zr : Module.End O M}
    {v : PrimitiveEigenvector (O := O) (M := M)}
    {a3 c3r zr : O}
    (h2max : (2 : O) ∈ IsLocalRing.maximalIdeal O)
    (ha3 : ActsBy T3 v a3)
    (hzr : ActsBy Zr v zr)
    (hdivision : Xr T3 c3r = (2 : O) ^ 7 • Zr)
    (hZ : MapsIntoMultiple (Fr Zr 1) (2 : O)) :
    ValuativelyCongruent (2 : O) 8 a3 c3r ∨
      ValuativelyCongruent (2 : O) 8 a3 (c3r + (2 : O) ^ 7) := by
  have hX : ActsBy (Xr T3 c3r) v (a3 - c3r) := by
    have hc : ActsBy (c3r • LinearMap.id) v c3r := by
      simpa using (ActsBy.id v).smul (s := c3r)
    exact ha3.sub hc
  have hscaled : ActsBy ((2 : O) ^ 7 • Zr) v ((2 : O) ^ 7 * zr) := hzr.smul
  have hscale : a3 - c3r = (2 : O) ^ 7 * zr := by
    rw [hdivision] at hX
    exact hX.eigenvalue_eq hscaled
  have hpoly : ActsBy (Fr Zr 1) v (zr * (zr - 1)) := by
    have hraw := (hzr.pow 2).sub (hzr.smul (s := (1 : O)))
    convert hraw using 1 <;> simp [Fr] <;> ring
  have hproduct_dvd : (2 : O) ∣ zr * (zr - 1) :=
    eigenvalue_dvd_of_mapsIntoMultiple hpoly hZ
  have hproduct_max : zr * (zr - 1) ∈ IsLocalRing.maximalIdeal O :=
    mem_maximalIdeal_of_dvd_by_nonunit h2max hproduct_dvd
  rcases factor_mem_maximalIdeal_of_product_mem hproduct_max with hzmax | hz1max
  · exact Or.inl (valuativelyCongruent_of_scaled_maximal hzmax hscale)
  · apply Or.inr
    apply valuativelyCongruent_of_scaled_maximal hz1max
    calc
      a3 - (c3r + (2 : O) ^ 7) = (a3 - c3r) - (2 : O) ^ 7 := by ring
      _ = (2 : O) ^ 7 * (zr - 1) := by rw [hscale]; ring

end HeckeCongruences.PrimeTwo

import HeckeCongruences.Basic

/-!
# The selected eigenvalues for `p = 5`, modulo `5^2`

This file follows Section 6 of the manuscript.  It uses both certified
identities: the squared shifted cubic for `Z₁₉=T₁₉/5`, and the joint
affine product `G_r(T₁₉,T₂)`.

The staged source uses numerator `T₁₉-5β_r` and terminal `(X^3+X)^2`.
Its divided operator is `W = Z₁₉-β_r`; hence that terminal is `Q_r(Z₁₉)^2`.
-/

namespace HeckeCongruences.PrimeFive

open HeckeCongruences

variable {O M : Type*} [CommRing O] [IsLocalRing O]
  [AddCommGroup M] [Module O M]

/-- `Q_r(Z)=(Z-β_r)^3+(Z-β_r)`. -/
def Qr (Z : Module.End O M) (βr : O) : Module.End O M :=
  let W := Z - βr • LinearMap.id
  W ^ 3 + W

/-- `F_{r,η}(T₁₉,T₂)` from the manuscript. -/
def Frη (T19 T2 : Module.End O M) (cr δrη γrη η : O) : Module.End O M :=
  T19 - δrη • (cr • T2 + (3 - η) • LinearMap.id) -
    (5 * γrη) • LinearMap.id

/-- `G_r=F_{r,0}F_{r,1}`. -/
def Gr (T19 T2 : Module.End O M)
    (cr δr0 γr0 δr1 γr1 : O) : Module.End O M :=
  Frη T19 T2 cr δr0 γr0 0 * Frη T19 T2 cr δr1 γr1 1

/-- Evaluation of the two exact propagated identities
`Q_r(Z₁₉)^2 L_d^+ ⊆ 5L_d^+` and
`G_r(T₁₉,T₂)L_d^+ ⊆ 25L_d^+`. -/
theorem eigenvalue_relations
    {T2 T19 Z19 : Module.End O M}
    {v : PrimitiveEigenvector (O := O) (M := M)}
    {a2 a19 z19 βr cr δr0 γr0 δr1 γr1 : O}
    (ha2 : ActsBy T2 v a2)
    (ha19 : ActsBy T19 v a19)
    (hz19 : ActsBy Z19 v z19)
    (hT19division : T19 = (5 : O) • Z19)
    (hQr : MapsIntoMultiple ((Qr Z19 βr) ^ 2) (5 : O))
    (hGr : MapsIntoMultiple (Gr T19 T2 cr δr0 γr0 δr1 γr1) ((5 : O) ^ 2)) :
    a19 = (5 : O) * z19 ∧
      (5 : O) ∣ (((z19 - βr) ^ 3 + (z19 - βr)) ^ 2) ∧
      (5 : O) ^ 2 ∣
        (a19 - δr0 * (cr * a2 + 3) - 5 * γr0) *
        (a19 - δr1 * (cr * a2 + 2) - 5 * γr1) := by
  have hscaled : ActsBy ((5 : O) • Z19) v ((5 : O) * z19) := hz19.smul
  have ha19scale : a19 = (5 : O) * z19 := by
    rw [hT19division] at ha19
    exact ha19.eigenvalue_eq hscaled
  let W : Module.End O M := Z19 - βr • LinearMap.id
  have hβ : ActsBy (βr • LinearMap.id) v βr := by
    simpa using (ActsBy.id v).smul (s := βr)
  have hW : ActsBy W v (z19 - βr) := hz19.sub hβ
  have hQeig : ActsBy (Qr Z19 βr) v ((z19 - βr) ^ 3 + (z19 - βr)) := by
    exact (hW.pow 3).add hW
  have hQsq : ActsBy ((Qr Z19 βr) ^ 2) v
      (((z19 - βr) ^ 3 + (z19 - βr)) ^ 2) := hQeig.pow 2
  have h2scalar (η δ γ : O) :
      ActsBy (Frη T19 T2 cr δ γ η) v
        (a19 - δ * (cr * a2 + 3 - η) - 5 * γ) := by
    have hcr : ActsBy (cr • T2) v (cr * a2) := ha2.smul
    have hconstant : ActsBy ((3 - η) • LinearMap.id) v (3 - η) := by
      simpa using (ActsBy.id v).smul (s := 3 - η)
    have hinner : ActsBy (cr • T2 + (3 - η) • LinearMap.id) v
        (cr * a2 + 3 - η) := by
      convert hcr.add hconstant using 1 <;> ring
    have hdelta := hinner.smul (s := δ)
    have hgamma : ActsBy ((5 * γ) • LinearMap.id) v (5 * γ) := by
      simpa using (ActsBy.id v).smul (s := 5 * γ)
    exact (ha19.sub hdelta).sub hgamma
  have hF0 := h2scalar (0 : O) δr0 γr0
  have hF1 := h2scalar (1 : O) δr1 γr1
  have hGeig : ActsBy (Gr T19 T2 cr δr0 γr0 δr1 γr1) v
      ((a19 - δr0 * (cr * a2 + 3) - 5 * γr0) *
       (a19 - δr1 * (cr * a2 + 2) - 5 * γr1)) := by
    convert hF0.mul hF1 using 1 <;> simp [Gr] <;> ring
  exact ⟨ha19scale, eigenvalue_dvd_of_mapsIntoMultiple hQsq hQr,
    eigenvalue_dvd_of_mapsIntoMultiple hGeig hGr⟩

/-- The shifted-cubic selector.  This proves, from the exact squared-cubic
identity, that `z₁₉` reduces to one of
`β_r`, `β_r+2`, or `β_r+3`. -/
theorem shifted_cubic_selector
    {z19 βr : O}
    (h5max : (5 : O) ∈ IsLocalRing.maximalIdeal O)
    (hQr : (5 : O) ∣ (((z19 - βr) ^ 3 + (z19 - βr)) ^ 2)) :
    z19 - βr ∈ IsLocalRing.maximalIdeal O ∨
      z19 - (βr + 2) ∈ IsLocalRing.maximalIdeal O ∨
      z19 - (βr + 3) ∈ IsLocalRing.maximalIdeal O := by
  let u := z19 - βr
  have hQsqMax : (u ^ 3 + u) ^ 2 ∈ IsLocalRing.maximalIdeal O :=
    mem_maximalIdeal_of_dvd_by_nonunit h5max hQr
  have hQMax : u ^ 3 + u ∈ IsLocalRing.maximalIdeal O :=
    mem_maximalIdeal_of_pow_mem (by decide) hQsqMax
  have hfive : (5 : O) * (u ^ 2 - u) ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.maximalIdeal O).mul_mem_right _ h5max
  have hproduct : u * (u - 2) * (u - 3) ∈ IsLocalRing.maximalIdeal O := by
    have heq : u * (u - 2) * (u - 3) = (u ^ 3 + u) - 5 * (u ^ 2 - u) := by ring
    rw [heq]
    exact (IsLocalRing.maximalIdeal O).sub_mem hQMax hfive
  rcases factor_mem_maximalIdeal_of_product_mem hproduct with hu01 | hu3
  · rcases factor_mem_maximalIdeal_of_product_mem hu01 with hu0 | hu2
    · left
      simpa [u]
    · right; left
      have heq : u - 2 = z19 - (βr + 2) := by dsimp [u]; ring
      rw [← heq]
      exact hu2
  · right; right
    have heq : u - 3 = z19 - (βr + 3) := by dsimp [u]; ring
    rw [← heq]
    exact hu3

/-- A selected root of the shifted cubic gives the manuscript's valuative
congruence `a₁₉ ≡ᵥₐₗ 5λ (mod 25)`. -/
theorem a19_selector
    {a19 z19 lambda : O}
    (ha19 : a19 = (5 : O) * z19)
    (hz19 : z19 - lambda ∈ IsLocalRing.maximalIdeal O) :
    ValuativelyCongruent (5 : O) 2 a19 ((5 : O) * lambda) := by
  apply valuativelyCongruent_of_scaled_maximal hz19
  rw [ha19]
  ring

/-- The unit factor in the joint identity may be cancelled.  This is the
step selecting `F_{r,ε}` from `G_r=F_{r,0}F_{r,1}`. -/
theorem selected_affine_factor
    {Aε Aother : O}
    (hproduct : (5 : O) ^ 2 ∣ Aε * Aother)
    (hother : IsUnit Aother) :
    (5 : O) ^ 2 ∣ Aε := by
  apply dvd_right_of_unit_mul_dvd hother
  simpa [mul_comm] using hproduct

/-- The exact algebra behind equations `p5-x-selector` and `p5-T2-selector`.
Here `ε` is the selected affine factor and `λ` is the root selected by the
shifted cubic. -/
theorem affine_selector_for_a2
    {a2 a19 z19 x lambda cr crInv ε δ δInv γ : O}
    (h5max : (5 : O) ∈ IsLocalRing.maximalIdeal O)
    (ha19 : a19 = (5 : O) * z19)
    (hz19 : z19 - lambda ∈ IsLocalRing.maximalIdeal O)
    (hx : x = cr * a2 + 3)
    (hcrInv : crInv * cr = 1)
    (hδInv : δInv * δ = 1)
    (hselected : (5 : O) ^ 2 ∣ a19 - δ * (x - ε) - 5 * γ) :
    let targetX := ε + 5 * δInv * (lambda - γ)
    ValuativelyCongruent (5 : O) 2 x targetX ∧
      ValuativelyCongruent (5 : O) 2 a2 (crInv * (targetX - 3)) := by
  dsimp
  obtain ⟨t, ht⟩ := hselected
  have hdeltaPart : δ * (x - ε) = a19 - 5 * γ - (5 : O) ^ 2 * t := by
    linear_combination -ht
  have hxformula : x - ε = 5 * δInv * (z19 - γ) - (5 : O) ^ 2 * δInv * t := by
    calc
      x - ε = (δInv * δ) * (x - ε) := by rw [hδInv]; ring
      _ = δInv * (δ * (x - ε)) := by ring
      _ = δInv * (a19 - 5 * γ - (5 : O) ^ 2 * t) := by rw [hdeltaPart]
      _ = 5 * δInv * (z19 - γ) - (5 : O) ^ 2 * δInv * t := by rw [ha19]; ring
  let u : O := δInv * (z19 - lambda) - 5 * δInv * t
  have hu : u ∈ IsLocalRing.maximalIdeal O := by
    apply (IsLocalRing.maximalIdeal O).sub_mem
    · exact (IsLocalRing.maximalIdeal O).mul_mem_left δInv hz19
    · simpa [mul_assoc] using
        (IsLocalRing.maximalIdeal O).mul_mem_right (δInv * t) h5max
  have hxdiff : x - (ε + 5 * δInv * (lambda - γ)) = (5 : O) * u := by
    calc
      x - (ε + 5 * δInv * (lambda - γ)) =
          (x - ε) - 5 * δInv * (lambda - γ) := by ring
      _ = (5 * δInv * (z19 - γ) - (5 : O) ^ 2 * δInv * t) -
          5 * δInv * (lambda - γ) := by rw [hxformula]
      _ = (5 : O) * u := by dsimp [u]; ring
  constructor
  · apply valuativelyCongruent_of_scaled_maximal hu
    simpa using hxdiff
  · have ha2diff :
        a2 - crInv * ((ε + 5 * δInv * (lambda - γ)) - 3) =
          crInv * (x - (ε + 5 * δInv * (lambda - γ))) := by
        rw [hx]
        calc
          a2 - crInv * ((ε + 5 * δInv * (lambda - γ)) - 3) =
              (crInv * cr) * a2 -
                crInv * ((ε + 5 * δInv * (lambda - γ)) - 3) := by
                rw [hcrInv, one_mul]
          _ = crInv *
              (cr * a2 + 3 - (ε + 5 * δInv * (lambda - γ))) := by ring
    have hcru : crInv * u ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.maximalIdeal O).mul_mem_left crInv hu
    apply valuativelyCongruent_of_scaled_maximal hcru
    rw [ha2diff, hxdiff]
    ring

end HeckeCongruences.PrimeFive

import HeckeCongruences.Propagation

/-!
# Staged division on the Manin source

This file formalizes `def:staged-p-division-witness` and the transfer and
propagation of its witnesses. The terminal polynomial is represented by its
coefficient function `coeff : ℕ → R`; only the entries `0,…,degree` are used.
Here `degree` is the manuscript's polynomial degree ν, not coefficient degree d.
-/

namespace HeckeCongruences

section Witness

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- A staged division witness for one initial source class.  The equalities
are exactly

`T x_(j-1) = p^α x_j` and `∑ c_j x_j = p^b ρ`

from the manuscript, with `pAlpha = p^α` and `pDepth = p^b`. -/
structure StagedDivisionWitness (T : Module.End R M) (pAlpha pDepth : R)
    (coeff : ℕ → R) (degree : ℕ) (x₀ : M) where
  chain : ℕ → M
  chain_zero : chain 0 = x₀
  step : ∀ j, j < degree → T (chain j) = pAlpha • chain (j + 1)
  rho : M
  terminal :
    ∑ j ∈ Finset.range (degree + 1), coeff j • chain j = pDepth • rho

/-- Every element of the module admits a staged witness. -/
def AdmitsStagedDivision (T : Module.End R M) (pAlpha pDepth : R)
    (coeff : ℕ → R) (degree : ℕ) : Prop :=
  ∀ x₀, Nonempty (StagedDivisionWitness T pAlpha pDepth coeff degree x₀)

end Witness

section TransferWitnesses

variable {R M₁ M₂ M₃ : Type*} [CommSemiring R]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
  [Module R M₁] [Module R M₂] [Module R M₃]

/-- Staged witnesses transfer through a surjective two-branch map.  This is
the formal version of the manuscript's `Transfer of staged division` lemma.
The operators on the two sources may differ; in the twisted Dickson
application they are `χ_m^q(T)` and `χ_m^(q+1)(T)`. -/
theorem stagedDivision_oneStep
    (T₁ : Module.End R M₁) (T₂ : Module.End R M₂)
    (T₃ : Module.End R M₃) (Ψ : M₁ × M₂ →ₗ[R] M₃)
    (pAlpha pDepth : R) (coeff : ℕ → R) (degree : ℕ)
    (hsurj : Function.Surjective Ψ)
    (hintertwine : ∀ x y, T₃ (Ψ (x, y)) = Ψ (T₁ x, T₂ y))
    (h₁ : AdmitsStagedDivision T₁ pAlpha pDepth coeff degree)
    (h₂ : AdmitsStagedDivision T₂ pAlpha pDepth coeff degree) :
    AdmitsStagedDivision T₃ pAlpha pDepth coeff degree := by
  intro z₀
  obtain ⟨⟨x₀, y₀⟩, rfl⟩ := hsurj z₀
  obtain ⟨wx⟩ := h₁ x₀
  obtain ⟨wy⟩ := h₂ y₀
  refine ⟨{
    chain := fun j ↦ Ψ (wx.chain j, wy.chain j)
    chain_zero := by rw [wx.chain_zero, wy.chain_zero]
    step := ?_
    rho := Ψ (wx.rho, wy.rho)
    terminal := ?_
  }⟩
  · intro j hj
    rw [hintertwine, wx.step j hj, wy.step j hj]
    simpa only [Prod.smul_mk] using
      Ψ.map_smul pAlpha (wx.chain (j + 1), wy.chain (j + 1))
  · calc
      ∑ j ∈ Finset.range (degree + 1),
          coeff j • Ψ (wx.chain j, wy.chain j) =
          Ψ (∑ j ∈ Finset.range (degree + 1),
            coeff j • (wx.chain j, wy.chain j)) := by
              rw [map_sum]
              simp only [map_smul]
      _ = Ψ (∑ j ∈ Finset.range (degree + 1), coeff j • wx.chain j,
            ∑ j ∈ Finset.range (degree + 1), coeff j • wy.chain j) := by
              congr 1
              ext
              · simp only [Prod.fst_sum, Prod.smul_mk]
              · simp only [Prod.snd_sum, Prod.smul_mk]
      _ = Ψ (pDepth • wx.rho, pDepth • wy.rho) := by
        rw [wx.terminal, wy.terminal]
      _ = pDepth • Ψ (wx.rho, wy.rho) := by
        exact Ψ.map_smul pDepth (wx.rho, wy.rho)

end TransferWitnesses

section AllWeightWitnesses

universe uR uM

variable {R : Type uR} [CommSemiring R]
variable (M : ℕ → ℕ → Type uM)
  [∀ j q, AddCommMonoid (M j q)] [∀ j q, Module R (M j q)]

/-- All-weight propagation of staged division witnesses, with the exact same
Dickson induction base and orientation change as ordinary propagation. -/
theorem stagedDivision_allWeights {u v : ℕ}
    (hu : 0 < u) (hv : 0 < v)
    (Ψ : ∀ j q, M (j - u) q × M (j - v) (q + 1) →ₗ[R] M j q)
    (T : ∀ j q, Module.End R (M j q))
    (pAlpha pDepth : R) (coeff : ℕ → R) (degree : ℕ)
    (hsurj : ∀ j, u + v ≤ j → ∀ q, Function.Surjective (Ψ j q))
    (hintertwine : ∀ j, u + v ≤ j → ∀ q x y,
      T j q (Ψ j q (x, y)) =
        Ψ j q (T (j - u) q x, T (j - v) (q + 1) y))
    (hbase : ∀ j, min u v ≤ j → j < u + v → ∀ q,
      AdmitsStagedDivision (T j q) pAlpha pDepth coeff degree) :
    ∀ j, min u v ≤ j → ∀ q,
      AdmitsStagedDivision (T j q) pAlpha pDepth coeff degree := by
  apply twoShift_allWeights
    (fun j q ↦ AdmitsStagedDivision (T j q) pAlpha pDepth coeff degree)
    (fun q ↦ q + 1) hu hv hbase
  intro j hj q hleft hright
  exact stagedDivision_oneStep _ _ _ (Ψ j q) pAlpha pDepth coeff degree
    (hsurj j hj q) (hintertwine j hj q) hleft hright

/-- The complete computational bridge: lower-degree verification plus the
exact induction-base verification proves existence of staged witnesses in
every coefficient degree. -/
theorem stagedDivision_allDegrees {u v : ℕ}
    (hu : 0 < u) (hv : 0 < v)
    (Ψ : ∀ j q, M (j - u) q × M (j - v) (q + 1) →ₗ[R] M j q)
    (T : ∀ j q, Module.End R (M j q))
    (pAlpha pDepth : R) (coeff : ℕ → R) (degree : ℕ)
    (hsurj : ∀ j, u + v ≤ j → ∀ q, Function.Surjective (Ψ j q))
    (hintertwine : ∀ j, u + v ≤ j → ∀ q x y,
      T j q (Ψ j q (x, y)) =
        Ψ j q (T (j - u) q x, T (j - v) (q + 1) y))
    (hlower : ∀ j, j < min u v → ∀ q,
      AdmitsStagedDivision (T j q) pAlpha pDepth coeff degree)
    (hbase : ∀ j, min u v ≤ j → j < u + v → ∀ q,
      AdmitsStagedDivision (T j q) pAlpha pDepth coeff degree) :
    ∀ j q, AdmitsStagedDivision (T j q) pAlpha pDepth coeff degree := by
  apply lowerDegrees_and_inductionBase_imply_allDegrees
    (fun j q ↦ AdmitsStagedDivision (T j q) pAlpha pDepth coeff degree)
    (fun q ↦ q + 1) hu hv hlower hbase
  intro j hj q hleft hright
  exact stagedDivision_oneStep _ _ _ (Ψ j q) pAlpha pDepth coeff degree
    (hsurj j hj q) (hintertwine j hj q) hleft hright

end AllWeightWitnesses

end HeckeCongruences

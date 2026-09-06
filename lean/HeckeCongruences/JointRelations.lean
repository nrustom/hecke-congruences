import Mathlib.Algebra.FreeAlgebra
import HeckeCongruences.Propagation

/-!
# Joint ordinary and joint divided relations

The computations use relations in more than one Hecke operator.  Ordinary
joint polynomials are represented by mathlib's `FreeAlgebra`; this is slightly
more general than a commutative polynomial ring and therefore does not require
commutativity merely to define evaluation.  The actual Hecke polynomials embed
in this formalism by choosing their displayed order of multiplication.

Joint staged division is represented by a finite-node witness circuit.  Its edges
record equations `T_i x_source = p^α_i x_target`, and its terminal linear
combination records the asserted joint polynomial relation.  This directly
models the two-variable `p = 5` calculation and the multi-operator `p = 7`
selector calculation, while allowing any finite number of variables.
-/

namespace HeckeCongruences

/-- Joint polynomials in exactly the two variables used, for example, by the
`p = 5` relation in `(T₁₉,T₂)`. -/
abbrev TwoOperatorPolynomial (R : Type*) [CommSemiring R] :=
  FreeAlgebra R (Fin 2)

/-- Joint polynomials in three variables.  The general API below permits any
finite index type, so it also covers all variables in the `p = 7` selector
circuits. -/
abbrev ThreeOperatorPolynomial (R : Type*) [CommSemiring R] :=
  FreeAlgebra R (Fin 3)

section JointOrdinary

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {I : Type*}

/-- Evaluate a (possibly noncommutative) polynomial in a family of module
endomorphisms. -/
def evaluateOperatorPolynomial (T : I → Module.End R M) :
    FreeAlgebra R I →ₐ[R] Module.End R M :=
  FreeAlgebra.lift R T

@[simp]
theorem evaluateOperatorPolynomial_generator (T : I → Module.End R M) (i : I) :
    evaluateOperatorPolynomial T (FreeAlgebra.ι R i) = T i := by
  exact FreeAlgebra.lift_ι_apply T i

variable {M₁ M₂ M₃ : Type*}
  [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
  [Module R M₁] [Module R M₂] [Module R M₃]

/-- Generatorwise equivariance implies equivariance for every joint
polynomial. -/
theorem jointPolynomial_intertwining
    (T₁ : I → Module.End R M₁) (T₂ : I → Module.End R M₂)
    (T₃ : I → Module.End R M₃) (Ψ : M₁ × M₂ →ₗ[R] M₃)
    (hgenerator : ∀ i x y, T₃ i (Ψ (x, y)) = Ψ (T₁ i x, T₂ i y))
    (F : FreeAlgebra R I) (z : M₁ × M₂) :
    evaluateOperatorPolynomial T₃ F (Ψ z) =
      Ψ (evaluateOperatorPolynomial T₁ F z.1,
        evaluateOperatorPolynomial T₂ F z.2) := by
  induction F using FreeAlgebra.induction generalizing z with
  | grade0 r =>
      simp [evaluateOperatorPolynomial]
      convert (Ψ.map_smul r z).symm using 1
      apply congrArg Ψ
      apply Prod.ext <;> rfl
  | grade1 i => simpa [evaluateOperatorPolynomial] using hgenerator i z.1 z.2
  | add F G hF hG =>
      simp only [map_add, LinearMap.add_apply]
      rw [hF, hG]
      exact (Ψ.map_add _ _).symm
  | mul F G hF hG =>
      simp only [map_mul, Module.End.mul_apply]
      rw [hG]
      exact hF _

/-- One-step propagation for a joint ordinary polynomial. -/
theorem jointOrdinaryRelation_oneStep
    (T₁ : I → Module.End R M₁) (T₂ : I → Module.End R M₂)
    (T₃ : I → Module.End R M₃) (Ψ : M₁ × M₂ →ₗ[R] M₃)
    (F : FreeAlgebra R I) (hsurj : Function.Surjective Ψ)
    (hgenerator : ∀ i x y, T₃ i (Ψ (x, y)) = Ψ (T₁ i x, T₂ i y))
    (h₁ : Annihilates (evaluateOperatorPolynomial T₁ F))
    (h₂ : Annihilates (evaluateOperatorPolynomial T₂ F)) :
    Annihilates (evaluateOperatorPolynomial T₃ F) := by
  intro z
  obtain ⟨⟨x, y⟩, rfl⟩ := hsurj z
  rw [jointPolynomial_intertwining T₁ T₂ T₃ Ψ hgenerator F (x, y),
    h₁, h₂]
  exact Ψ.map_zero

end JointOrdinary

section JointOrdinaryAllWeights

universe uR uM

variable {R : Type uR} [CommSemiring R] {I : Type*}
variable (M : ℕ → ℕ → Type uM)
  [∀ j q, AddCommMonoid (M j q)] [∀ j q, Module R (M j q)]

/-- Joint ordinary relations verified on the exact induction base propagate
to all higher weights. -/
theorem jointOrdinaryRelation_allWeights {u v : ℕ}
    (hu : 0 < u) (hv : 0 < v)
    (Ψ : ∀ j q, M (j - u) q × M (j - v) (q + 1) →ₗ[R] M j q)
    (T : ∀ j q, I → Module.End R (M j q)) (F : FreeAlgebra R I)
    (hsurj : ∀ j, u + v ≤ j → ∀ q, Function.Surjective (Ψ j q))
    (hgenerator : ∀ j, u + v ≤ j → ∀ q i x y,
      T j q i (Ψ j q (x, y)) =
        Ψ j q (T (j - u) q i x, T (j - v) (q + 1) i y))
    (hbase : ∀ j, min u v ≤ j → j < u + v → ∀ q,
      Annihilates (evaluateOperatorPolynomial (T j q) F)) :
    ∀ j, min u v ≤ j → ∀ q,
      Annihilates (evaluateOperatorPolynomial (T j q) F) := by
  apply twoShift_allWeights
    (fun j q ↦ Annihilates (evaluateOperatorPolynomial (T j q) F))
    (fun q ↦ q + 1) hu hv hbase
  intro j hj q hleft hright
  exact jointOrdinaryRelation_oneStep _ _ _ (Ψ j q) F (hsurj j hj q)
    (hgenerator j hj q) hleft hright

/-- Joint ordinary identities in the directly checked lower degrees and the
exact induction base hold in every degree. -/
theorem jointOrdinaryRelation_allDegrees {u v : ℕ}
    (hu : 0 < u) (hv : 0 < v)
    (Ψ : ∀ j q, M (j - u) q × M (j - v) (q + 1) →ₗ[R] M j q)
    (T : ∀ j q, I → Module.End R (M j q)) (F : FreeAlgebra R I)
    (hsurj : ∀ j, u + v ≤ j → ∀ q, Function.Surjective (Ψ j q))
    (hgenerator : ∀ j, u + v ≤ j → ∀ q i x y,
      T j q i (Ψ j q (x, y)) =
        Ψ j q (T (j - u) q i x, T (j - v) (q + 1) i y))
    (hlower : ∀ j, j < min u v → ∀ q,
      Annihilates (evaluateOperatorPolynomial (T j q) F))
    (hbase : ∀ j, min u v ≤ j → j < u + v → ∀ q,
      Annihilates (evaluateOperatorPolynomial (T j q) F)) :
    ∀ j q, Annihilates (evaluateOperatorPolynomial (T j q) F) := by
  apply lowerDegrees_and_inductionBase_imply_allDegrees
    (fun j q ↦ Annihilates (evaluateOperatorPolynomial (T j q) F))
    (fun q ↦ q + 1) hu hv hlower hbase
  intro j hj q hleft hright
  exact jointOrdinaryRelation_oneStep _ _ _ (Ψ j q) F (hsurj j hj q)
    (hgenerator j hj q) hleft hright

end JointOrdinaryAllWeights

section JointStaged

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {I Node Edge : Type*} [Fintype Node]

/-- A finite-node staged-division circuit for several divided operators.  This is
the multivariable version of `StagedDivisionWitness`. -/
structure JointStagedDivisionWitness
    (T : I → Module.End R M) (pAlpha : I → R)
    (source target : Edge → Node) (label : Edge → I)
    (root : Node) (coeff : Node → R) (pDepth : R) (x₀ : M) where
  value : Node → M
  root_value : value root = x₀
  step : ∀ e, T (label e) (value (source e)) = pAlpha (label e) • value (target e)
  rho : M
  terminal : ∑ n, coeff n • value n = pDepth • rho

/-- Every initial class admits a witness for the fixed joint circuit. -/
def AdmitsJointStagedDivision
    (T : I → Module.End R M) (pAlpha : I → R)
    (source target : Edge → Node) (label : Edge → I)
    (root : Node) (coeff : Node → R) (pDepth : R) : Prop :=
  ∀ x₀, Nonempty
    (JointStagedDivisionWitness T pAlpha source target label root coeff pDepth x₀)

variable {M₁ M₂ M₃ : Type*}
  [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
  [Module R M₁] [Module R M₂] [Module R M₃]

/-- Joint staged circuits transfer componentwise through the Dickson map. -/
theorem jointStagedDivision_oneStep
    (T₁ : I → Module.End R M₁) (T₂ : I → Module.End R M₂)
    (T₃ : I → Module.End R M₃) (Ψ : M₁ × M₂ →ₗ[R] M₃)
    (pAlpha : I → R) (source target : Edge → Node) (label : Edge → I)
    (root : Node) (coeff : Node → R) (pDepth : R)
    (hsurj : Function.Surjective Ψ)
    (hgenerator : ∀ i x y, T₃ i (Ψ (x, y)) = Ψ (T₁ i x, T₂ i y))
    (h₁ : AdmitsJointStagedDivision T₁ pAlpha source target label root coeff pDepth)
    (h₂ : AdmitsJointStagedDivision T₂ pAlpha source target label root coeff pDepth) :
    AdmitsJointStagedDivision T₃ pAlpha source target label root coeff pDepth := by
  intro z₀
  obtain ⟨⟨x₀, y₀⟩, rfl⟩ := hsurj z₀
  obtain ⟨wx⟩ := h₁ x₀
  obtain ⟨wy⟩ := h₂ y₀
  refine ⟨{
    value := fun n ↦ Ψ (wx.value n, wy.value n)
    root_value := by rw [wx.root_value, wy.root_value]
    step := ?_
    rho := Ψ (wx.rho, wy.rho)
    terminal := ?_
  }⟩
  · intro e
    rw [hgenerator, wx.step e, wy.step e]
    simpa only [Prod.smul_mk] using
      Ψ.map_smul (pAlpha (label e)) (wx.value (target e), wy.value (target e))
  · calc
      ∑ n, coeff n • Ψ (wx.value n, wy.value n) =
          Ψ (∑ n, coeff n • (wx.value n, wy.value n)) := by
            rw [map_sum]
            simp only [map_smul]
      _ = Ψ (∑ n, coeff n • wx.value n,
            ∑ n, coeff n • wy.value n) := by
              congr 1
              ext
              · simp only [Prod.fst_sum, Prod.smul_mk]
              · simp only [Prod.snd_sum, Prod.smul_mk]
      _ = Ψ (pDepth • wx.rho, pDepth • wy.rho) := by
        rw [wx.terminal, wy.terminal]
      _ = pDepth • Ψ (wx.rho, wy.rho) := by
        simpa only [Prod.smul_mk] using Ψ.map_smul pDepth (wx.rho, wy.rho)

/-- After each labelled division has been justified by cancellation on a
target at the retained precision, a joint source circuit becomes the same
joint circuit on that target.  Here `hcancel` is the exact equality obtained
after passing to that retained-precision quotient; consequently the target
edges have unit scale. -/
theorem jointStagedDivision_cancel_to_target
    {Source Target : Type*}
    [AddCommMonoid Source] [AddCommMonoid Target]
    [Module R Source] [Module R Target]
    (Tsource : I → Module.End R Source)
    (Ztarget : I → Module.End R Target)
    (φ : Source →ₗ[R] Target) (hφ : Function.Surjective φ)
    (pAlpha : I → R) (source target : Edge → Node) (label : Edge → I)
    (root : Node) (coeff : Node → R) (pDepth : R)
    (hcancel : ∀ i x y,
      Tsource i x = pAlpha i • y → Ztarget i (φ x) = φ y)
    (hsource : AdmitsJointStagedDivision Tsource pAlpha source target label
      root coeff pDepth) :
    AdmitsJointStagedDivision Ztarget (fun _ ↦ 1) source target label
      root coeff pDepth := by
  intro z₀
  obtain ⟨x₀, rfl⟩ := hφ z₀
  obtain ⟨w⟩ := hsource x₀
  refine ⟨{
    value := fun n ↦ φ (w.value n)
    root_value := by rw [w.root_value]
    step := ?_
    rho := φ w.rho
    terminal := ?_
  }⟩
  · intro e
    simpa using hcancel (label e) (w.value (source e))
      (w.value (target e)) (w.step e)
  · calc
      ∑ n, coeff n • φ (w.value n) =
          φ (∑ n, coeff n • w.value n) := by
            rw [map_sum]
            simp only [map_smul]
      _ = φ (pDepth • w.rho) := congrArg φ w.terminal
      _ = pDepth • φ w.rho := φ.map_smul _ _

end JointStaged

section JointAllWeights

universe uR uM

variable {R : Type uR} [CommSemiring R]
variable {I Node Edge : Type*} [Fintype Node]
variable (M : ℕ → ℕ → Type uM)
  [∀ j q, AddCommMonoid (M j q)] [∀ j q, Module R (M j q)]

/-- Finite joint staged computations on the exact induction base propagate to
every weight.  The index type `I` may have two, three, or more operators; in
particular it covers every joint circuit used in the current computations. -/
theorem jointStagedDivision_allWeights {u v : ℕ}
    (hu : 0 < u) (hv : 0 < v)
    (Ψ : ∀ j q, M (j - u) q × M (j - v) (q + 1) →ₗ[R] M j q)
    (T : ∀ j q, I → Module.End R (M j q))
    (pAlpha : I → R) (source target : Edge → Node) (label : Edge → I)
    (root : Node) (coeff : Node → R) (pDepth : R)
    (hsurj : ∀ j, u + v ≤ j → ∀ q, Function.Surjective (Ψ j q))
    (hgenerator : ∀ j, u + v ≤ j → ∀ q i x y,
      T j q i (Ψ j q (x, y)) =
        Ψ j q (T (j - u) q i x, T (j - v) (q + 1) i y))
    (hbase : ∀ j, min u v ≤ j → j < u + v → ∀ q,
      AdmitsJointStagedDivision (T j q) pAlpha source target label root coeff pDepth) :
    ∀ j, min u v ≤ j → ∀ q,
      AdmitsJointStagedDivision (T j q) pAlpha source target label root coeff pDepth := by
  apply twoShift_allWeights
    (fun j q ↦ AdmitsJointStagedDivision
      (T j q) pAlpha source target label root coeff pDepth)
    (fun q ↦ q + 1) hu hv hbase
  intro j hj q hleft hright
  exact jointStagedDivision_oneStep _ _ _ (Ψ j q) pAlpha source target label
    root coeff pDepth (hsurj j hj q) (hgenerator j hj q) hleft hright

/-- Lower-degree and exact-base certification of a joint staged circuit
implies that the circuit has witnesses in every degree. -/
theorem jointStagedDivision_allDegrees {u v : ℕ}
    (hu : 0 < u) (hv : 0 < v)
    (Ψ : ∀ j q, M (j - u) q × M (j - v) (q + 1) →ₗ[R] M j q)
    (T : ∀ j q, I → Module.End R (M j q))
    (pAlpha : I → R) (source target : Edge → Node) (label : Edge → I)
    (root : Node) (coeff : Node → R) (pDepth : R)
    (hsurj : ∀ j, u + v ≤ j → ∀ q, Function.Surjective (Ψ j q))
    (hgenerator : ∀ j, u + v ≤ j → ∀ q i x y,
      T j q i (Ψ j q (x, y)) =
        Ψ j q (T (j - u) q i x, T (j - v) (q + 1) i y))
    (hlower : ∀ j, j < min u v → ∀ q,
      AdmitsJointStagedDivision (T j q) pAlpha source target label root coeff pDepth)
    (hbase : ∀ j, min u v ≤ j → j < u + v → ∀ q,
      AdmitsJointStagedDivision (T j q) pAlpha source target label root coeff pDepth) :
    ∀ j q,
      AdmitsJointStagedDivision (T j q) pAlpha source target label root coeff pDepth := by
  apply lowerDegrees_and_inductionBase_imply_allDegrees
    (fun j q ↦ AdmitsJointStagedDivision
      (T j q) pAlpha source target label root coeff pDepth)
    (fun q ↦ q + 1) hu hv hlower hbase
  intro j hj q hleft hright
  exact jointStagedDivision_oneStep _ _ _ (Ψ j q) pAlpha source target label
    root coeff pDepth (hsurj j hj q) (hgenerator j hj q) hleft hright

end JointAllWeights

end HeckeCongruences

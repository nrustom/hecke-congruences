import HeckeCongruences.JointRelations
import HeckeCongruences.LatticeBridge

/-!
# Selected roots and the joint free-target bridge

Finite circuits retain independent witnesses on different monomial paths.
The root is S u, as in the manuscript's `rem:joint-staged-division`.
Here S is the selected starting operator, distinct from the Manin generator S.
Reachability and the edge identities for the monomial operators identify the
terminal circuit with its polynomial; no cancellation compatibility on the
smaller quotient is assumed.
-/

namespace HeckeCongruences

section SelectedTransfer

variable {R M M₁ M₂ M₃ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  [AddCommGroup M₃] [Module R M₃]
variable {I Node Edge : Type*} [Fintype Node]

def AdmitsSelectedJointDivision (S : Module.End R M)
    (T : I → Module.End R M) (pAlpha : I → R)
    (source target : Edge → Node) (label : Edge → I)
    (root : Node) (coeff : Node → R) (pDepth : R) : Prop :=
  ∀ u, Nonempty
    (JointStagedDivisionWitness T pAlpha source target label root coeff pDepth (S u))

theorem selectedJointDivision_oneStep
    (S₁ : Module.End R M₁) (S₂ : Module.End R M₂) (S₃ : Module.End R M₃)
    (T₁ : I → Module.End R M₁) (T₂ : I → Module.End R M₂)
    (T₃ : I → Module.End R M₃) (Ψ : M₁ × M₂ →ₗ[R] M₃)
    (pAlpha : I → R) (source target : Edge → Node) (label : Edge → I)
    (root : Node) (coeff : Node → R) (pDepth : R)
    (hsurj : Function.Surjective Ψ)
    (hS : ∀ x y, S₃ (Ψ (x,y)) = Ψ (S₁ x,S₂ y))
    (hT : ∀ i x y, T₃ i (Ψ (x,y)) = Ψ (T₁ i x,T₂ i y))
    (h₁ : AdmitsSelectedJointDivision S₁ T₁ pAlpha source target label root coeff pDepth)
    (h₂ : AdmitsSelectedJointDivision S₂ T₂ pAlpha source target label root coeff pDepth) :
    AdmitsSelectedJointDivision S₃ T₃ pAlpha source target label root coeff pDepth := by
  intro z
  obtain ⟨⟨x,y⟩, rfl⟩ := hsurj z
  obtain ⟨wx⟩ := h₁ x
  obtain ⟨wy⟩ := h₂ y
  refine ⟨{
    value := fun n => Ψ (wx.value n, wy.value n)
    root_value := by rw [wx.root_value, wy.root_value, hS]
    step := ?_
    rho := Ψ (wx.rho,wy.rho)
    terminal := ?_
  }⟩
  · intro e
    rw [hT, wx.step, wy.step]
    simpa only [Prod.smul_mk] using
      Ψ.map_smul (pAlpha (label e)) (wx.value (target e), wy.value (target e))
  · have hs : (∑ n, coeff n • (wx.value n, wy.value n)) =
        (pDepth • wx.rho, pDepth • wy.rho) := by
      ext <;> simp [Prod.fst_sum, Prod.snd_sum, wx.terminal, wy.terminal]
    rw [← map_smul]
    change _ = Ψ (pDepth • wx.rho, pDepth • wy.rho)
    rw [← hs, map_sum]
    simp only [map_smul]

end SelectedTransfer

section SelectedAllDegrees

universe uR uM
variable {R : Type uR} [CommRing R]
variable {I Node Edge : Type*} [Fintype Node]
variable (M : ℕ → ℕ → Type uM)
  [∀ j q, AddCommGroup (M j q)] [∀ j q, Module R (M j q)]

/-- Lower degrees and the critical induction base suffice also for roots
S u. The orientation of S changes together with all divided numerators. -/
theorem selectedJointDivision_allDegrees {u v : ℕ}
    (hu : 0 < u) (hv : 0 < v)
    (Ψ : ∀ j q, M (j-u) q × M (j-v) (q+1) →ₗ[R] M j q)
    (S : ∀ j q, Module.End R (M j q))
    (T : ∀ j q, I → Module.End R (M j q))
    (pAlpha : I → R) (source target : Edge → Node) (label : Edge → I)
    (root : Node) (coeff : Node → R) (pDepth : R)
    (hsurj : ∀ j, u+v ≤ j → ∀ q, Function.Surjective (Ψ j q))
    (hS : ∀ j, u+v ≤ j → ∀ q x y,
      S j q (Ψ j q (x,y)) = Ψ j q (S (j-u) q x, S (j-v) (q+1) y))
    (hT : ∀ j, u+v ≤ j → ∀ q i x y,
      T j q i (Ψ j q (x,y)) = Ψ j q (T (j-u) q i x,T (j-v) (q+1) i y))
    (hlower : ∀ j, j < min u v → ∀ q,
      AdmitsSelectedJointDivision (S j q) (T j q) pAlpha source target label root coeff pDepth)
    (hbase : ∀ j, min u v ≤ j → j < u+v → ∀ q,
      AdmitsSelectedJointDivision (S j q) (T j q) pAlpha source target label root coeff pDepth) :
    ∀ j q, AdmitsSelectedJointDivision (S j q) (T j q)
      pAlpha source target label root coeff pDepth := by
  apply lowerDegrees_and_inductionBase_imply_allDegrees
    (fun j q => AdmitsSelectedJointDivision (S j q) (T j q)
      pAlpha source target label root coeff pDepth) (· + 1) hu hv hlower hbase
  intro j hj q hleft hright
  exact selectedJointDivision_oneStep _ _ _ _ _ _ (Ψ j q) pAlpha source target
    label root coeff pDepth (hsurj j hj q) (hS j hj q) (hT j hj q) hleft hright

end SelectedAllDegrees

section JointTarget

variable {R Source P : Type*} [CommRing R]
  [AddCommGroup Source] [Module R Source] [AddCommGroup P] [Module R P]

/-- The first division equation alone suffices to construct the integral
divided operator. This specializes the existing one-variable bridge. -/
theorem sourceFirstDivision_implies_target_divisible
    (Tsource : Module.End R Source) (Ttarget : Module.End R P)
    (a guard modulus : R) (hmod : modulus = a*guard)
    (q : Source →ₗ[R] P ⧸ multipleSubmodule (M := P) modulus)
    (hq : Function.Surjective q)
    (hcompat : ∀ x, quotientEndomorphism Ttarget modulus (q x) = q (Tsource x))
    (hfirst : ∀ x, ∃ y, Tsource x = a • y) : MapsIntoMultiple Ttarget a := by
  apply stagedSource_implies_targetOperator_divisible Tsource Ttarget
    a guard modulus 1 (fun _ => 0) 1 (by decide) hmod q hq hcompat
  intro x
  obtain ⟨y,hy⟩ := hfirst x
  refine ⟨{
    chain := fun n => if n=0 then x else y
    chain_zero := by simp
    step := ?_
    rho := 0
    terminal := by simp
  }⟩
  intro j hj
  have hj0 : j=0 := by omega
  simpa [hj0] using hy

/-- Cancellation for one labelled edge, proved from the original quotient.
The common guard divides every p^(m-alpha_i). -/
theorem divided_edge_congruent
    (T : Module.End R Source) (N Z : Module.End R P)
    (a tail guard modulus : R) (hmod : modulus = a * (tail * guard))
    (hinj : Function.Injective (fun x : P => a • x))
    (hNZ : ∀ x, N x = a • Z x)
    (q : Source →ₗ[R] P ⧸ multipleSubmodule (M := P) modulus)
    (hcompat : ∀ x, quotientEndomorphism N modulus (q x) = q (T x))
    {x y : Source} {X Y : P}
    (hX : Submodule.Quotient.mk X = q x)
    (hY : Submodule.Quotient.mk Y = q y)
    (hstep : T x = a • y) : CongruentModulo guard (Z X) Y := by
  have heq : (Submodule.Quotient.mk (N X) : P ⧸ multipleSubmodule modulus) =
      Submodule.Quotient.mk (a • Y) := by
    rw [← quotientEndomorphism_mk, hX, hcompat, hstep, map_smul, ← hY]
    rfl
  have hc : CongruentModulo modulus (a • Z X) (a • Y) := by
    rw [← hNZ]
    exact quotient_mk_eq_iff.mp heq
  rw [hmod] at hc
  exact (hc.cancel_left a (tail*guard) hinj).weaken_left tail guard

variable {I Node Edge : Type*} [Fintype Node]

/-- Extract the first equation on a selected root. For the graph numerator
S N and root S u, its integral target is S N S = S^2 N. -/
theorem selectedJoint_first_divisibility
    (Ssource : Module.End R Source) (Tsource : I → Module.End R Source)
    (a : I → R) (source target : Edge → Node) (label : Edge → I)
    (root : Node) (coeff : Node → R) (depth : R)
    (hstage : AdmitsSelectedJointDivision Ssource Tsource a source target label root coeff depth)
    (e : Edge) (he : source e = root) :
    ∀ x, ∃ y, (Tsource (label e) * Ssource) x = a (label e) • y := by
  intro x
  obtain ⟨w⟩ := hstage x
  refine ⟨w.value (target e), ?_⟩
  simpa [he, w.root_value, Module.End.mul_apply] using w.step e

/-- The joint version of stagedSource_implies_targetPolynomial, including
selected roots. `W n` is the integral monomial at node n. Reachability rules
out unrelated free nodes and makes the terminal polynomial exact.

For powers of p the factorizations are precisely b ≤ m - max alpha_i.
The conclusion is F(Z) S P ⊆ p^b P; for Hecke polynomials S commutes with F.
-/
theorem selectedJointSource_implies_targetPolynomial
    (Ssource : Module.End R Source) (S : Module.End R P)
    (Tsource : I → Module.End R Source) (N Z : I → Module.End R P)
    (a tail : I → R) (guard modulus modTail depth depthTail : R)
    (hmod : ∀ i, modulus = a i * (tail i * guard))
    (hguard : modulus = modTail * guard) (hdepth : guard = depthTail * depth)
    (hinj : ∀ i, Function.Injective (fun x : P => a i • x))
    (hNZ : ∀ i x, N i x = a i • Z i x)
    (q : Source →ₗ[R] P ⧸ multipleSubmodule (M := P) modulus)
    (hq : Function.Surjective q)
    (hS : ∀ x, quotientEndomorphism S modulus (q x) = q (Ssource x))
    (hT : ∀ i x, quotientEndomorphism (N i) modulus (q x) = q (Tsource i x))
    (source target : Edge → Node) (label : Edge → I)
    (root : Node) (coeff : Node → R)
    (W : Node → Module.End R P) (hWroot : W root = LinearMap.id)
    (hWedge : ∀ e, W (target e) = Z (label e) * W (source e))
    (hreach : ∀ n, Relation.ReflTransGen
      (fun x y => ∃ e, source e = x ∧ target e = y) root n)
    (hstage : AdmitsSelectedJointDivision Ssource Tsource a
      source target label root coeff depth) :
    MapsIntoMultiple ((∑ n, coeff n • W n) * S) depth := by
  intro y
  obtain ⟨x, hx⟩ := hq (Submodule.Quotient.mk y)
  obtain ⟨w⟩ := hstage x
  let rep : Node → P := fun n => quotientRepresentative modulus (q (w.value n))
  have hrep n : (Submodule.Quotient.mk (rep n) : P ⧸ multipleSubmodule modulus) =
      q (w.value n) := quotientRepresentative_spec modulus _
  have hroot : CongruentModulo guard (S y) (rep root) := by
    have hm : CongruentModulo modulus (S y) (rep root) := by
      apply quotient_mk_eq_iff.mp
      rw [hrep, w.root_value, ← hS, hx, quotientEndomorphism_mk]
    rw [hguard] at hm
    exact hm.weaken_left modTail guard
  have hedge e : CongruentModulo guard (Z (label e) (rep (source e)))
      (rep (target e)) :=
    divided_edge_congruent _ _ _ _ _ _ _ (hmod _) (hinj _) (hNZ _) q
      (hT _) (hrep _) (hrep _) (w.step e)
  have hnode n : CongruentModulo guard (W n (S y)) (rep n) := by
    induction hreach n with
    | refl => simpa [hWroot] using hroot
    | @tail n n' hp he ih =>
      obtain ⟨e, rfl, rfl⟩ := he
      rw [hWedge, Module.End.mul_apply]
      exact (ih.map (Z (label e))).trans (hedge e)
  have hpoly : CongruentModulo guard
      (((∑ n, coeff n • W n) * S) y) (∑ n, coeff n • rep n) := by
    simp only [Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply]
    exact CongruentModulo.finset_sum _ _ _ (fun n _ => (hnode n).smul (coeff n))
  let rho := quotientRepresentative modulus (q w.rho)
  have hterminal : CongruentModulo modulus (∑ n, coeff n • rep n) (depth • rho) := by
    apply quotient_mk_eq_iff.mp
    change (Submodule.mkQ (multipleSubmodule modulus)) (∑ n, coeff n • rep n) =
      (Submodule.mkQ (multipleSubmodule modulus)) (depth • rho)
    simp only [map_sum, map_smul]
    simp only [Submodule.mkQ_apply, hrep, ← map_smul, ← map_sum]
    rw [w.terminal, map_smul]
    congr 1
    exact (quotientRepresentative_spec modulus (q w.rho)).symm
  rw [hdepth] at hpoly
  rw [hguard, hdepth, ← mul_assoc] at hterminal
  have ht := (hpoly.weaken_left depthTail depth).trans
    ((hterminal.weaken_left (modTail*depthTail) depth).trans
      (CongruentModulo.multiple_zero depth rho))
  obtain ⟨z,hz⟩ := congruentModulo_iff.mp ht
  exact ⟨z, by simpa using hz⟩

end JointTarget

end HeckeCongruences

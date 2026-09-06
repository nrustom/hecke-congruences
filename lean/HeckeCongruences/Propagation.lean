import Mathlib

/-!
# Dickson transfer and all-weight propagation

This file formalizes the manuscript's weight-propagation argument
(`thm:weight-propagation` and `thm:weight-propagation-p2`).
The modular-symbol computations enter only through hypotheses on a finite
induction base.  The proof below is the strong induction with the two Dickson
degree shifts

* `u = p(p-1)/2` (multiplication by `A_m`), and
* `v = (p+1)/2` (multiplication by `B_m`).

The second branch changes orientation from `q` to `q+1`; this packages both
the sign change and the determinant-character twist.

The induction variable `j` is a rescaled coefficient-degree index:
`d = r + 2*j*p^(m-1)` for odd p, with modular-form weight `k = d+2`.
For p=2 use `d = r + j*2^(m-1)`, shifts 2 and 3, and no orientation change
(either `next = id` in the abstract induction or a q-independent family).
-/

namespace HeckeCongruences

section AbstractRelations

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- An operator relation holds on a module when the corresponding
endomorphism is identically zero. -/
def Annihilates (T : Module.End R M) : Prop :=
  ∀ x, T x = 0

theorem annihilates_iff_eq_zero {T : Module.End R M} :
    Annihilates T ↔ T = 0 := by
  constructor
  · intro h
    ext x
    simpa using h x
  · rintro rfl x
    rfl

/-- A surjective intertwiner transports an operator identity from its source
to its target.  This is the abstract content of passing from
`M_d^+` to `P_d^+/p^mP_d^+`. -/
theorem annihilates_of_surjective_intertwining
    {N : Type*} [AddCommMonoid N] [Module R N]
    (sourceOperator : Module.End R M) (targetOperator : Module.End R N)
    (π : M →ₗ[R] N) (hπ : Function.Surjective π)
    (hintertwine : ∀ x, targetOperator (π x) = π (sourceOperator x))
    (hsource : Annihilates sourceOperator) :
    Annihilates targetOperator := by
  intro y
  obtain ⟨x, rfl⟩ := hπ y
  rw [hintertwine, hsource, map_zero]

/-- Restrict an endomorphism to an invariant submodule. -/
def restrictEndomorphism (T : Module.End R M) (L : Submodule R M)
    (hL : ∀ x ∈ L, T x ∈ L) : Module.End R L :=
  T.restrict hL

/-- An identity on an ambient module holds on every invariant submodule. -/
theorem annihilates_restrict (T : Module.End R M) (L : Submodule R M)
    (hL : ∀ x ∈ L, T x ∈ L) (hT : Annihilates T) :
    Annihilates (restrictEndomorphism T L hL) := by
  intro x
  apply Subtype.ext
  exact hT x

/-- The ordinary source-to-lattice bridge in one statement.  A certified
source identity descends through a surjective equivariant map and then holds
on every invariant target submodule, such as `L_d^+`. -/
theorem ordinarySourceIdentity_reachesInvariantLattice
    {N : Type*} [AddCommMonoid N] [Module R N]
    (sourceOperator : Module.End R M) (targetOperator : Module.End R N)
    (π : M →ₗ[R] N) (hπ : Function.Surjective π)
    (hintertwine : ∀ x, targetOperator (π x) = π (sourceOperator x))
    (L : Submodule R N) (hL : ∀ x ∈ L, targetOperator x ∈ L)
    (hsource : Annihilates sourceOperator) :
    Annihilates (restrictEndomorphism targetOperator L hL) := by
  apply annihilates_restrict
  exact annihilates_of_surjective_intertwining
    sourceOperator targetOperator π hπ hintertwine hsource

end AbstractRelations

section TwoStepInduction

variable {Q : Type*}

/-- The pure two-shift strong-induction principle behind both the ordinary
and staged propagation theorems.  The exact induction base is
`min u v ≤ j < u+v`. -/
theorem twoShift_allWeights
    (P : ℕ → Q → Prop) (next : Q → Q) {u v : ℕ}
    (hu : 0 < u) (hv : 0 < v)
    (hbase : ∀ j, min u v ≤ j → j < u + v → ∀ q, P j q)
    (hstep : ∀ j, u + v ≤ j → ∀ q,
      P (j - u) q → P (j - v) (next q) → P j q) :
    ∀ j, min u v ≤ j → ∀ q, P j q := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro hj q
      by_cases hbaseRange : j < u + v
      · exact hbase j hj hbaseRange q
      · have hlarge : u + v ≤ j := Nat.le_of_not_gt hbaseRange
        apply hstep j hlarge q
        · apply ih (j - u)
          · exact Nat.sub_lt (by omega) hu
          · omega
        · apply ih (j - v)
          · exact Nat.sub_lt (by omega) hv
          · omega

/-- The form used by the computation chapters: direct verification below
`min u v`, verification on the exact induction base, and the two-shift step
together prove the property in every degree. -/
theorem lowerDegrees_and_inductionBase_imply_allDegrees
    (P : ℕ → Q → Prop) (next : Q → Q) {u v : ℕ}
    (hu : 0 < u) (hv : 0 < v)
    (hlower : ∀ j, j < min u v → ∀ q, P j q)
    (hbase : ∀ j, min u v ≤ j → j < u + v → ∀ q, P j q)
    (hstep : ∀ j, u + v ≤ j → ∀ q,
      P (j - u) q → P (j - v) (next q) → P j q) :
    ∀ j q, P j q := by
  intro j q
  by_cases hj : j < min u v
  · exact hlower j hj q
  · exact twoShift_allWeights P next hu hv hbase hstep j (Nat.le_of_not_gt hj) q

/-- A finite check of all orientation residues is enough when orientation is
periodic.  In the odd-prime applications the period is `p-1`. -/
theorem allOrientations_of_period
    (P : ℕ → ℕ → Prop) {s : ℕ} (hs : 0 < s)
    (hperiod : ∀ j q, P j (q % s) ↔ P j q)
    (hfinite : ∀ j q, q < s → P j q) :
    ∀ j q, P j q := by
  intro j q
  exact (hperiod j q).mp (hfinite j (q % s) (Nat.mod_lt q hs))

end TwoStepInduction

section OrdinaryTransfer

universe uR uM

variable {R : Type uR} [Semiring R]
variable (M : ℕ → ℕ → Type uM)
  [∀ j q, AddCommMonoid (M j q)] [∀ j q, Module R (M j q)]

/-- One step of ordinary relation propagation through the two-branch Dickson
transfer.  The equation `hintertwine` is the abstract form of
`F ∘ Ψ = Ψ (F ⊕ χ_m(F))`. -/
theorem ordinaryRelation_oneStep {u v j q : ℕ}
    (Ψ : M (j - u) q × M (j - v) (q + 1) →ₗ[R] M j q)
    (Hleft : Module.End R (M (j - u) q))
    (Hright : Module.End R (M (j - v) (q + 1)))
    (Htarget : Module.End R (M j q))
    (hsurj : Function.Surjective Ψ)
    (hintertwine : ∀ x y,
      Htarget (Ψ (x, y)) = Ψ (Hleft x, Hright y))
    (hleft : Annihilates Hleft) (hright : Annihilates Hright) :
    Annihilates Htarget := by
  intro z
  obtain ⟨⟨x, y⟩, rfl⟩ := hsurj z
  rw [hintertwine, hleft, hright]
  exact Ψ.map_zero

/-- All-weight ordinary propagation in the exact manuscript indexing.  A
certificate on `min u v ≤ j < u+v` propagates to every `j ≥ min u v`.
The operator in orientation `q+1` on the `B_m` branch already incorporates
the twist by `χ_m`. -/
theorem ordinaryRelation_allWeights {u v : ℕ}
    (hu : 0 < u) (hv : 0 < v)
    (Ψ : ∀ j q, M (j - u) q × M (j - v) (q + 1) →ₗ[R] M j q)
    (H : ∀ j q, Module.End R (M j q))
    (hsurj : ∀ j, u + v ≤ j → ∀ q, Function.Surjective (Ψ j q))
    (hintertwine : ∀ j, u + v ≤ j → ∀ q x y,
      H j q (Ψ j q (x, y)) =
        Ψ j q (H (j - u) q x, H (j - v) (q + 1) y))
    (hbase : ∀ j, min u v ≤ j → j < u + v → ∀ q,
      Annihilates (H j q)) :
    ∀ j, min u v ≤ j → ∀ q, Annihilates (H j q) := by
  apply twoShift_allWeights (fun j q ↦ Annihilates (H j q)) (fun q ↦ q + 1)
      hu hv hbase
  intro j hj q hleft hright
  exact ordinaryRelation_oneStep M (Ψ j q) _ _ _ (hsurj j hj q)
    (hintertwine j hj q) hleft hright

/-- Direct checks in the lower degrees together with checks on the exact
induction base imply the ordinary identity in every coefficient degree. -/
theorem ordinaryRelation_allDegrees {u v : ℕ}
    (hu : 0 < u) (hv : 0 < v)
    (Ψ : ∀ j q, M (j - u) q × M (j - v) (q + 1) →ₗ[R] M j q)
    (H : ∀ j q, Module.End R (M j q))
    (hsurj : ∀ j, u + v ≤ j → ∀ q, Function.Surjective (Ψ j q))
    (hintertwine : ∀ j, u + v ≤ j → ∀ q x y,
      H j q (Ψ j q (x, y)) =
        Ψ j q (H (j - u) q x, H (j - v) (q + 1) y))
    (hlower : ∀ j, j < min u v → ∀ q, Annihilates (H j q))
    (hbase : ∀ j, min u v ≤ j → j < u + v → ∀ q,
      Annihilates (H j q)) :
    ∀ j q, Annihilates (H j q) := by
  apply lowerDegrees_and_inductionBase_imply_allDegrees
    (fun j q ↦ Annihilates (H j q)) (fun q ↦ q + 1) hu hv hlower hbase
  intro j hj q hleft hright
  exact ordinaryRelation_oneStep M (Ψ j q) _ _ _ (hsurj j hj q)
    (hintertwine j hj q) hleft hright

end OrdinaryTransfer

end HeckeCongruences

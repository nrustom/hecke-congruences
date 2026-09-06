import HeckeCongruences.CoefficientTransfer

/-!
# The actual Dickson coefficient multipliers

These are the displayed binary forms after setting Y=1. Mathlib's geometric
sum, finite-field root factorization, resultants, and bounded polynomial
spaces supply their coprimality and coefficient-transfer surjectivity.
-/

namespace HeckeCongruences
open Polynomial Finset
noncomputable section

def dicksonAlpha (R : Type*) [CommRing R] (p : ℕ) : R[X] :=
  ∑ i ∈ range (p+1), ((X : R[X])^(p-1))^i

def dicksonBeta (R : Type*) [CommRing R] (p : ℕ) : R[X] :=
  X^p-X

theorem dicksonAlpha_monic {R : Type*} [CommRing R] [Nontrivial R]
    {p : ℕ} (hp : 1 < p) : (dicksonAlpha R p).Monic := by
  exact (monic_X_pow (p-1)).geom_sum (by simp; omega) (by omega)

theorem dicksonBeta_monic {R : Type*} [CommRing R] [Nontrivial R]
    {p : ℕ} (hp : 1 < p) : (dicksonBeta R p).Monic := by
  apply Polynomial.monic_X_pow_sub
  simpa using (show (1 : WithBot ℕ) < (p : WithBot ℕ) by exact_mod_cast hp)

theorem dicksonAlpha_natDegree {R : Type*} [CommRing R] [Nontrivial R]
    {p : ℕ} (hp : 1 < p) : (dicksonAlpha R p).natDegree = p*(p-1) := by
  unfold dicksonAlpha
  rw [Polynomial.natDegree_sum_eq_of_disjoint]
  · simp only [Monic.natDegree_pow, monic_X_pow, natDegree_X_pow]
    apply le_antisymm
    · apply Finset.sup_le
      intro i hi
      have hi' := Finset.mem_range.mp hi
      nlinarith
    · exact Finset.le_sup_of_le (Finset.mem_range.mpr (Nat.lt_succ_self p)) (by omega)
  · intro i hi j hj hij
    simp only [Function.onFun, Function.comp_def, Monic.natDegree_pow,
      monic_X_pow, natDegree_X_pow]
    intro he
    apply hij
    have : 0 < p-1 := by omega
    nlinarith

theorem dicksonBeta_natDegree {R : Type*} [CommRing R] [Nontrivial R]
    {p : ℕ} (hp : 1 < p) : (dicksonBeta R p).natDegree = p := by
  unfold dicksonBeta
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
  · simp
  · simpa using hp

theorem dicksonAlpha_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : ℕ) : (dicksonAlpha R p).map f = dicksonAlpha S p := by
  simp [dicksonAlpha, Polynomial.map_sum]

theorem dicksonBeta_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : ℕ) : (dicksonBeta R p).map f = dicksonBeta S p := by
  simp [dicksonBeta]

/-- Alpha takes the value 1 at every element of F_p. -/
theorem dicksonAlpha_eval {p : ℕ} [Fact p.Prime] (c : ZMod p) :
    (dicksonAlpha (ZMod p) p).eval c = 1 := by
  by_cases hc : c = 0
  · subst c
    have hp : p-1 ≠ 0 := by have := (Fact.out : p.Prime).one_lt; omega
    simp [dicksonAlpha, Polynomial.eval_finsetSum, hp]
  · have hc' := ZMod.pow_card_sub_one_eq_one hc
    simp [dicksonAlpha, Polynomial.eval_finsetSum, hc']

/-- Coprimality is proved for the actual Dickson polynomials over F_p. -/
theorem dickson_coprime_mod_p {p : ℕ} [Fact p.Prime] :
    IsCoprime (dicksonAlpha (ZMod p) p) (dicksonBeta (ZMod p) p) := by
  have hp := (Fact.out : p.Prime).one_lt
  have hroots : (dicksonBeta (ZMod p) p).roots = Finset.univ.val := by
    simpa [dicksonBeta, ZMod.card] using FiniteField.roots_X_pow_card_sub_X (ZMod p)
  have hprod : (∏ c : ZMod p, (X-C c)) = dicksonBeta (ZMod p) p := by
    have h := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq
      (dicksonBeta_monic (R := ZMod p) hp)
      (by rw [hroots, dicksonBeta_natDegree hp]; simp)
    simpa [hroots] using h
  rw [← hprod]
  apply IsCoprime.prod_right
  intro c _
  let A := dicksonAlpha (ZMod p) p
  have hdiv := Polynomial.modByMonic_add_div A (X-C c)
  rw [Polynomial.modByMonic_X_sub_C_eq_C_eval, dicksonAlpha_eval, map_one] at hdiv
  refine ⟨1, -(A /ₘ (X-C c)), ?_⟩
  linear_combination -hdiv

/-- The actual powers A_m and B_m are coprime over any local coefficient
ring with residue characteristic p. -/
theorem dickson_powers_coprime {R : Type*} [CommRing R] [IsLocalRing R]
    {p : ℕ} [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p] (n : ℕ) :
    IsCoprime ((dicksonAlpha R p)^(p^n)) ((dicksonBeta R p)^(p^n)) := by
  have hp := (Fact.out : p.Prime).one_lt
  apply coprime_of_coprime_reduction _ _
    ((dicksonAlpha_monic hp).pow _) ((dicksonBeta_monic hp).pow _)
  have hc := (dickson_coprime_mod_p (p := p)).map
    (Polynomial.mapRingHom (ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField R)))
  change IsCoprime ((dicksonAlpha (ZMod p) p).map _)
    ((dicksonBeta (ZMod p) p).map _) at hc
  rw [dicksonAlpha_map, dicksonBeta_map] at hc
  simpa only [Polynomial.map_pow, dicksonAlpha_map, dicksonBeta_map] using hc.pow (m := p^n) (n := p^n)

/-- The surjective coefficient transfer at the manuscript's critical degree.
Here m=n+1, a_m=p^(n+1)(p-1), and b_m=p^n(p+1). -/
theorem dickson_coefficient_surjective {R : Type*} [CommRing R] [IsLocalRing R]
    {p : ℕ} [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]
    (n d : ℕ) (hd : p^(n+1)*(p-1) + p^n*(p+1) ≤ d)
    (P : BinaryForms R d) :
    ∃ F : BinaryForms R (d-p^(n+1)*(p-1)),
    ∃ G : BinaryForms R (d-p^n*(p+1)),
      (dicksonAlpha R p)^(p^n)*F.val + (dicksonBeta R p)^(p^n)*G.val = P.val := by
  have hp := (Fact.out : p.Prime).one_lt
  apply bounded_coefficient_preimages _ _ ((dicksonAlpha_monic hp).pow _) _
    _ (dickson_powers_coprime n) hd P
  · rw [Monic.natDegree_pow (dicksonAlpha_monic hp), dicksonAlpha_natDegree hp, pow_succ]
    ring
  · rw [Monic.natDegree_pow (dicksonBeta_monic hp), dicksonBeta_natDegree hp]
    exact Nat.mul_le_mul_left (p^n) (Nat.le_succ p)

/-- The quotient-transfer surjectivity theorem with coefficient surjectivity
discharged for the actual Dickson multipliers. The formula hypotheses just
identify the two coefficient linear maps with multiplication. -/
theorem dickson_maninTransfer_surjective {R : Type*} [CommRing R] [IsLocalRing R]
    {p : ℕ} [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]
    (n d : ℕ) (hd : p^(n+1)*(p-1) + p^n*(p+1) ≤ d)
    (S₁ U₁ : Module.End R (BinaryForms R (d-p^(n+1)*(p-1))))
    (S₂ U₂ : Module.End R (BinaryForms R (d-p^n*(p+1))))
    (S₃ U₃ : Module.End R (BinaryForms R d))
    (A : BinaryForms R (d-p^(n+1)*(p-1)) →ₗ[R] BinaryForms R d)
    (B : BinaryForms R (d-p^n*(p+1)) →ₗ[R] BinaryForms R d)
    (hA : maninRelations S₁ U₁ ≤ Submodule.comap A (maninRelations S₃ U₃))
    (hB : maninRelations S₂ U₂ ≤ Submodule.comap B (maninRelations S₃ U₃))
    (hAval : ∀ F, (A F).val = (dicksonAlpha R p)^(p^n)*F.val)
    (hBval : ∀ G, (B G).val = (dicksonBeta R p)^(p^n)*G.val) :
    Function.Surjective (maninTransfer S₁ U₁ S₂ U₂ S₃ U₃ A B hA hB) := by
  apply maninTransfer_surjective
  intro P
  obtain ⟨F,G,hFG⟩ := dickson_coefficient_surjective n d hd P
  refine ⟨(F,G), ?_⟩
  apply Subtype.ext
  change (A F).val + (B G).val = P.val
  rw [hAval,hBval]
  exact hFG

end
end HeckeCongruences

import HeckeCongruences.ManinQuotient
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Surjective coefficient multiplication

Binary forms of degree d are represented by their coefficients after setting
Y=1, namely polynomials of degree at most d. The second multiplier may have
degree smaller than its homogeneous degree (as happens for B_m).

We use the Sylvester adjugate instead of the equivalent dimension/Nakayama
argument: coprimality modulo the maximal ideal makes the resultant a unit,
and the adjugate supplies bounded-degree preimages.
-/

namespace HeckeCongruences

noncomputable section

open Polynomial

abbrev BinaryForms (R : Type*) [CommRing R] (d : ℕ) := Polynomial.degreeLT R (d + 1)

section LocalCoprimality

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- Coprimality of the reductions lifts when both polynomials are monic. -/
theorem coprime_of_coprime_reduction (A B : R[X]) (hA : A.Monic) (hB : B.Monic)
    (hcop : IsCoprime (A.map (IsLocalRing.residue R))
      (B.map (IsLocalRing.residue R))) : IsCoprime A B := by
  apply (Polynomial.isUnit_resultant_iff_isCoprime hA).mp
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  have hunit := (Polynomial.isUnit_resultant_iff_isCoprime
    (hA.map (IsLocalRing.residue R))).mpr hcop
  have hn := hunit.ne_zero
  simpa only [hA.natDegree_map, hB.natDegree_map,
    Polynomial.resultant_map_map] using hn

end LocalCoprimality

section BoundedMultiplication

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- A monic first multiplier makes padding the degree of the second
multiplier harmless for the resultant. -/
theorem padded_resultant_isUnit (A B : R[X]) (hA : A.Monic)
    (hcop : IsCoprime A B) {b : ℕ} (hB : B.natDegree ≤ b) :
    IsUnit (A.resultant B A.natDegree b) := by
  have hr := (Polynomial.isUnit_resultant_iff_isCoprime hA).mpr hcop
  have he : b = B.natDegree + (b - B.natDegree) := by omega
  rw [he, Polynomial.resultant_add_right_deg _ _ _ _ _ le_rfl]
  simpa [Polynomial.coeff_natDegree, hA.leadingCoeff] using hr

/-- Surjectivity with exactly the two degree bounds in the manuscript. -/
theorem bounded_coefficient_preimages (A B : R[X]) (hA : A.Monic)
    {a b d : ℕ} (ha : A.natDegree = a)
    (hB : B.natDegree ≤ b) (hcop : IsCoprime A B) (hd : a + b ≤ d)
    (P : BinaryForms R d) :
    ∃ F : BinaryForms R (d - a), ∃ G : BinaryForms R (d - b),
      A * F.val + B * G.val = P.val := by
  let r := P.val %ₘ A
  have hr : r.degree < ((a + b : ℕ) : WithBot ℕ) := by
    have hlt := Polynomial.degree_modByMonic_lt P.val hA
    have hdeg : A.degree = (a : WithBot ℕ) := by
      rw [Polynomial.degree_eq_natDegree hA.ne_zero, ha]
    exact hlt.trans_le (hdeg.trans_le (by exact_mod_cast (Nat.le_add_right a b)))
  let R0 : Polynomial.degreeLT R (a + b) := ⟨r, Polynomial.mem_degreeLT.mpr hr⟩
  have hu : IsUnit (A.resultant B a b) := by
    simpa [ha] using padded_resultant_isUnit A B hA hcop hB
  let uv := hu.unit⁻¹.val • Polynomial.adjSylvester (m := a) (n := b) A B R0
  have hsolve : A * uv.2.val + B * uv.1.val = r := by
    have hh : Polynomial.sylvesterMap A B ha.le hB uv = R0 := by
      dsimp [uv]
      rw [map_smul]
      change hu.unit⁻¹.val • ((Polynomial.sylvesterMap A B ha.le hB ∘ₗ
        Polynomial.adjSylvester A B) R0) = R0
      rw [Polynomial.sylveserMap_comp_adjSylvester]
      simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul,
        hu.val_inv_mul, one_smul]
    exact congrArg Subtype.val hh
  have hP : P.val.natDegree ≤ d := by
    have hp := Polynomial.mem_degreeLT.mp P.property
    by_cases hp0 : P.val = 0
    · simp [hp0]
    · have hn := (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hp
      omega
  have huF : uv.2.val.natDegree ≤ d - a := by
    have hp := Polynomial.mem_degreeLT.mp uv.2.property
    apply Polynomial.natDegree_le_of_degree_le
    exact hp.le.trans (by exact_mod_cast (show b ≤ d-a by omega))
  have huG : uv.1.val.degree < ((d-b+1 : ℕ) : WithBot ℕ) := by
    have hp := Polynomial.mem_degreeLT.mp uv.1.property
    exact hp.trans_le (by exact_mod_cast (show a ≤ d-b+1 by omega))
  let F := P.val /ₘ A + uv.2.val
  have hF : F.natDegree ≤ d-a := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · rw [Polynomial.natDegree_divByMonic _ hA, ha]
      omega
    · exact huF
  refine ⟨⟨F, Polynomial.mem_degreeLT.mpr ?_⟩,
    ⟨uv.1.val, Polynomial.mem_degreeLT.mpr huG⟩, ?_⟩
  · exact Polynomial.degree_le_natDegree.trans_lt
      (by exact_mod_cast (show F.natDegree < d-a+1 by omega))
  · change A * (P.val /ₘ A + uv.2.val) + B * uv.1.val = P.val
    calc
      _ = r + A * (P.val /ₘ A) := by rw [← hsolve]; ring
      _ = P.val := Polynomial.modByMonic_add_div P.val A

end BoundedMultiplication

end

end HeckeCongruences

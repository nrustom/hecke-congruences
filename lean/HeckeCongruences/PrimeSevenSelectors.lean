import HeckeCongruences.PrimeSeven
import HeckeCongruences.SelectedJoint

/-!
# Integrality of the projected graph operators

The selectors are the coefficientwise lifts used in the manuscript, reduced
modulo 7. Their elementary degree-eight divisibilities are checked with ring
normalization. The sixth-power kernel argument uses Mathlib polynomial
geometric sums and aeval; no primary decomposition is assumed.
-/

namespace HeckeCongruences.PrimeSeven
open HeckeCongruences Polynomial
noncomputable section

/-- The three Lagrange selectors, in the order 0, alpha_j, beta_j. -/
def selectorPolynomial {R : Type*} [CommRing R] (j : TangentIndex) (branch : Fin 3) : R[X] :=
  match j, branch.val with
  | .j0, 0 => 3 * X ^ 2 + 1 * X ^ 0
  | .j0, 1 => 2 * X ^ 2 + 6 * X ^ 1
  | .j0, 2 => 2 * X ^ 2 + 1 * X ^ 1
  | .j2, 0 => 5 * X ^ 2 + 1 * X ^ 0
  | .j2, 1 => 1 * X ^ 2 + 2 * X ^ 1
  | .j2, 2 => 1 * X ^ 2 + 5 * X ^ 1
  | .j4, 0 => 6 * X ^ 2 + 1 * X ^ 0
  | .j4, 1 => 4 * X ^ 2 + 4 * X ^ 1
  | .j4, 2 => 4 * X ^ 2 + 3 * X ^ 1
  | _, _ => 0

/-- Centre of the chosen Lagrange branch, with its integral representative. -/
def selectorCentre {R : Type*} [CommRing R] (j : TangentIndex) (branch : Fin 3) : R :=
  match branch.val with
  | 0 => 0
  | 1 => αj j
  | 2 => βj j
  | _ => 0

/-- On the selected residual branch the selector is 1 modulo the maximal
ideal. This is the stronger fact needed for the projected graph relations. -/
theorem selector_sub_one_mem {O : Type*} [CommRing O] [IsLocalRing O]
    (j : TangentIndex) (branch : Fin 3) {a : O}
    (h7 : (7 : O) ∈ IsLocalRing.maximalIdeal O)
    (ha : a-selectorCentre j branch ∈ IsLocalRing.maximalIdeal O) :
    (selectorPolynomial j branch).eval a - 1 ∈ IsLocalRing.maximalIdeal O := by
  have h7zero : (7 : IsLocalRing.ResidueField O) = 0 := by
    have hh : IsLocalRing.residue O (7 : O) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h7
    rwa [map_ofNat] at hh
  let : CharP (IsLocalRing.ResidueField O) 7 :=
    (CharP.charP_iff_prime_eq_zero (by decide : Nat.Prime 7)).mpr h7zero
  have ha' : IsLocalRing.residue O a = IsLocalRing.residue O (selectorCentre j branch) :=
    Ideal.Quotient.eq.mpr ha
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change IsLocalRing.residue O ((selectorPolynomial j branch).eval a - 1) = 0
  cases j <;> fin_cases branch <;>
    simp only [selectorPolynomial, selectorCentre, αj, βj, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat,
      Polynomial.eval_one, pow_zero, pow_one, one_mul,
      map_add, map_mul, map_sub, map_pow, map_one, map_zero, map_ofNat] at ha' ⊢ <;>
    rw [ha'] <;> norm_num <;> reduce_mod_char!

/-- F_j divides E^2(E-1)^2 over F_7 for each Lagrange selector. -/
theorem selector_base_divisible (j : TangentIndex) (branch : Fin 3) :
    Fj j (X : (ZMod 7)[X]) ∣
      (selectorPolynomial (R := ZMod 7) j branch)^2 * (selectorPolynomial (R := ZMod 7) j branch-1)^2 := by
  cases j <;> fin_cases branch
  · refine ⟨4 * X ^ 2, ?_⟩
    norm_num [Fj, F0, F2, F4, selectorPolynomial]
    ring_nf
    reduce_mod_char
  · refine ⟨2 * X ^ 2 + 3 * X ^ 1 + 2 * X ^ 0, ?_⟩
    norm_num [Fj, F0, F2, F4, selectorPolynomial]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  · refine ⟨2 * X ^ 2 + 4 * X ^ 1 + 2 * X ^ 0, ?_⟩
    norm_num [Fj, F0, F2, F4, selectorPolynomial]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  · refine ⟨2 * X ^ 2, ?_⟩
    norm_num [Fj, F0, F2, F4, selectorPolynomial]
    ring_nf
    reduce_mod_char
  · refine ⟨1 * X ^ 2 + 1 * X ^ 1 + 2 * X ^ 0, ?_⟩
    norm_num [Fj, F0, F2, F4, selectorPolynomial]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  · refine ⟨1 * X ^ 2 + 6 * X ^ 1 + 2 * X ^ 0, ?_⟩
    norm_num [Fj, F0, F2, F4, selectorPolynomial]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  · refine ⟨1 * X ^ 2, ?_⟩
    norm_num [Fj, F0, F2, F4, selectorPolynomial]
    ring_nf
    reduce_mod_char
  · refine ⟨4 * X ^ 2 + 2 * X ^ 1 + 2 * X ^ 0, ?_⟩
    norm_num [Fj, F0, F2, F4, selectorPolynomial]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  · refine ⟨4 * X ^ 2 + 5 * X ^ 1 + 2 * X ^ 0, ?_⟩
    norm_num [Fj, F0, F2, F4, selectorPolynomial]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char

/-- Raising E to the sixth power preserves the required annihilator. -/
theorem selector_sixth_divisible (j : TangentIndex) (branch : Fin 3) :
    Fj j (X : (ZMod 7)[X]) ∣
      (selectorPolynomial (R := ZMod 7) j branch)^6 * ((selectorPolynomial (R := ZMod 7) j branch)^6-1)^2 := by
  let E := selectorPolynomial (R := ZMod 7) j branch
  apply (selector_base_divisible j branch).trans
  refine ⟨E^4 * (∑ i ∈ Finset.range 6, E^i)^2, ?_⟩
  have hg := geom_sum_mul E 6
  change E^6*(E^6-1)^2 = E^2*(E-1)^2*(E^4*(∑ i ∈ Finset.range 6,E^i)^2)
  rw [← hg]
  ring

/-- A polynomial identity proves the kernel-stability argument used in the
manuscript, even for nonsemisimple T. -/
theorem selector_sixth_identity {A : Type*} [Ring A] [Algebra (ZMod 7) A]
    (j : TangentIndex) (branch : Fin 3) (T : A)
    (hF : Polynomial.aeval T (Fj j (X : (ZMod 7)[X])) = 0) :
    let S := (Polynomial.aeval T (selectorPolynomial (R := ZMod 7) j branch))^6
    (2-S)*S^2 = S := by
  dsimp
  obtain ⟨Q,hQ⟩ := selector_sixth_divisible j branch
  have hh := congrArg (Polynomial.aeval T) hQ
  simp only [map_mul, map_pow, map_sub, map_one, hF, zero_mul] at hh
  apply sub_eq_zero.mp
  calc
    _ = -(Polynomial.aeval T (selectorPolynomial (R := ZMod 7) j branch)^6 *
        (Polynomial.aeval T (selectorPolynomial (R := ZMod 7) j branch)^6-1)^2) := by noncomm_ring
    _ = 0 := by rw [hh, neg_zero]

/-- The first selected witness proves S^2 N P ⊆ pP. If the reduction of S
has stable kernel, this gives S N P ⊆ pP, which is the needed integrality
of S N / p. -/
theorem projected_numerator_divisible
    {R P : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    (S N : Module.End R P) (p : R)
    (hfirst : MapsIntoMultiple (S^2*N) p)
    (hstable : LinearMap.ker ((quotientEndomorphism S p)^2) ≤
      LinearMap.ker (quotientEndomorphism S p)) :
    MapsIntoMultiple (S*N) p := by
  intro x
  obtain ⟨y,hy⟩ := hfirst x
  have hsquare : ((quotientEndomorphism S p)^2)
      (Submodule.Quotient.mk (N x)) = 0 := by
    simp only [pow_two, Module.End.mul_apply, quotientEndomorphism_mk]
    have he : S (S (N x)) = p • y := by simpa [pow_two, Module.End.mul_apply] using hy
    rw [he]
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (mem_multipleSubmodule_iff.mpr ⟨y,rfl⟩)
  have hs := hstable hsquare
  change quotientEndomorphism S p (Submodule.Quotient.mk (N x)) = 0 at hs
  rw [quotientEndomorphism_mk] at hs
  have hm : S (N x) ∈ multipleSubmodule p := (Submodule.Quotient.mk_eq_zero _).mp hs
  exact mem_multipleSubmodule_iff.mp hm

/-- Kernel stability follows from the explicit polynomial identity; it does
not require semisimplicity or a primary-decomposition hypothesis. -/
theorem selector_sixth_ker_sq_le
    {R Q : Type*} [CommRing R] [AddCommGroup Q] [Module R Q]
    [Algebra (ZMod 7) (Module.End R Q)]
    (j : TangentIndex) (branch : Fin 3) (T : Module.End R Q)
    (hF : Polynomial.aeval T (Fj j (X : (ZMod 7)[X])) = 0) :
    let S := (Polynomial.aeval T (selectorPolynomial (R := ZMod 7) j branch))^6
    LinearMap.ker (S^2) ≤ LinearMap.ker S := by
  intro S x hx
  change S x = 0
  have hid : (2-S)*S^2 = S := selector_sixth_identity j branch T hF
  rw [← hid, Module.End.mul_apply]
  change (S^2) x = 0 at hx
  rw [hx, map_zero]

section ProjectedIntegrality
variable {R P Source : Type*} [CommRing R] [AddCommGroup P] [Module R P]
  [AddCommGroup Source] [Module R Source]
local instance : Algebra (ZMod 7)
    (Module.End R (P ⧸ multipleSubmodule (M := P) (7 : R))) := quotientEndZModAlgebra R P 7

/-- The actual sixth-power selector makes S N / 7 an integral operator.
The two reduction hypotheses identify the tangent and selector polynomials
on P/7P; kernel stability is proved, not assumed. -/
theorem projected_operator_integral
    (j : TangentIndex) (branch : Fin 3)
    (Tbar : Module.End R (P ⧸ multipleSubmodule (M := P) (7 : R)))
    (S N : Module.End R P)
    (hF : Polynomial.aeval Tbar (Fj j (X : (ZMod 7)[X])) = 0)
    (hS : quotientEndomorphism S (7 : R) =
      (Polynomial.aeval Tbar (selectorPolynomial (R := ZMod 7) j branch))^6)
    (hfirst : MapsIntoMultiple (S^2*N) (7 : R))
    (hinj : Function.Injective (fun x : P => (7 : R) • x)) :
    ∃ J : Module.End R P, S*N = (7 : R) • J := by
  have hstable : LinearMap.ker ((quotientEndomorphism S (7 : R))^2) ≤
      LinearMap.ker (quotientEndomorphism S (7 : R)) := by
    rw [hS]
    exact selector_sixth_ker_sq_le j branch Tbar hF
  have hdiv := projected_numerator_divisible S N (7 : R) hfirst hstable
  exact ⟨divideEndomorphism (S*N) (7 : R) hdiv hinj,
    LinearMap.ext (divideEndomorphism_spec (S*N) (7 : R) hdiv hinj)⟩

/-- The first selected source equation supplies the S^2 N divisibility
needed above. This theorem starts on the original precision quotient. -/
theorem selected_first_implies_projected_integral
    (j : TangentIndex) (branch : Fin 3)
    (Tbar : Module.End R (P ⧸ multipleSubmodule (M := P) (7 : R)))
    (S N : Module.End R P) (Ssource Nsource : Module.End R Source)
    (modulus guard : R) (hmod : modulus = 7*guard)
    (q : Source →ₗ[R] P ⧸ multipleSubmodule (M := P) modulus)
    (hq : Function.Surjective q)
    (hScompat : ∀ x, quotientEndomorphism S modulus (q x) = q (Ssource x))
    (hNcompat : ∀ x, quotientEndomorphism (S*N) modulus (q x) = q (Nsource x))
    (hcomm : Commute S N)
    (hfirst : ∀ x, ∃ y, (Nsource*Ssource) x = (7 : R) • y)
    (hF : Polynomial.aeval Tbar (Fj j (X : (ZMod 7)[X])) = 0)
    (hS : quotientEndomorphism S (7 : R) =
      (Polynomial.aeval Tbar (selectorPolynomial (R := ZMod 7) j branch))^6)
    (hinj : Function.Injective (fun x : P => (7 : R) • x)) :
    ∃ J : Module.End R P, S*N = (7 : R) • J := by
  have hd : MapsIntoMultiple ((S*N)*S) (7 : R) := by
    apply sourceFirstDivision_implies_target_divisible (Nsource*Ssource) ((S*N)*S)
      7 guard modulus hmod q hq _ hfirst
    intro x
    rw [quotientEndomorphism_mul, Module.End.mul_apply, hScompat, hNcompat]
    rfl
  have he : (S*N)*S = S^2*N := by
    rw [mul_assoc, ← hcomm.eq, ← mul_assoc, ← pow_two]
  rw [he] at hd
  exact projected_operator_integral j branch Tbar S N hF hS hd hinj

end ProjectedIntegrality

end
end HeckeCongruences.PrimeSeven

import Mathlib

/-!
# From lattice identities to eigenvalue congruences

This file contains the common formal algebra used in Part II of
`prime_power_congruences_level_one_dickson_twisted.tex`.

The manuscript chooses a primitive simultaneous eigenvector in a Hecke-stable
lattice.  `PrimitiveEigenvector` records primitivity by a coordinate functional
which takes the value `1` on that vector.  This is exactly what permits a
divisibility statement for a vector to be converted into a divisibility
statement for its eigenvalue.
-/

namespace HeckeCongruences

section Congruences

variable {O : Type*} [CommRing O] [IsLocalRing O]

/-- The ideal-theoretic form of the manuscript's literal congruence
`x ≡ₗᵢₜ y (mod p^m)`: the difference is divisible by `p^m`. -/
def LiterallyCongruent (p : O) (m : ℕ) (x y : O) : Prop :=
  p ^ m ∣ x - y

/-- The ideal-theoretic form of the manuscript's valuative congruence
`x ≡ᵥₐₗ y (mod p^m)`. For positive `m` and the integer ring of a finite extension of `ℚ_p`,
membership in `p^(m-1) 𝔪` is equivalent to `v_p (x-y) > m-1`. -/
def ValuativelyCongruent (p : O) (m : ℕ) (x y : O) : Prop :=
  x - y ∈ Ideal.span ({p ^ (m - 1)} : Set O) * IsLocalRing.maximalIdeal O

theorem valuativelyCongruent_of_scaled_maximal
    {p x y z : O} {m : ℕ}
    (hz : z ∈ IsLocalRing.maximalIdeal O)
    (hxy : x - y = p ^ (m - 1) * z) :
    ValuativelyCongruent p m x y := by
  rw [ValuativelyCongruent, hxy]
  exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hz

theorem literallyCongruent_of_eq_mul
    {p x y z : O} {m : ℕ}
    (hxy : x - y = p ^ m * z) :
    LiterallyCongruent p m x y := by
  exact ⟨z, hxy⟩

theorem literallyCongruent_iff
    {p x y : O} {m : ℕ} :
    LiterallyCongruent p m x y ↔ x - y ∈ Ideal.span ({p ^ m} : Set O) := by
  simp [LiterallyCongruent, Ideal.mem_span_singleton]

end Congruences

section Eigenvectors

variable {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M]

/-- A primitive lattice vector, represented by a coordinate functional taking
the value `1`.  For a vector in a finite free module this is equivalent to the
usual notion of primitivity used in the manuscript. -/
structure PrimitiveEigenvector where
  vector : M
  coordinate : M →ₗ[O] O
  coordinate_vector : coordinate vector = 1

/-- `T` acts on the chosen primitive vector with eigenvalue `a`. -/
def ActsBy (T : Module.End O M) (v : PrimitiveEigenvector (O := O) (M := M))
    (a : O) : Prop :=
  T v.vector = a • v.vector

/-- The image of `T` is contained in the scalar multiple `s M`. -/
def MapsIntoMultiple (T : Module.End O M) (s : O) : Prop :=
  ∀ x : M, ∃ y : M, T x = s • y

theorem ActsBy.add {S T : Module.End O M}
    {v : PrimitiveEigenvector (O := O) (M := M)} {a b : O}
    (hS : ActsBy S v a) (hT : ActsBy T v b) :
    ActsBy (S + T) v (a + b) := by
  unfold ActsBy at *
  rw [LinearMap.add_apply, hS, hT, add_smul]

theorem ActsBy.sub {S T : Module.End O M}
    {v : PrimitiveEigenvector (O := O) (M := M)} {a b : O}
    (hS : ActsBy S v a) (hT : ActsBy T v b) :
    ActsBy (S - T) v (a - b) := by
  unfold ActsBy at *
  rw [LinearMap.sub_apply, hS, hT, sub_smul]

theorem ActsBy.smul {T : Module.End O M}
    {v : PrimitiveEigenvector (O := O) (M := M)} {a s : O}
    (hT : ActsBy T v a) :
    ActsBy (s • T) v (s * a) := by
  unfold ActsBy at *
  rw [LinearMap.smul_apply, hT, smul_smul]

theorem ActsBy.id (v : PrimitiveEigenvector (O := O) (M := M)) :
    ActsBy LinearMap.id v 1 := by
  simp [ActsBy]

theorem ActsBy.mul {S T : Module.End O M}
    {v : PrimitiveEigenvector (O := O) (M := M)} {a b : O}
    (hS : ActsBy S v a) (hT : ActsBy T v b) :
    ActsBy (S * T) v (a * b) := by
  unfold ActsBy at *
  rw [Module.End.mul_apply, hT, map_smul, hS, smul_smul, mul_comm]

theorem ActsBy.pow {T : Module.End O M}
    {v : PrimitiveEigenvector (O := O) (M := M)} {a : O}
    (hT : ActsBy T v a) (n : ℕ) :
    ActsBy (T ^ n) v (a ^ n) := by
  induction n with
  | zero => simp [ActsBy]
  | succ n ih => simpa [pow_succ] using ih.mul hT

/-- Mathlib's polynomial action on an eigenspace, with the chosen primitive vector. -/
theorem ActsBy.aeval {T : Module.End O M}
    {v : PrimitiveEigenvector (O := O) (M := M)} {a : O}
    (hT : ActsBy T v a) (f : Polynomial O) :
    ActsBy (Polynomial.aeval T f) v (f.eval a) :=
  Module.End.aeval_apply_of_mem_apply_eq_smul hT

theorem ActsBy.eigenvalue_eq {T : Module.End O M}
    {v : PrimitiveEigenvector (O := O) (M := M)} {a b : O}
    (ha : ActsBy T v a) (hb : ActsBy T v b) : a = b := by
  have hvector : a • v.vector = b • v.vector := ha.symm.trans hb
  have hcoordinate := congrArg v.coordinate hvector
  simpa [map_smul, v.coordinate_vector] using hcoordinate

/-- An integral divided operator automatically has an integral eigenvalue
on the original primitive eigenvector. No eigenvector hypothesis for `Z`
is needed. Injectivity is supplied by the free target lattice. -/
theorem ActsBy.of_division {T Z : Module.End O M}
    {v : PrimitiveEigenvector (O := O) (M := M)} {a s : O}
    (hT : ActsBy T v a) (hdivision : T = s • Z)
    (hinjective : Function.Injective (fun x : M ↦ s • x)) :
    ∃ z : O, ActsBy Z v z ∧ a = s * z := by
  let z := v.coordinate (Z v.vector)
  have hscaled : s • Z v.vector = a • v.vector := by
    simpa [hdivision, ActsBy] using hT
  have ha : a = s * z := by
    have h := congrArg v.coordinate hscaled
    simpa [z, map_smul, v.coordinate_vector] using h.symm
  refine ⟨z, ?_, ha⟩
  apply hinjective
  simpa [ActsBy, smul_smul, ← ha] using hscaled

/-- Evaluating an image-containment identity on a primitive eigenvector gives
the corresponding divisibility of the eigenvalue. -/
theorem eigenvalue_dvd_of_mapsIntoMultiple
    {T : Module.End O M} {v : PrimitiveEigenvector (O := O) (M := M)}
    {a s : O} (heigen : ActsBy T v a) (himage : MapsIntoMultiple T s) :
    s ∣ a := by
  obtain ⟨y, hy⟩ := himage v.vector
  refine ⟨v.coordinate y, ?_⟩
  calc
    a = v.coordinate (T v.vector) := by
      rw [heigen]
      simp [v.coordinate_vector]
    _ = v.coordinate (s • y) := congrArg v.coordinate hy
    _ = s * v.coordinate y := by simp

/-- Evaluation of the ordinary relation `(T-c)L ⊆ p^m L`. -/
theorem ordinary_identity_implies_literal_congruence
    {p a c : O} {m : ℕ} {T : Module.End O M}
    {v : PrimitiveEigenvector (O := O) (M := M)}
    (heigen : ActsBy T v a)
    (hidentity : MapsIntoMultiple (T - c • LinearMap.id) (p ^ m)) :
    LiterallyCongruent p m a c := by
  have hshift : ActsBy (T - c • LinearMap.id) v (a - c) := by
    have hc : ActsBy (c • LinearMap.id) v c := by
      simpa using (ActsBy.id v).smul (s := c)
    exact heigen.sub hc
  exact eigenvalue_dvd_of_mapsIntoMultiple hshift hidentity

end Eigenvectors

section LocalRing

variable {O : Type*} [CommRing O] [IsLocalRing O]

theorem mem_maximalIdeal_of_pow_mem
    {x : O} {n : ℕ} (hn : 0 < n)
    (hx : x ^ n ∈ IsLocalRing.maximalIdeal O) :
    x ∈ IsLocalRing.maximalIdeal O := by
  exact (IsLocalRing.maximalIdeal.isMaximal O).isPrime.mem_of_pow_mem n hx

theorem factor_mem_maximalIdeal_of_product_mem
    {x y : O} (hxy : x * y ∈ IsLocalRing.maximalIdeal O) :
    x ∈ IsLocalRing.maximalIdeal O ∨ y ∈ IsLocalRing.maximalIdeal O := by
  exact (IsLocalRing.maximalIdeal.isMaximal O).isPrime.mem_or_mem hxy

/-- In a local ring, if two elements differ by a unit then at least one of
them is a unit.  This is the elementary root-separation argument used in the
`p = 3` chapter. -/
theorem isUnit_or_isUnit_of_sub_isUnit
    {x y : O} (hxy : IsUnit (x - y)) : IsUnit x ∨ IsUnit y := by
  simpa only [IsUnit.neg_iff] using
    (IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := x) (b := -y)
      (by simpa only [sub_eq_add_neg] using hxy))

/-- A unit factor can be cancelled from a divisibility statement. -/
theorem dvd_right_of_unit_mul_dvd
    {s u x : O} (hu : IsUnit u) (h : s ∣ u * x) : s ∣ x :=
  hu.dvd_mul_left.mp h

theorem mem_maximalIdeal_of_dvd_by_nonunit
    {p x : O} (hp : p ∈ IsLocalRing.maximalIdeal O) (hx : p ∣ x) :
    x ∈ IsLocalRing.maximalIdeal O := by
  obtain ⟨y, rfl⟩ := hx
  exact (IsLocalRing.maximalIdeal O).mul_mem_right y hp

end LocalRing

end HeckeCongruences

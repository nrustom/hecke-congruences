import HeckeCongruences.Basic
import HeckeCongruences.StagedDivision

/-!
# From propagated source identities to integral target lattices

This file contains the algebraic bridge in `prop:staged-p-division`. It is
independent of modular forms. The source is an `R`-module mapping
surjectively to an integral target modulo a scalar, and the target is assumed
torsion-free for the scalar by which cancellation is performed.

In the manuscript application R is the integral base ring Z_p. The finite
source over R_m is viewed as an R-module by restriction of scalars; the free
target P is not an R_m-module. The quotient map `q` denotes q_{d,m}, not an
orientation index.
-/

namespace HeckeCongruences

section ScalarMultiples

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The submodule `s M`, expressed using the range of scalar multiplication. -/
def multipleSubmodule (s : R) : Submodule R M :=
  LinearMap.range (s • (LinearMap.id : Module.End R M))

theorem mem_multipleSubmodule_iff {s : R} {x : M} :
    x ∈ multipleSubmodule s ↔ ∃ y : M, x = s • y := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, hy.symm.trans (by simp)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, by simp⟩

/-- Mathlib congruence modulo the scalar-multiple submodule `s M`. -/
abbrev CongruentModulo (s : R) (x y : M) : Prop :=
  SModEq (multipleSubmodule s) x y

theorem congruentModulo_iff {s : R} {x y : M} :
    CongruentModulo s x y ↔ ∃ z : M, x - y = s • z :=
  SModEq.sub_mem.trans mem_multipleSubmodule_iff

theorem CongruentModulo.refl (s : R) (x : M) : CongruentModulo s x x :=
  SModEq.refl x

theorem CongruentModulo.symm {s : R} {x y : M}
    (h : CongruentModulo s x y) : CongruentModulo s y x := SModEq.symm h

theorem CongruentModulo.trans {s : R} {x y z : M}
    (hxy : CongruentModulo s x y) (hyz : CongruentModulo s y z) :
    CongruentModulo s x z := SModEq.trans hxy hyz

theorem CongruentModulo.add {s : R} {x₁ x₂ y₁ y₂ : M}
    (h₁ : CongruentModulo s x₁ y₁) (h₂ : CongruentModulo s x₂ y₂) :
    CongruentModulo s (x₁ + x₂) (y₁ + y₂) := SModEq.add h₁ h₂

theorem CongruentModulo.finset_sum {s : R} {I : Type*}
    (A : Finset I) (f g : I → M)
    (h : ∀ i ∈ A, CongruentModulo s (f i) (g i)) :
    CongruentModulo s (∑ i ∈ A, f i) (∑ i ∈ A, g i) := SModEq.sum h

theorem CongruentModulo.multiple_zero (s : R) (x : M) :
    CongruentModulo s (s • x) 0 :=
  SModEq.zero.mpr (mem_multipleSubmodule_iff.mpr ⟨x,rfl⟩)

theorem CongruentModulo.map {N : Type*} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) {s : R} {x y : M} (h : CongruentModulo s x y) :
    CongruentModulo s (f x) (f y) := by
  apply (SModEq.map h f).mono
  rintro _ ⟨z,hz,rfl⟩
  obtain ⟨w,rfl⟩ := mem_multipleSubmodule_iff.mp hz
  exact mem_multipleSubmodule_iff.mpr ⟨f w, f.map_smul s w⟩

theorem CongruentModulo.smul (r : R) {s : R} {x y : M}
    (h : CongruentModulo s x y) : CongruentModulo s (r • x) (r • y) := SModEq.smul h r

theorem CongruentModulo.weaken_left (a b : R) {x y : M}
    (h : CongruentModulo (a * b) x y) : CongruentModulo b x y := by
  obtain ⟨z, hz⟩ := congruentModulo_iff.mp h
  apply congruentModulo_iff.mpr
  refine ⟨a • z, ?_⟩
  simpa only [smul_smul, mul_comm] using hz

theorem CongruentModulo.cancel_left (a b : R)
    (ha : Function.Injective (fun x : M ↦ a • x)) {x y : M}
    (h : CongruentModulo (a * b) (a • x) (a • y)) :
    CongruentModulo b x y := by
  obtain ⟨z, hz⟩ := congruentModulo_iff.mp h
  apply congruentModulo_iff.mpr
  refine ⟨z, ?_⟩
  apply ha
  simpa only [smul_sub, smul_smul] using hz

theorem quotient_mk_eq_iff {s : R} {x y : M} :
    (Submodule.Quotient.mk x : M ⧸ multipleSubmodule (M := M) s) =
      Submodule.Quotient.mk y ↔ CongruentModulo s x y := by
  rfl

/-- Every endomorphism preserves a scalar-multiple submodule. -/
theorem endomorphism_preserves_multiple (T : Module.End R M) (s : R) :
    multipleSubmodule s ≤ Submodule.comap T (multipleSubmodule s) := by
  intro x hx
  obtain ⟨y, rfl⟩ := mem_multipleSubmodule_iff.mp hx
  apply mem_multipleSubmodule_iff.mpr
  exact ⟨T y, by simp⟩

/-- The endomorphism induced modulo `s`. -/
def quotientEndomorphism (T : Module.End R M) (s : R) :
    Module.End R (M ⧸ multipleSubmodule (M := M) s) :=
  Submodule.mapQ (multipleSubmodule (M := M) s) (multipleSubmodule (M := M) s) T
    (endomorphism_preserves_multiple T s)

theorem quotientEndomorphism_mk (T : Module.End R M) (s : R) (x : M) :
    quotientEndomorphism T s (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (T x) := by
  exact Submodule.mapQ_apply _ _ _ x

/-- Mathlib's ZMod algebra structure on endomorphisms modulo n.
This also works when the quotient module is zero. -/
@[instance_reducible]
noncomputable def quotientEndZModAlgebra
    (R P : Type*) [CommRing R] [AddCommGroup P] [Module R P] (n : ℕ) :
    Algebra (ZMod n) (Module.End R (P ⧸ multipleSubmodule (M := P) (n : R))) := by
  let Q := P ⧸ multipleSubmodule (M := P) (n : R)
  have hn : (n : Module.End R Q) = 0 := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      change (n : Module.End R Q) (Submodule.Quotient.mk x) = 0
      have he : (n : Module.End R Q) = (n : R) • (LinearMap.id : Module.End R Q) := by
        rw [← Module.algebraMap_end_eq_smul_id, map_natCast]
      rw [he, LinearMap.smul_apply, LinearMap.id_apply]
      change (Submodule.mkQ (multipleSubmodule (M := P) (n : R))) ((n : R) • x) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (mem_multipleSubmodule_iff.mpr ⟨x,rfl⟩)
  exact ZMod.algebra' (Module.End R Q) (ringChar (Module.End R Q))
    ((CharP.cast_eq_zero_iff (Module.End R Q) (ringChar (Module.End R Q)) n).mp hn)

@[simp] theorem quotientEndomorphism_mul (S T : Module.End R M) (s : R) :
    quotientEndomorphism (S*T) s = quotientEndomorphism S s * quotientEndomorphism T s := by
  ext x
  rfl

end ScalarMultiples

section Division

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Pointwise divisibility and injectivity construct the divided operator
using Mathlib's equivalence between a module and the range of an injective
linear map. -/
noncomputable def divideEndomorphism (T : Module.End R M) (s : R)
    (himage : MapsIntoMultiple T s)
    (hinjective : Function.Injective (fun x : M ↦ s • x)) : Module.End R M :=
  ((LinearEquiv.ofInjective (s • (LinearMap.id : Module.End R M))
    hinjective).symm.toLinearMap).comp
    (T.codRestrict (multipleSubmodule s)
      (fun x ↦ mem_multipleSubmodule_iff.mpr (himage x)))

theorem divideEndomorphism_spec (T : Module.End R M) (s : R)
    (himage : MapsIntoMultiple T s)
    (hinjective : Function.Injective (fun x : M ↦ s • x)) (x : M) :
    T x = s • divideEndomorphism T s himage hinjective x := by
  exact (LinearEquiv.ofInjective_symm_apply
    (s • (LinearMap.id : Module.End R M)) (h := hinjective)
    (T.codRestrict (multipleSubmodule s)
      (fun x ↦ mem_multipleSubmodule_iff.mpr (himage x)) x)).symm

/-- Saturation by one scalar, the exact property used when a divided
operator is restricted from `P_d^+` to `L_d^+`. -/
def IsSaturatedBy (s : R) (L : Submodule R M) : Prop :=
  ∀ x : M, s • x ∈ L → x ∈ L

theorem mapsIntoMultiple_restrict_of_saturated
    (T : Module.End R M) (L : Submodule R M)
    (hL : ∀ x ∈ L, T x ∈ L) (s : R)
    (hsaturated : IsSaturatedBy s L) (hT : MapsIntoMultiple T s) :
    MapsIntoMultiple (restrictEndomorphism T L hL) s := by
  intro x
  obtain ⟨y, hy⟩ := hT x
  have hyL : y ∈ L := hsaturated y (hy ▸ hL x x.property)
  exact ⟨⟨y, hyL⟩, Subtype.ext hy⟩

end Division

section StagedSourceToTarget

variable {R Source Target : Type*} [CommRing R]
  [AddCommGroup Source] [Module R Source]
  [AddCommGroup Target] [Module R Target]

/-- A chosen representative of a class in a scalar quotient. -/
noncomputable def quotientRepresentative (s : R)
    (z : Target ⧸ multipleSubmodule (M := Target) s) : Target :=
  Classical.choose (Submodule.mkQ_surjective (multipleSubmodule (M := Target) s) z)

theorem quotientRepresentative_spec (s : R)
    (z : Target ⧸ multipleSubmodule (M := Target) s) :
    Submodule.Quotient.mk (quotientRepresentative s z) = z :=
  Classical.choose_spec (Submodule.mkQ_surjective (multipleSubmodule (M := Target) s) z)

/-- The first equation in a staged witness, together with source--target
compatibility modulo `pMod`, proves divisibility of the target operator by
`pAlpha`.  The factorization `pMod = pAlpha*pGuard` is the abstract form of
`α ≤ m`. -/
theorem stagedSource_implies_targetOperator_divisible
    (Tsource : Module.End R Source) (Ttarget : Module.End R Target)
    (pAlpha pGuard pMod pDepth : R) (coeff : ℕ → R) (degree : ℕ)
    (hdegree : 0 < degree) (hmod : pMod = pAlpha * pGuard)
    (q : Source →ₗ[R] Target ⧸ multipleSubmodule (M := Target) pMod)
    (hq : Function.Surjective q)
    (hcompat : ∀ x,
      quotientEndomorphism Ttarget pMod (q x) = q (Tsource x))
    (hstage : AdmitsStagedDivision Tsource pAlpha pDepth coeff degree) :
    MapsIntoMultiple Ttarget pAlpha := by
  intro y
  obtain ⟨x, hx⟩ := hq (Submodule.Quotient.mk y)
  obtain ⟨w⟩ := hstage x
  let y₁ : Target := quotientRepresentative pMod (q (w.chain 1))
  have hy₁ : (Submodule.Quotient.mk y₁ :
      Target ⧸ multipleSubmodule (M := Target) pMod) = q (w.chain 1) :=
    quotientRepresentative_spec pMod _
  have hstep : Tsource x = pAlpha • w.chain 1 := by
    simpa [w.chain_zero] using w.step 0 hdegree
  have hquotient :
      (Submodule.Quotient.mk (Ttarget y) :
          Target ⧸ multipleSubmodule (M := Target) pMod) =
        Submodule.Quotient.mk (pAlpha • y₁) := by
    calc
      Submodule.Quotient.mk (Ttarget y) =
          quotientEndomorphism Ttarget pMod (Submodule.Quotient.mk y) := by
            symm
            exact quotientEndomorphism_mk Ttarget pMod y
      _ = quotientEndomorphism Ttarget pMod (q x) := by rw [hx]
      _ = q (Tsource x) := hcompat x
      _ = q (pAlpha • w.chain 1) := congrArg q hstep
      _ = pAlpha • q (w.chain 1) := q.map_smul _ _
      _ = pAlpha • Submodule.Quotient.mk y₁ := by rw [hy₁]
      _ = Submodule.Quotient.mk (pAlpha • y₁) := by
        exact (map_smul (Submodule.mkQ (multipleSubmodule (M := Target) pMod))
          pAlpha y₁).symm
  have hcongruent : CongruentModulo pMod (Ttarget y) (pAlpha • y₁) :=
    quotient_mk_eq_iff.mp hquotient
  obtain ⟨error, herror⟩ := congruentModulo_iff.mp hcongruent
  refine ⟨y₁ + pGuard • error, ?_⟩
  calc
    Ttarget y = pAlpha • y₁ + pMod • error := by
      rw [← herror]
      abel
    _ = pAlpha • (y₁ + pGuard • error) := by
      rw [hmod, smul_add, smul_smul]

/-- The endomorphism obtained by substituting `Z` into
`Σ_(j=0)^degree coeff_j X^j`. -/
def polynomialOperator (coeff : ℕ → R) (degree : ℕ)
    (Z : Module.End R Target) : Module.End R Target :=
  ∑ j ∈ Finset.range (degree + 1), coeff j • Z ^ j

theorem polynomialOperator_apply (coeff : ℕ → R) (degree : ℕ)
    (Z : Module.End R Target) (x : Target) :
    polynomialOperator coeff degree Z x =
      ∑ j ∈ Finset.range (degree + 1), coeff j • (Z ^ j) x := by
  simp [polynomialOperator]

/-- The full cancellation statement of the manuscript's staged-division
proposition.  A propagated source witness produces an integral divided target
operator `Z`, and its terminal polynomial maps the target into `pDepth`.

The scalar factorizations say
`pMod = pAlpha*pGuard` and `pGuard = pDepth*pTail`; for powers of one prime
these are precisely `α ≤ m` and `b ≤ m-α`. -/
theorem stagedSource_implies_targetPolynomial
    (Tsource : Module.End R Source) (Ttarget : Module.End R Target)
    (pAlpha pGuard pDepth pTail pMod : R) (coeff : ℕ → R) (degree : ℕ)
    (hdegree : 0 < degree)
    (hmod : pMod = pAlpha * pGuard)
    (hguard : pGuard = pDepth * pTail)
    (hinjective : Function.Injective (fun x : Target ↦ pAlpha • x))
    (q : Source →ₗ[R] Target ⧸ multipleSubmodule (M := Target) pMod)
    (hq : Function.Surjective q)
    (hcompat : ∀ x,
      quotientEndomorphism Ttarget pMod (q x) = q (Tsource x))
    (hstage : AdmitsStagedDivision Tsource pAlpha pDepth coeff degree) :
    ∃ Z : Module.End R Target,
      (∀ y, Ttarget y = pAlpha • Z y) ∧
      MapsIntoMultiple (polynomialOperator coeff degree Z) pDepth := by
  let hdiv : MapsIntoMultiple Ttarget pAlpha :=
    stagedSource_implies_targetOperator_divisible Tsource Ttarget
      pAlpha pGuard pMod pDepth coeff degree hdegree hmod q hq hcompat hstage
  let Z : Module.End R Target :=
    divideEndomorphism Ttarget pAlpha hdiv hinjective
  have hTZ : ∀ y, Ttarget y = pAlpha • Z y :=
    divideEndomorphism_spec Ttarget pAlpha hdiv hinjective
  refine ⟨Z, hTZ, ?_⟩
  intro y
  obtain ⟨x₀, hx₀⟩ := hq (Submodule.Quotient.mk y)
  obtain ⟨w⟩ := hstage x₀
  let representative : ℕ → Target := fun j ↦
    quotientRepresentative pMod (q (w.chain j))
  have hrepresentative : ∀ j,
      (Submodule.Quotient.mk (representative j) :
        Target ⧸ multipleSubmodule (M := Target) pMod) = q (w.chain j) := by
    intro j
    exact quotientRepresentative_spec pMod _
  have hinitialMod : CongruentModulo pMod y (representative 0) := by
    apply quotient_mk_eq_iff.mp
    calc
      Submodule.Quotient.mk y = q x₀ := hx₀.symm
      _ = q (w.chain 0) := by rw [w.chain_zero]
      _ = Submodule.Quotient.mk (representative 0) := (hrepresentative 0).symm
  have hinitial : CongruentModulo pGuard y (representative 0) := by
    rw [hmod] at hinitialMod
    exact hinitialMod.weaken_left pAlpha pGuard
  have honeStep : ∀ j, j < degree →
      CongruentModulo pGuard (Z (representative j)) (representative (j + 1)) := by
    intro j hj
    have hquotient :
        (Submodule.Quotient.mk (Ttarget (representative j)) :
            Target ⧸ multipleSubmodule (M := Target) pMod) =
          Submodule.Quotient.mk (pAlpha • representative (j + 1)) := by
      calc
        Submodule.Quotient.mk (Ttarget (representative j)) =
            quotientEndomorphism Ttarget pMod
              (Submodule.Quotient.mk (representative j)) := by
                symm
                exact quotientEndomorphism_mk Ttarget pMod _
        _ = quotientEndomorphism Ttarget pMod (q (w.chain j)) := by
          rw [hrepresentative]
        _ = q (Tsource (w.chain j)) := hcompat _
        _ = q (pAlpha • w.chain (j + 1)) := congrArg q (w.step j hj)
        _ = pAlpha • q (w.chain (j + 1)) := q.map_smul _ _
        _ = pAlpha • Submodule.Quotient.mk (representative (j + 1)) := by
          rw [hrepresentative]
        _ = Submodule.Quotient.mk (pAlpha • representative (j + 1)) := by
          exact (map_smul (Submodule.mkQ (multipleSubmodule (M := Target) pMod))
            pAlpha _).symm
    have hscaled : CongruentModulo pMod
        (pAlpha • Z (representative j))
        (pAlpha • representative (j + 1)) := by
      rw [← hTZ]
      exact quotient_mk_eq_iff.mp hquotient
    rw [hmod] at hscaled
    exact hscaled.cancel_left pAlpha pGuard hinjective
  have hchain : ∀ j, j ≤ degree →
      CongruentModulo pGuard ((Z ^ j) y) (representative j) := by
    intro j hj
    induction j with
    | zero => simpa using hinitial
    | succ j ih =>
        have hjlt : j < degree := by omega
        have hmapped := (ih (by omega)).map Z
        have hnext := hmapped.trans (honeStep j hjlt)
        rw [pow_succ', Module.End.mul_apply]
        exact hnext
  have hpolynomial : CongruentModulo pGuard
      (polynomialOperator coeff degree Z y)
      (∑ j ∈ Finset.range (degree + 1), coeff j • representative j) := by
    rw [polynomialOperator_apply]
    apply CongruentModulo.finset_sum
    intro j hj
    apply CongruentModulo.smul
    apply hchain
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  let rhoRepresentative : Target := quotientRepresentative pMod (q w.rho)
  have hrhoRepresentative :
      (Submodule.Quotient.mk rhoRepresentative :
        Target ⧸ multipleSubmodule (M := Target) pMod) = q w.rho :=
    quotientRepresentative_spec pMod _
  have hterminalQuotient :
      (Submodule.Quotient.mk
          (∑ j ∈ Finset.range (degree + 1), coeff j • representative j) :
          Target ⧸ multipleSubmodule (M := Target) pMod) =
        Submodule.Quotient.mk (pDepth • rhoRepresentative) := by
    calc
      Submodule.Quotient.mk
          (∑ j ∈ Finset.range (degree + 1), coeff j • representative j) =
          ∑ j ∈ Finset.range (degree + 1),
            coeff j • Submodule.Quotient.mk (representative j) := by
              change (Submodule.mkQ (multipleSubmodule (M := Target) pMod))
                  (∑ j ∈ Finset.range (degree + 1), coeff j • representative j) =
                ∑ j ∈ Finset.range (degree + 1), coeff j •
                  (Submodule.mkQ (multipleSubmodule (M := Target) pMod)) (representative j)
              rw [map_sum]
              apply Finset.sum_congr rfl
              intro j hj
              exact (Submodule.mkQ (multipleSubmodule (M := Target) pMod)).map_smul
                (coeff j) (representative j)
      _ = ∑ j ∈ Finset.range (degree + 1), coeff j • q (w.chain j) := by
        simp_rw [hrepresentative]
      _ = q (∑ j ∈ Finset.range (degree + 1), coeff j • w.chain j) := by
        simp
      _ = q (pDepth • w.rho) := congrArg q w.terminal
      _ = pDepth • q w.rho := q.map_smul _ _
      _ = pDepth • Submodule.Quotient.mk rhoRepresentative := by
        rw [hrhoRepresentative]
      _ = Submodule.Quotient.mk (pDepth • rhoRepresentative) := by simp
  have hterminalMod : CongruentModulo pMod
      (∑ j ∈ Finset.range (degree + 1), coeff j • representative j)
      (pDepth • rhoRepresentative) :=
    quotient_mk_eq_iff.mp hterminalQuotient
  have hguardDepth : pGuard = pTail * pDepth := by
    rw [hguard, mul_comm]
  have hmodDepth : pMod = (pAlpha * pTail) * pDepth := by
    rw [hmod, hguard]
    ring
  rw [hguardDepth] at hpolynomial
  have hpolynomialDepth := hpolynomial.weaken_left pTail pDepth
  rw [hmodDepth] at hterminalMod
  have hterminalDepth := hterminalMod.weaken_left (pAlpha * pTail) pDepth
  have htotal : CongruentModulo pDepth
      (polynomialOperator coeff degree Z y) 0 :=
    hpolynomialDepth.trans
      (hterminalDepth.trans (CongruentModulo.multiple_zero pDepth rhoRepresentative))
  obtain ⟨z, hz⟩ := congruentModulo_iff.mp htotal
  exact ⟨z, by simpa using hz⟩

/-- A divided operator preserves a saturated sublattice whenever its
undivided numerator does. -/
theorem dividedOperator_preserves_saturated
    (T Z : Module.End R Target) (pAlpha : R) (L : Submodule R Target)
    (hTZ : ∀ y, T y = pAlpha • Z y)
    (hTL : ∀ x ∈ L, T x ∈ L) (hsaturated : IsSaturatedBy pAlpha L) :
    ∀ x ∈ L, Z x ∈ L := by
  intro x hx
  apply hsaturated
  rw [← hTZ]
  exact hTL x hx

/-- Polynomials in an endomorphism preserve every submodule preserved by the
endomorphism. -/
theorem polynomialOperator_preserves
    (coeff : ℕ → R) (degree : ℕ) (Z : Module.End R Target)
    (L : Submodule R Target) (hZL : ∀ x ∈ L, Z x ∈ L) :
    ∀ x ∈ L, polynomialOperator coeff degree Z x ∈ L := by
  intro x hx
  rw [polynomialOperator_apply]
  apply Submodule.sum_mem
  intro j hj
  apply L.smul_mem
  have hpow : ∀ n : ℕ, (Z ^ n) x ∈ L := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
        rw [pow_succ', Module.End.mul_apply]
        exact hZL _ ih
  exact hpow j

/-- The final restriction from `P_d^+` to its saturated cuspidal sublattice
`L_d^+`. -/
theorem stagedTargetRelation_restricts_to_saturatedLattice
    (T Z : Module.End R Target) (pAlpha pDepth : R)
    (coeff : ℕ → R) (degree : ℕ) (L : Submodule R Target)
    (hTZ : ∀ y, T y = pAlpha • Z y)
    (hTL : ∀ x ∈ L, T x ∈ L)
    (hsaturatedAlpha : IsSaturatedBy pAlpha L)
    (hsaturatedDepth : IsSaturatedBy pDepth L)
    (hterminal : MapsIntoMultiple (polynomialOperator coeff degree Z) pDepth) :
    MapsIntoMultiple
      (restrictEndomorphism (polynomialOperator coeff degree Z) L
        (polynomialOperator_preserves coeff degree Z L
          (dividedOperator_preserves_saturated T Z pAlpha L hTZ hTL hsaturatedAlpha)))
      pDepth := by
  apply mapsIntoMultiple_restrict_of_saturated
  · exact hsaturatedDepth
  · exact hterminal

end StagedSourceToTarget

end HeckeCongruences

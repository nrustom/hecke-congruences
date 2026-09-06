import HeckeCongruences.Basic
import HeckeCongruences.PrimeSevenData

/-!
# The selected eigenvalues for `p = 7`, modulo `7^2`

This file follows Section 7 of the manuscript. Its conditional theorems use
the displayed operators and relations:

* the three tangent polynomials `F₀`, `F₂`, `F₄` and the divided operators
  `Q_j(T₃)=F_j(T₃)/49`;
* `G_j(T₃,T₂₉)` and both `H(X)=(X⁷-X)³` identities;
* both coordinate relations `R_{r,c}^{(1)}`, `R_{r,c}^{(2)}`;
* the projected `E^6 U_c-φ_{r,c}` and `E^6 V-ψ_{r,c}` graph relations.

`PrimeSevenData.lean` transcribes the 210 archived relation polynomials.
Their source identities remain hypotheses; the transcription does not
certify the source computations.
-/

namespace HeckeCongruences.PrimeSeven

open HeckeCongruences
open PrimeSevenData

variable {O M : Type*} [CommRing O] [IsLocalRing O]
  [AddCommGroup M] [Module O M]

/-- The manuscript index `j ∈ {0,2,4}` for the three tangent branches. -/
inductive TangentIndex where
  | j0 | j2 | j4
  deriving DecidableEq, Repr

/-- The exact tangent polynomial `F₀`. -/
def F0 (X : O) : O :=
  X ^ 6 + 7 * X ^ 5 + 45 * X ^ 4 + 7 * X ^ 3 + 4 * X ^ 2 + 7 * X

/-- The exact tangent polynomial `F₂`. -/
def F2 (X : O) : O :=
  X ^ 6 + 42 * X ^ 5 + 6 * X ^ 4 + 9 * X ^ 2 + 14 * X

/-- The exact tangent polynomial `F₄`. -/
def F4 (X : O) : O :=
  X ^ 6 + 7 * X ^ 5 + 47 * X ^ 4 + 14 * X ^ 3 + X ^ 2 + 28 * X

/-- `F_j`, with `j ∈ {0,2,4}`. -/
def Fj (j : TangentIndex) (X : O) : O :=
  match j with
  | .j0 => F0 X
  | .j2 => F2 X
  | .j4 => F4 X

def αj (j : TangentIndex) : O :=
  match j with
  | .j0 => 3
  | .j2 => 2
  | .j4 => 1

def βj (j : TangentIndex) : O :=
  match j with
  | .j0 => 4
  | .j2 => 5
  | .j4 => 6

/-- The numerator of
`G_j(X,Y)=(Y-2-X(X-α_j)(X-β_j))/7`. -/
def Gnumerator (j : TangentIndex) (X Y : O) : O :=
  Y - 2 - X * (X - αj j) * (X - βj j)

/-- `H(X)=(X⁷-X)³`. -/
def H (X : O) : O :=
  (X ^ 7 - X) ^ 3

/-- Mathlib polynomial evaluation of the displayed tangent polynomial. -/
noncomputable def FjOperator (j : TangentIndex) (T3 : Module.End O M) :
    Module.End O M :=
  Polynomial.aeval T3 (Fj j (Polynomial.X : Polynomial O))

theorem actsBy_FjOperator
    (j : TangentIndex) (T3 : Module.End O M)
    (v : PrimitiveEigenvector (O := O) (M := M)) (a3 : O)
    (hT3 : ActsBy T3 v a3) :
    ActsBy (FjOperator j T3) v (Fj j a3) := by
  have h := hT3.aeval (Fj j (Polynomial.X : Polynomial O))
  cases j <;> simpa [FjOperator, Fj, F0, F2, F4] using h

/-- The operator numerator
`T₂₉-2-T₃(T₃-α_j)(T₃-β_j)`. -/
def GjNumeratorOperator (j : TangentIndex)
    (T3 T29 : Module.End O M) : Module.End O M :=
  T29 - (2 : O) • LinearMap.id -
    T3 * (T3 - αj (O := O) j • LinearMap.id) *
      (T3 - βj (O := O) j • LinearMap.id)

/-- The first two divided identities, including both exact `H` relations,
evaluated on the primitive eigenvector. -/
theorem Qj_Gj_eigenvalue_relations
    {T3 T29 QjT3 GjT3T29 : Module.End O M}
    {v : PrimitiveEigenvector (O := O) (M := M)}
    {a3 a29 qf gf : O} (j : TangentIndex)
    (ha3 : ActsBy T3 v a3)
    (ha29 : ActsBy T29 v a29)
    (hqf : ActsBy QjT3 v qf)
    (hgf : ActsBy GjT3T29 v gf)
    (hQdivision : FjOperator j T3 = (7 : O) ^ 2 • QjT3)
    (hGdivision : GjNumeratorOperator j T3 T29 = (7 : O) • GjT3T29)
    (hQrelation : MapsIntoMultiple ((QjT3 ^ 7 - QjT3) ^ 3) (7 : O))
    (hGrelation : MapsIntoMultiple ((GjT3T29 ^ 7 - GjT3T29) ^ 3) (7 : O)) :
    Fj j a3 = (7 : O) ^ 2 * qf ∧
      Gnumerator j a3 a29 = (7 : O) * gf ∧
      (7 : O) ∣ H qf ∧ (7 : O) ∣ H gf := by
  have hF := actsBy_FjOperator j T3 v a3 ha3
  have hQscaled : ActsBy ((7 : O) ^ 2 • QjT3) v ((7 : O) ^ 2 * qf) := hqf.smul
  have hFeq : Fj j a3 = (7 : O) ^ 2 * qf := by
    rw [hQdivision] at hF
    exact hF.eigenvalue_eq hQscaled
  have htwo : ActsBy ((2 : O) • LinearMap.id) v (2 : O) := by
    simpa using (ActsBy.id v).smul (s := (2 : O))
  have hα : ActsBy (αj (O := O) j • LinearMap.id) v (αj (O := O) j) := by
    simpa using (ActsBy.id v).smul (s := αj (O := O) j)
  have hβ : ActsBy (βj (O := O) j • LinearMap.id) v (βj (O := O) j) := by
    simpa using (ActsBy.id v).smul (s := βj (O := O) j)
  have hGnum : ActsBy (GjNumeratorOperator j T3 T29) v
      (Gnumerator j a3 a29) := by
    exact (ha29.sub htwo).sub ((ha3.mul (ha3.sub hα)).mul (ha3.sub hβ))
  have hGscaled : ActsBy ((7 : O) • GjT3T29) v ((7 : O) * gf) := hgf.smul
  have hGeq : Gnumerator j a3 a29 = (7 : O) * gf := by
    rw [hGdivision] at hGnum
    exact hGnum.eigenvalue_eq hGscaled
  have hQH : ActsBy ((QjT3 ^ 7 - QjT3) ^ 3) v (H qf) := by
    exact ((hqf.pow 7).sub hqf).pow 3
  have hGH : ActsBy ((GjT3T29 ^ 7 - GjT3T29) ^ 3) v (H gf) := by
    exact ((hgf.pow 7).sub hgf).pow 3
  exact ⟨hFeq, hGeq, eigenvalue_dvd_of_mapsIntoMultiple hQH hQrelation,
    eigenvalue_dvd_of_mapsIntoMultiple hGH hGrelation⟩

/-- The exact `H(X)=(X⁷-X)³` relation says that the reduction of the
divided eigenvalue is fixed by Frobenius, hence belongs to the prime field
inside the residue field. -/
theorem H_relation_implies_frobenius_fixed
    {z : O}
    (h7max : (7 : O) ∈ IsLocalRing.maximalIdeal O)
    (hH : (7 : O) ∣ H z) :
    z ^ 7 - z ∈ IsLocalRing.maximalIdeal O := by
  have hcube : (z ^ 7 - z) ^ 3 ∈ IsLocalRing.maximalIdeal O :=
    mem_maximalIdeal_of_dvd_by_nonunit h7max hH
  exact mem_maximalIdeal_of_pow_mem (by decide) hcube

/-- Evaluate one monomial of an exact certificate polynomial. -/
def evaluateTerm (term : RelationTerm) (Q G J : O) : O :=
  term.coefficient * Q ^ term.QPower * G ^ term.GPower * J ^ term.JPower

/-- Evaluate one of the 210 exact certificate polynomials. -/
def evaluateRelation (relation : Relation) (Q G J : O) : O :=
  (relation.terms.map fun term => evaluateTerm term Q G J).sum

private def evaluateTermOperator (term : RelationTerm)
    (Q G J : Module.End O M) : Module.End O M :=
  (term.coefficient : O) •
    (Q ^ term.QPower * G ^ term.GPower * J ^ term.JPower)

/-- The endomorphism obtained by substituting the divided operators into one
of the exact stored polynomials. -/
def evaluateRelationOperator (relation : Relation)
    (Q G J : Module.End O M) : Module.End O M :=
  (relation.terms.map fun term => evaluateTermOperator term Q G J).sum

theorem actsBy_evaluateRelationOperator
    (relation : Relation) (Q G J : Module.End O M)
    (v : PrimitiveEigenvector (O := O) (M := M)) (q g j : O)
    (hQ : ActsBy Q v q) (hG : ActsBy G v g) (hJ : ActsBy J v j) :
    ActsBy (evaluateRelationOperator relation Q G J) v
      (evaluateRelation relation q g j) := by
  unfold evaluateRelationOperator evaluateRelation
  induction relation.terms with
  | nil => simp [ActsBy]
  | cons term terms ih =>
      simp only [List.map_cons, List.sum_cons]
      apply ActsBy.add
      · have hterm := (((hQ.pow term.QPower).mul (hG.pow term.GPower)).mul
            (hJ.pow term.JPower)).smul (s := (term.coefficient : O))
        convert hterm using 1 <;> simp [evaluateTermOperator, evaluateTerm] <;> ring
      · exact ih

def graphScalar (family : RelationFamily) (x y : O) : O :=
  match family with
  | .coordinate => 0
  | .graphU => x
  | .graphV => y

/-- The exact selected relation
`E_{j,c}(T₃)^6 [R(Q_j,G_j)]^3` (coordinate family), or the corresponding
`E^6 U_c-φ` / `E^6 V-ψ` graph relation.  The exponents are read from the literal
certificate transcription. -/
def selectedRelationOperator (relation : Relation)
    (E R : Module.End O M) : Module.End O M :=
  E ^ relation.selectorPower * R ^ relation.relationPower

/-- Every exact `p=7` coordinate and graph identity, after evaluation and
cancellation of the selector `E_{j,c}(a₃)^6`, gives its scalar relation in the
maximal ideal.  Taking `relation` over `PrimeSevenData.relations` uses all 210
polynomials transcribed from the certificate. -/
theorem selected_relation_eigenvalue_in_maximalIdeal
    {E R : Module.End O M}
    {v : PrimitiveEigenvector (O := O) (M := M)}
    {e q g x y : O} (relation : Relation)
    (hrelation : relation ∈ relations)
    (h7max : (7 : O) ∈ IsLocalRing.maximalIdeal O)
    (hE : ActsBy E v e)
    (hR : ActsBy R v
      (evaluateRelation relation q g (graphScalar relation.family x y)))
    (hEunit : IsUnit e)
    (hidentity : MapsIntoMultiple
      (selectedRelationOperator relation E R) (7 : O)) :
    evaluateRelation relation q g (graphScalar relation.family x y) ∈
      IsLocalRing.maximalIdeal O := by
  have hselected : ActsBy (selectedRelationOperator relation E R) v
      (e ^ relation.selectorPower *
        (evaluateRelation relation q g (graphScalar relation.family x y)) ^
          relation.relationPower) := by
    exact (hE.pow relation.selectorPower).mul (hR.pow relation.relationPower)
  have hdiv := eigenvalue_dvd_of_mapsIntoMultiple hselected hidentity
  have hRpowDiv : (7 : O) ∣
      (evaluateRelation relation q g (graphScalar relation.family x y)) ^
        relation.relationPower :=
    dvd_right_of_unit_mul_dvd (hEunit.pow relation.selectorPower) hdiv
  have hRpowMax := mem_maximalIdeal_of_dvd_by_nonunit h7max hRpowDiv
  have hpositive : 0 < relation.relationPower := by
    rw [relation_powers relation hrelation]
    decide
  exact mem_maximalIdeal_of_pow_mem hpositive hRpowMax

/-- The inner selector reduces to 1 on the selected branch. This uses
`e ≡ 1`, not merely invertibility of e. It applies to arbitrary stored
polynomials, so the computational table remains an input. -/
theorem projected_relation_implies_raw_relation
    (relation : Relation) {e q g x y : O}
    (he : e - 1 ∈ IsLocalRing.maximalIdeal O)
    (hprojected : evaluateRelation relation q g
      (graphScalar relation.family (e^6*x) (e^6*y)) ∈ IsLocalRing.maximalIdeal O) :
    evaluateRelation relation q g (graphScalar relation.family x y) ∈
      IsLocalRing.maximalIdeal O := by
  have heq : IsLocalRing.residue O e = 1 := by
    have hh : IsLocalRing.residue O e = IsLocalRing.residue O 1 :=
      Ideal.Quotient.eq.mpr he
    simpa using hh
  have hp := (Ideal.Quotient.eq_zero_iff_mem).mpr hprojected
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  change IsLocalRing.residue O (evaluateRelation relation q g
    (graphScalar relation.family x y)) = 0
  change IsLocalRing.residue O (evaluateRelation relation q g
    (graphScalar relation.family (e^6*x) (e^6*y))) = 0 at hp
  cases hfamily : relation.family <;>
    simpa [evaluateRelation, evaluateTerm, graphScalar, hfamily,
      map_list_sum, List.map_map, Function.comp_def, map_mul, map_pow, heq] using hp

/-- Evaluate the actual coordinate or projected graph identity checked by
Python. The graph eigenvalues are e^6*x and e^6*y; the conclusion is the
unprojected scalar relation after reduction modulo the maximal ideal. -/
theorem exact_selected_relation_implies_scalar_relation
    {E R : Module.End O M}
    {v : PrimitiveEigenvector (O := O) (M := M)}
    {e q g x y : O} (relation : Relation)
    (hrelation : relation ∈ relations)
    (h7max : (7 : O) ∈ IsLocalRing.maximalIdeal O)
    (hE : ActsBy E v e)
    (hR : ActsBy R v (evaluateRelation relation q g
      (graphScalar relation.family (e^6*x) (e^6*y))))
    (hEone : e - 1 ∈ IsLocalRing.maximalIdeal O)
    (hidentity : MapsIntoMultiple (selectedRelationOperator relation E R) (7 : O)) :
    evaluateRelation relation q g (graphScalar relation.family x y) ∈
      IsLocalRing.maximalIdeal O := by
  have heq : IsLocalRing.residue O e = 1 := by
    have hh : IsLocalRing.residue O e = IsLocalRing.residue O 1 :=
      Ideal.Quotient.eq.mpr hEone
    simpa using hh
  have hunit : IsUnit e := (IsLocalRing.residue_ne_zero_iff_isUnit e).mp
    (by rw [heq]; exact one_ne_zero)
  exact projected_relation_implies_raw_relation relation hEone
    (selected_relation_eigenvalue_in_maximalIdeal relation hrelation h7max hE hR hunit hidentity)

/-- Batch form of the preceding theorem.  For a fixed archived weight residue
`kResidue` and centre `c`, it consumes every coordinate and graph identity in
the exact 210-relation table.  The manuscript writes `r=d=k-2`; hence its
branch `r` is obtained here by taking `kResidue = r+2 (mod 42)`.

`Rop relation` is the integral combined operator supplied by staged division;
in particular this statement does **not** assume that
`U_c=(T₃-c)/7` or `V=(T₂₉-2)/7` separately preserves the lattice. -/
theorem all_exact_branch_relations_imply_scalar_relations
    {E : Module.End O M} (Rop : Relation → Module.End O M)
    {v : PrimitiveEigenvector (O := O) (M := M)}
    {e q g x y : O} {kResidue c : Nat}
    (h7max : (7 : O) ∈ IsLocalRing.maximalIdeal O)
    (hE : ActsBy E v e) (hEone : e - 1 ∈ IsLocalRing.maximalIdeal O)
    (hR : ∀ relation, relation ∈ relations →
      relation.weightResidueMod42 = kResidue → relation.centre = c →
      ActsBy (Rop relation) v
        (evaluateRelation relation q g (graphScalar relation.family (e^6*x) (e^6*y))))
    (hidentities : ∀ relation, relation ∈ relations →
      relation.weightResidueMod42 = kResidue → relation.centre = c →
      MapsIntoMultiple (selectedRelationOperator relation E (Rop relation)) (7 : O)) :
    ∀ relation, relation ∈ relations →
      relation.weightResidueMod42 = kResidue → relation.centre = c →
      evaluateRelation relation q g (graphScalar relation.family x y) ∈
        IsLocalRing.maximalIdeal O := by
  intro relation hrelation hr hc
  exact exact_selected_relation_implies_scalar_relation relation hrelation h7max hE
    (hR relation hrelation hr hc) hEone (hidentities relation hrelation hr hc)

/-- Apply the two exact graph polynomials for a branch after their scalar
forms have been obtained from
`all_exact_branch_relations_imply_scalar_relations`.  The equalities
`hUformula` and `hVformula` are literal readings of the stored
`U_c-φ_{r,c}` and `V-ψ_{r,c}` polynomials. -/
theorem exact_graph_relations_imply_generator_congruences
    {a3 a29 c q g x y φrc ψrc : O}
    (relationU relationV : Relation)
    (hfamilyU : relationU.family = .graphU)
    (hfamilyV : relationV.family = .graphV)
    (hUrelation :
      evaluateRelation relationU q g (graphScalar relationU.family x y) ∈
        IsLocalRing.maximalIdeal O)
    (hVrelation :
      evaluateRelation relationV q g (graphScalar relationV.family x y) ∈
        IsLocalRing.maximalIdeal O)
    (hUformula :
      evaluateRelation relationU q g (graphScalar relationU.family x y) = x - φrc)
    (hVformula :
      evaluateRelation relationV q g (graphScalar relationV.family x y) = y - ψrc)
    (ha3 : a3 = c + 7 * x)
    (ha29 : a29 = 2 + 7 * y) :
    ValuativelyCongruent (7 : O) 2 a3 (c + 7 * φrc) ∧
      ValuativelyCongruent (7 : O) 2 a29 (2 + 7 * ψrc) := by
  simp only [hfamilyU, graphScalar] at hUrelation hUformula
  simp only [hfamilyV, graphScalar] at hVrelation hVformula
  have hx : x - φrc ∈ IsLocalRing.maximalIdeal O := by
    rw [← hUformula]
    exact hUrelation
  have hy : y - ψrc ∈ IsLocalRing.maximalIdeal O := by
    rw [← hVformula]
    exact hVrelation
  constructor
  · apply valuativelyCongruent_of_scaled_maximal hx
    rw [ha3]
    ring
  · apply valuativelyCongruent_of_scaled_maximal hy
    rw [ha29]
    ring

/-- Once the exact graph identities have selected the raw digits, their
translation into the two selected Hecke-eigenvalue congruences is immediate.
This is precisely the last step of the `p=7` argument. -/
theorem raw_digit_graph_implies_generator_congruences
    {a3 a29 c x y φrc ψrc : O}
    (ha3 : a3 = c + 7 * x)
    (ha29 : a29 = 2 + 7 * y)
    (hx : x - φrc ∈ IsLocalRing.maximalIdeal O)
    (hy : y - ψrc ∈ IsLocalRing.maximalIdeal O) :
    ValuativelyCongruent (7 : O) 2 a3 (c + 7 * φrc) ∧
      ValuativelyCongruent (7 : O) 2 a29 (2 + 7 * ψrc) := by
  constructor
  · apply valuativelyCongruent_of_scaled_maximal hx
    rw [ha3]
    ring
  · apply valuativelyCongruent_of_scaled_maximal hy
    rw [ha29]
    ring

theorem actsBy_GjNumeratorOperator (j : TangentIndex)
    {T3 T29 : Module.End O M} {v : PrimitiveEigenvector (O := O) (M := M)}
    {a3 a29 : O} (ha3 : ActsBy T3 v a3) (ha29 : ActsBy T29 v a29) :
    ActsBy (GjNumeratorOperator j T3 T29) v (Gnumerator j a3 a29) := by
  have hc (c : O) : ActsBy (c • (LinearMap.id : Module.End O M)) v c := by
    simpa using (ActsBy.id v).smul (s := c)
  exact (ha29.sub (hc 2)).sub ((ha3.mul (ha3.sub (hc (αj j)))).mul (ha3.sub (hc (βj j))))

theorem QG_integral_eigenvalues (j : TangentIndex)
    {T3 T29 Q G : Module.End O M} {v : PrimitiveEigenvector (O := O) (M := M)}
    {a3 a29 : O} (ha3 : ActsBy T3 v a3) (ha29 : ActsBy T29 v a29)
    (hQ : FjOperator j T3 = (7 : O)^2 • Q)
    (hG : GjNumeratorOperator j T3 T29 = (7 : O) • G)
    (hinj : Function.Injective (fun x : M => (7 : O) • x)) :
    ∃ q g : O, ActsBy Q v q ∧ ActsBy G v g ∧
      Fj j a3 = (7 : O)^2*q ∧ Gnumerator j a3 a29 = 7*g := by
  have hinj2 : Function.Injective (fun x : M => (7 : O)^2 • x) := by
    simpa [pow_two, mul_smul, Function.comp_def] using hinj.comp hinj
  obtain ⟨q,hq,hF⟩ := (actsBy_FjOperator j T3 v a3 ha3).of_division hQ hinj2
  obtain ⟨g,hg,hG⟩ := (actsBy_GjNumeratorOperator j ha3 ha29).of_division hG hinj
  exact ⟨q,g,hq,hg,hF,hG⟩

theorem H_relation_implies_residue_in_primeField {z : O}
    (h7 : (7 : O) ∈ IsLocalRing.maximalIdeal O) (hH : (7 : O) ∣ H z) :
    IsLocalRing.residue O z ∈ (⊥ : Subfield (IsLocalRing.ResidueField O)) := by
  have hp : Nat.Prime 7 := by decide
  let : Fact (Nat.Prime 7) := ⟨hp⟩
  have h7zero : (7 : IsLocalRing.ResidueField O) = 0 := by
    have hh : IsLocalRing.residue O (7 : O) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h7
    rwa [map_ofNat] at hh
  let : CharP (IsLocalRing.ResidueField O) 7 := (CharP.charP_iff_prime_eq_zero hp).mpr h7zero
  apply (Subfield.mem_bot_iff_pow_eq_self (IsLocalRing.ResidueField O) 7).mpr
  have hh : IsLocalRing.residue O (z^7-z) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (H_relation_implies_frobenius_fixed h7 hH)
  simpa only [map_sub, map_pow, sub_eq_zero] using hh


/-- The projected divided operator has eigenvalue e^6*x. This requires
integrality of the projected operator only. -/
theorem projected_division_actsBy
    {E T J : Module.End O M} {v : PrimitiveEigenvector (O := O) (M := M)}
    {e a c x : O} (hE : ActsBy E v e) (hT : ActsBy T v a)
    (ha : a = c+7*x)
    (hdivision : E^6*(T-c • LinearMap.id) = (7 : O) • J)
    (hinj : Function.Injective (fun v : M => (7 : O) • v)) :
    ActsBy J v (e^6*x) := by
  have hc : ActsBy (c • (LinearMap.id : Module.End O M)) v c := by
    simpa using (ActsBy.id v).smul (s := c)
  have hnum := (hE.pow 6).mul (hT.sub hc)
  have hs : e^6*(a-c) = 7*(e^6*x) := by rw [ha]; ring
  rw [hdivision, hs] at hnum
  apply hinj
  simpa only [ActsBy, LinearMap.smul_apply, smul_smul] using hnum

/-- A projected graph identity yields the raw Hecke eigenvalue congruence.
The hypotheses are the integral projected operator and the actual
E^6 (J-Phi)^3 lattice inclusion. No raw divided operator or eigenvalue for
J is assumed, and this theorem is independent of the finite relation table. -/
theorem projected_graph_identity_implies_congruence
    {E T J Phi : Module.End O M}
    {v : PrimitiveEigenvector (O := O) (M := M)} {e a c x phi : O}
    (h7 : (7 : O) ∈ IsLocalRing.maximalIdeal O)
    (hE : ActsBy E v e) (hT : ActsBy T v a) (hPhi : ActsBy Phi v phi)
    (hEone : e-1 ∈ IsLocalRing.maximalIdeal O) (ha : a=c+7*x)
    (hdivision : E^6*(T-c • LinearMap.id) = (7 : O) • J)
    (hinj : Function.Injective (fun v : M => (7 : O) • v))
    (hidentity : MapsIntoMultiple (E^6*(J-Phi)^3) (7 : O)) :
    ValuativelyCongruent (7 : O) 2 a (c+7*phi) := by
  have hJ := projected_division_actsBy hE hT ha hdivision hinj
  have hscalar := eigenvalue_dvd_of_mapsIntoMultiple
    ((hE.pow 6).mul ((hJ.sub hPhi).pow 3)) hidentity
  have hm := mem_maximalIdeal_of_dvd_by_nonunit h7 hscalar
  have heq : IsLocalRing.residue O e = 1 := by
    have hh : IsLocalRing.residue O e = IsLocalRing.residue O 1 := Ideal.Quotient.eq.mpr hEone
    simpa using hh
  have hh : IsLocalRing.residue O (e^6*(e^6*x-phi)^3) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hm
  have hz : (IsLocalRing.residue O x - IsLocalRing.residue O phi)^3 = 0 := by
    simpa [map_mul, map_pow, map_sub, heq] using hh
  have hraw : x-phi ∈ IsLocalRing.maximalIdeal O := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change IsLocalRing.residue O (x-phi) = 0
    simpa only [map_sub] using (pow_eq_zero_iff (by decide : 3 ≠ 0)).mp hz
  apply valuativelyCongruent_of_scaled_maximal hraw
  rw [ha]
  ring

end HeckeCongruences.PrimeSeven

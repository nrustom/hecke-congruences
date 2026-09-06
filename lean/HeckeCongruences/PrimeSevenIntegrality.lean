import HeckeCongruences.PrimeSeven
import HeckeCongruences.ValuationBridge

/-!
# Integral modulo-7 digits

The nine elementary Taylor expansions of the displayed F_j are checked here
and used to derive integral raw digits. These proofs do not use source
matrices, finite-degree certificates, or classification point tables.
-/

namespace HeckeCongruences.PrimeSeven
open HeckeCongruences
variable {O : Type*} [CommRing O] [IsLocalRing O]

/-- The quadratic coefficient is a unit on each of the three residual
branches, including in a ramified extension. -/
theorem Fj_double_root_data (j : TangentIndex) {c : O}
    (hc : c = 0 ∨ c = αj j ∨ c = βj j)
    (h7 : (7 : O) ∈ IsLocalRing.maximalIdeal O) :
    ∃ A B C : O, IsUnit C ∧ ∀ y : O, ∃ D : O,
      Fj j (c+y) = 7^2*A + 7*B*y + C*y^2 + y^3*D := by
  cases j <;> simp only [αj, βj] at hc
  all_goals rcases hc with rfl | rfl | rfl
  · refine ⟨0, 1, 4, isUnit_of_residue_inverse (u := 2)
      (v := (-1)) h7 (by norm_num), ?_⟩
    intro y
    refine ⟨y ^ 3 + 7*y ^ 2 + 45*y + 7, ?_⟩
    simp only [Fj, F0]
    ring
  · refine ⟨129, 1339, 5602, isUnit_of_residue_inverse (u := 4)
      (v := (-3201)) h7 (by norm_num), ?_⟩
    intro y
    refine ⟨y ^ 3 + 25*y ^ 2 + 285*y + 1717, ?_⟩
    simp only [Fj, F0]
    ring
  · refine ⟨476, 3857, 12728, isUnit_of_residue_inverse (u := 4)
      (v := (-7273)) h7 (by norm_num), ?_⟩
    intro y
    refine ⟨y ^ 3 + 31*y ^ 2 + 425*y + 3127, ?_⟩
    simp only [Fj, F0]
    ring
  · refine ⟨0, 2, 9, isUnit_of_residue_inverse (u := 4)
      (v := (-5)) h7 (by norm_num), ?_⟩
    intro y
    refine ⟨y ^ 3 + 42*y ^ 2 + 6*y, ?_⟩
    simp only [Fj, F2]
    ring
  · refine ⟨32, 542, 3753, isUnit_of_residue_inverse (u := 1)
      (v := (-536)) h7 (by norm_num), ?_⟩
    intro y
    refine ⟨y ^ 3 + 54*y ^ 2 + 486*y + 1888, ?_⟩
    simp only [Fj, F2]
    ring
  · refine ⟨3080, 21872, 62784, isUnit_of_residue_inverse (u := 1)
      (v := (-8969)) h7 (by norm_num), ?_⟩
    intro y
    refine ⟨y ^ 3 + 72*y ^ 2 + 1431*y + 13120, ?_⟩
    simp only [Fj, F2]
    ring
  · refine ⟨0, 4, 1, isUnit_of_residue_inverse (u := 1)
      (v := (0)) h7 (by norm_num), ?_⟩
    intro y
    refine ⟨y ^ 3 + 7*y ^ 2 + 47*y + 14, ?_⟩
    simp only [Fj, F4]
    ring
  · refine ⟨2, 43, 410, isUnit_of_residue_inverse (u := 2)
      (v := (-117)) h7 (by norm_num), ?_⟩
    intro y
    refine ⟨y ^ 3 + 13*y ^ 2 + 97*y + 292, ?_⟩
    simp only [Fj, F4]
    ring
  · refine ⟨3372, 19168, 44965, isUnit_of_residue_inverse (u := 2)
      (v := (-12847)) h7 (by norm_num), ?_⟩
    intro y
    refine ⟨y ^ 3 + 43*y ^ 2 + 797*y + 7982, ?_⟩
    simp only [Fj, F4]
    ring

/-- The squared cubic factorizations of F_j modulo 7. -/
theorem Fj_cubic_remainder (j : TangentIndex) (a : O) :
    ∃ D : O, Fj j a - (a*(a-αj j)*(a-βj j))^2 = 7*D := by
  cases j
  · refine ⟨3*a ^ 5 - 4*a ^ 4 + 25*a ^ 3 - 20*a ^ 2 + a, ?_⟩
    simp only [Fj, F0, αj, βj]
    ring
  · refine ⟨8*a ^ 5 - 9*a ^ 4 + 20*a ^ 3 - 13*a ^ 2 + 2*a, ?_⟩
    simp only [Fj, F2, αj, βj]
    ring
  · refine ⟨3*a ^ 5 - 2*a ^ 4 + 14*a ^ 3 - 5*a ^ 2 + 4*a, ?_⟩
    simp only [Fj, F4, αj, βj]
    ring

theorem Fj_residual_centre (j : TangentIndex) {a : O}
    (h7 : (7 : O) ∈ IsLocalRing.maximalIdeal O) (hF : (7 : O)^2 ∣ Fj j a) :
    ∃ c : O, (c = 0 ∨ c = αj j ∨ c = βj j) ∧
      a-c ∈ IsLocalRing.maximalIdeal O := by
  have h7dvd : (7 : O) ∣ (7 : O)^2 := ⟨7, by ring⟩
  have hFm := mem_maximalIdeal_of_dvd_by_nonunit h7 (h7dvd.trans hF)
  obtain ⟨D,hD⟩ := Fj_cubic_remainder j a
  have hprodSq : (a*(a-αj j)*(a-βj j))^2 ∈ IsLocalRing.maximalIdeal O := by
    have he : (a*(a-αj j)*(a-βj j))^2 = Fj j a - 7*D := by linear_combination -hD
    rw [he]
    exact (IsLocalRing.maximalIdeal O).sub_mem hFm
      ((IsLocalRing.maximalIdeal O).mul_mem_right D h7)
  have hprod := mem_maximalIdeal_of_pow_mem (by decide : 0 < 2) hprodSq
  rcases factor_mem_maximalIdeal_of_product_mem hprod with hleft | hright
  · rcases factor_mem_maximalIdeal_of_product_mem hleft with hzero | halpha
    · exact ⟨0, Or.inl rfl, by simpa using hzero⟩
    · exact ⟨αj j, Or.inr (Or.inl rfl), halpha⟩
  · exact ⟨βj j, Or.inr (Or.inr rfl), hright⟩

variable [IsDomain O] [ValuationRing O]

/-- The Taylor argument derives a3=c+7x with x integral; it is not an input. -/
theorem Fj_integral_digit (j : TangentIndex) {a : O}
    (h7 : (7 : O) ∈ IsLocalRing.maximalIdeal O) (hF : (7 : O)^2 ∣ Fj j a) :
    ∃ c x : O, (c = 0 ∨ c = αj j ∨ c = βj j) ∧ a = c+7*x := by
  obtain ⟨c,hc,hac⟩ := Fj_residual_centre j h7 hF
  obtain ⟨A,B,C,hC,hTaylor⟩ := Fj_double_root_data j hc h7
  obtain ⟨D,hD⟩ := hTaylor (a-c)
  have hd : (7 : O) ∣ a-c := dvd_of_double_root_expansion hac hC
    (by rw [← hD]; simpa using hF)
  obtain ⟨x,hx⟩ := hd
  exact ⟨c,x,hc,by linear_combination hx⟩

/-- Both integral raw digits follow from the two divided numerator identities. -/
theorem QG_integral_digits (j : TangentIndex) {a3 a29 q g : O}
    (h7 : (7 : O) ∈ IsLocalRing.maximalIdeal O)
    (hF : Fj j a3 = (7 : O)^2*q)
    (hG : Gnumerator j a3 a29 = (7 : O)*g) :
    ∃ c x y : O, (c = 0 ∨ c = αj j ∨ c = βj j) ∧
      a3 = c+7*x ∧ a29 = 2+7*y := by
  obtain ⟨c,x,hc,hx⟩ := Fj_integral_digit j h7 ⟨q,hF⟩
  have hd : (7 : O) ∣ a3-c := ⟨x,by linear_combination hx⟩
  have hcubic : (7 : O) ∣ a3*(a3-αj j)*(a3-βj j) := by
    rcases hc with rfl | rfl | rfl
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by simpa using hd) _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _
    · exact dvd_mul_of_dvd_right hd _
  have hg : (7 : O) ∣ a29-2-a3*(a3-αj j)*(a3-βj j) := ⟨g,hG⟩
  have hy : (7 : O) ∣ a29-2 := by
    convert dvd_add hg hcubic using 1 <;> ring
  obtain ⟨y,hy⟩ := hy
  exact ⟨c,x,y,hc,hx,by linear_combination hy⟩

/-- Starting with the original T3 and T29 eigenvector equations, integral
Q and G imply integral raw digits. Their eigenvalues are derived internally. -/
theorem integral_operators_imply_raw_digits
    {M : Type*} [AddCommGroup M] [Module O M]
    (j : TangentIndex) {T3 T29 Q G : Module.End O M}
    {v : PrimitiveEigenvector (O := O) (M := M)} {a3 a29 : O}
    (h7 : (7 : O) ∈ IsLocalRing.maximalIdeal O)
    (ha3 : ActsBy T3 v a3) (ha29 : ActsBy T29 v a29)
    (hQ : FjOperator j T3 = (7 : O)^2 • Q)
    (hG : GjNumeratorOperator j T3 T29 = (7 : O) • G)
    (hinj : Function.Injective (fun x : M => (7 : O) • x)) :
    ∃ c x y : O, (c = 0 ∨ c = αj j ∨ c = βj j) ∧
      a3 = c+7*x ∧ a29 = 2+7*y := by
  obtain ⟨q,g,_,_,hF,hG⟩ := QG_integral_eigenvalues j ha3 ha29 hQ hG hinj
  exact QG_integral_digits j h7 hF hG

end HeckeCongruences.PrimeSeven

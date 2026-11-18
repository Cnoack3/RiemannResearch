import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Mixed-norm Gabriel interpolation for finite analytic families

The endpoint powers are the orders 4/3 and 2 in Chourasiya and Simonič,
https://arxiv.org/html/2507.15184v2, equations (19)--(21). The proof
interpolates the dual test vector analytically and applies Hadamard's
three-lines theorem to the resulting scalar holomorphic function.
-/
noncomputable section
open Set Complex Complex.HadamardThreeLines
open scoped BigOperators
namespace RiemannResearch.Analysis.InghamInterpolation

private def dualWeight (v : ℝ) (z : ℂ) : ℂ :=
  if v = 0 then 0 else Complex.exp ((Real.log v : ℂ) * ((1+z)/4))

private theorem dualWeight_diff (v : ℝ) : Differentiable ℂ (dualWeight v) := by
  by_cases h : v = 0
  · unfold dualWeight
    simp only [if_pos h]
    exact differentiable_const 0
  · unfold dualWeight
    simp only [if_neg h]
    fun_prop

private theorem dualWeight_norm {v : ℝ} (hv : 0 ≤ v) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖dualWeight v z‖ = v ^ ((1+z.re)/4) := by
  by_cases h : v = 0
  · subst v
    simp [dualWeight, Real.zero_rpow (by positivity : (1+z.re)/4 ≠ 0)]
  · rw [dualWeight, if_neg h, Complex.norm_exp, Real.rpow_def_of_pos (lt_of_le_of_ne hv (Ne.symm h))]
    congr 1
    simp [div_eq_mul_inv, Complex.mul_re]

private theorem dualWeight_real {v θ : ℝ} (hv : 0 ≤ v) (hθ : 0 ≤ θ) :
    dualWeight v (θ : ℂ) = (v ^ ((1+θ)/4) : ℝ) := by
  by_cases h : v = 0
  · subst v
    simp [dualWeight, Real.zero_rpow (by positivity : (1+θ)/4 ≠ 0)]
  · rw [dualWeight, if_neg h, Real.rpow_def_of_pos (lt_of_le_of_ne hv (Ne.symm h)), Complex.ofReal_exp]
    push_cast
    rfl

private theorem finite_edge_test {ι : Type*} (s : Finset ι) (f c : ι → ℂ) (v : ι → ℝ)
    (hc : ∀ j ∈ s, ‖c j‖ ≤ 1) (hv : ∀ j ∈ s, 0 ≤ v j) (hsum : ∑ j ∈ s, v j = 1)
    {p q : ℝ} (hpq : p.HolderConjugate q) {z : ℂ} (hz : 0 ≤ z.re)
    (hpow : ((1+z.re)/4)*q = 1) :
    ‖∑ j ∈ s, f j * c j * dualWeight (v j) z‖ ≤
      (∑ j ∈ s, ‖f j‖ ^ p) ^ (1/p) := by
  have hn (j) (hj : j ∈ s) :
      ‖f j * c j * dualWeight (v j) z‖ ≤ ‖f j‖ * ‖dualWeight (v j) z‖ := by
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right (norm_nonneg _) (hc j hj)) (norm_nonneg _)
  have hsum' : ∑ j ∈ s, ‖dualWeight (v j) z‖ ^ q = 1 := by
    convert hsum using 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [dualWeight_norm (hv j hj) hz, ← Real.rpow_mul (hv j hj), hpow, Real.rpow_one]
  calc _ ≤ ∑ j ∈ s, ‖f j * c j * dualWeight (v j) z‖ := norm_sum_le _ _
       _ ≤ ∑ j ∈ s, ‖f j‖ * ‖dualWeight (v j) z‖ := Finset.sum_le_sum hn
       _ ≤ _ := (Real.inner_le_Lp_mul_Lq_of_nonneg s (f := fun j => ‖f j‖)
          (g := fun j => ‖dualWeight (v j) z‖) hpq
          (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)).trans_eq (by rw [hsum', Real.one_rpow, mul_one])

/-- Finite dual-family form of Gabriel's mixed-norm interpolation theorem. -/
theorem finite_gabriel_dual {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hhol : ∀ j ∈ s, DiffContOnCl ℂ (f j) (verticalStrip 0 1))
    (hbd : ∀ j ∈ s, ∃ B : ℝ, ∀ z ∈ verticalClosedStrip 0 1, ‖f j z‖ ≤ B)
    {A B : ℝ}
    (hL : ∀ z : ℂ, z.re = 0 → (∑ j ∈ s, ‖f j z‖^(4/3:ℝ))^(3/4:ℝ) ≤ A)
    (hR : ∀ z : ℂ, z.re = 1 → (∑ j ∈ s, ‖f j z‖^(2:ℝ))^(1/2:ℝ) ≤ B)
    (c : ι → ℂ) (v : ι → ℝ) (hc : ∀ j ∈ s, ‖c j‖ ≤ 1)
    (hv : ∀ j ∈ s, 0 ≤ v j) (hsum : ∑ j ∈ s, v j = 1)
    {θ : ℝ} (hθ : θ ∈ Icc (0:ℝ) 1) :
    ‖∑ j ∈ s, f j (θ:ℂ) * c j * ((v j ^ ((1+θ)/4) : ℝ) : ℂ)‖ ≤
      A^(1-θ) * B^θ := by
  classical
  let F (z : ℂ) := ∑ j ∈ s, f j z * c j * dualWeight (v j) z
  have hF : DiffContOnCl ℂ F (verticalStrip 0 1) := by
    constructor
    · exact DifferentiableOn.fun_sum (fun j hj =>
        (((hhol j hj).differentiableOn.mul_const _).mul (dualWeight_diff _).differentiableOn))
    · exact continuousOn_finsetSum _ (fun j hj =>
        ((hhol j hj).continuousOn.mul continuousOn_const).mul
          (dualWeight_diff _).continuous.continuousOn)
  have hv1 (j) (hj : j ∈ s) : v j ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j hj => hv j hj) hj
  choose bound hbound using fun j : {j // j ∈ s} => hbd j.1 j.2
  let C (j : ι) := if h : j ∈ s then bound ⟨j,h⟩ else 0
  have hB : BddAbove ((norm ∘ F) '' verticalClosedStrip 0 1) := by
    refine ⟨∑ j ∈ s, C j, ?_⟩
    rintro _ ⟨z,hz,rfl⟩
    have hz0 : 0 ≤ z.re := hz.1
    change ‖∑ j ∈ s, _‖ ≤ _
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro j hj
    rw [norm_mul, norm_mul, dualWeight_norm (hv j hj) hz0]
    have hw := Real.rpow_le_one (hv j hj) (hv1 j hj) (show 0 ≤ (1+z.re)/4 by positivity)
    apply le_trans (mul_le_of_le_one_right (by positivity) hw)
    apply le_trans (mul_le_of_le_one_right (norm_nonneg _) (hc j hj))
    simpa [C,hj] using hbound ⟨j,hj⟩ z hz
  have hleft (z : ℂ) (hz : z ∈ re ⁻¹' ({(0:ℝ)} : Set ℝ)) : ‖F z‖ ≤ A := by
    have hzr : z.re = 0 := hz
    have h := finite_edge_test s (fun j => f j z) c v hc hv hsum
      (p := 4/3) (q := 4) (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
      (z := z) (by linarith) (by rw [hzr]; norm_num)
    exact (by convert h using 1; norm_num : ‖F z‖ ≤ _).trans (hL z hzr)
  have hright (z : ℂ) (hz : z ∈ re ⁻¹' ({(1:ℝ)} : Set ℝ)) : ‖F z‖ ≤ B := by
    have hzr : z.re = 1 := hz
    exact (finite_edge_test s (fun j => f j z) c v hc hv hsum
      (p := 2) (q := 2) (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
      (z := z) (by linarith) (by rw [hzr]; norm_num)).trans (hR z hzr)
  have hd := norm_le_interp_of_mem_verticalClosedStrip' (f := F) (by norm_num : (0:ℝ) < 1)
    (z := (θ:ℂ)) (show (θ:ℂ) ∈ verticalClosedStrip 0 1 from hθ) hF hB hleft hright
  have hvreal : F (θ:ℂ) = _ := Finset.sum_congr rfl (fun j hj =>
    congrArg (fun w => f j (θ:ℂ)* c j*w) (dualWeight_real (hv j hj) hθ.1))
  rw [hvreal] at hd
  simpa using hd



private def normingPhase (z : ℂ) : ℂ := (starRingEnd ℂ z) / (‖z‖ : ℂ)

private theorem normingPhase_le (z : ℂ) : ‖normingPhase z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [normingPhase,hz]
  · simp [normingPhase, hz]

private theorem mul_normingPhase (z : ℂ) : z * normingPhase z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [normingPhase, ← mul_div_assoc,
      div_eq_iff (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)), Complex.mul_conj]
    exact_mod_cast (Complex.sq_norm z).symm.trans (by ring)

/-- Gabriel's varying-exponent inequality for every finite family of bounded
holomorphic strip functions at left exponent 4/3 and right exponent 2. -/
theorem finite_gabriel_interpolation {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hhol : ∀ j ∈ s, DiffContOnCl ℂ (f j) (verticalStrip 0 1))
    (hbd : ∀ j ∈ s, ∃ B : ℝ, ∀ z ∈ verticalClosedStrip 0 1, ‖f j z‖ ≤ B)
    {A B : ℝ}
    (hL : ∀ z : ℂ, z.re = 0 → (∑ j ∈ s, ‖f j z‖^(4/3:ℝ))^(3/4:ℝ) ≤ A)
    (hR : ∀ z : ℂ, z.re = 1 → (∑ j ∈ s, ‖f j z‖^(2:ℝ))^(1/2:ℝ) ≤ B)
    {θ : ℝ} (hθ : θ ∈ Icc (0:ℝ) 1) :
    (∑ j ∈ s, ‖f j (θ:ℂ)‖ ^ (4/(3-θ)))^((3-θ)/4) ≤ A^(1-θ)*B^θ := by
  let d (j : ι) := ‖f j (θ:ℂ)‖
  let p := 4/(3-θ)
  let r := (1+θ)/4
  let S := ∑ j ∈ s, d j ^ p
  have hden : 0 < 3-θ := by linarith [hθ.2]
  have hθ' : 0 < (3-θ)/4 := by positivity
  have hr : 0 < r := by dsimp [r]; linarith [hθ.1]
  have hd0 (j : ι) : 0 ≤ d j := norm_nonneg _
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (hd0 j) _)
  have hA : 0 ≤ A := (Real.rpow_nonneg (Finset.sum_nonneg (fun j _ =>
    Real.rpow_nonneg (norm_nonneg _) _)) _).trans (hL 0 (by simp))
  have hB : 0 ≤ B := (Real.rpow_nonneg (Finset.sum_nonneg (fun j _ =>
    Real.rpow_nonneg (norm_nonneg _) _)) _).trans (hR 1 (by simp))
  change S ^ ((3-θ)/4) ≤ _
  by_cases hzero : S = 0
  · rw [hzero, Real.zero_rpow hθ'.ne']
    positivity
  have hS : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hzero)
  let v (j : ι) := d j^p/S
  have hv (j : ι) : 0 ≤ v j := div_nonneg (Real.rpow_nonneg (hd0 _) _) hS.le
  have hsum : ∑ j ∈ s, v j = 1 := by
    simp only [v, ← Finset.sum_div]
    exact div_self hzero
  have hp : 1 + p*r = p := by
    dsimp [p,r]; field_simp [hden.ne']; ring
  have term (j : ι) : d j*(v j)^r = d j^p / S^r := by
    dsimp only [v]
    rw [Real.div_rpow (Real.rpow_nonneg (hd0 j) _) hS.le, ← mul_div_assoc,
      ← Real.rpow_mul (hd0 j)]
    congr 1
    calc d j * d j^(p*r) = d j^((1:ℝ)+p*r) := by rw [Real.rpow_add' (hd0 j)
            (by dsimp [p] at *; positivity : (1:ℝ) + p*r ≠ 0), Real.rpow_one]
         _ = d j^p := by rw [hp]
  have hnorm : ∑ j ∈ s, d j*(v j)^r = S^((3-θ)/4) := by
    simp_rw [term]
    rw [← Finset.sum_div]
    change S / S^r = _
    have hrr : (3-θ)/4 = 1-r := by dsimp [r]; ring
    rw [hrr, Real.rpow_sub hS, Real.rpow_one]
  have hb := finite_gabriel_dual s f hhol hbd hL hR (fun j => normingPhase (f j (θ:ℂ))) v
    (fun j _ => normingPhase_le _) (fun j _ => hv _) hsum hθ
  have hcomplex : ∑ j ∈ s, f j (θ:ℂ) * normingPhase (f j (θ:ℂ))
      * ((v j ^ ((1+θ)/4) : ℝ) : ℂ) = (S ^ ((3-θ)/4) : ℝ) := by
    rw [← hnorm]
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_normingPhase]
  rw [hcomplex, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hS0 _)] at hb
  exact hb

end RiemannResearch.Analysis.InghamInterpolation

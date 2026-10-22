import RiemannResearch.RH.PrimeLogPeriodRigidity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Continuity and linearity of positive-domain scaling profiles

Source: user-provided two-seed rigidity argument. These positive-domain
corollaries reuse the project's existing prime-log period theorem.
-/

namespace RiemannResearch.Analysis

/-- A square-increment estimate gives continuity on the positive half-line.
The factor involving the larger argument is bounded on each neighborhood. -/
theorem continuousOn_Ioi_of_sq_increment_le
    (H : ℝ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hinc : ∀ x y : ℝ, 0 ≤ x → x ≤ y →
      (H y - H x) ^ 2 ≤ C * y * (y - x)) :
    ContinuousOn H (Set.Ioi 0) := by
  intro x hx
  change 0 < x at hx
  apply Metric.continuousWithinAt_iff.2
  intro ε hε
  let M : ℝ := C * (x + 1) + 1
  have hA : 0 ≤ C * (x + 1) := mul_nonneg hC (by linarith)
  have hM : 0 < M := by dsimp [M]; linarith
  refine ⟨min 1 (ε ^ 2 / M),
    lt_min (by norm_num) (div_pos (pow_pos hε 2) hM), ?_⟩
  intro y hy hyδ
  change 0 < y at hy
  rw [Real.dist_eq] at hyδ ⊢
  have hd1 : |y - x| < 1 := lt_of_lt_of_le hyδ (min_le_left _ _)
  have hdε : |y - x| < ε ^ 2 / M :=
    lt_of_lt_of_le hyδ (min_le_right _ _)
  have hnear : y ≤ x + 1 := by
    have h := le_abs_self (y - x)
    linarith
  have hsq : (H y - H x) ^ 2 ≤ C * (x + 1) * |y - x| := by
    rcases le_total x y with hxy | hyx
    · rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
      exact (hinc x y (le_of_lt hx) hxy).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnear hC)
          (sub_nonneg.mpr hxy))
    · have hb : (H y - H x) ^ 2 ≤ C * x * (x - y) := by
        have h := hinc y x (le_of_lt hy) hyx
        nlinarith only [h]
      rw [abs_of_nonpos (sub_nonpos.mpr hyx), neg_sub]
      exact hb.trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith : x ≤ x + 1) hC)
          (sub_nonneg.mpr hyx))
  have hAM : C * (x + 1) * |y - x| ≤ M * |y - x| :=
    mul_le_mul_of_nonneg_right (by dsimp [M]; linarith) (abs_nonneg _)
  have hprod : M * |y - x| < ε ^ 2 := by
    simpa only [mul_comm] using (lt_div_iff₀ hM).mp hdε
  exact abs_lt_of_sq_lt_sq (hsq.trans_lt (hAM.trans_lt hprod)) (le_of_lt hε)

/-- Continuous invariance under multiplication by both 2 and 3 forces
constancy throughout the positive half-line. -/
theorem continuousOn_two_three_scaling_const
    (F : ℝ → ℝ) (hF : ContinuousOn F (Set.Ioi 0))
    (h2 : ∀ x, 0 < x → F (2 * x) = F x)
    (h3 : ∀ x, 0 < x → F (3 * x) = F x)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : F x = F y := by
  let G : ℝ → ℝ := fun t => F (Real.exp t)
  have hG : Continuous G :=
    hF.comp_continuous Real.continuous_exp (fun t => Real.exp_pos t)
  have hp2 : Function.Periodic G (Real.log 2) := by
    intro t
    dsimp [G]
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simpa only [mul_comm] using h2 (Real.exp t) (Real.exp_pos t)
  have hp3 : Function.Periodic G (Real.log 3) := by
    intro t
    dsimp [G]
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    simpa only [mul_comm] using h3 (Real.exp t) (Real.exp_pos t)
  have hc := RiemannResearch.RH.PrimePhaseCRT.continuous_twoSeed_log_periods_constant
    G hG hp2 hp3
  have h := (hc (Real.log x)).trans (hc (Real.log y)).symm
  simpa only [G, Real.exp_log hx, Real.exp_log hy] using h

/-- A continuous function homogeneous for the two integer factors 2 and 3
is genuinely linear on the positive half-line. -/
theorem continuousOn_two_three_homogeneous
    (H : ℝ → ℝ) (hH : ContinuousOn H (Set.Ioi 0))
    (h2 : ∀ x, 0 < x → H (2 * x) = 2 * H x)
    (h3 : ∀ x, 0 < x → H (3 * x) = 3 * H x)
    {x : ℝ} (hx : 0 < x) : H x = x * H 1 := by
  let F : ℝ → ℝ := fun z => H z / z
  have hF : ContinuousOn F (Set.Ioi 0) :=
    hH.div continuousOn_id (fun z hz => ne_of_gt hz)
  have hf2 : ∀ z, 0 < z → F (2 * z) = F z := by
    intro z hz
    dsimp [F]
    rw [h2 z hz]
    exact mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)
  have hf3 : ∀ z, 0 < z → F (3 * z) = F z := by
    intro z hz
    dsimp [F]
    rw [h3 z hz]
    exact mul_div_mul_left _ _ (by norm_num : (3 : ℝ) ≠ 0)
  have h := continuousOn_two_three_scaling_const F hF hf2 hf3 hx
    (by norm_num : (0 : ℝ) < 1)
  dsimp [F] at h
  rw [div_one] at h
  have he := (div_eq_iff (ne_of_gt hx)).mp h
  simpa only [mul_comm] using he

end RiemannResearch.Analysis

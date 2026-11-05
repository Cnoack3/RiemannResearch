/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.VinogradovKorobovProfile

/-!
# Secondary Vinogradov–Korobov scale

Lee–Leong's variable coefficient (arXiv:2208.06141v5, Theorem 1.1) motivates
the secondary scale below. We use its monotonicity for uniform cutoff bounds.
-/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.Analysis

/-- The first secondary scale in the explicit VK exponent. -/
def vkSecondProfile (x : ℝ) : ℝ := vkProfile x / Real.log (Real.log x)

private theorem vkSecondProfile_log {x : ℝ} (hx : 0 < Real.log x)
    (hL : 0 < Real.log (Real.log x)) :
    Real.log (vkSecondProfile x) =
      (3 / 5 : ℝ) * Real.log (Real.log x) - (6 / 5 : ℝ) * Real.log (Real.log (Real.log x)) := by
  have hV : 0 < vkProfile x :=
    div_pos (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hL _)
  rw [vkSecondProfile, Real.log_div hV.ne' hL.ne', vkProfile,
    Real.log_div (Real.rpow_pos_of_pos hx _).ne' (Real.rpow_pos_of_pos hL _).ne',
    Real.log_rpow hx, Real.log_rpow hL]
  ring

/-- The secondary scale is increasing once the double logarithm exceeds two. -/
theorem vkSecondProfile_eventually_mono :
    ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ≤ y → vkSecondProfile x ≤ vkSecondProfile y := by
  have htop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    htop.eventually (eventually_ge_atTop (2 : ℝ))] with x hx ht hlarge y hxy
  let u := Real.log (Real.log x)
  let v := Real.log (Real.log y)
  change 2 ≤ u at hlarge
  have hu : 0 < u := by linarith
  have hxy' := Real.log_le_log hx hxy
  have ht' := ht.trans_le hxy'
  have huv : u ≤ v := Real.log_le_log ht hxy'
  have hv := hu.trans_le huv
  have hdiff : 2 * (Real.log v - Real.log u) ≤ v - u := by
    have h := Real.log_le_sub_one_of_pos (div_pos hv hu)
    rw [Real.log_div hv.ne' hu.ne'] at h
    have hlog := Real.log_le_log hu huv
    have hmul := mul_le_mul_of_nonneg_right h hu.le
    have he : (v / u - 1) * u = v - u := by rw [sub_mul, div_mul_cancel₀ _ hu.ne', one_mul]
    rw [he] at hmul
    linarith only [hmul, mul_le_mul_of_nonneg_left hlarge (sub_nonneg.mpr hlog)]
  have hΨ (z : ℝ) (htz : 0 < Real.log z) (hLz : 0 < Real.log (Real.log z)) :
      0 < vkSecondProfile z :=
    div_pos (div_pos (Real.rpow_pos_of_pos htz _) (Real.rpow_pos_of_pos hLz _)) hLz
  apply (Real.log_le_log_iff (hΨ x ht hu) (hΨ y ht' hv)).mp
  rw [vkSecondProfile_log ht hu, vkSecondProfile_log ht' hv]
  change (3 / 5 : ℝ) * u - (6 / 5 : ℝ) * Real.log u ≤
    (3 / 5 : ℝ) * v - (6 / 5 : ℝ) * Real.log v
  linarith only [hdiff]

/-- Every positive multiple of the secondary scale absorbs the square-root correction. -/
theorem sqrt_vk_le_mul_secondProfile (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, Real.sqrt (vkProfile x) ≤ δ * vkSecondProfile x := by
  have htop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [vkProfile_dominates_logLog_sq (δ ^ 2) (sq_pos_of_pos hδ),
    vkProfile_tendsto_atTop.eventually (eventually_ge_atTop (0 : ℝ)),
    htop.eventually (eventually_gt_atTop (0 : ℝ))] with x hdom hV hlog
  change 0 < Real.log (Real.log x) at hlog
  have hL : Real.log (Real.log x) ≤ δ * Real.sqrt (vkProfile x) := by
    refine le_of_sq_le_sq ?_ (mul_nonneg hδ.le (Real.sqrt_nonneg _))
    simpa only [mul_pow, Real.sq_sqrt hV] using hdom
  rw [vkSecondProfile, ← mul_div_assoc]
  apply (le_div_iff₀ hlog).mpr
  calc
    _ ≤ Real.sqrt (vkProfile x) * (δ * Real.sqrt (vkProfile x)) :=
      mul_le_mul_of_nonneg_left hL (Real.sqrt_nonneg _)
    _ = δ * Real.sqrt (vkProfile x) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt hV]


/-- Every positive multiple of the profile eventually dominates the fourth power
of the double logarithm. -/
theorem vkProfile_dominates_logLog_fourth (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, Real.log (Real.log x) ^ 4 ≤ δ * vkProfile x := by
  have hr : Tendsto (fun t : ℝ => Real.log t / t ^ (1 / 10 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/10)).tendsto_div_nhds_zero
  have hp : Tendsto (fun x : ℝ =>
      (Real.log (Real.log x) / (Real.log x) ^ (1 / 10 : ℝ)) ^ 4) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (hr.pow 4).comp Real.tendsto_log_atTop
  filter_upwards [(tendsto_order.1 hp).2 δ hδ,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.exp 1))] with x h hx
  have hx0 : 0 < Real.log x := (Real.exp_pos 1).trans_le hx
  have hL : 0 < Real.log (Real.log x) := by linarith [(Real.le_log_iff_exp_le hx0).mpr hx]
  rw [div_pow] at h
  have hl := (div_lt_iff₀ (pow_pos (Real.rpow_pos_of_pos hx0 (1 / 10 : ℝ)) 4)).mp h
  have hid : ((Real.log x) ^ (1/10 : ℝ)) ^ 4 = (Real.log x) ^ (2/5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  rw [hid] at hl
  apply hl.le.trans
  apply mul_le_mul_of_nonneg_left _ hδ.le
  unfold vkProfile
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hL _)).mpr
  calc
    _ ≤ (Real.log x) ^ (2/5 : ℝ) * (Real.log x) ^ (1/5 : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hL.le
        (le_trans (Real.log_le_sub_one_of_pos hx0) (by linarith)) (by norm_num))
        (Real.rpow_nonneg hx0.le _)
    _ = _ := by rw [← Real.rpow_add hx0]; norm_num

end RiemannResearch.Analysis

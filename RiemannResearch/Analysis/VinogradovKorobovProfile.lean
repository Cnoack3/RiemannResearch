/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The logarithmic profile in Walfisz's estimate for the Mertens function

Gerhold, *Acta Arithmetica* 142 (2010), equation (2), records the arithmetic
estimate. Here only the elementary real-variable properties of its exponent
are proved. The positive real domain needed for the power laws is explicit.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis

/-- The Vinogradov–Korobov profile. Only its values for large x are used. -/
def vkProfile (x : ℝ) : ℝ :=
  (Real.log x) ^ (3 / 5 : ℝ) / (Real.log (Real.log x)) ^ (1 / 5 : ℝ)

private def vkLogScale (t : ℝ) : ℝ :=
  t ^ (3 / 5 : ℝ) / (Real.log t) ^ (1 / 5 : ℝ)

private theorem vkLogScale_factor {t : ℝ} (ht : Real.exp 1 ≤ t) :
    vkLogScale t = t ^ (2 / 5 : ℝ) * (t / Real.log t) ^ (1 / 5 : ℝ) := by
  have ht0 : 0 < t := (Real.exp_pos 1).trans_le ht
  have hL := (Real.le_log_iff_exp_le ht0).mpr ht
  have hL0 : 0 ≤ Real.log t := by linarith
  rw [Real.div_rpow ht0.le hL0, ← mul_div_assoc, ← Real.rpow_add ht0]
  norm_num [vkLogScale]

private theorem vkLogScale_mono {t T : ℝ} (ht : Real.exp 1 ≤ t) (h : t ≤ T) :
    vkLogScale t ≤ vkLogScale T := by
  have ht0 : 0 < t := (Real.exp_pos 1).trans_le ht
  have hT0 : 0 < T := ht0.trans_le h
  have htL := (Real.le_log_iff_exp_le ht0).mpr ht
  have htL0 : 0 < Real.log t := by linarith
  have hTL0 : 0 < Real.log T := htL0.trans_le (Real.log_le_log ht0 h)
  have hanti := Real.log_div_self_antitoneOn ht (ht.trans h) h
  have hcross := (div_le_div_iff₀ hT0 ht0).mp hanti
  have hdiv : t / Real.log t ≤ T / Real.log T :=
    (div_le_div_iff₀ htL0 hTL0).mpr (by linarith only [hcross])
  rw [vkLogScale_factor ht, vkLogScale_factor (ht.trans h)]
  exact mul_le_mul (Real.rpow_le_rpow ht0.le h (by norm_num))
    (Real.rpow_le_rpow (div_nonneg ht0.le htL0.le) hdiv (by norm_num))
    (Real.rpow_nonneg (div_nonneg ht0.le htL0.le) _)
    (Real.rpow_nonneg hT0.le _)

private theorem vkLogScale_div {t : ℝ} (ht : 0 < t) :
    vkLogScale t / t = t ^ (-(2 / 5 : ℝ)) / (Real.log t) ^ (1 / 5 : ℝ) := by
  rw [show -(2 / 5 : ℝ) = (3 / 5 : ℝ) - 1 by norm_num,
    Real.rpow_sub ht, Real.rpow_one]
  unfold vkLogScale
  ring

private theorem vkLogScale_div_antitone {t T : ℝ} (ht : Real.exp 1 ≤ t) (h : t ≤ T) :
    vkLogScale T / T ≤ vkLogScale t / t := by
  have ht0 : 0 < t := (Real.exp_pos 1).trans_le ht
  have hT0 : 0 < T := ht0.trans_le h
  have htL := (Real.le_log_iff_exp_le ht0).mpr ht
  have htL0 : 0 < Real.log t := by linarith
  have hL := Real.log_le_log ht0 h
  have hTL0 : 0 < Real.log T := htL0.trans_le hL
  rw [vkLogScale_div hT0, vkLogScale_div ht0]
  apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hTL0 _) (Real.rpow_pos_of_pos htL0 _)).mpr
  exact mul_le_mul (Real.rpow_le_rpow_of_nonpos ht0 h (by norm_num))
    (Real.rpow_le_rpow htL0.le hL (by norm_num))
    (Real.rpow_nonneg htL0.le _) (Real.rpow_nonneg ht0.le _)

private theorem vkLogScale_lower {t : ℝ} (ht : Real.exp 1 ≤ t) :
    t ^ (2 / 5 : ℝ) ≤ vkLogScale t := by
  rw [vkLogScale_factor ht]
  have ht0 : 0 < t := (Real.exp_pos 1).trans_le ht
  have hlog := (Real.le_log_iff_exp_le ht0).mpr ht
  have htL0 : 0 < Real.log t := by linarith
  have hratio : 1 ≤ t / Real.log t :=
    (le_div_iff₀ htL0).mpr (by linarith [Real.log_le_sub_one_of_pos ht0])
  have hm := mul_le_mul_of_nonneg_left
    (Real.one_le_rpow hratio (by norm_num : (0 : ℝ) ≤ 1/5))
    (Real.rpow_nonneg ht0.le (2/5 : ℝ))
  simpa only [mul_one] using hm

theorem vkProfile_tendsto_atTop : Tendsto vkProfile atTop atTop := by
  have hp : Tendsto (fun t : ℝ => t ^ (2 / 5 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [tendsto_atTop.mp (hp.comp Real.tendsto_log_atTop) B,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.exp 1))] with x hB hx
  change B ≤ (Real.log x) ^ (2 / 5 : ℝ) at hB
  exact hB.trans (vkLogScale_lower hx)

theorem vkProfile_eventually_mono :
    ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ≤ y → vkProfile x ≤ vkProfile y := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.exp 1))] with x hx hx6 y hxy
  exact vkLogScale_mono hx6 (Real.log_le_log hx hxy)

/-- Uniform in all later y, the increment in the profile is an arbitrarily
small multiple of the increment in log x. -/
theorem vkProfile_eventual_log_increment (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ≤ y →
      vkProfile y - vkProfile x ≤ δ * (Real.log y - Real.log x) := by
  have hp : Tendsto (fun t : ℝ => t ^ (-(2 / 5 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hs := (tendsto_order.1 (hp.comp Real.tendsto_log_atTop)).2 δ hδ
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.exp 1)), hs]
    with x hx hx6 hδx y hxy
  change (Real.log x) ^ (-(2 / 5 : ℝ)) < δ at hδx
  have ht0 : 0 < Real.log x := (Real.exp_pos 1).trans_le hx6
  have htT := Real.log_le_log hx hxy
  have hT0 : 0 < Real.log y := ht0.trans_le htT
  have hfrac := (div_le_iff₀ hT0).mp (vkLogScale_div_antitone hx6 htT)
  have hself := div_mul_cancel₀ (vkLogScale (Real.log x)) ht0.ne'
  have hsmall : vkLogScale (Real.log x) / Real.log x ≤ δ := by
    rw [vkLogScale_div ht0]
    exact (div_le_self (Real.rpow_nonneg ht0.le _)
      (Real.one_le_rpow ((Real.le_log_iff_exp_le ht0).mpr hx6) (by norm_num))).trans hδx.le
  calc
    _ ≤ (vkLogScale (Real.log x) / Real.log x) * (Real.log y - Real.log x) := by
      change vkLogScale (Real.log y) - vkLogScale (Real.log x) ≤ _
      nlinarith only [hfrac, hself]
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall (sub_nonneg.mpr htT)

/-- The VK scale absorbs even the square of the double logarithm. This is
needed to retain the first correction in a variable exponential coefficient. -/
theorem vkProfile_dominates_logLog_sq (c : ℝ) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, Real.log (Real.log x) ^ 2 ≤ c * vkProfile x := by
  have hr : Tendsto (fun t : ℝ => Real.log t / t ^ (1 / 5 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/5)).tendsto_div_nhds_zero
  have hsq : Tendsto (fun x : ℝ =>
      (Real.log (Real.log x) / (Real.log x) ^ (1 / 5 : ℝ)) ^ 2) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (hr.pow 2).comp Real.tendsto_log_atTop
  filter_upwards [(tendsto_order.1 hsq).2 c hc,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.exp 1))] with x h hx
  have hx0 : 0 < Real.log x := (Real.exp_pos 1).trans_le hx
  rw [div_pow] at h
  have hl := (div_lt_iff₀ (pow_pos (Real.rpow_pos_of_pos hx0 (1 / 5 : ℝ)) 2)).mp h
  have hid : ((Real.log x) ^ (1/5 : ℝ)) ^ 2 = (Real.log x) ^ (2/5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  rw [hid] at hl
  exact hl.le.trans (mul_le_mul_of_nonneg_left (vkLogScale_lower hx) hc.le)

private theorem reciprocal_fifth_power_tangent (u : ℝ) (hu : u < 1) :
    1 + u / 5 ≤ (1 - u) ^ (-(1 / 5 : ℝ)) := by
  have h := Real.log_le_sub_one_of_pos (sub_pos.mpr hu)
  rw [Real.rpow_def_of_pos (sub_pos.mpr hu)]
  linarith [Real.add_one_le_exp (Real.log (1 - u) * (-(1 / 5 : ℝ)))]

/-- A variable-coefficient bound of the form of Lee–Leong (12) implies a
fixed leading coefficient A and any second coefficient k < A*r/5. -/
theorem vk_second_order_of_variable_coefficient (F : ℝ → ℝ) (A r K k : ℝ)
    (hA : 0 < A) (hK : 0 < K) (hk : k < A * r / 5)
    (hM : ∀ᶠ x : ℝ in atTop, |F x| ≤ K * x * Real.log x *
      Real.exp (-(A * (1 - r / Real.log (Real.log x)) ^ (-(1 / 5 : ℝ)) * vkProfile x))) :
    ∀ᶠ x : ℝ in atTop, |F x| ≤ x *
      Real.exp (-A * vkProfile x - k * (vkProfile x / Real.log (Real.log x))) := by
  have hLtop : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hdom := vkProfile_dominates_logLog_sq ((A * r / 5 - k) / 2) (by linarith)
  filter_upwards [hM, hdom, hLtop.eventually (eventually_gt_atTop (max r 0)),
    hLtop.eventually (eventually_ge_atTop (Real.log K)), eventually_ge_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    vkProfile_tendsto_atTop.eventually (eventually_ge_atTop (0 : ℝ))]
    with x hx hD hL hLK hx0 hlogx hV
  let L := Real.log (Real.log x)
  let V := vkProfile x
  change max r 0 < L at hL
  change Real.log K ≤ L at hLK
  change L ^ 2 ≤ (A * r / 5 - k) / 2 * V at hD
  change 0 ≤ V at hV
  have hL0 : 0 < L := (le_max_right _ _).trans_lt hL
  have hu : r / L < 1 := (div_lt_iff₀ hL0).mpr (by simpa using (le_max_left r 0).trans_lt hL)
  have ht := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (reciprocal_fifth_power_tangent (r / L) hu) hA.le) hV
  have heq : A * (1 + (r / L) / 5) * V = A * V + (A * r / 5) * (V / L) := by ring
  rw [heq] at ht
  have hcost : Real.log K + L ≤ (A * r / 5 - k) * (V / L) := by
    calc
      _ ≤ 2 * L := by linarith only [hLK]
      _ ≤ (A * r / 5 - k) * V / L := (le_div_iff₀ hL0).mpr (by nlinarith only [hD])
      _ = _ := by ring
  have hexp : (Real.log K + L) + (-(A * (1 - r / L) ^ (-(1/5 : ℝ)) * V)) ≤
      -A * V - k * (V / L) := by linarith only [ht, hcost]
  calc
    |F x| ≤ K * x * Real.log x * Real.exp (-(A * (1 - r / L) ^ (-(1/5 : ℝ)) * V)) := hx
    _ = x * Real.exp ((Real.log K + L) + (-(A * (1 - r / L) ^ (-(1/5 : ℝ)) * V))) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hK, show Real.exp L = Real.log x by
        exact Real.exp_log hlogx]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hx0

end RiemannResearch.Analysis

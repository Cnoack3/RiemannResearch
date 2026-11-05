import RiemannResearch.RH.MertensDelayedSummability
import RiemannResearch.RH.MertensFullEnvelope

/-! # Comparison of the translated damping and the square-root margins -/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QMertensFirstMoment
open RiemannResearch.Analysis

/-- A concrete upper bound for the translated-profile loss. The displacement of
the argument costs at most a constant times Φ²/log, plus the two logarithms. -/
theorem leeLeongDelayedDamping_eventually_le_explicit :
    ∀ᶠ x : ℝ in atTop, leeLeongDelayedDamping x ≤
      Real.exp (-leeLeongFullProfile x +
        (2 * leeLeongRate)^2 * (vkProfile x ^ 2 / Real.log x) + 2 * Real.log (Real.log x)) := by
  let C := 2 * leeLeongRate
  have hC : 0 ≤ C := by unfold C leeLeongRate; positivity
  have hA : 0 ≤ leeLeongRate := by unfold leeLeongRate; positivity
  filter_upwards [leeLeongFullProfile_eventually_bounds,
    vkProfile_tendsto_atTop.eventually (eventually_ge_atTop (0:ℝ)),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0:ℝ)), eventually_gt_atTop (0:ℝ),
    leeLeongDelayedArg_tendsto_atTop.eventually leeLeongFullProfile_eventually_increment,
    leeLeongDelayedArg_tendsto_atTop.eventually vk_eventual_relative_increment]
    with x hb hV ht hx hchg hinc
  let D := leeLeongDelayedArg x
  have hF := (mul_nonneg hA hV).trans hb.1
  have hD : D ≤ x := by
    change Real.exp (Real.log x - leeLeongFullProfile x) ≤ x
    calc
      _ ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr (sub_le_self _ hF)
      _ = x := Real.exp_log hx
  have hlogD : Real.log D = Real.log x - leeLeongFullProfile x := Real.log_exp _
  have h1 := hinc x hD
  change vkProfile x - vkProfile D ≤ (vkProfile x / Real.log x) * (Real.log x - Real.log D) at h1
  rw [hlogD, sub_sub_cancel] at h1
  have h2 := hchg x hD
  have hh : leeLeongFullProfile x - leeLeongFullProfile D ≤ C^2 * (vkProfile x^2 / Real.log x) := by
    calc
      _ ≤ C * (vkProfile x - vkProfile D) := h2
      _ ≤ C * (vkProfile x / Real.log x * leeLeongFullProfile x) :=
        mul_le_mul_of_nonneg_left h1 hC
      _ ≤ C * (vkProfile x / Real.log x * (C * vkProfile x)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb.2 (div_nonneg hV ht.le)) hC
      _ = _ := by ring
  calc
    _ = Real.exp (-leeLeongFullProfile D + (Real.log (Real.log x) + Real.log (Real.log x))) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log ht]
      change Real.log x ^ 2 * _ = _
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by dsimp only [C] at hh; linarith only [hh])

/-- The translated damping is bounded by every fixed positive square-root
margin. Consequently the previously established absolute moments imply the
translated one, with the reverse implication not required. -/
theorem leeLeongDelayedDamping_le_full_margin (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, leeLeongDelayedDamping x ≤
      Real.exp (-leeLeongFullProfile x + δ * Real.sqrt (vkProfile x)) := by
  let C := 2 * leeLeongRate
  have hA : 0 < leeLeongRate := Real.rpow_pos_of_pos
    (by positivity : 0 < 5 / (3 * (53.99 : ℝ) ^ 3)) _
  have hC : 0 < C := mul_pos (by norm_num) hA
  let γ := (δ/2) / C^2
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hcost : C^2 * γ = δ/2 := by dsimp [γ]; field_simp [hC.ne']
  filter_upwards [leeLeongDelayedDamping_eventually_le_explicit, vk_sq_div_log_eventual_le_sqrt γ hγ,
    vkProfile_dominates_logLog_sq ((δ/4)^2) (by positivity),
    vkProfile_tendsto_atTop.eventually (eventually_ge_atTop (0:ℝ))] with x hD hv hl hV
  have hL : Real.log (Real.log x) ≤ (δ/4) * Real.sqrt (vkProfile x) := by
    apply le_of_sq_le_sq _ (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
    simpa only [mul_pow, Real.sq_sqrt hV] using hl
  have hh := mul_le_mul_of_nonneg_left hv (sq_nonneg C)
  rw [← mul_assoc, hcost] at hh
  apply hD.trans (Real.exp_le_exp.mpr ?_)
  change -leeLeongFullProfile x + C^2*(vkProfile x ^ 2 / Real.log x) +
    2*Real.log (Real.log x) ≤ _
  linarith only [hh, hL]

end RiemannResearch.RH.QMertensFirstMoment

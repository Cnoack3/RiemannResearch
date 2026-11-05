/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.MertensFullProfile
import RiemannResearch.RH.QHarmonicMomentComparison

/-! # Summability of the delayed Lee–Leong damping

The shifted logarithm log x − F(x) is eventually at least half of log x.
At the shifted argument the full exponent still dominates every fixed
multiple of log(log x). These two inequalities pay for the prefactor and
the scalar summability in the cutoff pairing.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QMertensFirstMoment
open RiemannResearch.Analysis RiemannResearch.NumberTheory.PrimeNumberTheorem
open ZetaTwoHilbert ZetaTwoProbability

def leeLeongDelayedArg (x : ℝ) : ℝ :=
  Real.exp (Real.log x - leeLeongFullProfile x)

def leeLeongDelayedDamping (x : ℝ) : ℝ :=
  Real.log x ^ 2 * Real.exp (-leeLeongFullProfile (leeLeongDelayedArg x))

theorem leeLeongDelayedDamping_nonneg (x : ℝ) : 0 ≤ leeLeongDelayedDamping x :=
  mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

/-- The complete published exponent grows sublinearly in log x. -/
theorem leeLeongFullProfile_eventually_le_mul_log (c : ℝ) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, leeLeongFullProfile x ≤ c * Real.log x := by
  have hp : Tendsto (fun x : ℝ => (Real.log x) ^ (2/5 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 2/5)).comp Real.tendsto_log_atTop
  have hA : 0 ≤ leeLeongRate := by unfold leeLeongRate; positivity
  filter_upwards [leeLeongFullProfile_eventually_bounds,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.exp 1)),
    hp.eventually (eventually_ge_atTop (2 * leeLeongRate / c))] with x hF hlog hbig
  let t := Real.log x
  change Real.exp 1 ≤ t at hlog
  change 2 * leeLeongRate / c ≤ t ^ (2/5 : ℝ) at hbig
  have ht := (Real.exp_pos (1:ℝ)).trans_le hlog
  have hL : 1 ≤ Real.log t := (Real.le_log_iff_exp_le ht).mpr hlog
  have hV : vkProfile x ≤ t ^ (3/5 : ℝ) := div_le_self
    (Real.rpow_nonneg ht.le _) (Real.one_le_rpow hL (by norm_num))
  have hprod : t ^ (2/5 : ℝ) * t ^ (3/5 : ℝ) = t := by
    rw [← Real.rpow_add ht, show (2/5 : ℝ) + 3/5 = 1 by norm_num, Real.rpow_one]
  have hcoeff := (div_le_iff₀ hc).mp hbig
  calc
    _ ≤ (2 * leeLeongRate) * vkProfile x := hF.2
    _ ≤ (2 * leeLeongRate) * t ^ (3/5 : ℝ) :=
      mul_le_mul_of_nonneg_left hV (mul_nonneg (by norm_num) hA)
    _ ≤ (t ^ (2/5 : ℝ) * c) * t ^ (3/5 : ℝ) :=
      mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg ht.le _)
    _ = c * (t ^ (2/5 : ℝ) * t ^ (3/5 : ℝ)) := by ring
    _ = _ := by rw [hprod]

theorem leeLeongDelayedArg_tendsto_atTop :
    Tendsto leeLeongDelayedArg atTop atTop := by
  unfold leeLeongDelayedArg
  apply Real.tendsto_exp_atTop.comp
  apply tendsto_atTop.2
  intro b
  filter_upwards [leeLeongFullProfile_eventually_le_mul_log (1/2) (by norm_num),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2*b))] with x hF hx
  change 2*b ≤ Real.log x at hx
  change b ≤ Real.log x - leeLeongFullProfile x
  linarith

/-- Delaying the input leaves the exponent larger than any logarithmic
prefactor in the original logarithmic variable. -/
theorem leeLeongDelayedProfile_dominates_logLog (c : ℝ) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, c * Real.log (Real.log x) ≤
      leeLeongFullProfile (leeLeongDelayedArg x) := by
  have hA : 0 < leeLeongRate := Real.rpow_pos_of_pos
    (by positivity : 0 < 5 / (3 * (53.99 : ℝ)^3)) _
  have htop := leeLeongDelayedArg_tendsto_atTop
  have hlogtop := Real.tendsto_log_atTop.comp htop
  have hLtop := Real.tendsto_log_atTop.comp hlogtop
  filter_upwards [htop.eventually leeLeongFullProfile_eventually_bounds,
    htop.eventually (vkProfile_dominates_logLog_sq 1 (by norm_num)),
    leeLeongFullProfile_eventually_le_mul_log (1/2) (by norm_num),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0:ℝ)),
    hlogtop.eventually (eventually_ge_atTop (2:ℝ)),
    hLtop.eventually (eventually_ge_atTop (2*c / leeLeongRate))] with x hF hV hhalf ht hs hlarge
  let s := Real.log (leeLeongDelayedArg x)
  change (0:ℝ) < Real.log x at ht
  change 2 ≤ s at hs
  change 2*c / leeLeongRate ≤ Real.log s at hlarge
  have hspos : 0 < s := by linarith
  have hsdef : s = Real.log x - leeLeongFullProfile x := Real.log_exp _
  have hlogcmp : Real.log (Real.log x) ≤ 2 * Real.log s := by
    have hle : Real.log x ≤ 2*s := by linarith only [hsdef, hhalf]
    have h := Real.log_le_log ht hle
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hspos.ne'] at h
    linarith only [h, Real.log_le_log (by norm_num : (0:ℝ)<2) hs]
  have hL : 0 ≤ Real.log s := Real.log_nonneg (by linarith only [hs])
  have hlinear := mul_le_mul_of_nonneg_right ((div_le_iff₀ hA).mp hlarge) hL
  have hsquare : (Real.log s)^2 ≤ vkProfile (leeLeongDelayedArg x) := by
    simpa only [one_mul] using hV
  calc
    _ ≤ c * (2 * Real.log s) := mul_le_mul_of_nonneg_left hlogcmp hc.le
    _ ≤ leeLeongRate * (Real.log s)^2 := by nlinarith only [hlinear]
    _ ≤ leeLeongRate * vkProfile (leeLeongDelayedArg x) :=
      mul_le_mul_of_nonneg_left hsquare hA.le
    _ ≤ _ := hF.1

private theorem delayed_exp_log_nat (k : ℕ) {t : ℝ} (ht : 0 < t) :
    Real.exp ((k:ℝ) * Real.log t) = t^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, add_mul, one_mul, Real.exp_add, ih, Real.exp_log ht, pow_succ]

theorem leeLeongDelayedDamping_mul_log_pow_eventually_le_one (k : ℕ) :
    ∀ᶠ x : ℝ in atTop, leeLeongDelayedDamping x * Real.log x ^ k ≤ 1 := by
  have hp : (0 : ℝ) < ((k+2 : ℕ) : ℝ) := by positivity
  filter_upwards [leeLeongDelayedProfile_dominates_logLog (k+2 : ℕ) hp,
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0:ℝ))] with x hF ht
  change 0 < Real.log x at ht
  have he : Real.exp (((k+2 : ℕ):ℝ) * Real.log (Real.log x) -
      leeLeongFullProfile (leeLeongDelayedArg x)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [sub_eq_add_neg, Real.exp_add, delayed_exp_log_nat (k+2) ht, pow_add] at he
  unfold leeLeongDelayedDamping
  linarith only [he]

/-- In particular the damping is little-o of the inverse squared logarithm. -/
theorem leeLeongDelayedDamping_mul_log_sq_tendsto_zero :
    Tendsto (fun x : ℝ => leeLeongDelayedDamping x * Real.log x ^ 2) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (Real.tendsto_log_atTop.const_div_atTop 1)
    (Eventually.of_forall (fun x => mul_nonneg (leeLeongDelayedDamping_nonneg x) (sq_nonneg _)))
  filter_upwards [leeLeongDelayedDamping_mul_log_pow_eventually_le_one 3,
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0:ℝ))] with x h ht
  change 0 < Real.log x at ht
  apply (le_div_iff₀ ht).mpr
  calc
    _ = leeLeongDelayedDamping x * Real.log x ^ 3 := by ring
    _ ≤ _ := h

theorem summable_leeLeongDelayedDamping_div_nat :
    Summable (fun n : ℕ => leeLeongDelayedDamping n / (n:ℝ)) := by
  apply summable_inv_mul_log_sq.of_norm_bounded_eventually_nat
  have hn : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hn.eventually (leeLeongDelayedDamping_mul_log_pow_eventually_le_one 2),
    eventually_ge_atTop (2:ℕ)] with n h hn
  have hn' : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hnp := zero_lt_one.trans hn'
  have hlog := Real.log_pos hn'
  change ‖leeLeongDelayedDamping n / (n:ℝ)‖ ≤ ((n:ℝ) * Real.log (n:ℝ)^2)⁻¹
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (leeLeongDelayedDamping_nonneg _) hnp.le)]
  rw [← one_div, le_div_iff₀ (mul_pos hnp (sq_pos_of_pos hlog))]
  calc
    _ = leeLeongDelayedDamping n * Real.log (n:ℝ)^2 := by field_simp [hnp.ne']
    _ ≤ _ := h

theorem summable_leeLeongDelayedDamping_Q :
    Summable (fun n : ℕ => positiveQWeight n * ((n:ℝ) * leeLeongDelayedDamping n)) := by
  apply (summable_leeLeongDelayedDamping_div_nat.div_const zetaTwo).congr
  intro n
  by_cases hn : n = 0
  · simp [hn, positiveQWeight]
  · have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn
    unfold positiveQWeight
    field_simp [hn', zetaTwo_pos.ne']

end RiemannResearch.RH.QMertensFirstMoment

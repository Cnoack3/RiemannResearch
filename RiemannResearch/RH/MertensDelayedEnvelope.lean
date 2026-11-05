/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.MertensFullDisplacement
import RiemannResearch.RH.MertensDelayedSummability

/-! # A translated exponent for the raw Lee–Leong cutoff envelope
The generic proof uses the two branches of the physical error envelope
directly. With F evaluated at physical x, the translated argument is
x exp(-F(x)), equivalently log(x)-F(x) in logarithmic coordinates. -/
noncomputable section
open Filter
namespace RiemannResearch.RH.QMertensFirstMoment

/-- Physical damping after accounting for the printed Mertens prefactor
and one additional logarithm from the physical error envelope. -/
def delayedFullDamping (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  (Real.log x)^2 * Real.exp (-F (x * Real.exp (-F x)))

/-- The raw input epsilon has one logarithmic prefactor. A translated
argument and two powers of log dominate the two-branch cutoff envelope. -/
theorem errorEnvelope_eventually_le_delayed (F : ℝ → ℝ)
    (hmono : ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ≤ y → F x ≤ F y)
    (hshape : ∀ᶠ x : ℝ in atTop, 0 ≤ F x ∧ F x ≤ Real.log x)
    (hdelay : Tendsto (fun x : ℝ => x * Real.exp (-F x)) atTop atTop) :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
      errorEnvelope N n (25.85 * Real.log (N : ℝ) * Real.exp (-F N)) ≤
        2 + 400 * ((n : ℝ) * delayedFullDamping F n) := by
  have hncast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  obtain ⟨X, hX⟩ := eventually_atTop.1 ((hdelay.eventually hmono).and hshape)
  filter_upwards [hncast.eventually (eventually_ge_atTop X),
    hncast.eventually (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))),
    eventually_ge_atTop (1 : ℕ)] with N hN hL hN1 n
  have hD : 0 ≤ (n : ℝ) * delayedFullDamping F n :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  unfold errorEnvelope
  split_ifs with hhead
  · linarith
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast (show N ≤ n by omega)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hnpos := hNpos.trans_le hNn
  let t := Real.log (n : ℝ)
  let s := Real.log (N : ℝ)
  let D := (n : ℝ) * Real.exp (-F n)
  let V := Real.exp (-F D)
  let e := 25.85 * s * Real.exp (-F N)
  change min (3 * (N : ℝ)) (2 + (n : ℝ) * (e * (2 + t) +
    5 * (e * (1 + Real.log (1 / e))))) ≤ 2 + 400 * ((n : ℝ) * (t^2 * V))
  have hs : 1 ≤ s := hL
  have hst : s ≤ t := Real.log_le_log hNpos hNn
  have ht : 1 ≤ t := hs.trans hst
  have ht0 : 0 ≤ t := by linarith
  have hm : ∀ y : ℝ, D ≤ y → F D ≤ F y := (hX (n : ℝ) (hN.trans hNn)).1
  have hFn := (hX (n : ℝ) (hN.trans hNn)).2.1
  have hFN := (hX (N : ℝ) hN).2.2
  have hDn : D ≤ (n : ℝ) := by
    simpa only [D, mul_one] using mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hFn)) hnpos.le
  have hV : 0 ≤ V := (Real.exp_pos _).le
  by_cases hcut : (N : ℝ) ≤ D
  · apply (min_le_left _ _).trans
    have hVn : Real.exp (-F n) ≤ V :=
      Real.exp_le_exp.mpr (neg_le_neg (hm _ hDn))
    have hlarge : V ≤ t^2 * V := by
      have h1 : 1 ≤ t ^ 2 := by nlinarith
      simpa using mul_le_mul_of_nonneg_right h1 hV
    have hcut' : (N : ℝ) ≤ (n : ℝ) * (t^2 * V) :=
      hcut.trans (mul_le_mul_of_nonneg_left (hVn.trans hlarge) hnpos.le)
    change 0 ≤ (n : ℝ) * (t^2 * V) at hD
    linarith
  · apply (min_le_right _ _).trans
    have hFD : F D ≤ F N := hm _ (le_of_lt (lt_of_not_ge hcut))
    have hspos : 0 < s := by linarith
    have hcoef : 0 < (25.85 : ℝ) * s := mul_pos (by norm_num) hspos
    have hlog : Real.log (1 / e) ≤ t := by
      have hcoeff : 0 ≤ Real.log (25.85 * s) := Real.log_nonneg (by linarith)
      dsimp only [e]
      rw [one_div, Real.log_inv, Real.log_mul hcoef.ne' (Real.exp_pos _).ne', Real.log_exp]
      change F (N : ℝ) ≤ s at hFN
      linarith
    have hE : 0 ≤ e := mul_nonneg hcoef.le (Real.exp_pos _).le
    have he : e ≤ (25.85 * t) * V :=
      mul_le_mul (mul_le_mul_of_nonneg_left hst (by norm_num))
        (Real.exp_le_exp.mpr (neg_le_neg hFD)) (Real.exp_pos _).le (by positivity)
    have hfac : (2 + t) + 5 * (1 + Real.log (1 / e)) ≤ 13 * t := by linarith
    have hmix : e * (2 + t) + 5 * (e * (1 + Real.log (1 / e))) ≤ 400 * (t^2 * V) := by
      calc
        _ = e * ((2 + t) + 5 * (1 + Real.log (1 / e))) := by ring
        _ ≤ e * (13 * t) := mul_le_mul_of_nonneg_left hfac hE
        _ ≤ ((25.85 * t) * V) * (13 * t) := mul_le_mul_of_nonneg_right he (by positivity)
        _ = 336.05 * (t^2 * V) := by ring
        _ ≤ 400 * (t^2 * V) := mul_le_mul_of_nonneg_right (by norm_num)
          (mul_nonneg (sq_nonneg _) hV)
    have := mul_le_mul_of_nonneg_left hmix hnpos.le
    linarith

/-- Specialization to the precise published exponent. No Mertens bound
is needed just to dominate the two-branch envelope algebraically. -/
theorem errorEnvelope_eventually_le_leeLeongDelayed :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
      errorEnvelope N n (25.85 * Real.log (N : ℝ) *
        Real.exp (-leeLeongFullProfile N)) ≤
        2 + 400 * ((n : ℝ) * leeLeongDelayedDamping n) := by
  have hm : ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ≤ y →
      leeLeongFullProfile x ≤ leeLeongFullProfile y := by
    simpa only [zero_mul, sub_zero] using leeLeongFullProfile_sub_sqrt_eventually_mono 0
  have hF : ∀ᶠ x : ℝ in atTop, 0 ≤ leeLeongFullProfile x ∧ leeLeongFullProfile x ≤ Real.log x := by
    filter_upwards [leeLeongFullProfile_eventually_bounds,
      RiemannResearch.Analysis.vkProfile_tendsto_atTop.eventually (eventually_ge_atTop (0 : ℝ)),
      leeLeongFullProfile_eventually_le_mul_log 1 (by norm_num)] with x hx hv hl
    have hA : 0 ≤ leeLeongRate := by unfold leeLeongRate; positivity
    exact ⟨(mul_nonneg hA hv).trans hx.1, by simpa only [one_mul] using hl⟩
  have hD : Tendsto (fun x : ℝ => x * Real.exp (-leeLeongFullProfile x)) atTop atTop := by
    apply leeLeongDelayedArg_tendsto_atTop.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp only [leeLeongDelayedArg, sub_eq_add_neg, Real.exp_add, Real.exp_log hx]
  filter_upwards [errorEnvelope_eventually_le_delayed leeLeongFullProfile hm hF hD] with N hN n
  by_cases hn : n = 0
  · simpa only [hn, Nat.cast_zero, zero_mul] using hN n
  · have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    simpa only [delayedFullDamping, leeLeongDelayedDamping, leeLeongDelayedArg,
      sub_eq_add_neg, Real.exp_add, Real.exp_log hn'] using hN n

end RiemannResearch.RH.QMertensFirstMoment

/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.SignedPowerDampingAbel
import RiemannResearch.Analysis.LogPowerSummability

/-!
# Dini and critical logarithmic signed-prefix damping

These are Banach-valued Abel criteria. The norm is taken only after the
complete signed prefix has been formed. The Dini criterion permits arbitrary
non-power profiles; the logarithmic application includes the critical equality
between raw growth and damping exponents. All growth hypotheses are explicit,
and the logarithmic bound is required only eventually.

Source: standard Abel summation, using the repository's exact finite identity
and the classical logarithmic p-series. No novelty is claimed.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.Analysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A Dini integral of the complete signed prefix, together with its vanishing
boundary term, suffices for naturally ordered power damping. -/
theorem signedVector_power_damped_tendsto_of_dini
    (u : ℕ → E) {ε : ℝ} (hε : 0 ≤ ε)
    (hdini : Summable (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ) ^ (-ε - 1) * ‖signedVectorPrefix u (n + 1)‖))
    (hboundary : Tendsto (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ) ^ (-ε) * ‖signedVectorPrefix u (n + 1)‖)
      atTop (𝓝 0)) :
    Tendsto (fun N => ∑ n ∈ Finset.range N,
      ((n + 1 : ℕ) : ℝ) ^ (-ε) • u n) atTop
      (𝓝 (∑' n, ((((n + 1 : ℕ) : ℝ) ^ (-ε)) -
        (((n + 2 : ℕ) : ℝ) ^ (-ε))) • signedVectorPrefix u (n + 1))) := by
  apply signedVector_weighted_partial_tendsto
  · apply (hdini.mul_left ε).of_nonneg_of_le
    · intro n
      exact mul_nonneg (abs_nonneg _) (norm_nonneg _)
    · intro n
      have hx : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hstep := abs_power_damping_step_le hε hx
      have hcast : (((n + 1 : ℕ) : ℝ) + 1) = ((n + 2 : ℕ) : ℝ) := by
        push_cast
        ring
      rw [hcast] at hstep
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right hstep (norm_nonneg (signedVectorPrefix u (n + 1)))
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hnorm (n : ℕ) :
        ‖((n + 1 : ℕ) : ℝ)^(-ε) • signedVectorPrefix u (n + 1)‖ =
          ((n + 1 : ℕ) : ℝ)^(-ε) * ‖signedVectorPrefix u (n + 1)‖ := by
      rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg (n + 1)) _)]
    simpa only [hnorm] using hboundary

/-- The strict power gap can be replaced by a logarithmic saving greater than
one at the exact critical exponent. Only the eventual estimate is required. -/
theorem signedVector_power_damped_tendsto_of_critical_log
    (u : ℕ → E) {C ε q : ℝ} (hε : 0 ≤ ε) (hq : 1 < q)
    (hgrowth : ∀ᶠ n : ℕ in atTop,
      ‖signedVectorPrefix u (n + 1)‖ ≤
        C * ((n + 1 : ℕ) : ℝ)^ε /
          Real.log (2 * ((n + 1 : ℕ) : ℝ))^q) :
    Tendsto (fun N => ∑ n ∈ Finset.range N,
      ((n + 1 : ℕ) : ℝ) ^ (-ε) • u n) atTop
      (𝓝 (∑' n, ((((n + 1 : ℕ) : ℝ) ^ (-ε)) -
        (((n + 2 : ℕ) : ℝ) ^ (-ε))) • signedVectorPrefix u (n + 1))) := by
  apply signedVector_power_damped_tendsto_of_dini u hε
  · have hs : Summable (fun n : ℕ =>
        1 / (((n + 1 : ℕ) : ℝ) *
          Real.log (2 * ((n + 1 : ℕ) : ℝ))^q)) :=
      (summable_nat_add_iff 1).mpr (summable_log_power_majorant hq)
    apply (hs.mul_left C).of_norm_bounded_eventually_nat
    filter_upwards [hgrowth] with n hn
    have hx : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hL : 0 < Real.log (2 * ((n + 1 : ℕ) : ℝ)) := by
      apply Real.log_pos
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      push_cast
      linarith
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hx.le _) (norm_nonneg _))]
    calc
      _ ≤ ((n + 1 : ℕ) : ℝ)^(-ε - 1) *
          (C * ((n + 1 : ℕ) : ℝ)^ε /
            Real.log (2 * ((n + 1 : ℕ) : ℝ))^q) :=
        mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg hx.le _)
      _ = C * ((((n + 1 : ℕ) : ℝ)^(-ε - 1)) *
          ((n + 1 : ℕ) : ℝ)^ε) /
            Real.log (2 * ((n + 1 : ℕ) : ℝ))^q := by ring
      _ = C * ((n + 1 : ℕ) : ℝ)^(-1 : ℝ) /
            Real.log (2 * ((n + 1 : ℕ) : ℝ))^q := by
        rw [← Real.rpow_add hx, show -ε - 1 + ε = (-1 : ℝ) by ring]
      _ = C * (1 / (((n + 1 : ℕ) : ℝ) *
          Real.log (2 * ((n + 1 : ℕ) : ℝ))^q)) := by
        rw [Real.rpow_neg_one]
        field_simp [hx.ne', (Real.rpow_pos_of_pos hL q).ne']
  · have hxlim : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hloglim : Tendsto (fun n : ℕ =>
        Real.log (2 * ((n + 1 : ℕ) : ℝ))) atTop atTop :=
      Real.tendsto_log_atTop.comp (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) hxlim)
    have hlim : Tendsto (fun n : ℕ =>
        C * Real.log (2 * ((n + 1 : ℕ) : ℝ))^(-q)) atTop (𝓝 0) := by
      simpa using ((tendsto_rpow_neg_atTop (by linarith : 0 < q)).comp hloglim).const_mul C
    apply squeeze_zero' (Filter.Eventually.of_forall (fun n =>
      mul_nonneg (Real.rpow_nonneg (by positivity) _) (norm_nonneg _))) _ hlim
    filter_upwards [hgrowth] with n hn
    have hx : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hL : 0 < Real.log (2 * ((n + 1 : ℕ) : ℝ)) := by
      apply Real.log_pos
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      push_cast
      linarith
    calc
      _ ≤ ((n + 1 : ℕ) : ℝ)^(-ε) *
          (C * ((n + 1 : ℕ) : ℝ)^ε /
            Real.log (2 * ((n + 1 : ℕ) : ℝ))^q) :=
        mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg hx.le _)
      _ = C * ((((n + 1 : ℕ) : ℝ)^(-ε)) *
          ((n + 1 : ℕ) : ℝ)^ε) /
            Real.log (2 * ((n + 1 : ℕ) : ℝ))^q := by ring
      _ = C / Real.log (2 * ((n + 1 : ℕ) : ℝ))^q := by
        rw [← Real.rpow_add hx, neg_add_cancel, Real.rpow_zero, mul_one]
      _ = C * Real.log (2 * ((n + 1 : ℕ) : ℝ))^(-q) := by
        rw [Real.rpow_neg hL.le]
        rfl

end RiemannResearch.Analysis

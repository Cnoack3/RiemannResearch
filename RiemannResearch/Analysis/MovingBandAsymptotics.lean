/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Amplification tests for logarithmic endpoint error bounds

These elementary real-variable lemmas convert a logarithmic endpoint error
rate into explicit shrinking conductor bands.  They make no arithmetic or
fixed-subhalf finite-energy assertion.  The margin condition is exactly
equivalent to the vanishing of the endpoint amplification majorant.

Source: direct algebra and elementary logarithmic asymptotics.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis

/-- The amplification/error product is exactly an exponential margin. -/
theorem exp_mul_log_rpow_eq_exp_margin (x δ a : ℝ) (hx : 0 < 6 + x) :
    Real.exp (δ * x) * (6 + x) ^ (-a) =
      Real.exp (δ * x - a * Real.log (6 + x)) := by
  rw [Real.rpow_def_of_pos hx, ← Real.exp_add]
  congr 1
  ring

/-- The sharp margin condition is equivalent to decay of this majorant. -/
theorem exp_mul_log_rpow_tendsto_zero_iff
    (x δ : ℕ → ℝ) (a : ℝ) (hx : ∀ j, 0 < 6 + x j) :
    Tendsto (fun j => Real.exp (δ j * x j) * (6 + x j) ^ (-a)) atTop (𝓝 0) ↔
      Tendsto (fun j => δ j * x j - a * Real.log (6 + x j)) atTop atBot := by
  simp_rw [exp_mul_log_rpow_eq_exp_margin _ _ _ (hx _)]
  exact Real.tendsto_exp_comp_nhds_zero

/-- An exact shifted logarithmic quotient limit, convenient at log-conductor scale. -/
theorem tendsto_shifted_log_div_self
    (x : ℕ → ℝ) (hx : Tendsto x atTop atTop) :
    Tendsto (fun j => Real.log (6 + x j) / x j) atTop (𝓝 0) := by
  have hshift : Tendsto (fun j => 6 + x j) atTop atTop :=
    tendsto_atTop_add_const_left atTop 6 hx
  have h := (Real.tendsto_pow_log_div_mul_add_atTop
    (1 : ℝ) (-6) 1 one_ne_zero).comp hshift
  have heq (z : ℝ) : 6 + z + -6 = z := by ring
  simpa only [Function.comp_def, pow_one, one_mul, heq] using h

/-- Any nonnegative damping shift with an eventually nonpositive margin
necessarily tends to zero. -/
theorem damping_shift_tendsto_zero_of_log_margin
    (x δ : ℕ → ℝ) (hx : Tendsto x atTop atTop)
    (hδ : ∀ j, 0 ≤ δ j) (a : ℝ)
    (hmargin : Tendsto (fun j => δ j * x j - a * Real.log (6 + x j))
      atTop atBot) :
    Tendsto δ atTop (𝓝 0) := by
  have hquot : Tendsto (fun j => a * Real.log (6 + x j) / x j)
      atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using
      (tendsto_shifted_log_div_self x hx).const_mul a
  apply squeeze_zero' (Eventually.of_forall hδ) _ hquot
  filter_upwards [hx.eventually (eventually_gt_atTop (0 : ℝ)),
    hmargin.eventually (eventually_le_atBot (0 : ℝ))] with j hj hm
  exact (le_div_iff₀ hj).mpr (by linarith)

/-- Every fixed coefficient strictly below the available logarithmic
error exponent forces the exact margin to negative infinity. -/
theorem logarithmic_margin_tendsto_atBot_of_strict_coefficient
    (x δ : ℕ → ℝ) (hx : Tendsto x atTop atTop) (a c : ℝ) (hca : c < a)
    (hband : ∀ᶠ j in atTop, δ j * x j ≤ c * Real.log (6 + x j)) :
    Tendsto (fun j => δ j * x j - a * Real.log (6 + x j)) atTop atBot := by
  have hlog : Tendsto (fun j => Real.log (6 + x j)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_left atTop 6 hx)
  have hbound : Tendsto (fun j => (c - a) * Real.log (6 + x j)) atTop atBot :=
    hlog.const_mul_atTop_of_neg (sub_neg.mpr hca)
  apply tendsto_atBot.mpr
  intro b
  filter_upwards [tendsto_atBot.mp hbound b, hband] with j hj hb
  calc
    δ j * x j - a * Real.log (6 + x j) ≤
        (c - a) * Real.log (6 + x j) := by nlinarith
    _ ≤ b := hj

/-- Exact criterion at conductor scale, including automatic convergence
of the shift back to the endpoint.  The arbitrary exponent permits reuse
if the endpoint logarithmic rate is strengthened later. -/
theorem conductor_amplification_tendsto_zero_of_margin
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (δ : ℕ → ℝ) (hδ : ∀ j, 0 ≤ δ j) (a : ℝ)
    (hmargin : Tendsto (fun j =>
      δ j * Real.log ((M j + 1 : ℕ) : ℝ) -
        a * Real.log (6 + Real.log ((M j + 1 : ℕ) : ℝ))) atTop atBot) :
    Tendsto δ atTop (𝓝 0) ∧
    Tendsto (fun j => ((M j + 1 : ℕ) : ℝ) ^ (δ j) *
      (6 + Real.log ((M j + 1 : ℕ) : ℝ)) ^ (-a)) atTop (𝓝 0) := by
  let x : ℕ → ℝ := fun j => Real.log ((M j + 1 : ℕ) : ℝ)
  have hx : Tendsto x atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hM))
  have hxpos (j : ℕ) : 0 < 6 + x j := by
    have hlog : 0 ≤ x j := Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (M j)))
    linarith
  refine ⟨damping_shift_tendsto_zero_of_log_margin x δ hx hδ a hmargin, ?_⟩
  have h := (exp_mul_log_rpow_tendsto_zero_iff x δ a hxpos).mpr hmargin
  convert h using 1
  funext j
  rw [Real.rpow_def_of_pos (by positivity)]
  dsimp [x]
  rw [mul_comm (Real.log _) (δ j)]

/-- Explicit bands with coefficient c below a. At a = 1/4 these have
width c log(6+log(M+1))/log(M+1), whenever the denominator is positive. -/
theorem conductor_amplification_tendsto_zero_of_strict_coefficient
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (δ : ℕ → ℝ) (hδ : ∀ j, 0 ≤ δ j) (a c : ℝ) (hca : c < a)
    (hband : ∀ᶠ j in atTop,
      δ j * Real.log ((M j + 1 : ℕ) : ℝ) ≤
        c * Real.log (6 + Real.log ((M j + 1 : ℕ) : ℝ))) :
    Tendsto δ atTop (𝓝 0) ∧
    Tendsto (fun j => ((M j + 1 : ℕ) : ℝ) ^ (δ j) *
      (6 + Real.log ((M j + 1 : ℕ) : ℝ)) ^ (-a)) atTop (𝓝 0) := by
  apply conductor_amplification_tendsto_zero_of_margin M hM δ hδ a
  apply logarithmic_margin_tendsto_atBot_of_strict_coefficient
    (fun j => Real.log ((M j + 1 : ℕ) : ℝ)) δ _ a c hca hband
  exact Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hM))

end RiemannResearch.Analysis

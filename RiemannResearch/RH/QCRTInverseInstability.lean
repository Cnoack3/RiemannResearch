/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QGcdCellEstimates
import RiemannResearch.NumberTheory.DivisorCountSqrt
import RiemannResearch.Analysis.ConductorLogEnvelope
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

/-!
# Divergence of full-space CRT inverse stability factors

This is a worst-target obstruction. It does not say that the canonical
specific-target norms diverge, and does not settle their RH growth criterion.
-/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QCRTInverseInstability
open ZetaTwoHilbert QCRTFiniteCollocation QGcdCellEstimates
open RiemannResearch.NumberTheory.DivisorCountSqrt
open RiemannResearch.Analysis.ConductorLogEnvelope

/-- A fixed squared stability factor forces a scalar envelope bounded below
by one; the envelope tends to zero as L tends to infinity. -/
theorem stability_factor_envelope (L : ℕ) (hL : 2 ≤ L) (C : ℝ) (hC : 0 ≤ C)
    (hstability : ∀ f : trialSpace L,
      ‖(f : QHilbert)‖^2 ≤ C * ‖conditionalProjection L f‖^2) :
    1 ≤ 4 * C * ((6 + Real.log ((L : ℝ)+1))^2 / Real.sqrt (L : ℝ)) := by
  have hLR : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hLp : (0 : ℝ) < L := by linarith
  have hspos : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.mpr hLp
  have hlog : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg (by linarith)
  have hlog' : Real.log (L : ℝ) ≤ Real.log ((L : ℝ)+1) :=
    Real.log_le_log hLp (by linarith)
  have hsquares : (2 + Real.log (L : ℝ))^2 ≤
      (6 + Real.log ((L : ℝ)+1))^2 := by
    nlinarith
  have hc := card_divisors_le_two_sqrt L
  have hnecessity := trial_stability_factor_necessary L hL C hC hstability
  have hmajor : (L : ℝ)-1 ≤
      C * (2 * Real.sqrt (L : ℝ)) * (6 + Real.log ((L : ℝ)+1))^2 := by
    apply hnecessity.trans
    calc
      _ ≤ (C * (2 * Real.sqrt (L : ℝ))) * (2 + Real.log (L : ℝ))^2 := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hC) (sq_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hsquares (by positivity)
  have hprod : Real.sqrt (L : ℝ) * Real.sqrt (L : ℝ) ≤
      Real.sqrt (L : ℝ) * (4*C*(6 + Real.log ((L : ℝ)+1))^2) := by
    nlinarith [Real.sq_sqrt hLp.le]
  have hcancel := (mul_le_mul_iff_right₀ hspos).mp hprod
  calc
    1 ≤ (4*C*(6 + Real.log ((L : ℝ)+1))^2) / Real.sqrt (L : ℝ) := by
      apply (le_div_iff₀ hspos).mpr
      simpa only [one_mul] using hcancel
    _ = _ := by ring

/-- Every fixed squared full-trial stability factor eventually fails along
EVERY cutoff sequence tending to infinity, including the LCM tower. -/
theorem eventually_no_trial_stability_factor (L : ℕ → ℕ)
    (hL : Tendsto L atTop atTop) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n in atTop, ¬ (∀ f : trialSpace (L n),
      ‖(f : QHilbert)‖^2 ≤ C * ‖conditionalProjection (L n) f‖^2) := by
  have hsmall : Tendsto (fun n =>
      4*C*((6 + Real.log ((L n : ℝ)+1))^2 / Real.sqrt (L n : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((shifted_log_power_div_sqrt_tendsto_zero 2).comp hL).const_mul (4*C)
  filter_upwards [hL.eventually (eventually_ge_atTop (2 : ℕ)),
    hsmall.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with n hn hlt
  intro hstability
  exact (not_lt_of_ge (stability_factor_envelope (L n) hn C hC hstability)) hlt

/-- In ordinary norm units, every proposed fixed inverse bound eventually
has an actual legal counterexample. No inverse operator needs to be introduced. -/
theorem eventually_exists_unstable_trial (L : ℕ → ℕ)
    (hL : Tendsto L atTop atTop) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n in atTop, ∃ f : trialSpace (L n),
      C * ‖conditionalProjection (L n) f‖ < ‖(f : QHilbert)‖ := by
  filter_upwards [eventually_no_trial_stability_factor L hL (C^2) (sq_nonneg C)]
    with n hn
  classical
  push Not at hn
  obtain ⟨f, hf⟩ := hn
  refine ⟨f, ?_⟩
  by_contra h
  have hle : ‖(f : QHilbert)‖ ≤ C * ‖conditionalProjection (L n) f‖ := le_of_not_gt h
  have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mpr hle
  rw [mul_pow] at hsq
  exact (not_lt_of_ge hsq) hf

end RiemannResearch.RH.QCRTInverseInstability

/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoResidueCriticalGramRate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic.FunProp

/-!
# Microscopic coefficients of the complete grouped Gram

The rescaled ordinate difference multiplies the logarithm of the period.
The phase sum retains its continuous sinc profile at zero separation.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.SpectralObstruction

/-- The rectangular logarithmic-window kernel, with its continuous value at zero. -/
def logPhaseKernel (x : ℝ) : ℂ :=
  Complex.exp (-((x : ℂ) / 2) * Complex.I) * (Real.sinc (x / 2) : ℂ)

@[simp] theorem logPhaseKernel_zero : logPhaseKernel 0 = 1 := by simp [logPhaseKernel]

theorem continuous_logPhaseKernel : Continuous logPhaseKernel := by
  unfold logPhaseKernel
  exact (Complex.continuous_exp.comp (by fun_prop)).mul
    (Complex.continuous_ofReal.comp (Real.continuous_sinc.comp (by fun_prop)))

theorem norm_logPhaseKernel (x : ℝ) : ‖logPhaseKernel x‖ = |Real.sinc (x / 2)| := by
  have he : (-((x : ℂ) / 2) * Complex.I).re = 0 := by
    rw [show (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) by push_cast; rfl]
    simp [Complex.mul_re]
  rw [logPhaseKernel, norm_mul, Complex.norm_exp, he, Real.exp_zero, one_mul,
    Complex.norm_real, Real.norm_eq_abs]

theorem norm_logPhaseKernel_lt_one {x : ℝ} (hx : x ≠ 0) : ‖logPhaseKernel x‖ < 1 := by
  have hh : x / 2 ≠ 0 := div_ne_zero hx (by norm_num)
  rw [norm_logPhaseKernel, Real.sinc_of_ne_zero hh, abs_div, div_lt_one (abs_pos.mpr hh)]
  exact Real.abs_sin_lt_abs hh

/-- The two-ordinate limiting determinant is positive at every nonzero scaled gap. -/
theorem logPhaseKernel_pairDet_pos {x : ℝ} (hx : x ≠ 0) :
    0 < 1 - ‖logPhaseKernel x‖ ^ 2 := by
  have h := norm_logPhaseKernel_lt_one hx
  nlinarith [norm_nonneg (logPhaseKernel x)]

theorem norm_logPhaseKernel_le {x : ℝ} (hx : x ≠ 0) :
    ‖logPhaseKernel x‖ ≤ 2 / |x| := by
  have hh : x / 2 ≠ 0 := div_ne_zero hx (by norm_num)
  rw [norm_logPhaseKernel, Real.sinc_of_ne_zero hh, abs_div, abs_div,
    show |(2 : ℝ)| = 2 by norm_num]
  calc
    _ ≤ 1 / (|x| / 2) := div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)
    _ = _ := by ring

theorem mul_logPhaseKernel (v : ℝ) :
    (v : ℂ) * Complex.I * logPhaseKernel v =
      1 - Complex.exp (-(v : ℂ) * Complex.I) := by
  by_cases hv : v = 0
  · simp [hv]
  let z : ℂ := (v : ℂ) / 2
  have hz : z ≠ 0 := div_ne_zero (by exact_mod_cast hv) (by norm_num)
  have hreal : ((v / 2 : ℝ) : ℂ) = z := by dsimp only [z]; push_cast; rfl
  have hs : Complex.sin z * (2 * Complex.I) =
      Complex.exp (z * Complex.I) - Complex.exp (-z * Complex.I) := by
    unfold Complex.sin
    calc
      _ = (Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) * Complex.I ^ 2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [logPhaseKernel, Real.sinc_of_ne_zero (div_ne_zero hv (by norm_num)),
    Complex.ofReal_div, Complex.ofReal_sin, hreal]
  calc
    _ = Complex.exp (-z * Complex.I) * (Complex.sin z * (2 * Complex.I)) := by
      have hvz : (v : ℂ) = 2 * z := by dsimp only [z]; ring
      change (v : ℂ) * Complex.I *
        (Complex.exp (-z * Complex.I) * (Complex.sin z / z)) = _
      rw [hvz]
      field_simp [hz]
    _ = _ := by
      rw [hs, mul_sub, ← Complex.exp_add, ← Complex.exp_add]
      have h₁ : -z * Complex.I + z * Complex.I = 0 := by ring
      have h₂ : -z * Complex.I + -z * Complex.I = -(v : ℂ) * Complex.I := by
        dsimp only [z]; ring
      rw [h₁, h₂, Complex.exp_zero]

theorem powerPhase_eq_exp_log (v : ℝ) (N : ℕ) :
    powerPhase v N = Complex.exp (-((v * Real.log ((N : ℝ) + 1) : ℝ) : ℂ) * Complex.I) := by
  have hp : 0 < (N : ℝ) + 1 := by positivity
  have hc : (N : ℂ) + 1 = ((((N : ℝ) + 1) : ℝ) : ℂ) := by push_cast; rfl
  rw [powerPhase, hc, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
    ← Complex.ofReal_log hp.le, Complex.ofReal_mul]
  congr 1
  ring

/-- A finite microscopic approximation with no reciprocal gap in the error. -/
theorem harmonicPhaseSum_sub_logPhaseKernel_le (v : ℝ) (N : ℕ) :
    ‖(∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-1 - (v : ℂ) * Complex.I)) -
      (Real.log ((N : ℝ) + 1) : ℂ) * logPhaseKernel (v * Real.log ((N : ℝ) + 1))‖ ≤
      1 + reciprocalSquareMass * ‖(v : ℂ) * Complex.I + 1‖ := by
  let S := ∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-1 - (v : ℂ) * Complex.I)
  let L := Real.log ((N : ℝ) + 1)
  let K := logPhaseKernel (v * L)
  have hmass : 0 ≤ reciprocalSquareMass := tsum_nonneg (fun _ => by positivity)
  by_cases hv : v = 0
  · subst v
    simpa [phaseSumBudget, add_comm] using harmonicPhaseSum_sub_diag_le 0 N |>.trans
      (show phaseSumBudget 0 ≤ 1 + reciprocalSquareMass by simp [phaseSumBudget, hmass])
  have he : (v : ℂ) * Complex.I * ((L : ℂ) * K) = 1 - powerPhase v N := by
    have h := mul_logPhaseKernel (v * L)
    rw [powerPhase_eq_exp_log]
    change _ = 1 - Complex.exp (-((v * L : ℝ) : ℂ) * Complex.I)
    rw [← h, Complex.ofReal_mul]
    dsimp only [K]
    ring
  have hS := phase_sum_exact v N
  change (v : ℂ) * Complex.I * S =
    1 - powerPhase v N - ∑ n ∈ Finset.range N, phaseSlopeError v n / ((n : ℂ) + 1) at hS
  have h := phaseSlopeError_sum_bound v N
  have hd : (v : ℂ) * Complex.I * (S - (L : ℂ) * K) =
      -(∑ n ∈ Finset.range N, phaseSlopeError v n / ((n : ℂ) + 1)) := by
    rw [mul_sub, hS, he]
    ring
  have hnorm : ‖(v : ℂ) * Complex.I‖ = |v| := by simp [Real.norm_eq_abs]
  have hmul : |v| * ‖S - (L : ℂ) * K‖ ≤
      |v| * ‖(v : ℂ) * Complex.I + 1‖ * reciprocalSquareMass := by
    calc
      _ = ‖∑ n ∈ Finset.range N, phaseSlopeError v n / ((n : ℂ) + 1)‖ := by
        rw [← hnorm, ← norm_mul, hd, norm_neg]
      _ ≤ _ := h
  change ‖S - (L : ℂ) * K‖ ≤ _
  have h0 : ‖S - (L : ℂ) * K‖ ≤
      ‖(v : ℂ) * Complex.I + 1‖ * reciprocalSquareMass := by
    by_contra! hn
    have hh := mul_lt_mul_of_pos_left hn (abs_pos.mpr hv)
    rw [← mul_assoc] at hh
    exact (not_lt_of_ge hmul) hh
  linarith only [h0]

end RiemannResearch.RH.Pareto.SpectralObstruction

namespace RiemannResearch.RH.Pareto.ResidueMellin
open SpectralObstruction
open MellinFrequency (criticalPoint)

/-- The grouped cross coefficient with the critical Mellin factors removed. -/
def phaseStrippedCross (t u : ℝ) (N : ℕ) : ℂ :=
  classCross t u N / (criticalPoint t * star (criticalPoint u))

/-- The error budget at microscopic separation remains finite at a collision. -/
def microscopicCrossBudget (t u : ℝ) : ℝ :=
  2 * (1 + criticalTailMass) ^ 2 + 1 +
    reciprocalSquareMass * (1 + ‖criticalPoint t + 1‖ + ‖criticalPoint u + 1‖ +
      ‖((t - u : ℝ) : ℂ) * Complex.I + 1‖)

/-- Quantitative microscopic coefficient for the actual grouped Pareto rows. -/
theorem phaseStrippedCross_sub_logPhaseKernel_le (t u : ℝ) (N : ℕ) (hN : 0 < N) :
    ‖phaseStrippedCross t u N - logPhaseKernel ((t - u) * Real.log ((N : ℝ) + 1))‖ ≤
      microscopicCrossBudget t u / Real.log ((N : ℝ) + 1) := by
  let L := Real.log ((N : ℝ) + 1)
  let a := criticalPoint t * star (criticalPoint u)
  let K := logPhaseKernel ((t - u) * L)
  let S := ∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-1 - ((t - u : ℝ) : ℂ) * Complex.I)
  have hL : 0 < L := Real.log_pos (by
    have hp : 0 < (N : ℝ) := by exact_mod_cast hN
    linarith)
  have ha : a ≠ 0 := mul_ne_zero (MellinFrequency.criticalPoint_ne_zero t)
    (by simp [MellinFrequency.criticalPoint_ne_zero])
  have hLC : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  have h₁ := classCrossSum_sub_phaseSum_le t u N
  have h₂ := harmonicPhaseSum_sub_logPhaseKernel_le (t - u) N
  change ‖S - (L : ℂ) * K‖ ≤ _ at h₂
  have han : ‖a‖ = ‖criticalPoint t‖ * ‖criticalPoint u‖ := by simp [a]
  rw [← han] at h₁
  have h₃ : ‖classCrossSum t u N - (L : ℂ) * a * K‖ ≤ ‖a‖ * microscopicCrossBudget t u := by
    rw [show classCrossSum t u N - (L : ℂ) * a * K =
      (classCrossSum t u N - a * S) + a * (S - (L : ℂ) * K) by ring]
    have h₂' : ‖a * (S - (L : ℂ) * K)‖ ≤
        ‖a‖ * (1 + reciprocalSquareMass * ‖((t - u : ℝ) : ℂ) * Complex.I + 1‖) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left h₂ (norm_nonneg _)
    refine ((norm_add_le _ _).trans (add_le_add h₁ h₂')).trans_eq ?_
    unfold microscopicCrossBudget
    ring
  have hform : phaseStrippedCross t u N - K =
      (classCrossSum t u N - (L : ℂ) * a * K) / ((L : ℂ) * a) := by
    change classCrossSum t u N / (L : ℂ) / a - K = _
    field_simp [hLC, ha]
  change ‖phaseStrippedCross t u N - K‖ ≤ microscopicCrossBudget t u / L
  rw [hform, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
  refine (div_le_div_of_nonneg_right h₃ (mul_nonneg hL.le (norm_nonneg _))).trans_eq ?_
  field_simp [hL.ne', norm_ne_zero_iff.mpr ha]

theorem phaseStrippedCross_microscopic_tendsto (N : ℕ → ℕ) (t u : ℕ → ℝ) (v : ℝ)
    (hN : ∀ᶠ j in atTop, 0 < N j)
    (hv : Tendsto (fun j => (t j - u j) * Real.log ((N j : ℝ) + 1)) atTop (𝓝 v))
    (hE : Tendsto (fun j => microscopicCrossBudget (t j) (u j) /
      Real.log ((N j : ℝ) + 1)) atTop (𝓝 0)) :
    Tendsto (fun j => phaseStrippedCross (t j) (u j) (N j)) atTop (𝓝 (logPhaseKernel v)) := by
  have hdiff : Tendsto (fun j => phaseStrippedCross (t j) (u j) (N j) -
      logPhaseKernel ((t j - u j) * Real.log ((N j : ℝ) + 1))) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
      (hN.mono (fun j hj => phaseStrippedCross_sub_logPhaseKernel_le (t j) (u j) (N j) hj)) hE
  have hk := (continuous_logPhaseKernel.tendsto v).comp hv
  simpa only [Function.comp_apply, Pi.add_apply, sub_add_cancel, zero_add] using hdiff.add hk

end RiemannResearch.RH.Pareto.ResidueMellin

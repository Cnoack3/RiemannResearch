/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteStrictTailSecondMoment
import RiemannResearch.Analysis.ActualZeroTailLayerCake
import RiemannResearch.Analysis.ActualZeroSelbergDensity
import RiemannResearch.Analysis.ActualZeroSublinearEnergy
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Explicit logarithmic rate for actual horizontal zero energy

Source: user-provided layer-cake deduction of 22 October 2026.
Ford--Zaharescu, "On the distribution of imaginary parts of zeros of the
Riemann zeta function", Lemma 2, p. 7,
https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf ,
supports the classical density statement used as an explicit input.

All actual positive-height zeros and analytic multiplicities are retained.
From SelbergDensityBound T C a, the proved rate is
E(T)/T <= 4 C/(a^2 log T), and a=1/4 gives 64 C/log T.
UniformSelbergDensity supplies the big-O deduction; an eventual logarithmic
bound supplies convergence to zero.

The classical Selberg estimate is unconditional mathematics. Its analytic
provider is not formalized here: these density-dependent deductions remain
conditional research reductions in Lean. No RH premise or new axiom is used.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace RiemannResearch.Analysis.ActualZeroOrdinate
open Filter
open scoped Topology

/-- Exact actual-zero layer cake; every analytic occurrence is counted. -/
theorem horizontalEnergy_eq_strictTail_integral (T : ℝ) :
    horizontalEnergy T =
      ∫ t in (0 : ℝ)..(1 / 2), strictTail T t * (2 * t) := by
  rw [horizontalEnergy, realSum_eq_copies]
  simpa only [strictTail, copyDisplacement, sq_abs] using
    FiniteStrictTail.secondMoment_eq_integral
      (Finset.univ : Finset (Copies T)) (copyDisplacement T) (1 / 2)
      (by norm_num) (fun c _ =>
        ⟨abs_nonneg _, (displacement_lt_half c.1.2).le⟩)

theorem horizontalEnergy_le_of_exponential_strictTail
    (T M a : ℝ) (hM : 0 ≤ M) (ha : 0 < a)
    (htail : ∀ t ∈ Icc (0 : ℝ) (1 / 2),
      strictTail T t ≤ M * Real.exp (-a * t)) :
    horizontalEnergy T ≤ 2 * M / a ^ 2 := by
  rw [horizontalEnergy, realSum_eq_copies]
  simpa only [strictTail, copyDisplacement, sq_abs] using
    FiniteStrictTail.secondMoment_le_exponential_tail
      (Finset.univ : Finset (Copies T)) (copyDisplacement T) (1 / 2) M a
      (by norm_num) hM ha
      (fun c _ => ⟨abs_nonneg _, (displacement_lt_half c.1.2).le⟩) htail

theorem horizontalEnergy_div_height_le_log_rate
    (T C a : ℝ) (hT : 1 < T) (hC : 0 ≤ C) (ha : 0 < a)
    (hD : SelbergDensityBound T C a) :
    horizontalEnergy T / T ≤ 4 * C / (a ^ 2 * Real.log T) := by
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  have hbase := horizontalEnergy_le_of_exponential_strictTail
    T (2 * C * T * Real.log T) (a * Real.log T) (by positivity)
    (mul_pos ha hL)
    (fun t ht => by
      simpa only [mul_assoc] using strictTail_of_selbergDensity T C a t hT0 ht hD)
  calc
    _ ≤ (2 * (2 * C * T * Real.log T) / (a * Real.log T) ^ 2) / T :=
      div_le_div_of_nonneg_right hbase hT0.le
    _ = _ := by field_simp [ne_of_gt hT0, ne_of_gt ha, ne_of_gt hL]; ring

theorem horizontalEnergy_div_height_le_selberg_quarter
    (T C : ℝ) (hT : 1 < T) (hC : 0 ≤ C)
    (hD : SelbergDensityBound T C (1 / 4)) :
    0 ≤ horizontalEnergy T / T ∧ horizontalEnergy T / T ≤ 64 * C / Real.log T := by
  refine ⟨div_nonneg (horizontalEnergy_nonneg T) (by linarith), ?_⟩
  convert horizontalEnergy_div_height_le_log_rate T C (1 / 4) hT hC
    (by norm_num) hD using 1; ring

/-- One uniform Selberg provider gives the height-normalized logarithmic big-O bound. -/
theorem horizontalEnergy_div_height_isBigO_inv_log (a : ℝ) (ha : 0 < a)
    (hD : UniformSelbergDensity a) :
    Asymptotics.IsBigO atTop (fun T : ℝ => horizontalEnergy T / T)
      (fun T : ℝ => 1 / Real.log T) := by
  obtain ⟨C, T₀, hC, hT₀, hD⟩ := hD
  refine Asymptotics.IsBigO.of_bound (4 * C / a ^ 2) ?_
  filter_upwards [eventually_ge_atTop T₀] with T hT
  have hT1 : 1 < T := hT₀.trans_le hT
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT1
  rw [Real.norm_eq_abs, abs_of_nonneg
    (div_nonneg (horizontalEnergy_nonneg T) hT0.le),
    Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hL)]
  convert horizontalEnergy_div_height_le_log_rate T C a hT1 hC ha (hD T hT)
    using 1; ring

/-- Any eventual logarithmic rate proves the exact requested limit. -/
theorem sublinearHorizontalEnergy_of_eventual_log_rate (K : ℝ)
    (hbound : ∀ᶠ T : ℝ in atTop, horizontalEnergy T / T ≤ K / Real.log T) :
    SublinearHorizontalEnergy := by
  have hlim : Tendsto (fun T : ℝ => K / Real.log T) atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      ((tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp
        Real.tendsto_log_atTop).const_mul K
  exact squeeze_zero'
    (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      exact div_nonneg (horizontalEnergy_nonneg T) hT.le)
    hbound hlim

end RiemannResearch.Analysis.ActualZeroOrdinate

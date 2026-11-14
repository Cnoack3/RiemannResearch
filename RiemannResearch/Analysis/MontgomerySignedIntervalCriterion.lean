/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomeryIntervalCriterion
import RiemannResearch.Analysis.MontgomeryIntervalIdentity
import RiemannResearch.Analysis.ActualZeroCountNormalization
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! # The exact signed arithmetic obligation for Montgomery interval averages

The interval identity and the unconditional zero-count normalization reduce
all interval averages above one to a countable family of signed cancellation
limits. These limits remain open. Source for the interval-average target:
Carneiro--Milinovich--Ramos, https://arxiv.org/abs/2310.01913, equation (1.4).
The equivalence below does not prove PCC, assume RH, or import the published
RH-conditional equivalence between interval averages and PCC.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryFormFactor
open ActualZeroOrdinate

/-- The interval mass with the exact N(T) normalization used in the cited paper. -/
def countNormalizedInterval (T a b : ℝ) : ℝ :=
  (∫ α in a..b, (pairSum (copyOrdinate T) (α * Real.log T)).re) /
    (Zeta23.Ncount 0 T : ℝ)

theorem integral_formFactor_eq_countNormalized (T a b : ℝ)
    (hN : Zeta23.Ncount 0 T ≠ 0) :
    (∫ α in a..b, formFactor T α) =
      countNormalizedInterval T a b *
        ((Zeta23.Ncount 0 T : ℝ) / (T * Real.log T / (2 * Real.pi))) := by
  have hNr : (Zeta23.Ncount 0 T : ℝ) ≠ 0 := by exact_mod_cast hN
  simp only [formFactor, countNormalizedInterval, intervalIntegral.integral_div]
  field_simp [hNr]
  simp only [mul_comm]

/-- The two published normalization conventions have exactly the same finite
interval limits, using the proved actual zero-count asymptotic. -/
theorem countNormalized_interval_limit_iff (a b v : ℝ) :
    Tendsto (fun T : ℝ => countNormalizedInterval T a b) atTop (𝓝 v) ↔
    Tendsto (fun T : ℝ => ∫ α in a..b, formFactor T α) atTop (𝓝 v) := by
  constructor
  · intro h
    have hh := h.mul tendsto_count_div_mainTerm
    simp only [mul_one] at hh
    apply hh.congr'
    filter_upwards [eventually_count_pos] with T hT
    exact (integral_formFactor_eq_countNormalized T a b (ne_of_gt hT)).symm
  · intro h
    have hh := h.div tendsto_count_div_mainTerm (by norm_num : (1 : ℝ) ≠ 0)
    simp only [div_one] at hh
    apply hh.congr'
    filter_upwards [eventually_count_pos, eventually_gt_atTop (1 : ℝ)] with T hN hT
    change (∫ α in a..b, formFactor T α) /
      ((Zeta23.Ncount 0 T : ℝ) / (T * Real.log T / (2 * Real.pi))) =
      countNormalizedInterval T a b
    rw [integral_formFactor_eq_countNormalized T a b (ne_of_gt hN)]
    have hNr : (Zeta23.Ncount 0 T : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
    have hlog : 0 < Real.log T := Real.log_pos hT
    have hD : T * Real.log T / (2 * Real.pi) ≠ 0 := ne_of_gt (by positivity)
    exact mul_div_cancel_right₀ _ (div_ne_zero hNr hD)

/-- The signed remainder from every pair of distinct occurrence labels. -/
def normalizedOffDiagonalWindow (T a b : ℝ) : ℝ :=
  offDiagonalWindow (copyOrdinate T) (Real.log T) a b /
    (T * Real.log T / (2 * Real.pi))

theorem integral_formFactor_eq_diagonal_add (T a b : ℝ) :
    (∫ α in a..b, formFactor T α) =
      (b - a) * ((Zeta23.Ncount 0 T : ℝ) / (T * Real.log T / (2 * Real.pi))) +
      normalizedOffDiagonalWindow T a b := by
  rw [integral_formFactor_diagonal]
  unfold normalizedOffDiagonalWindow
  ring

/-- For each fixed interval, its expected mass is equivalent to cancellation
of the complete signed remainder; no unsigned majorant is substituted. -/
theorem interval_limit_iff_signed_cancellation (a b : ℝ) :
    Tendsto (fun T : ℝ => ∫ α in a..b, formFactor T α) atTop (𝓝 (b - a)) ↔
    Tendsto (fun T : ℝ => normalizedOffDiagonalWindow T a b) atTop (𝓝 0) := by
  have hd : Tendsto
      (fun T : ℝ => (b - a) * ((Zeta23.Ncount 0 T : ℝ) /
        (T * Real.log T / (2 * Real.pi)))) atTop (𝓝 (b - a)) := by
    simpa only [mul_one] using tendsto_count_div_mainTerm.const_mul (b - a)
  constructor
  · intro h
    have hh := h.sub hd
    simpa only [integral_formFactor_eq_diagonal_add, add_sub_cancel_left, sub_self]
      using hh
  · intro h
    have hh := hd.add h
    simpa only [← integral_formFactor_eq_diagonal_add, add_zero] using hh

/-- Open arithmetic target: signed cancellation on rational anchored intervals. -/
def RationalSignedCancellation : Prop :=
  ∀ q : ℚ, 1 < q → Tendsto
    (fun T : ℝ => normalizedOffDiagonalWindow T 1 (q : ℝ)) atTop (𝓝 0)

theorem rationalAnchoredLimit_iff_signedCancellation :
    RationalAnchoredLimit ↔ RationalSignedCancellation := by
  constructor
  · intro h q hq
    exact (interval_limit_iff_signed_cancellation 1 q).mp (h q hq)
  · intro h q hq
    exact (interval_limit_iff_signed_cancellation 1 q).mpr (h q hq)

/-- Checked equivalence with an explicitly open arithmetic condition. -/
theorem intervalAverageLimit_iff_rationalSignedCancellation :
    IntervalAverageLimit ↔ RationalSignedCancellation :=
  rationalAnchoredLimit_iff_intervalAverageLimit.symm.trans
    rationalAnchoredLimit_iff_signedCancellation

end RiemannResearch.Analysis.MontgomeryFormFactor

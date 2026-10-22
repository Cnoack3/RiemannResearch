/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualConsecutiveOrdinates
import RiemannResearch.Analysis.ConsecutivePhaseTaylor
import RiemannResearch.Analysis.OrdinateLagEquidistribution
import RiemannResearch.Analysis.ActualRationalFMZLimits

/-!
# Consecutive Fourier transport on the actual zeta-zero cutoffs

Source: the consecutive-ordinate argument of 2026-10-11, using
Ford--Zaharescu, https://ford126.web.illinois.edu/wwwpapers/fz.pdf, and
Fujii's unconditional gap estimates recorded in Ivić, arXiv:1610.01317.
The references support the classical analytic inputs, not a novelty claim.

The finite identities here are unconditional theorems about actual zeta zeros
with analytic multiplicity. The final pair is padded to T, and the exact
replacement by an external next ordinate is in ActualConsecutiveOrdinates.
The rational asymptotic theorem explicitly retains Selberg density and the
vanishing squared-gap energy per unit height as formalization obligations.
Neither input is a new axiom and neither theorem assumes RH.
-/

noncomputable section
open Filter Zeta23
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.ActualZeroOrdinate
open OrdinateLagEquidistribution

/-- The actual chronological pair sum, with its last endpoint at T. -/
def cutoffPairSum (T a b : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (Ncount 0 T),
    ZeroOrdinate.phase a (cutoffOrdinate T j) *
      ZeroOrdinate.phase b (cutoffOrdinate T (j+1))

/-- The full squared-gap energy, including the final truncated gap to T. -/
def cutoffGapEnergy (T : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (Ncount 0 T), (cutoffGap T j)^2

theorem cutoffGapEnergy_nonneg (T : ℝ) : 0 ≤ cutoffGapEnergy T :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Exact signed Fourier transport on actual zero copies. -/
theorem cutoffPairSum_transport_eq (T a b c : ℝ) (hc : b = c * (a+b)) :
    cutoffPairSum T a b = ordinateSum T (a+b) +
      (c : ℂ) * (ZeroOrdinate.phase (a+b) T -
        ZeroOrdinate.phase (a+b) (cutoffOrdinate T 0)) +
      OrdinateLagPhase.consecutiveTransportDefect
        (cutoffOrdinate T) (Ncount 0 T) (a+b) b c := by
  simpa only [cutoffPairSum, lagPhase_eq_zeroOrdinatePhase,
    cutoffOrdinate_phase_sum, cutoffOrdinate_at_count] using
    OrdinateLagPhase.consecutive_phase_transport_eq
      (cutoffOrdinate T) (Ncount 0 T) a b c hc

theorem norm_cutoff_transport_defect_le (T q b c : ℝ) :
    ‖OrdinateLagPhase.consecutiveTransportDefect
      (cutoffOrdinate T) (Ncount 0 T) q b c‖ ≤
      2 * (b^2 + |c| * q^2) * cutoffGapEnergy T := by
  exact OrdinateLagPhase.norm_consecutiveTransportDefect_le
    (cutoffOrdinate T) (Ncount 0 T) q b c

/-- The endpoint contribution stays explicit alongside the squared-gap term. -/
theorem norm_cutoffPairSum_sub_ordinateSum_le
    (T a b c : ℝ) (hc : b = c * (a+b)) :
    ‖cutoffPairSum T a b - ordinateSum T (a+b)‖ ≤
      2 * |c| + 2 * (b^2 + |c| * (a+b)^2) * cutoffGapEnergy T := by
  rw [cutoffPairSum_transport_eq T a b c hc]
  have he : ordinateSum T (a+b) +
      (c : ℂ) * (ZeroOrdinate.phase (a+b) T -
        ZeroOrdinate.phase (a+b) (cutoffOrdinate T 0)) +
      OrdinateLagPhase.consecutiveTransportDefect
        (cutoffOrdinate T) (Ncount 0 T) (a+b) b c - ordinateSum T (a+b) =
      (c : ℂ) * (ZeroOrdinate.phase (a+b) T -
        ZeroOrdinate.phase (a+b) (cutoffOrdinate T 0)) +
      OrdinateLagPhase.consecutiveTransportDefect
        (cutoffOrdinate T) (Ncount 0 T) (a+b) b c := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add _ (norm_cutoff_transport_defect_le T (a+b) b c)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |c| * (‖ZeroOrdinate.phase (a+b) T‖ +
        ‖ZeroOrdinate.phase (a+b) (cutoffOrdinate T 0)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (abs_nonneg c)
    _ = _ := by simp only [ZeroOrdinate.phase_norm]; ring

/-- Exact energy assumption used for the zeta specialization below.
Fujii's classical theorem implies it, but is not asserted by this definition. -/
def VanishingCutoffGapEnergy : Prop :=
  Tendsto (fun T : ℝ => cutoffGapEnergy T / T) atTop (𝓝 0)

/-- Consecutive transport preserves height-normalized nonresonant modes. -/
theorem cutoffPair_difference_div_tendsto_zero (a b c : ℝ)
    (hc : b = c * (a+b)) (hgap : VanishingCutoffGapEnergy) :
    Tendsto (fun T : ℝ =>
      (cutoffPairSum T a b - ordinateSum T (a+b)) / (T : ℂ))
      atTop (𝓝 0) := by
  have hfirst : Tendsto (fun T : ℝ => (2 * |c|) / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hsecond := hgap.const_mul (2 * (b^2 + |c| * (a+b)^2))
  have hmajor : Tendsto (fun T : ℝ =>
      (2 * |c| + 2 * (b^2 + |c| * (a+b)^2) * cutoffGapEnergy T) / T)
      atTop (𝓝 0) := by
    simpa only [add_div, mul_div_assoc, mul_zero, add_zero] using hfirst.add hsecond
  apply squeeze_zero_norm' _ hmajor
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  exact div_le_div_of_nonneg_right
    (norm_cutoffPairSum_sub_ordinateSum_le T a b c hc) hT.le

/-- Actual rational prime-power main term for consecutive pairs.
Only the named Selberg and gap-energy analytic obligations remain. -/
theorem tendsto_cutoffPair_rational_div_of_selberg_gap
    {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n) (a b : ℝ)
    (hab : a+b = Real.log ((n : ℝ) / (m : ℝ)))
    (hD : UniformSelbergDensity (1/4)) (hgap : VanishingCutoffGapEnergy) :
    Tendsto (fun T : ℝ => cutoffPairSum T a b / (T : ℂ))
      atTop (𝓝 (-(rationalLandauMain n m : ℂ))) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hmnR : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
  have hq : a+b ≠ 0 := by
    rw [hab]
    exact (Real.log_pos ((one_lt_div hm0).mpr hmnR)).ne'
  have hc : b = (b / (a+b)) * (a+b) := by field_simp [hq]
  have hd := cutoffPair_difference_div_tendsto_zero a b (b/(a+b)) hc hgap
  have hmode := tendsto_rational_ordinate_div_of_uniformSelberg hm hmn hD
  rw [← hab] at hmode
  have h := hd.add hmode
  simpa only [← add_div, sub_add_cancel, zero_add] using h

end RiemannResearch.Analysis.ActualZeroOrdinate

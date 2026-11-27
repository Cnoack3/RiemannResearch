import RiemannResearch.RH.MixedCaptureLegalTrials
import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.ParetoNegativeMassHead
import RiemannResearch.RH.ThresholdHilbertL1
import RiemannResearch.RH.ScreenedFeketeDefect
import RiemannResearch.RH.ScreenedParityPhysicalBounds
import RiemannResearch.RH.MixedConductorMetricLifting
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# Choosing the mean section and testing the negative mass of finite screened parity

The user proposed using the split mean sequence to attain the ambient norm.
The least norm of a legal mean section is already known. The sign test below
uses the literal finite mixed projection at cutoff L and allows the number of
physical sites read to tend to infinity at any rate.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.ScreenedParityNegativeMass
open CoefficientStabilization

private theorem screened_eq_one_iff_rh : normalizedScreenedTwo = hilbertOne ↔ RiemannHypothesis :=
  (ScreenedFeketeDefect.defect_fekete_rate_zero_iff_screened (by decide : 1 < 2)).symm.trans
    (ScreenedFeketeDefect.defect_fekete_rate_zero_iff_rh (by decide : 1 < 2))

/-- A contractive right inverse of the original, unscaled legal mean exists exactly under RH. -/
theorem contractive_legal_section_iff_rh :
    (∃ s : ℝ →L[ℝ] closedSpace,
      legalPacketMean.comp s = ContinuousLinearMap.id ℝ ℝ ∧ ‖s‖ ≤ 1) ↔ RiemannHypothesis := by
  rw [exists_legalMeanSection_norm_le_iff]
  constructor
  · intro h
    exact riemannHypothesis_of_normalizedScreenedTwo_norm_eq_one
      (le_antisymm h one_le_norm_normalizedScreenedTwo)
  · intro h
    rw [screened_eq_one_iff_rh.mpr h]
    nlinarith [hilbertOne_norm_sq, norm_nonneg hilbertOne]

/-- It suffices to eliminate the negative mass of the screened vector. -/
theorem screened_negativeMass_zero_iff_rh :
    hilbertNegativeMass normalizedScreenedTwo = 0 ↔ RiemannHypothesis := by
  rw [negativeMass_eq_zero_iff, ← screened_eq_one_iff_rh]
  constructor
  · intro h
    exact normalizedScreenedTwo_eq_one_of_oneSidedBound (Or.inl ⟨0,h⟩)
  · intro h n hn
    rw [h, hilbertOne_sequence]
    simp [zeroAnchor, hn.ne']

/-- A sign may be verified along a different unbounded set of conductors at each site. -/
theorem rh_iff_frequently_nonnegative_at_each_site :
    RiemannHypothesis ↔ ∀ n : ℕ, 0 < n →
      ∃ᶠ L : ℕ in atTop, 0 ≤ hilbertSequence (fixedTwoTrial L) n := by
  constructor
  · intro h n hn
    have ht : Tendsto (fun L => hilbertSequence (fixedTwoTrial L) n) atTop
        (𝓝 (hilbertSequence normalizedScreenedTwo n)) := by
      simpa only [Function.comp_def, anchoredEvaluationCLM_apply] using
        (anchoredEvaluationCLM n).continuous.continuousAt.tendsto.comp fixedTwoTrial_tendsto
    have hp : 0 < hilbertSequence normalizedScreenedTwo n := by
      rw [screened_eq_one_iff_rh.mpr h, hilbertOne_sequence]
      simp [zeroAnchor, hn.ne']
    exact ((ht.eventually_const_lt hp).mono (fun _ hL => hL.le)).frequently
  · intro h
    exact screened_eq_one_iff_rh.mp
      (screenedTwo_eq_one_of_cofinal_trial_bounds (Or.inl ⟨0, h⟩))

/-- A complete norm enclosure certifies positivity at every site satisfying this inequality. -/
theorem site_pos_of_variance {n : ℕ} (hn : 0 < n)
    (h : ((n : ℝ) * ((n : ℝ)+1)-1) * (‖normalizedScreenedTwo‖^2-1) < 1) :
    0 < hilbertSequence normalizedScreenedTwo n := by
  have he := screenedTwo_coordinate_sq_le n hn
  rw [← CenteredMeanSnake.boundary_norm, CenteredMeanSnake.boundary_norm_sq] at he
  by_contra! hx
  nlinarith only [he.trans_lt h, hx, sq_nonneg (hilbertSequence normalizedScreenedTwo n)]

/-- The repository's period-5040 complete trial already proves strict positivity through site four. -/
theorem screened_first_four_positive {n : ℕ} (hn : 0 < n) (h4 : n ≤ 4) :
    0 < hilbertSequence normalizedScreenedTwo n := by
  apply site_pos_of_variance hn
  have hb := normalizedScreenedTwo_norm_sq_lt_period5040
  interval_cases n <;> norm_num <;> linarith

/-- Signed finite-head test with both the physical tail and the change of trial retained. -/
theorem negativeMassHead_error (K : ℕ) (v : ThresholdHilbert) :
    |negativeMassHead K v - hilbertNegativeMass normalizedScreenedTwo| ≤
      ‖v‖ * Real.sqrt (1 / ((K : ℝ)+1)) + ‖v-normalizedScreenedTwo‖ := by
  have hh : |negativeMassHead K v - hilbertNegativeMass v| ≤
      ‖v‖ * Real.sqrt (1 / ((K : ℝ)+1)) := by
    rw [abs_of_nonpos (sub_nonpos.mpr (negativeMassHead_le K v))]
    linarith only [negativeMassHead_truncation_upper K v]
  have hv := (hilbertNegativeMass_abs_sub_le v normalizedScreenedTwo).trans
    (hilbertL1Norm_le_norm (v-normalizedScreenedTwo))
  exact (abs_sub_le _ (hilbertNegativeMass v) _).trans (add_le_add hh hv)

/-- The finite sum over any growing head converges to the actual negative mass.
The omitted tail is bounded by the full trial norm divided by sqrt(head+1). -/
theorem trial_negativeMassHead_tendsto (K : ℕ → ℕ) (hK : Tendsto K atTop atTop) :
    Tendsto (fun L => negativeMassHead (K L) (fixedTwoTrial L)) atTop
      (𝓝 (hilbertNegativeMass normalizedScreenedTwo)) := by
  have hm : Tendsto (fun L => hilbertNegativeMass (fixedTwoTrial L)) atTop
      (𝓝 (hilbertNegativeMass normalizedScreenedTwo)) :=
    hilbertNegativeMass_continuous.continuousAt.tendsto.comp fixedTwoTrial_tendsto
  have hr : Tendsto (fun L => Real.sqrt (1 / ((K L : ℝ)+1))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp
        ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hK)
  have hl : Tendsto (fun L => hilbertNegativeMass (fixedTwoTrial L) -
      ‖fixedTwoTrial L‖ * Real.sqrt (1 / ((K L : ℝ)+1))) atTop
      (𝓝 (hilbertNegativeMass normalizedScreenedTwo)) := by
    simpa only [mul_zero, sub_zero] using hm.sub (fixedTwoTrial_tendsto.norm.mul hr)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl hm
    (fun L => by linarith only [negativeMassHead_truncation_upper (K L) (fixedTwoTrial L)])
    (fun L => negativeMassHead_le (K L) (fixedTwoTrial L))

/-- The analytic obligation on a single sequence of entirely finite signed head sums. -/
theorem trial_negativeMassHead_zero_iff_rh (K : ℕ → ℕ) (hK : Tendsto K atTop atTop) :
    Tendsto (fun L => negativeMassHead (K L) (fixedTwoTrial L)) atTop (𝓝 0) ↔
      RiemannHypothesis := by
  have ht := trial_negativeMassHead_tendsto K hK
  exact ⟨fun hz => screened_negativeMass_zero_iff_rh.mp (tendsto_nhds_unique ht hz),
    fun h => screened_negativeMass_zero_iff_rh.mpr h ▸ ht⟩

end RiemannResearch.RH.Pareto.PrimePowerSchur.ScreenedParityNegativeMass

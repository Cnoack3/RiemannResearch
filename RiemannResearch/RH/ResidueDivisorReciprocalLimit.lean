import RiemannResearch.RH.ResidueCorrectionDivisorAbel
import RiemannResearch.RH.ReciprocalGramCorrection
import RiemannResearch.RH.MovingReciprocalCharge
import RiemannResearch.Analysis.FiniteHarmonicBounds

/-!
# The reciprocal mean of certified signed divisor values

Source: continuation of the supplied RH_Lean_Continuation_Handoff_2026-09-29,
combined with the already formalized Balazard reciprocal-charge theorem
(https://arxiv.org/abs/1812.04309, Propositions 6--7), actual projection limits,
and the residual dilation identity. The paper supports the reciprocal-charge
input; the finite certified-cutoff assembly here is independently developed.
No mathematical novelty claim is made.

Established: the complete growing approximation error is at most
`harmonic n / sqrt(n+1)`, and the finite signed statistic converges to minus
the first residual coordinate. Positive residual energy forces negative drift.
The one-sided arithmetic lower estimate in the final RH implication is Open.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
open GramMobiusCorrection

/-- The actual certified, signed progression values, summed with reciprocal
conductor weights. Stage n contains conductors 2 through n+1; this sum ends at n. -/
def divisorReciprocalStatistic (n : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 2 n,
    correctionDivisorAbelValue n d (correctionPeriodCutoff n d) / (d : ℝ)

/-- Uniform truncation control for the growing arithmetic head. -/
theorem divisorReciprocalStatistic_error_le (n : ℕ) :
    |divisorReciprocalStatistic n -
      ∑ d ∈ Finset.Icc 2 n, correction n d / (d : ℝ)| ≤
      (harmonic n : ℝ) / Real.sqrt ((n : ℝ) + 1) := by
  have he (d : ℕ) (hd : d ∈ Finset.Icc 2 n) :
      |correctionDivisorAbelValue n d (correctionPeriodCutoff n d) - correction n d| ≤
        1 / Real.sqrt ((n : ℝ) + 1) := by
    have hb := correction_sub_period_divisor_sq_le n d
      (by have := (Finset.mem_Icc.mp hd).1; omega) (Finset.mem_Icc.mp hd).2
    rw [sq_abs] at hb
    have ha := Real.abs_le_sqrt hb
    rw [abs_sub_comm] at ha
    simpa only [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one] using ha
  have hhar : (∑ d ∈ Finset.Icc 1 n, (1 : ℝ) / (d : ℝ)) = (harmonic n : ℝ) := by
    simp [harmonic_eq_sum_Icc, one_div]
  have hsub : Finset.Icc 2 n ⊆ Finset.Icc 1 n := by
    intro d hd
    have := Finset.mem_Icc.mp hd
    exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩
  have hh : (∑ d ∈ Finset.Icc 2 n, (1 : ℝ) / (d : ℝ)) ≤ (harmonic n : ℝ) := by
    rw [← hhar]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  unfold divisorReciprocalStatistic
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 2 n,
        |correctionDivisorAbelValue n d (correctionPeriodCutoff n d) / (d : ℝ) -
          correction n d / (d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 2 n,
        (1 / Real.sqrt ((n : ℝ) + 1)) / (d : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [← sub_div, abs_div]
      have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      rw [abs_of_nonneg hd0]
      exact div_le_div_of_nonneg_right (he d hd) (Nat.cast_nonneg d)
    _ = (∑ d ∈ Finset.Icc 2 n, (1 : ℝ) / (d : ℝ)) /
        Real.sqrt ((n : ℝ) + 1) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ _ := div_le_div_of_nonneg_right hh (Real.sqrt_nonneg _)

/-- The complete growing reciprocal error vanishes; the finite estimate is
`harmonic n / sqrt(n+1)`, not a coordinatewise limit interchange. -/
theorem divisorReciprocalStatistic_error_tendsto_zero :
    Tendsto (fun n => divisorReciprocalStatistic n -
      ∑ d ∈ Finset.Icc 2 n, correction n d / (d : ℝ)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using
    squeeze_zero (fun n => abs_nonneg _)
      divisorReciprocalStatistic_error_le
      RiemannResearch.Analysis.harmonic_over_sqrt_succ_tendsto_zero

/-- Unconditional exact limit of the actual finite signed divisor statistic. -/
theorem divisorReciprocalStatistic_tendsto :
    Tendsto divisorReciprocalStatistic atTop
      (𝓝 (-hilbertSequence limitResidual 1)) := by
  have h := divisorReciprocalStatistic_error_tendsto_zero.add
    (truncated_reciprocalCorrection_tendsto id tendsto_id)
  simpa only [id_eq, sub_add_cancel, zero_add] using h

/-- Exact dilation-covariance value, retaining the signed residual correlation. -/
theorem divisorReciprocalStatistic_tendsto_energy_covariance :
    Tendsto divisorReciprocalStatistic atTop
      (𝓝 (-2 * limitEnergy +
        inner ℝ limitResidual (hilbertDilation 2 (by decide) limitResidual))) := by
  have he := firstCoordinate_energy_identity
  have hv : -hilbertSequence limitResidual 1 = -2 * limitEnergy +
      inner ℝ limitResidual (hilbertDilation 2 (by decide) limitResidual) := by linarith
  simpa only [hv] using divisorReciprocalStatistic_tendsto

/-- A nonzero actual residual forces uniform negative drift in these finite
signed arithmetic progression sums. No RH or sign assumption is used. -/
theorem divisorReciprocalStatistic_eventually_negative (hD : 0 < limitEnergy) :
    ∀ᶠ n : ℕ in atTop, divisorReciprocalStatistic n <
      -(2 - Real.sqrt 2) * limitEnergy / 2 := by
  have hs : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hp : 0 < (2 - Real.sqrt 2) * limitEnergy := mul_pos (by linarith) hD
  apply divisorReciprocalStatistic_tendsto.eventually_lt_const
  have hb := reciprocalCorrection_limit_bounds.2
  nlinarith

/-- Exact zero-limit characterization of the actual residual, not an assertion
that either side holds. -/
theorem divisorReciprocalStatistic_zero_iff_residual_zero :
    Tendsto divisorReciprocalStatistic atTop (𝓝 0) ↔ limitResidual = 0 := by
  constructor
  · intro h
    have he := tendsto_nhds_unique divisorReciprocalStatistic_tendsto h
    apply firstCoordinate_zero_iff_residual_zero.mp
    linarith
  · intro h
    simpa [h, hilbertSequence] using divisorReciprocalStatistic_tendsto

/-- CONDITIONAL RESEARCH REDUCTION. A single one-sided arithmetic lower estimate
replaces the separate absolute-smallness conditions for every conductor.
The provider of this cofinal lower estimate remains Open. -/
theorem riemannHypothesis_of_divisorReciprocalStatistic_cofinal_lower
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
      -ε < divisorReciprocalStatistic n) : RiemannHypothesis := by
  apply riemannHypothesis_of_firstCoordinate_zero
  by_contra hne
  have hp : 0 < hilbertSequence limitResidual 1 :=
    lt_of_le_of_ne firstCoordinate_nonneg (Ne.symm hne)
  have he : 0 < hilbertSequence limitResidual 1 / 2 := by positivity
  have hlarge : ∀ᶠ n : ℕ in atTop,
      divisorReciprocalStatistic n < -(hilbertSequence limitResidual 1 / 2) :=
    divisorReciprocalStatistic_tendsto.eventually_lt_const (by linarith)
  obtain ⟨n, hn, hn'⟩ := ((hsmall _ he).and_eventually hlarge).exists
  linarith

end RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail

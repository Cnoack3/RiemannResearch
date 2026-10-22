import RiemannResearch.Analysis.FiniteSpectralJensen
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.RH.OptimalTwoCoefficientCriterion
import RiemannResearch.Analysis.FiniteSpectralCriticalFeedback
import RiemannResearch.RH.ParetoActualSpectralLimits
import RiemannResearch.RH.ParetoActualSpectralMomentUpper
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith

/-!
# Actual cofinal critical-margin contrast implies RH

Source: user-requested backwards RH verification, 13 October 2026.
These conditional deductions are independently formalized, without a novelty claim.
No missing arithmetic bound is asserted.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open Filter
open scoped Topology BigOperators
open RiemannResearch.Analysis
open FiniteSpectralBudget FiniteHeadTailSpectralRealization

def compactSpectrumInnerLogScale (n : ℕ) : ℝ :=
  1 + Real.log (1 / compactSpectrumTailEnvelope n)

theorem compactSpectrumInnerLogScale_tendsto_atTop :
    Tendsto compactSpectrumInnerLogScale atTop atTop := by
  have hwithin : Tendsto compactSpectrumTailEnvelope atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨compactSpectrumTailEnvelope_tendsto_zero,
      Filter.Eventually.of_forall compactSpectrumTailEnvelope_pos⟩
  have hinv : Tendsto (fun n => 1 / compactSpectrumTailEnvelope n) atTop atTop := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_nhdsGT_zero.comp hwithin
  have hlog : Tendsto (fun n => Real.log (1 / compactSpectrumTailEnvelope n))
      atTop atTop := Real.tendsto_log_atTop.comp hinv
  apply tendsto_atTop.2
  intro b
  filter_upwards [hlog.eventually (eventually_ge_atTop (b - 1))] with n hn
  dsimp only [compactSpectrumInnerLogScale]
  linarith

/-- Actual conditional RH consumer for the critical moving margin 1/a.
The literal arithmetic contrast estimate remains an explicit hypothesis.
-/
theorem riemannHypothesis_of_actual_compactSpectrum_cofinal_critical_contrast
    (k : ℕ → ℕ) (E : ℕ → ℝ)
    (hk : Tendsto k atTop atTop)
    (hE : Tendsto (fun n => compactSpectrumInnerLogScale (k n) * E n) atTop (𝓝 0))
    (hcontrast : ∀ᶠ n in atTop,
      (doubleLog (compactSpectrumConductorCap (k n)) -
          compactSpectrumDoubleLogScale (k n) +
          compactSpectrumDoubleLogScale (k n) / compactSpectrumInnerLogScale (k n)) *
        correction Finset.univ (compactSpectrumWeight (k n)) (compactSpectrumEigenvalue (k n)) ≤
      compactSpectrumDoubleLogContrast (k n) + compactSpectrumDoubleLogScale (k n) * E n) :
    RiemannHypothesis := by
  let a : ℕ → ℝ := fun n => compactSpectrumInnerLogScale (k n)
  let T : ℕ → ℝ := fun n =>
    correction Finset.univ (compactSpectrumWeight (k n)) (compactSpectrumEigenvalue (k n))
  let J : ℕ → ℝ := fun n =>
    correctionDoubleLog Finset.univ (compactSpectrumWeight (k n)) (compactSpectrumEigenvalue (k n))
  have hz : compactProjectionDefect = 0 := by
    apply defect_eq_zero_of_critical_doubleLog_feedback a T J E compactProjectionDefect
    · exact compactSpectrum_correction_tendsto_defect.comp hk
    · exact compactSpectrumInnerLogScale_tendsto_atTop.comp hk
    · exact hE
    · intro n
      exact correction_nonneg _ _ _
        (fun i _ => compactSpectrumWeight_nonneg (k n) i)
        (fun i _ => compactSpectrumEigenvalue_nonneg (k n) i)
    · apply Filter.Eventually.of_forall
      intro n hnT hninside
      exact correctionDoubleLog_ge_envelope_jensen Finset.univ
        (compactSpectrumWeight (k n)) (compactSpectrumEigenvalue (k n))
        (compactSpectrumTailEnvelope (k n))
        (fun i _ => compactSpectrumWeight_nonneg (k n) i)
        (fun i _ => compactSpectrumEigenvalue_nonneg (k n) i)
        hnT (compactSpectrumTailEnvelope_pos (k n))
        (compactSpectrum_optimizerTail_le_envelope (k n)) hninside
    · filter_upwards [hcontrast] with n hn
      have h₁ := moment_eq_correctionDoubleLog_add_remainder Finset.univ
        (compactSpectrumWeight (k n)) (compactSpectrumEigenvalue (k n))
        (fun i _ => compactSpectrumEigenvalue_nonneg (k n) i)
      have h₂ := compactSpectrum_doubleLog_exact_contrast (k n)
      dsimp only [compactSpectrumDoubleLogRemainder] at h₂
      have hj : J n = doubleLog (compactSpectrumConductorCap (k n)) * T n -
          compactSpectrumDoubleLogContrast (k n) := by
        dsimp only [J, T]
        linarith only [h₁, h₂]
      change (doubleLog (compactSpectrumConductorCap (k n)) - Real.log (a n) +
          Real.log (a n) / a n) * T n ≤
        compactSpectrumDoubleLogContrast (k n) + Real.log (a n) * E n at hn
      nlinarith only [hn, hj]
  have hd0 : Tendsto (fun n => ‖twoThreeDualResidual n‖ ^ 2)
      atTop (𝓝 compactProjectionDefect) :=
    ExhaustiveWalk.walkError_tendsto residueAtom id Function.surjective_id twoThreeDual
  apply riemannHypothesis_of_twoThreeDual_error_tendsto_zero
  simpa only [hz] using hd0

end RiemannResearch.RH.Pareto.CoefficientStabilization

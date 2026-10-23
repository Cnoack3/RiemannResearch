import RiemannResearch.RH.QParetoGramComparison
import RiemannResearch.RH.QParetoMetric
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Exact error budgets for the two actual metric optimizers

Source: user-requested second Ramanujan transfer program, 23 October 2026.
Every finite Q dictionary and every Q target are permitted. The two inverse
solves retain their own source moments. The difference between their complete
errors is resolved into an optimizer displacement and the exact reciprocal
metric correction, strengthening the earlier two-sided comparison bounds.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QParetoGramComparison
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoEquivalence
open QParetoMetric
open RiemannResearch.Analysis.FiniteHilbertGram

variable {ι : Type*} [Fintype ι]

def qFit {v : ι → QHilbert} (hv : LinearIndependent ℝ v) (x : QHilbert) : QHilbert :=
  Fintype.linearCombination ℝ v (inverseCoeff hv x)

def pFit {v : ι → QHilbert} (hv : LinearIndependent ℝ v) (x : QHilbert) : QHilbert :=
  Fintype.linearCombination ℝ v
    (inverseCoeff (paretoFamily_independent hv) (toPareto x))

theorem toPareto_residual_synthesis (v : ι → QHilbert) (x : QHilbert)
    (c : ι → ℝ) :
    toPareto (x - Fintype.linearCombination ℝ v c) =
      toPareto x - Fintype.linearCombination ℝ (paretoFamily v) c := by
  change toParetoLinear (x - Fintype.linearCombination ℝ v c) = _
  rw [map_sub]
  change toPareto x - toPareto (Fintype.linearCombination ℝ v c) = _
  rw [toPareto_synthesis]

/-- Both the optimizer displacement and the complete metric correction survive. -/
theorem optimizer_error_lower_identity {v : ι → QHilbert}
    (hv : LinearIndependent ℝ v) (x : QHilbert) :
    zetaTwo * ‖x - qFit hv x‖ ^ 2 =
      ‖toPareto (x - pFit hv x)‖ ^ 2 +
      ‖toPareto (qFit hv x - pFit hv x)‖ ^ 2 +
      metricCorrection (x - qFit hv x) := by
  have h := residual_completion (paretoFamily_independent hv)
    (toPareto x) (inverseCoeff hv x)
  have hlin :
      Fintype.linearCombination ℝ (paretoFamily v)
        (inverseCoeff hv x -
          inverseCoeff (paretoFamily_independent hv) (toPareto x)) =
      toPareto (qFit hv x - pFit hv x) := by
    calc
      _ = Fintype.linearCombination ℝ (paretoFamily v) (inverseCoeff hv x) -
          Fintype.linearCombination ℝ (paretoFamily v)
            (inverseCoeff (paretoFamily_independent hv) (toPareto x)) := map_sub _ _ _
      _ = toPareto (qFit hv x) - toPareto (pFit hv x) := by
        unfold qFit pFit
        rw [toPareto_synthesis, toPareto_synthesis]
      _ = _ := (toParetoLinear.map_sub (qFit hv x) (pFit hv x)).symm
  rw [hlin] at h
  rw [norm_identity]
  unfold qFit pFit
  rw [toPareto_residual_synthesis, toPareto_residual_synthesis]
  exact congrArg (fun t : ℝ => t + metricCorrection
    (x - Fintype.linearCombination ℝ v (inverseCoeff hv x))) h

/-- Reversing the competitor keeps the full Q displacement with its scale. -/
theorem optimizer_error_upper_identity {v : ι → QHilbert}
    (hv : LinearIndependent ℝ v) (x : QHilbert) :
    ‖toPareto (x - pFit hv x)‖ ^ 2 +
      metricCorrection (x - pFit hv x) =
      zetaTwo * ‖x - qFit hv x‖ ^ 2 +
      zetaTwo * ‖pFit hv x - qFit hv x‖ ^ 2 := by
  have h := residual_completion hv x
    (inverseCoeff (paretoFamily_independent hv) (toPareto x))
  have hlin :
      Fintype.linearCombination ℝ v
        (inverseCoeff (paretoFamily_independent hv) (toPareto x) - inverseCoeff hv x) =
      pFit hv x - qFit hv x := by
    simp only [pFit, qFit, map_sub]
  rw [hlin] at h
  change ‖x - pFit hv x‖ ^ 2 =
    ‖x - qFit hv x‖ ^ 2 + ‖pFit hv x - qFit hv x‖ ^ 2 at h
  rw [← norm_identity, h, mul_add]

theorem optimizer_displacement_bound {v : ι → QHilbert}
    (hv : LinearIndependent ℝ v) (x : QHilbert) :
    ‖toPareto (qFit hv x - pFit hv x)‖ ^ 2 ≤
      zetaTwo * ‖x - qFit hv x‖ ^ 2 -
        ‖toPareto (x - pFit hv x)‖ ^ 2 := by
  linarith [optimizer_error_lower_identity hv x,
    metricCorrection_nonneg (x - qFit hv x)]

/-- Equality in the lower scaled error bound occurs only at exact interpolation. -/
theorem optimizer_lower_equality_iff {v : ι → QHilbert}
    (hv : LinearIndependent ℝ v) (x : QHilbert) :
    ‖toPareto (x - pFit hv x)‖ ^ 2 =
      zetaTwo * ‖x - qFit hv x‖ ^ 2 ↔ x = qFit hv x := by
  constructor
  · intro he
    have h := optimizer_error_lower_identity hv x
    have hc := metricCorrection_nonneg (x - qFit hv x)
    have hs := sq_nonneg ‖toPareto (qFit hv x - pFit hv x)‖
    have hz : metricCorrection (x - qFit hv x) = 0 := by linarith
    exact sub_eq_zero.mp ((metricCorrection_eq_zero_iff _).mp hz)
  · intro he
    have h := optimizer_error_lower_identity hv x
    have hp := sq_nonneg ‖toPareto (x - pFit hv x)‖
    have hs := sq_nonneg ‖toPareto (qFit hv x - pFit hv x)‖
    have hz : x - qFit hv x = 0 := sub_eq_zero.mpr he
    rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
      (metricCorrection_eq_zero_iff _).mpr rfl] at h
    simpa only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] using
      (show ‖toPareto (x - pFit hv x)‖ ^ 2 = 0 by linarith)

/-- Every genuinely nonzero residual gives a strict scaled comparison. -/
theorem optimizer_error_strict {v : ι → QHilbert}
    (hv : LinearIndependent ℝ v) (x : QHilbert) (hx : x ≠ qFit hv x) :
    ‖toPareto (x - pFit hv x)‖ ^ 2 <
      zetaTwo * ‖x - qFit hv x‖ ^ 2 := by
  have hc : 0 < metricCorrection (x - qFit hv x) :=
    lt_of_le_of_ne (metricCorrection_nonneg _) (by
      intro hz
      exact hx (sub_eq_zero.mp ((metricCorrection_eq_zero_iff _).mp hz.symm)))
  linarith [optimizer_error_lower_identity hv x,
    sq_nonneg ‖toPareto (qFit hv x - pFit hv x)‖]

end RiemannResearch.RH.QParetoGramComparison

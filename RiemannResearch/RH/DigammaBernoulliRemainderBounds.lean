import RiemannResearch.RH.DigammaBernoulliRemainder
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

/-!
# Literal digamma: exact arbitrary-order Bernoulli remainder and bounds

All analytic identities are discharged from the actual cell-error HasSum and
actual Bernoulli-polynomial integrals. No Binet or asymptotic formula is supplied
as a hypothesis. The exact infinite remainder is retained before norm bounds.

The following remainder identities are for the actual Gamma logarithmic derivative.

Source for the classical asymptotic statement: NIST DLMF 5.11.2
(https://dlmf.nist.gov/5.11.E2). The formal proof uses the actual digamma
partial-fraction series and Bernoulli integration by parts.
-/

noncomputable section

open Filter Set MeasureTheory intervalIntegral
open scoped BigOperators Topology

namespace RiemannResearch.RH.DigammaBernoulliRemainderBounds

open RiemannResearch.RH.DigammaAsymptotic
open RiemannResearch.RH.DigammaBernoulliCells
open RiemannResearch.RH.DigammaBernoulliRemainder

/-- Consecutive inverse-power Bernoulli terms; the odd terms beyond degree one
vanish by the proved Bernoulli identities. -/
def bernoulliPowerSum (m : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range m, bernoulliCoefficient (j + 2) * (x⁻¹) ^ (j + 2)

/-- The finite coefficient layer has its exact complete HasSum. -/
theorem hasSum_bernoulliDifferences {x : ℝ} (hx : 0 < x) (m : ℕ) :
    HasSum (fun n : ℕ => ∑ j ∈ Finset.range m,
      bernoulliCoefficient (j + 2) *
        inversePowerDifference ((n : ℝ) + x) (j + 2))
      (bernoulliPowerSum m x) := by
  induction m with
  | zero => simp [bernoulliPowerSum]
  | succ m ih =>
      have hlast := (hasSum_inversePowerDifference hx (m + 2) (by omega)).mul_left
        (bernoulliCoefficient (m + 2))
      simpa only [bernoulliPowerSum, Finset.sum_range_succ] using ih.add hlast

/-- The literal complete Bernoulli-cell remainder series, identified using
actual `Complex.digamma` rather than an assumed expansion. -/
theorem hasSum_bernoulliCell_remainder {x : ℝ} (hx : 0 < x) (m : ℕ) :
    HasSum (fun n : ℕ => bernoulliCell (m + 1) ((n : ℝ) + x))
      (bernoulliPowerSum m x -
        (Real.log x - 1 / (2 * x) - (Complex.digamma (x : ℂ)).re)) := by
  have h := (hasSum_bernoulliDifferences hx m).sub (hasSum_cellError hx)
  have hfun : (fun n : ℕ =>
      (∑ j ∈ Finset.range m,
        bernoulliCoefficient (j + 2) *
          inversePowerDifference ((n : ℝ) + x) (j + 2)) -
        cellError ((n : ℝ) + x)) =
      (fun n : ℕ => bernoulliCell (m + 1) ((n : ℝ) + x)) := by
    funext n
    have hn : 0 < (n : ℝ) + x := by positivity
    linarith [cellError_expansion hn m]
  rw [hfun] at h
  exact h

/-- Exact arbitrary-order expansion of literal positive-real digamma, retaining
its full infinite Bernoulli remainder before estimating it. -/
theorem re_digamma_eq_bernoulli_with_tsum_remainder {x : ℝ}
    (hx : 0 < x) (m : ℕ) :
    (Complex.digamma (x : ℂ)).re =
      Real.log x - 1 / (2 * x) - bernoulliPowerSum m x +
        ∑' n : ℕ, bernoulliCell (m + 1) ((n : ℝ) + x) := by
  have hsum := (hasSum_bernoulliCell_remainder hx m).tsum_eq
  linarith

/-- A bound for the actual Bernoulli polynomial on the actual compact cell.
This discharges the constant provider instead of assuming it. -/
theorem exists_bernoulliFun_bound (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u ∈ Icc (0 : ℝ) 1, |bernoulliFun k u| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn (continuous_bernoulliFun k).continuousOn
  have hM0 := hM 0 (by constructor <;> norm_num)
  have hMnonneg : 0 ≤ M := le_trans (norm_nonneg _) hM0
  refine ⟨M, hMnonneg, ?_⟩
  intro u hu
  simpa only [Real.norm_eq_abs] using hM u hu

end RiemannResearch.RH.DigammaBernoulliRemainderBounds

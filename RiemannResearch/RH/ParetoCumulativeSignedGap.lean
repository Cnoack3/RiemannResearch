/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.CumulativeSignedGap
import RiemannResearch.RH.ParetoTrialTailConditions
import RiemannResearch.Analysis.ExhaustiveProjectionWalk

/-!
# Actual cumulative signed Pareto trial criterion

Source: user-provided Green-Pareto-Schur continuation, Appendix A,
and its signed-variation improvement. Complete tails and signed heads remain.
The cumulative arithmetic budget and normalized smallness remain Open.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

open RiemannResearch.Analysis.HeadTailStrengthening

/-- Actual signed physical head paired against the full legal optimizer. -/
def twoThreeTrialHeadPairing (N : ℕ) (u : ThresholdHilbert) : ℝ :=
  inner ℝ (compactHead N (twoThreeDualResidual (N-1)))
    (twoThreeDual - compactHead N u)

/-- Actual cumulative signed-tail consumer. The finite projection normal
equations, residual decrease, and residual limit are discharged internally.
The only analytic provider is the displayed complete cumulative signed budget
with its normalized head-and-negative-prefix-variation numerator. -/
theorem riemannHypothesis_of_cofinal_cumulative_signed_trial_variation
    (u : ℕ → ThresholdHilbert) (a Z : ℕ → ℝ) (k : ℕ → ℕ)
    (hu : ∀ n, u n ∈ finiteSpace (n+2))
    (hk : Tendsto k atTop atTop)
    (hpos : ∀ᶠ n in atTop, 0 < signedGapPrefix a (k n))
    (hbudget : ∀ᶠ n in atTop,
      (∑ i ∈ Finset.range (k n), (twoThreeTrialTailPairing (i+3) (u i) -
        (1-a i)*‖twoThreeDualResidual (i+2)‖^2)) ≤ Z (k n))
    (hsmall : Tendsto (fun n =>
      ((∑ i ∈ Finset.range (k n), (twoThreeTrialHeadPairing (i+3) (u i))) +
        Z (k n) + negativePrefixVariationPenalty a
          (fun i => ‖twoThreeDualResidual (i+2)‖^2) (k n)) /
        signedGapPrefix a (k n)) atTop (𝓝 0)) : RiemannHypothesis := by
  let D : ℕ → ℝ := fun n => ‖twoThreeDualResidual (n+2)‖^2
  let H : ℕ → ℝ := fun n => twoThreeTrialHeadPairing (n+3) (u n)
  let L : ℕ → ℝ := fun n => twoThreeTrialTailPairing (n+3) (u n)
  let delta : ℝ := ‖twoThreeDual - closedSpace.starProjection twoThreeDual‖^2
  have hd0 : Tendsto (fun n => ‖twoThreeDualResidual n‖^2) atTop (𝓝 delta) :=
    RiemannResearch.Analysis.ExhaustiveWalk.walkError_tendsto
      residueAtom id Function.surjective_id twoThreeDual
  have hd : Tendsto D atTop (𝓝 delta) :=
    (tendsto_add_atTop_iff_nat 2).mpr hd0
  have hm0 : Antitone (fun n => ‖twoThreeDualResidual n‖^2) :=
    RiemannResearch.Analysis.ExhaustiveWalk.walkError_antitone
      residueAtom id twoThreeDual
  have hm : Antitone D := by
    intro i j hij
    exact hm0 (Nat.add_le_add_right hij 2)
  have hid : ∀ n, D n = H n + L n := by
    intro n
    simpa only [D, H, L, twoThreeTrialHeadPairing, twoThreeTrialTailPairing,
      show n+3-1=n+2 by omega] using
      twoThree_actual_trial_signed_identity (n+3) (by omega) (u n)
        (by simpa only [show n+3-1=n+2 by omega] using hu n)
  have hz : delta = 0 :=
    limit_eq_zero_of_cofinal_signed_prefix_variation D H L a Z k delta
      (sq_nonneg _) hd hk hm hid hpos hbudget hsmall
  apply riemannHypothesis_of_twoThreeDual_error_tendsto_zero
  simpa only [hz] using hd0

end RiemannResearch.RH.Pareto.CoefficientStabilization

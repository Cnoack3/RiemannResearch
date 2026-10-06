/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.CumulativeRelativeFloor
import RiemannResearch.RH.ParetoCumulativeSignedGap

/-!
# Actual cumulative Pareto absorption with relative negative excursions

All Hilbert normal equations, residual monotonicity, and residual convergence
are discharged by actual Pareto objects. Earlier negative cumulative prefixes
may be unbounded; a fixed relative floor at the selected positive horizons
automatically eliminates their normalized variation penalty. The complete
signed tail budget and normalized signed numerator remain open arithmetic
providers. No unconditional RH proof is claimed.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis.HeadTailStrengthening

/-- The negative-prefix variation estimate is automatic under relative
excursion control; only the signed arithmetic budget is still a provider. -/
theorem riemannHypothesis_of_cofinal_cumulative_signed_trial_relative_floor
    (u : ℕ → ThresholdHilbert) (a Z : ℕ → ℝ) (k : ℕ → ℕ) (C : ℝ)
    (hu : ∀ n, u n ∈ finiteSpace (n+2))
    (hk : Tendsto k atTop atTop) (hC : 0 ≤ C)
    (hmass : Tendsto (fun n => signedGapPrefix a (k n)) atTop atTop)
    (hfloor : ∀ᶠ n in atTop, ∀ i < k n,
      -(C * signedGapPrefix a (k n)) ≤ signedGapPrefix a (i+1))
    (hbudget : ∀ᶠ n in atTop,
      (∑ i ∈ Finset.range (k n), (twoThreeTrialTailPairing (i+3) (u i) -
        (1-a i)*‖twoThreeDualResidual (i+2)‖^2)) ≤ Z (k n))
    (hsmall : Tendsto (fun n =>
      ((∑ i ∈ Finset.range (k n), (twoThreeTrialHeadPairing (i+3) (u i))) +
        Z (k n)) / signedGapPrefix a (k n)) atTop (𝓝 0)) :
    RiemannHypothesis := by
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
    limit_eq_zero_of_cofinal_signed_prefix_relative_floor D H L a Z k delta C
      (sq_nonneg _) hd hk hm hid hC hmass hfloor hbudget hsmall
  apply riemannHypothesis_of_twoThreeDual_error_tendsto_zero
  simpa only [hz] using hd0

end RiemannResearch.RH.Pareto.CoefficientStabilization

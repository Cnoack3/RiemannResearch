import RiemannResearch.RH.ParetoTrialTailConditions
import RiemannResearch.Analysis.MovingSignedGap

/-!
# Moving signed absorption gaps for actual Pareto trials
Source: user-provided Green-Pareto-Schur continuation, Sections 18 and 20.
The normal equations and physical cutoff identity are actual checked objects.
The eventual signed budget and relative error estimates remain arithmetic
hypotheses. No positive lower bound for the gap is assumed.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- A strict fraction tending to one is sufficient when both errors are
little-o of its remaining gap. Entire signed physical tails are retained. -/
theorem riemannHypothesis_of_cofinal_signed_trial_moving_gap
    (u : ℕ → ThresholdHilbert) (k : ℕ → ℕ) (Z gap : ℕ → ℝ)
    (hu : ∀ n, u n ∈ finiteSpace (n+2))
    (hk : Tendsto k atTop atTop)
    (hgap : ∀ᶠ n in atTop, 0 < gap n)
    (hhead : Tendsto (fun n =>
      ‖twoThreeDual - compactHead (k n+3) (u (k n))‖ / gap n)
      atTop (𝓝 0))
    (hZ : Tendsto (fun n => Z n / gap n) atTop (𝓝 0))
    (hsigned : ∀ᶠ n in atTop,
      twoThreeTrialTailPairing (k n+3) (u (k n)) ≤
        (1-gap n) * ‖twoThreeDualResidual (k n+2)‖^2 + Z n) :
    RiemannHypothesis := by
  let D : ℕ → ℝ := fun n => ‖twoThreeDualResidual (k n+2)‖^2
  let E : ℕ → ℝ := fun n =>
    ‖twoThreeDual - compactHead (k n+3) (u (k n))‖
  let H : ℕ → ℝ := fun n =>
    inner ℝ (compactHead (k n+3) (twoThreeDualResidual (k n+2)))
      (twoThreeDual - compactHead (k n+3) (u (k n)))
  let L : ℕ → ℝ := fun n => twoThreeTrialTailPairing (k n+3) (u (k n))
  let delta : ℝ := ‖twoThreeDual - closedSpace.starProjection twoThreeDual‖^2
  have hd0 : Tendsto (fun n => ‖twoThreeDualResidual n‖^2) atTop (𝓝 delta) :=
    RiemannResearch.Analysis.ExhaustiveWalk.walkError_tendsto
      residueAtom id Function.surjective_id twoThreeDual
  have hd : Tendsto D atTop (𝓝 delta) :=
    ((tendsto_add_atTop_iff_nat 2).mpr hd0).comp hk
  have hid : ∀ n, D n = H n + L n := by
    intro n
    simpa only [D, H, L, twoThreeTrialTailPairing,
      show k n+3-1=k n+2 by omega] using
      twoThree_actual_trial_signed_identity (k n+3) (by omega) (u (k n))
        (by simpa only [show k n+3-1=k n+2 by omega] using hu (k n))
  have hhb : ∀ᶠ n in atTop, |H n| ≤ ‖twoThreeDual‖ * E n := by
    apply Filter.Eventually.of_forall
    intro n
    simpa only [H, E, show k n+3-1=k n+2 by omega] using
      twoThree_actual_trial_head_pair_abs_le (k n+3) (u (k n))
  have hz : delta = 0 :=
    RiemannResearch.Analysis.HeadTailStrengthening.limit_eq_zero_of_head_error_moving_gap
      D H L E Z gap delta ‖twoThreeDual‖ (sq_nonneg _) hd hgap hid hhb
      hsigned hhead hZ
  apply riemannHypothesis_of_twoThreeDual_error_tendsto_zero
  simpa only [hz] using hd0

end RiemannResearch.RH.Pareto.CoefficientStabilization

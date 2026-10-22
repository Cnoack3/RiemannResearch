import RiemannResearch.RH.ZetaTwoReciprocalCompactness
import RiemannResearch.Analysis.CompactWeightedFloorNormalization

/-!
# Actual inverse-square weighted floor normalization

Source: exact optimizer cancellation continuation, 8 October 2026. The actual
reciprocal multiplier's finite-head/full-tail estimate is provided by
`ZetaTwoReciprocalCompactness`, and canonical normalized weak convergence is
provided by `NormalizedProjectionWeakConvergence`.

Absolute weighted-floor decay suffices for relative decay in the actual Q
Hilbert space. No Burnol lower bound, rate estimate, RH premise, or abstract
compact-ratio assumption occurs in the theorem below. The absolute floor
decay remains displayed as the arithmetic input.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.ZetaTwoHilbert

open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.NormalizedProjectionWeakConvergence
open RiemannResearch.Analysis.FiniteHeadWeakContinuity
open RiemannResearch.Analysis.CompactWeightedFloorNormalization

/-- The actual reciprocal-coordinate multiplier sends the canonical unit
residuals to zero whenever the unnormalized optimizer residual tends to zero. -/
theorem normalizedWalkResidual_reciprocalEnergy_tendsto_zero
    (v : ℕ → QHilbert) (x : QHilbert)
    (hr : Tendsto (fun n => x - (walkSpan v id n).starProjection x) atTop (𝓝 0))
    (hne : ∀ n, x - (walkSpan v id n).starProjection x ≠ 0) :
    Tendsto (fun n =>
      ‖reciprocalD (x - (walkSpan v id n).starProjection x)‖ ^ 2 /
        ‖x - (walkSpan v id n).starProjection x‖ ^ 2) atTop (𝓝 0) := by
  let u : ℕ → QHilbert := fun n =>
    normalizedResidual (x - (walkSpan v id n).starProjection x)
  have hb : ∀ n, ‖u n‖ ≤ (1 : ℝ) := by
    intro n
    change ‖normalizedResidual (x - (walkSpan v id n).starProjection x)‖ ≤ 1
    rw [normalizedResidual_norm_eq_one _ (hne n)]
  have hweak : ∀ y : QHilbert,
      Tendsto (fun n => inner ℝ y (u n)) atTop (𝓝 0) := by
    intro y
    exact normalizedWalkResidual_inner_tendsto_zero v x hr hne y
  have hnorm := reciprocalD_norm_tendsto_zero_of_weak u 1 (by norm_num) hb hweak
  simpa only [u, normalizedResidual_image_norm_sq, zero_pow (by decide : 2 ≠ 0)]
    using hnorm.pow 2

/-- In the genuine Q Hilbert geometry, absolute weighted-floor decay and its
exact optimizer upper bound imply normalized floor decay. The reciprocal
compact provider and canonical residual convergence are discharged internally. -/
theorem reciprocalWeightedFloor_ratio_tendsto_zero
    (v : ℕ → QHilbert) (x : QHilbert) (ε : ℕ → ℝ)
    (hne : ∀ n, x - (walkSpan v id n).starProjection x ≠ 0)
    (hε : ∀ n, 0 ≤ ε n)
    (hbound : ∀ n, ε n ≤
      ‖reciprocalD (x - (walkSpan v id n).starProjection x)‖ ^ 2)
    (hfloor : Tendsto ε atTop (𝓝 0)) :
    Tendsto
      (fun n => ε n / ‖x - (walkSpan v id n).starProjection x‖ ^ 2)
      atTop (𝓝 0) := by
  have hr : Tendsto (fun n => x - (walkSpan v id n).starProjection x) atTop
      (𝓝 (x - (RiemannResearch.Analysis.ExhaustiveWalk.dictionaryClosure v).starProjection x)) :=
    tendsto_const_nhds.sub (walkProjection_tendsto v id Function.surjective_id x)
  apply weightedFloor_ratio_tendsto_zero
    (fun n => x - (walkSpan v id n).starProjection x)
    (x - (RiemannResearch.Analysis.ExhaustiveWalk.dictionaryClosure v).starProjection x) reciprocalD ε hr
    (fun n => sq_pos_of_pos (norm_pos_iff.mpr (hne n))) hε hbound hfloor
  intro hzero
  apply normalizedWalkResidual_reciprocalEnergy_tendsto_zero v x ?_ hne
  simpa only [hzero] using hr

end RiemannResearch.RH.ZetaTwoHilbert

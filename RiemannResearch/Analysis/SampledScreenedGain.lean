/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteSampledGain
import RiemannResearch.Analysis.FiniteWeightedSampling
import RiemannResearch.Analysis.ScreenedBlockGain
import RiemannResearch.Analysis.ScreenedCarry
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.Order.Field.Basic

/-!
# Sampled certificates for actual screened projection gains

Source: user-directed zero-phase/CRT continuation, 21 October 2026.
These theorems assemble the signed finite sampling certificates with actual
orthogonal projections. The exact single-direction gain identity is the
existing `ScreenedCarry.projection_gain`; its full equality is used before
estimating the source. For a larger new block, the exact nested Pythagorean
identity underlying `screened_score_sq_le_nested_gain` retains all other gains.

The finite realization hypotheses must be provided using the caller's complete
metric, such as `QZeroPhaseSampling.qInner_eq_periodic_weights`. Positive sampled
margins, legality of an arithmetic direction, and cofinal gain accumulation are
not supplied.
-/
noncomputable section

namespace RiemannResearch.Analysis.SampledScreenedGain

open ScreenedCarry FiniteWeightedSampling

variable {H α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Every old-space approximant has the same true pairing against a screened
new direction. In particular the old approximant may be chosen by sampling. -/
theorem old_approximant_screened_source_eq
    (V : Submodule ℝ H) [V.HasOrthogonalProjection]
    (x p z : H) (hp : p ∈ V) :
    inner ℝ (x - p) (screen V z) = inner ℝ (screen V x) (screen V z) := by
  have hp0 : inner ℝ p (screen V z) = 0 := by
    rw [real_inner_comm]
    exact Submodule.starProjection_inner_eq_zero z p hp
  have hproj0 : inner ℝ (V.starProjection x) (screen V z) = 0 := by
    rw [real_inner_comm]
    exact Submodule.starProjection_inner_eq_zero z (V.starProjection x)
      (V.starProjection_apply_mem x)
  change inner ℝ (x - p) (screen V z) =
    inner ℝ (x - V.starProjection x) (screen V z)
  simp only [inner_sub_left, hp0, hproj0]

/-- A source certificate bounds the actual one-direction projection gain;
this is obtained by rewriting the full existing exact gain identity. -/
theorem sampled_source_le_projection_gain
    (V : Submodule ℝ H) [V.HasOrthogonalProjection]
    (x z : H) [(V ⊔ Submodule.span ℝ {z}).HasOrthogonalProjection]
    (hz : screen V z ≠ 0) (sampledSource sampledEnergy error scale : ℝ)
    (henergy : 0 < sampledEnergy)
    (hsource : |sampledSource - inner ℝ (screen V x) z| ≤ error)
    (hcomparison : scale * ‖screen V z‖ ^ 2 ≤ sampledEnergy) :
    scale * (max 0 (|sampledSource| - error)) ^ 2 / sampledEnergy ≤
      ‖screen V x‖ ^ 2 -
        ‖x - (V ⊔ Submodule.span ℝ {z}).starProjection x‖ ^ 2 := by
  rw [projection_gain V x z hz]
  exact FiniteSampledGain.gain_lower_bound_of_source_error
    (sq_pos_of_pos (norm_pos_iff.mpr hz)) henergy hsource hcomparison

/-- The same certificate bounds the actual defect drop for any containing
new space; redundant additional directions cause no difficulty. -/
theorem sampled_source_le_nested_gain
    (V W : Submodule ℝ H) [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hVW : V ≤ W) (x z : H) (hzW : z ∈ W) (hz : screen V z ≠ 0)
    (sampledSource sampledEnergy error scale : ℝ)
    (henergy : 0 < sampledEnergy)
    (hsource : |sampledSource - inner ℝ (screen V z) (screen V x)| ≤ error)
    (hcomparison : scale * ‖screen V z‖ ^ 2 ≤ sampledEnergy) :
    scale * (max 0 (|sampledSource| - error)) ^ 2 / sampledEnergy ≤
      ‖screen V x‖ ^ 2 - ‖screen W x‖ ^ 2 := by
  have hzenergy : 0 < ‖screen V z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hcertificate := FiniteSampledGain.gain_lower_bound_of_source_error
    hzenergy henergy hsource hcomparison
  apply hcertificate.trans
  apply (div_le_iff₀ hzenergy).mpr
  simpa only [mul_comm] using screened_score_sq_le_nested_gain V W hVW x z hzW

/-- A complete finite realization transfers the fully sampled squared budget
to a lower bound on the actual nested projection defect drop. `r` and `g` may
be common-period physical representatives of a residual and screened direction.
-/
theorem finite_sampled_budget_le_nested_gain
    (V W : Submodule ℝ H) [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hVW : V ≤ W) (x z : H) (hzW : z ∈ W) (hz : screen V z ≠ 0)
    (s : Finset α) (w q r g : α → ℝ) (δ error : ℝ)
    (hδ : δ < 1) (herror : 0 ≤ error)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hq : ∀ a ∈ s, |q a - 1| ≤ δ)
    (hsource : form s w r g = inner ℝ (screen V z) (screen V x))
    (henergy : energy s w g = ‖screen V z‖ ^ 2)
    (hbudget : δ ^ 2 * energy s (fun a => w a * q a) r *
        energy s (fun a => w a * q a) g ≤ (1 - δ) ^ 2 * error ^ 2) :
    (1 - δ) * (max 0 (|form s (fun a => w a * q a) r g| - error)) ^ 2 /
        energy s (fun a => w a * q a) g ≤
      ‖screen V x‖ ^ 2 - ‖screen W x‖ ^ 2 := by
  have hzenergy : 0 < ‖screen V z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hgenergy : 0 < energy s w g := by rw [henergy]; exact hzenergy
  have hcertificate := FiniteSampledGain.sampled_gain_lower_bound_of_sampled_budget
    s w q r g δ error hδ herror hw hq hgenergy hbudget
  rw [hsource, henergy] at hcertificate
  apply hcertificate.trans
  apply (div_le_iff₀ hzenergy).mpr
  simpa only [mul_comm] using screened_score_sq_le_nested_gain V W hVW x z hzW

end RiemannResearch.Analysis.SampledScreenedGain

/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.FiniteHeadHilbertConvergence
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.MobiusCoefficientStabilization

/-!
# Uniform finite-head convergence of the standard Q and Pareto projections

Source: user-provided request, 25 October 2026.
For each fixed H, the maximum physical-coordinate error on 1,...,H tends
to zero. Q uses the existing squarefree stages; Pareto uses the existing
full-conductor stages. Each converges to its own orthogonal projection.
No RH, target-membership, or uniform bound over all sites is assumed.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.FiniteHeadProjectionConvergence
open ZetaTwoHilbert ZetaTwoOptimizerStage
open Pareto Pareto.CoefficientStabilization

/-- Uniform convergence on each fixed nonempty head for the actual Q squarefree optimizers. -/
theorem q_optimizer_head_max_tendsto (H : ℕ) (hH : 1 ≤ H) :
    Tendsto (fun M => (Finset.Icc 1 H).sup' (Finset.nonempty_Icc.mpr hH)
      (fun k => |qSequence (optimizer M) k -
        qSequence (closure.starProjection qOne) k|)) atTop (𝓝 0) :=
  qSequence_head_max_tendsto optimizer_tendsto H hH

/-- The epsilon form for Q, also valid for the empty head. -/
theorem q_optimizer_uniform_on_head (H : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M in atTop, ∀ k, 1 ≤ k → k ≤ H →
      |qSequence (optimizer M) k -
        qSequence (closure.starProjection qOne) k| < ε :=
  qSequence_uniform_on_head optimizer_tendsto H hε

/-- Uniform convergence on each fixed nonempty head for the actual Pareto projections. -/
theorem pareto_projection_head_max_tendsto (H : ℕ) (hH : 1 ≤ H) :
    Tendsto (fun M => (Finset.Icc 1 H).sup' (Finset.nonempty_Icc.mpr hH)
      (fun k => |hilbertSequence (projection M) k -
        hilbertSequence limitProjection k|)) atTop (𝓝 0) :=
  hilbertSequence_head_max_tendsto projection_tendsto H hH

/-- The epsilon form for Pareto, also valid for the empty head. -/
theorem pareto_projection_uniform_on_head (H : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M in atTop, ∀ k, 1 ≤ k → k ≤ H →
      |hilbertSequence (projection M) k - hilbertSequence limitProjection k| < ε :=
  hilbertSequence_uniform_on_head projection_tendsto H hε

end RiemannResearch.RH.FiniteHeadProjectionConvergence

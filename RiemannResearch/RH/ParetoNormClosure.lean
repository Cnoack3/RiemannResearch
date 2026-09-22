import RiemannResearch.RH.MobiusCoefficientStabilization

/-!
# Norm convergence and the closed residue span

Source: user-provided argument,
Pareto_Norm_Convergence_and_Closure_Equivalence(1).md (22 September 2026).
This module formalizes the unsquared norm equivalence for the actual complete
Pareto Hilbert space, using the existing canonical projections.
Stage n is the manuscript's N = n + 1: the generators are g_2,...,g_(n+1).
The RH conclusion retains norm convergence as an explicit open hypothesis.
No unconditional density or Riemann hypothesis is asserted.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- Unconditional convergence of the full, unsquared Pareto error. -/
theorem projection_norm_error_tendsto :
    Tendsto (fun n => ‖hilbertOne - projection n‖) atTop
      (𝓝 ‖limitResidual‖) :=
  (tendsto_const_nhds.sub projection_tendsto).norm

/-- Closedness and best approximation give the precise norm/closure equivalence. -/
theorem projection_norm_tendsto_zero_iff_mem :
    Tendsto (fun n => ‖hilbertOne - projection n‖) atTop (𝓝 0) ↔
      hilbertOne ∈ closedSpace := by
  constructor
  · intro h
    have he : ‖limitResidual‖ = 0 :=
      tendsto_nhds_unique projection_norm_error_tendsto h
    apply (Submodule.starProjection_eq_self_iff).mp
    exact (sub_eq_zero.mp (norm_eq_zero.mp he)).symm
  · intro h
    have he : limitProjection = hilbertOne :=
      (Submodule.starProjection_eq_self_iff).mpr h
    simpa only [limitResidual, he, sub_self, norm_zero] using
      projection_norm_error_tendsto

/-- The third formulation in the supplied markdown, with no density premise hidden. -/
theorem projection_norm_tendsto_zero_iff_fixed_point :
    Tendsto (fun n => ‖hilbertOne - projection n‖) atTop (𝓝 0) ↔
      limitProjection = hilbertOne := by
  rw [projection_norm_tendsto_zero_iff_mem]
  exact (Submodule.starProjection_eq_self_iff).symm

/-- The limiting defect is a lower bound at every finite stage. -/
theorem limitResidual_norm_le_projection_error (n : ℕ) :
    ‖limitResidual‖ ≤ ‖hilbertOne - projection n‖ := by
  have h := energy_eq_limit_add n
  change ‖hilbertOne - projection n‖ ^ 2 =
    ‖limitResidual‖ ^ 2 + ‖limitProjection - projection n‖ ^ 2 at h
  nlinarith [sq_nonneg ‖limitProjection - projection n‖,
    norm_nonneg limitResidual, norm_nonneg (hilbertOne - projection n)]

/-- Conditional research reduction: the displayed norm limit is the open input.
The conclusion is Mathlib's actual RiemannHypothesis. -/
theorem riemannHypothesis_of_projection_norm_tendsto_zero
    (h : Tendsto (fun n => ‖hilbertOne - projection n‖) atTop (𝓝 0)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_hilbertOne_mem_legalClosure {n : ℕ | 0 < n}
    (fun _ hn => hn)
  exact closedSpace_le_legalClosure (projection_norm_tendsto_zero_iff_mem.mp h)

/-- If RH fails, the very same canonical errors have a positive uniform floor.
This conditional statement is compatible with their unconditional convergence. -/
theorem projection_error_uniform_floor_of_not_rh (h : ¬ RiemannHypothesis) :
    0 < ‖limitResidual‖ ∧
      ∀ n, ‖limitResidual‖ ≤ ‖hilbertOne - projection n‖ := by
  refine ⟨?_, limitResidual_norm_le_projection_error⟩
  apply norm_pos_iff.mpr
  intro hz
  apply h
  apply riemannHypothesis_of_projection_norm_tendsto_zero
  simpa only [hz, norm_zero] using projection_norm_error_tendsto

end RiemannResearch.RH.Pareto.CoefficientStabilization

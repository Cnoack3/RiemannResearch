import RiemannResearch.Analysis.WeakConvergenceDenseTests
import RiemannResearch.RH.DyadicBoundaryCompleteness

/-! Weak convergence from actual mean/boundary coordinates and an eventual
complete norm bound. Source: user-provided FourierBridgeUniformSignedEnergy20260910.md,
Section 11. The arithmetic bounds and coordinate limits are explicit hypotheses. -/

open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto

/-- Conditional weak-convergence assembly using the actual complete dyadic
mean and boundary family. No finite prefix replaces completeness. -/
theorem dyadicQuotient_tendsto_inner_zero_of_boundaries
    {I : Type*} {l : Filter I} (f : I → ThresholdHilbert) {C : ℝ}
    (hC : 0 ≤ C) (hbounded : ∀ᶠ i in l, ‖f i‖ ≤ C)
    (hQ : ∀ i, dyadicQuotientProjection (f i) = f i)
    (hmean : Tendsto (fun i => inner ℝ hilbertOne (f i)) l (𝓝 0))
    (hboundary : ∀ k (hk : 0 < k),
      Tendsto (fun i => inner ℝ
        (dyadicQuotientProjection (dyadicStepBoundary k hk)) (f i)) l (𝓝 0))
    (x : ThresholdHilbert) :
    Tendsto (fun i => inner ℝ x (f i)) l (𝓝 0) := by
  have hx : dyadicQuotientProjection x ∈ dyadicBoundarySpan.topologicalClosure := by
    rw [dyadicBoundarySpan_closure_eq_quotient]
    exact dyadicQuotientProjection_mem x
  have ht : Tendsto (fun i => inner ℝ (dyadicQuotientProjection x) (f i)) l (𝓝 0) := by
    apply RiemannResearch.Analysis.tendsto_inner_zero_of_mem_closure_span hC hbounded _ hx
    rintro y (rfl | ⟨k, hk, rfl⟩)
    · exact hmean
    · exact hboundary k hk
  have heq : (fun i => inner ℝ (dyadicQuotientProjection x) (f i)) =
      (fun i => inner ℝ x (f i)) := by
    funext i
    rw [dyadicQuotientProjection_inner, hQ i]
  rw [heq] at ht
  exact ht

/-- The resulting convergence is tested against every continuous linear
functional on the actual Hilbert space: the full weak-convergence assertion. -/
theorem dyadicQuotient_tendsto_dual_zero_of_boundaries
    {I : Type*} {l : Filter I} (f : I → ThresholdHilbert) {C : ℝ}
    (hC : 0 ≤ C) (hbounded : ∀ᶠ i in l, ‖f i‖ ≤ C)
    (hQ : ∀ i, dyadicQuotientProjection (f i) = f i)
    (hmean : Tendsto (fun i => inner ℝ hilbertOne (f i)) l (𝓝 0))
    (hboundary : ∀ k (hk : 0 < k),
      Tendsto (fun i => inner ℝ
        (dyadicQuotientProjection (dyadicStepBoundary k hk)) (f i)) l (𝓝 0))
    (φ : ThresholdHilbert →L[ℝ] ℝ) :
    Tendsto (fun i => φ (f i)) l (𝓝 0) := by
  apply RiemannResearch.Analysis.tendsto_dual_zero_of_inner
  exact dyadicQuotient_tendsto_inner_zero_of_boundaries f hC hbounded hQ hmean hboundary

end RiemannResearch.RH.Pareto

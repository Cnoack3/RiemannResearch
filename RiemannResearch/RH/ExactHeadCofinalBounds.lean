import RiemannResearch.RH.ExactHeadResidualTail

/-!
# Cofinal bounds for complete exact-head errors

Source: continuation of the user-provided Pareto projection argument,
26 September 2026, for the cofinal strengthening; the proof reuses the
established residual-tail Cauchy--Schwarz inequality.

A common energy bound at arbitrarily late exact-head approximants forces
the actual limiting projection defect to vanish. The approximants belong
to the actual closed residue span, and all energies are complete norms.

CONDITIONAL RESEARCH REDUCTION: the cofinal arithmetic bound is an explicit
hypothesis, not a proved estimate. No RH-to-density implication is used.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- A finite common bound at arbitrarily late indices suffices to kill the
limiting defect. No bound at every index, decay rate, or monotonicity is required. -/
theorem limitEnergy_eq_zero_of_cofinally_bounded_exact_head_errors
    (F : ℕ → ThresholdHilbert)
    (hlegal : ∀ N, F N ∈ closedSpace)
    (hhead : ∀ N k, 0 < k → k ≤ N → hilbertSequence (F N) k = 1)
    (C : ℝ)
    (hbound : ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧ ‖hilbertOne - F N‖^2 ≤ C) :
    limitEnergy = 0 := by
  by_contra hz
  have hpos : 0 < limitEnergy^2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hz))
  have ht : Tendsto (fun N => residualTailEnergy N * C) atTop (𝓝 0) := by
    simpa using residualTailEnergy_tendsto_zero.mul_const C
  obtain ⟨M, hM⟩ := eventually_atTop.mp (ht.eventually_lt_const hpos)
  obtain ⟨N, hMN, hN⟩ := hbound M
  have hle := (residual_tail_product_lower N (hlegal N) (hhead N)).trans
    (mul_le_mul_of_nonneg_left hN (residualTailEnergy_nonneg N))
  exact (not_lt_of_ge hle) (hM N hMN)


end RiemannResearch.RH.Pareto.CoefficientStabilization

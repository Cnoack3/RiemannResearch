import RiemannResearch.RH.NaturalMobiusPrimitiveTests
import RiemannResearch.RH.MobiusResidualFirstCoordinate

/-!
# Primitive growth criteria for the actual orthogonal residual

Source: direct continuation of the raw Möbius Abel argument, 24 September 2026.
No mathematical novelty is claimed.

Every raw Möbius approximant belongs to the actual closed legal span. Its error
therefore has the exact pairing `limitEnergy` with the actual orthogonal residual.
Weighted summability of the residual primitive forces this pairing to vanish.
Any fixed sublinear power bound is sufficient by the divisor-count series.

The arithmetic primitive bound is explicit and OPEN. No provider-free
converse from RH, nor an unconditional RH proof, is asserted here.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.CoefficientStabilization

theorem rawMobiusHilbert_mem_closedSpace (N : ℕ) :
    rawMobiusHilbert N ∈ closedSpace := by
  unfold rawMobiusHilbert
  apply closedSpace.neg_mem
  apply closedSpace.sum_mem
  intro d hd
  apply closedSpace.smul_mem
  exact (Submodule.span ℝ (Set.range residueAtom)).le_topologicalClosure
    (normalizedResidue_mem_atomSpan d (Finset.mem_Icc.mp d.property).1)

/-- The exact pairing retains the full infinite Pareto projection error. -/
theorem rawMobiusResidual_inner_limitResidual (N : ℕ) :
    inner ℝ (hilbertOne - rawMobiusHilbert N) limitResidual = limitEnergy := by
  have ho : inner ℝ (rawMobiusHilbert N) limitResidual = 0 :=
    limitResidual_mem_orthogonal _ (rawMobiusHilbert_mem_closedSpace N)
  rw [inner_sub_left, ho, sub_zero, real_inner_comm]
  exact limitResidual_inner_one

/-- Integrability of the actual residual primitive against the explicit
    variation weight forces the complete orthogonal residual to vanish. -/
theorem limitResidual_eq_zero_of_summable_primitive
    (hH : Summable (fun K : ℕ =>
      |∑ k ∈ Finset.range K, hilbertSequence limitResidual (k + 1)| *
        ((3 + ((K + 1).divisors.card : ℝ)) /
          (((K : ℝ) + 1) * ((K : ℝ) + 2))))) :
    limitResidual = 0 := by
  have ht := rawMobiusResidual_inner_tendsto_of_summable_primitive limitResidual hH
  have hc : Tendsto (fun _ : ℕ => limitEnergy) atTop (𝓝 0) := by
    simpa only [rawMobiusResidual_inner_limitResidual] using ht
  have he : limitEnergy = 0 := tendsto_nhds_unique tendsto_const_nhds hc
  exact limitResidual_zero_iff_energy_zero.mpr he

/-- This is an equivalence with residual vanishing, not an assertion that the
    required arithmetic summability is available. -/
theorem limitResidual_zero_iff_summable_primitive :
    limitResidual = 0 ↔ Summable (fun K : ℕ =>
      |∑ k ∈ Finset.range K, hilbertSequence limitResidual (k + 1)| *
        ((3 + ((K + 1).divisors.card : ℝ)) /
          (((K : ℝ) + 1) * ((K : ℝ) + 2)))) := by
  constructor
  · intro hz
    simp [hz, hilbertSequence]
  · exact limitResidual_eq_zero_of_summable_primitive

/-- Any fixed sublinear power bound on the actual primitive forces vanishing. -/
theorem limitResidual_eq_zero_of_primitive_rpow_bound
    (C α : ℝ) (hα : α < 1)
    (hH : ∀ K : ℕ, |∑ k ∈ Finset.range K,
      hilbertSequence limitResidual (k + 1)| ≤ C * ((K : ℝ) + 1) ^ α) :
    limitResidual = 0 := by
  have ht := rawMobiusResidual_inner_tendsto_of_primitive_rpow_bound
    limitResidual C α hα hH
  have hc : Tendsto (fun _ : ℕ => limitEnergy) atTop (𝓝 0) := by
    simpa only [rawMobiusResidual_inner_limitResidual] using ht
  have he : limitEnergy = 0 := tendsto_nhds_unique tendsto_const_nhds hc
  exact limitResidual_zero_iff_energy_zero.mpr he

/-- Conditional RH reduction. The sublinear primitive estimate remains OPEN. -/
theorem riemannHypothesis_of_residual_primitive_rpow_bound
    (C α : ℝ) (hα : α < 1)
    (hH : ∀ K : ℕ, |∑ k ∈ Finset.range K,
      hilbertSequence limitResidual (k + 1)| ≤ C * ((K : ℝ) + 1) ^ α) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_firstCoordinate_zero
  exact firstCoordinate_zero_iff_residual_zero.mpr
    (limitResidual_eq_zero_of_primitive_rpow_bound C α hα hH)

/-- If RH fails, every proposed fixed sublinear power bound is exceeded. -/
theorem not_RH_residual_primitive_exceeds_sublinear_power
    (hRH : ¬ RiemannHypothesis) (C α : ℝ) (hα : α < 1) :
    ∃ K : ℕ, C * ((K : ℝ) + 1) ^ α <
      |∑ k ∈ Finset.range K, hilbertSequence limitResidual (k + 1)| := by
  by_contra! hH
  exact hRH (riemannHypothesis_of_residual_primitive_rpow_bound C α hα hH)

end RiemannResearch.RH.Pareto.CoefficientStabilization

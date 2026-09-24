import RiemannResearch.RH.CanonicalMobiusPNT
import RiemannResearch.RH.CanonicalMobiusQuantitativeEnergy

/-!
# PNT consequences for the actual limiting residual tail

Source: user-requested continuation, 24 September 2026, and the project's
exact-head Cauchy--Schwarz argument. This module assembles established
sublinear-energy reductions with their now proved classical PNT provider.
It also transfers the explicit full-error ceiling to a quantitative lower
bound on the actual limiting residual tail. No novelty claim is made.

The positive-energy implications do not assert positive energy. The bounded
cofinal-tail RH criterion is a conditional research reduction: its tail
bound remains OPEN. No limit is passed through growing inverse matrices.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- A nonzero limiting energy forces a positive tail at every cutoff. -/
theorem residualTailEnergy_pos_of_limitEnergy_pos (hpos : 0 < limitEnergy) (N : ℕ) :
    0 < residualTailEnergy N := by
  have hp := residual_tail_product_lower N
    (canonicalMobiusHilbert_mem_closedSpace N) (canonicalMobiusHilbert_exact N)
  have he := sq_pos_of_pos hpos
  have ht := residualTailEnergy_nonneg N
  by_contra! hn
  have hz : residualTailEnergy N = 0 := le_antisymm hn ht
  rw [hz, zero_mul] at hp
  linarith

/-- The established sublinear-energy reduction with its PNT premise discharged. -/
theorem normalized_residual_tail_tendsto_atTop (hpos : 0 < limitEnergy) :
    Tendsto (fun N : ℕ => (N : ℝ) * residualTailEnergy N) atTop atTop :=
  canonical_normalized_tail_tendsto_atTop hpos canonicalMobiusHilbert_sublinear

/-- Exact characterization for the actual residual; boundedness is not asserted. -/
theorem limitResidual_eq_zero_iff_frequently_bounded_normalized_tail :
    limitResidual = 0 ↔
      ∃ C : ℝ, ∃ᶠ N : ℕ in atTop, (N : ℝ) * residualTailEnergy N ≤ C := by
  constructor
  · intro hz
    refine ⟨0, (Eventually.of_forall ?_).frequently⟩
    intro N
    have hshift : hilbertTailShift limitResidual N = 0 := by
      ext n
      simp [hilbertTailShift, hz]
    simp [residualTailEnergy, hshift]
  · rintro ⟨C, hC⟩
    apply limitResidual_zero_iff_energy_zero.mpr
    exact limitEnergy_zero_of_frequently_bounded_normalized_tail
      canonicalMobiusHilbert canonicalMobiusHilbert_mem_closedSpace
      canonicalMobiusHilbert_exact canonicalMobiusHilbert_sublinear C hC

/-- Conditional research reduction. Only the bounded cofinal tail remains open. -/
theorem riemannHypothesis_of_frequently_bounded_residual_tail
    (C : ℝ) (hbounded : ∃ᶠ N : ℕ in atTop, (N : ℝ) * residualTailEnergy N ≤ C) :
    RiemannHypothesis :=
  riemannHypothesis_of_reciprocal_cancellation_and_bounded_tail
    mobiusReciprocalSum_tendsto_zero C hbounded

/-- An unconditional explicit lower bound, using the same arithmetic constant
as the complete canonical error ceiling. The denominator tends to zero. -/
theorem residual_tail_eventual_explicit_lower :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      0 < canonicalMobiusResidualCeiling C N ∧
      limitEnergy ^ 2 / canonicalMobiusResidualCeiling C N ≤
        ((N : ℝ) + 1) * residualTailEnergy N := by
  obtain ⟨C, hC, hbound⟩ := canonicalMobiusResidual_eventual_explicit_ceiling
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with N hN
  have hden : 0 < canonicalMobiusResidualCeiling C N :=
    lt_of_lt_of_le (by positivity : 0 < 1 / ((N : ℝ) + 1)) hN.1
  refine ⟨hden, (div_le_iff₀ hden).mpr ?_⟩
  calc
    limitEnergy ^ 2 ≤ residualTailEnergy N * ‖hilbertOne - canonicalMobiusHilbert N‖ ^ 2 :=
      residual_tail_product_lower N (canonicalMobiusHilbert_mem_closedSpace N)
        (canonicalMobiusHilbert_exact N)
    _ ≤ residualTailEnergy N * (((N : ℝ) + 1) * canonicalMobiusResidualCeiling C N) :=
      mul_le_mul_of_nonneg_left hN.2 (residualTailEnergy_nonneg N)
    _ = (((N : ℝ) + 1) * residualTailEnergy N) * canonicalMobiusResidualCeiling C N := by ring

end RiemannResearch.RH.Pareto.CoefficientStabilization

import RiemannResearch.RH.CanonicalMobiusPNT

/-!
# Dichotomy for the actual normalized residual tails

Source: the user-provided residual-tail argument. The exact-head product
inequality and the canonical sublinear-energy theorem give the divergent
branch; classical Möbius cancellation is supplied by `CanonicalMobiusPNT`.

This is a dichotomy for the actual projection residual. The implication
from RH to zero residual is not assumed or asserted here. Bounded cofinal
normalized tails remain an open research estimate.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- Positive actual residual energy forces normalized tails to diverge. -/
theorem normalized_residual_tail_tendsto_atTop_of_limitEnergy_pos
    (hpos : 0 < limitEnergy) :
    Tendsto (fun N : ℕ => (N : ℝ) * residualTailEnergy N)
      atTop atTop :=
  canonical_normalized_tail_tendsto_atTop hpos canonicalMobiusHilbert_sublinear

/-- Zero residual energy makes every tail identically zero. -/
theorem residualTailEnergy_eq_zero_of_limitEnergy_zero
    (hE : limitEnergy = 0) (N : ℕ) :
    residualTailEnergy N = 0 := by
  have hr := limitResidual_zero_iff_energy_zero.mpr hE
  rw [residualTailEnergy, hilbertTailShift_norm_sq]
  simp [hr]

/-- The normalized tails of the zero residual converge to zero. -/
theorem normalized_residual_tail_tendsto_zero_of_limitEnergy_zero
    (hE : limitEnergy = 0) :
    Tendsto (fun N : ℕ => (N : ℝ) * residualTailEnergy N)
      atTop (𝓝 0) := by
  have hz : (fun N : ℕ => (N : ℝ) * residualTailEnergy N) =
      (fun _ : ℕ => (0 : ℝ)) := by
    funext N
    rw [residualTailEnergy_eq_zero_of_limitEnergy_zero hE N, mul_zero]
  rw [hz]
  exact tendsto_const_nhds

/-- The actual residual is zero, with identically zero normalized tails,
or it is nonzero and the normalized tails tend to positive infinity. -/
theorem actual_normalized_residual_tail_dichotomy :
    (limitResidual = 0 ∧
      ∀ N : ℕ, (N : ℝ) * residualTailEnergy N = 0) ∨
    (limitResidual ≠ 0 ∧
      Tendsto (fun N : ℕ => (N : ℝ) * residualTailEnergy N)
        atTop atTop) := by
  by_cases hr : limitResidual = 0
  · refine Or.inl ⟨hr, fun N => ?_⟩
    rw [residualTailEnergy_eq_zero_of_limitEnergy_zero
      (limitResidual_zero_iff_energy_zero.mp hr) N, mul_zero]
  · have hE : limitEnergy ≠ 0 := by
      intro h
      exact hr (limitResidual_zero_iff_energy_zero.mpr h)
    have hp : 0 < limitEnergy :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm hE)
    exact Or.inr ⟨hr,
      normalized_residual_tail_tendsto_atTop_of_limitEnergy_pos hp⟩

/-- A bounded cofinal normalized-tail estimate would force residual
vanishing. That estimate remains an explicit research hypothesis. -/
theorem limitResidual_zero_of_frequently_bounded_actual_tail
    (C : ℝ)
    (hbounded : ∃ᶠ N : ℕ in atTop,
      (N : ℝ) * residualTailEnergy N ≤ C) :
    limitResidual = 0 := by
  have hE := canonical_limitEnergy_zero_of_frequently_bounded_tail
    (mobius_sum_div_tendsto_zero_of_reciprocal_tendsto
      mobiusReciprocalSum_tendsto_zero)
    mobiusReciprocalSum_tendsto_zero C hbounded
  exact limitResidual_zero_iff_energy_zero.mpr hE

/-- An exact formulation of the remaining tail obligation. Existence of a
finite bound at arbitrarily large cutoffs is equivalent to zero residual;
no bound is constructed here. Source: the 2026-09-23 unconditional-RH audit. -/
theorem frequently_bounded_actual_tail_iff_residual_zero :
    (∃ C : ℝ, ∃ᶠ N : ℕ in atTop,
      (N : ℝ) * residualTailEnergy N ≤ C) ↔ limitResidual = 0 := by
  constructor
  · rintro ⟨C, hC⟩
    exact limitResidual_zero_of_frequently_bounded_actual_tail C hC
  · intro hr
    refine ⟨0, Filter.Eventually.frequently (Filter.Eventually.of_forall ?_)⟩
    intro N
    rw [residualTailEnergy_eq_zero_of_limitEnergy_zero
      (limitResidual_zero_iff_energy_zero.mp hr) N, mul_zero]

/-- Conditional research reduction: bounded cofinal normalized tails imply
Mathlib RH. No arithmetic cancellation hypothesis remains. -/
theorem riemannHypothesis_of_frequently_bounded_actual_tail
    (C : ℝ)
    (hbounded : ∃ᶠ N : ℕ in atTop,
      (N : ℝ) * residualTailEnergy N ≤ C) :
    RiemannHypothesis :=
  riemannHypothesis_of_reciprocal_cancellation_and_bounded_tail
    mobiusReciprocalSum_tendsto_zero C hbounded

/-- Failure of RH forces divergence of the normalized actual tails. -/
theorem not_RH_normalized_residual_tail_tendsto_atTop
    (hRH : ¬ RiemannHypothesis) :
    Tendsto (fun N : ℕ => (N : ℝ) * residualTailEnergy N)
      atTop atTop :=
  normalized_residual_tail_tendsto_atTop_of_limitEnergy_pos
    (not_RH_limitEnergy_pos hRH)

end RiemannResearch.RH.Pareto.CoefficientStabilization

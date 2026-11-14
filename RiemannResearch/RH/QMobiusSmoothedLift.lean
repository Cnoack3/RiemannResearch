/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCanonicalMobiusCost
import RiemannResearch.RH.QMobiusExactHead
import RiemannResearch.RH.CanonicalMobiusFullEnergy
import RiemannResearch.RH.CanonicalMobiusPNT
import RiemannResearch.RH.QReciprocalTargetLift
import RiemannResearch.RH.QReciprocalMetric
import RiemannResearch.RH.QReciprocalCostEquivalence
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.Analysis.BoundedWeakInterpolation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Explicit smoothed lifts and their missing uniform source bound

Source: the user's 14 November 2026 request to construct a bounded legal lift
of D1 using weak-star compactness. The explicit formula is the existing
boundary-corrected Mobius exact head, and the quantitative estimates are
consequences of the complete-cost and PNT bounds in the imported modules.
Banach--Alaoglu/Riesz extraction is reused from BoundedWeakInterpolation.

Every exact head is finite legal, and its D-image converges to D1
unconditionally. Its squared source norm is bounded by 8N/zeta(2), and is
o(N); neither statement supplies a uniform bound. A bounded cofinal
selection gives a weakly convergent subsequence with limit 1. Existence of
that bounded selection remains an Open arithmetic obligation.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QMobiusSmoothedLift
open ZetaTwoHilbert ZetaTwoProbability QReciprocalMetric
open QReciprocalCostEquivalence QMobiusExactHead QCanonicalMobiusCost

/-- An elementary complete-image error bound; no tail is discarded. -/
theorem exactHead_D_error_sq_le (N : ℕ) (hN : 0 < N) :
    ‖D (exactHead N - qOne)‖ ^ 2 ≤ 16 / (zetaTwo * (N : ℝ)) := by
  have hc := balanced_cost_explicit N hN
  unfold cost at hc
  have hp : 0 ≤ ((N : ℝ)^2)⁻¹ * ‖exactHead N‖^2 := by positivity
  linarith only [hc, hp]

/-- The elementary source estimate grows with the head length. -/
theorem exactHead_source_sq_le (N : ℕ) (hN : 0 < N) :
    ‖exactHead N‖ ^ 2 ≤ (8 / zetaTwo) * (N : ℝ) := by
  calc
    _ ≤ (2 / zetaTwo) * ‖Pareto.canonicalMobiusHilbert N‖ ^ 2 :=
      exactHead_norm_sq_le N
    _ ≤ (2 / zetaTwo) * (4 * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (Pareto.canonicalMobiusHilbert_norm_sq_lt_four_mul N hN).le
        (by positivity [zetaTwo_pos])
    _ = _ := by ring

/-- The explicit finite legal Mobius heads solve the smoothed approximation problem. -/
theorem exactHead_D_tendsto :
    Tendsto (fun N => D (exactHead N)) atTop (𝓝 (D qOne)) := by
  have hu : Tendsto (fun N : ℕ => 16 / (zetaTwo * (N : ℝ))) atTop (𝓝 0) := by
    have hi : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa only [div_eq_mul_inv, mul_inv_rev, mul_zero, mul_assoc, mul_left_comm,
      mul_comm, zero_mul] using hi.const_mul (16 / zetaTwo)
  have hs : Tendsto (fun N => ‖D (exactHead N - qOne)‖ ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun N => sq_nonneg _)) ?_ hu
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact exactHead_D_error_sq_le N hN
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero,
    map_sub] using hn

/-- The checked PNT saving improves the squared image error to o(1/N). -/
theorem exactHead_scaled_D_error_tendsto :
    Tendsto (fun N : ℕ => (N : ℝ) * ‖D (exactHead N - qOne)‖ ^ 2)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun N => mul_nonneg (Nat.cast_nonneg N) (sq_nonneg _))
    (fun N => ?_) balanced_cost_little_o
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
  unfold cost
  exact le_add_of_nonneg_right (by positivity)

/-- The complete source energy is o(N), not a uniform energy estimate. -/
theorem exactHead_source_sublinear :
    Tendsto (fun N : ℕ => ‖exactHead N‖ ^ 2 / (N : ℝ)) atTop (𝓝 0) := by
  have hu : Tendsto (fun N : ℕ => (2 / zetaTwo) *
      (‖Pareto.canonicalMobiusHilbert N‖ ^ 2 / (N : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      Pareto.canonicalMobiusHilbert_sublinear.const_mul (2 / zetaTwo)
  apply squeeze_zero (fun N => by positivity) (fun N => ?_) hu
  simpa only [mul_div_assoc] using
    div_le_div_of_nonneg_right (exactHead_norm_sq_le N) (Nat.cast_nonneg N)

/-- If RH is false, this particular successful smoothed lift must escape every norm ball. -/
theorem exactHead_norm_tendsto_atTop_of_not_RH
    (hRH : ¬ RiemannHypothesis) :
    Tendsto (fun N => ‖exactHead N‖) atTop atTop :=
  QReciprocalTargetLift.D_target_norm_tendsto_atTop_of_not_RH hRH exactHead
    (fun N => QFullResidueProjection.legalSpan.le_topologicalClosure
      (exactHead_mem_legalSpan N)) exactHead_D_tendsto


/-- Weak compactness identifies the limit along any bounded cofinal selection.
The existence of a uniform source bound remains explicit. -/
theorem exactHead_weak_subsequence_of_bounded_cofinal
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (C : ℝ) (hbound : ∀ j, ‖exactHead (H j)‖ ≤ C) :
    qOne ∈ QFullResidueProjection.closure ∧ ‖qOne‖ ≤ C ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun j => toWeakSpace ℝ QHilbert (exactHead (H (φ j))))
          atTop (𝓝 (toWeakSpace ℝ QHilbert qOne)) := by
  let S := QFullResidueProjection.closure
  have hm : ∀ j, exactHead (H j) ∈ S := fun j =>
    QFullResidueProjection.legalSpan.le_topologicalClosure
      (exactHead_mem_legalSpan (H j))
  obtain ⟨f, hf, hfn, φ, hφ, hw⟩ :=
    S.exists_ambient_weak_subsequence_of_norm_le C (fun j => exactHead (H j)) hm hbound
  have hi := exactHead_D_tendsto.comp (hH.comp hφ.tendsto_atTop)
  have he (z : QHilbert) : inner ℝ z (D f) = inner ℝ z (D qOne) := by
    have hleft := WeakSpace.tendsto_eval_of_tendsto hw ((innerSL ℝ z).comp D)
    have hright := ((innerSL ℝ z).continuous.tendsto (D qOne)).comp hi
    exact tendsto_nhds_unique hleft hright
  have hz : D f = D qOne := by
    have hh := he (D f - D qOne)
    have hzero : inner ℝ (D f - D qOne) (D f - D qOne) = 0 := by
      rw [inner_sub_right, hh, sub_self]
    rw [real_inner_self_eq_norm_sq] at hzero
    apply sub_eq_zero.mp
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (D f - D qOne)])
  have hfx : f = qOne := QReciprocalTargetLift.D_injective hz
  subst f
  exact ⟨hf, hfn, φ, hφ, hw⟩

end RiemannResearch.RH.QMobiusSmoothedLift

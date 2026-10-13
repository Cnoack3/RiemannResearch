/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.RH.ParetoAnnihilatorPositivity
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.ThresholdHilbertMean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity

/-!
# Odd-coordinate sign criterion for the actual Pareto projection

Continuation of Section 6 of Pareto_Parity_Endpoint_Continuation.
The implication uses the entire Pareto law, orthogonality to g₂, and the
established nonnegative first coordinate. No uniformity over coordinates,
finite Gram approximation, or RH hypothesis is introduced.

Verification status is recorded in the accompanying continuation and catalog.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.RH.ArithmeticCumulative

/-- In a g₂-orthogonal vector, nonnegative odd coordinates force a
nonnegative first coordinate to vanish. Even coordinates are unrestricted. -/
theorem firstCoordinate_zero_of_odd_coordinate_nonnegative
    (f : ThresholdHilbert)
    (hfirst : 0 ≤ hilbertSequence f 1)
    (ho : inner ℝ f (residueAtom 0) = 0)
    (hodd : ∀ k : ℕ, 3 ≤ k → k % 2 = 1 → 0 ≤ hilbertSequence f k) :
    hilbertSequence f 1 = 0 := by
  have hb (k : ℕ) : |residueFraction 2 k| ≤ 1 := by
    unfold residueFraction
    rw [abs_of_nonneg (by positivity)]
    apply (div_le_one₀ (by norm_num : (0 : ℝ) < 2)).mpr
    exact_mod_cast (Nat.mod_lt k (by decide : 0 < 2)).le
  have hs := weighted_product_summable_of_square_of_bounded
    (hilbertSequence_square_summable f) hb
  have hterm (k : ℕ) :
      0 ≤ positiveWeight k * (hilbertSequence f k * residueFraction 2 k) := by
    by_cases hk : k % 2 = 0
    · simp [residueFraction, hk]
    · have hkodd : k % 2 = 1 := by omega
      have hfk : 0 ≤ hilbertSequence f k := by
        by_cases hkone : k = 1
        · simpa [hkone] using hfirst
        · exact hodd k (by omega) hkodd
      exact mul_nonneg (positiveWeight_nonneg k)
        (mul_nonneg hfk (by unfold residueFraction; positivity))
  have ht := hs.le_tsum 1 (fun k _ => hterm k)
  change positiveWeight 1 * (hilbertSequence f 1 * residueFraction 2 1) ≤
    paretoInner (hilbertSequence f) (residueFraction 2) at ht
  rw [hilbert_inner_weighted, residueAtom, normalizedResidueHilbert_sequence] at ho
  change paretoInner (hilbertSequence f) (residueFraction 2) = 0 at ho
  rw [ho] at ht
  have hw : positiveWeight 1 = (1 / 2 : ℝ) := by
    norm_num [positiveWeight]
  have hg : residueFraction 2 1 = (1 / 2 : ℝ) := by
    norm_num [residueFraction]
  rw [hw, hg] at ht
  linarith

/-- The actual residual cannot be nonnegative at every odd coordinate ≥3
unless the full Hilbert defect vanishes. -/
theorem limitResidual_zero_of_odd_coordinate_nonnegative
    (hodd : ∀ k : ℕ, 3 ≤ k → k % 2 = 1 →
      0 ≤ hilbertSequence limitResidual k) : limitResidual = 0 := by
  have ha : residueAtom 0 ∈ closedSpace :=
    (Submodule.span ℝ (Set.range residueAtom)).le_topologicalClosure
      (Submodule.subset_span ⟨0, rfl⟩)
  have ho : inner ℝ limitResidual (residueAtom 0) = 0 := by
    rw [real_inner_comm]
    exact (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal _ ha
  exact firstCoordinate_zero_iff_residual_zero.mp
    (firstCoordinate_zero_of_odd_coordinate_nonnegative limitResidual
      firstCoordinate_nonneg ho hodd)

/-- Qualitative odd-coordinate signs are exactly equivalent to zero residual. -/
theorem odd_limitResidual_coordinate_nonnegative_iff_zero :
    (∀ k : ℕ, 3 ≤ k → k % 2 = 1 → 0 ≤ hilbertSequence limitResidual k) ↔
      limitResidual = 0 := by
  constructor
  · exact limitResidual_zero_of_odd_coordinate_nonnegative
  · intro hz k _ _
    rw [hz]
    change 0 ≤ hilbertSequenceLinear (0 : ThresholdHilbert) k
    rw [map_zero]
    exact le_rfl

/-- This is the actual full-Pareto optimizer form of the manuscript's
Section 6 condition. Only the fixed odd-coordinate limits are constrained. -/
theorem limitResidual_zero_of_odd_limitProjection_le_one
    (hodd : ∀ k : ℕ, 3 ≤ k → k % 2 = 1 →
      hilbertSequence limitProjection k ≤ 1) : limitResidual = 0 := by
  apply limitResidual_zero_of_odd_coordinate_nonnegative
  intro k hk hkodd
  have hk0 : k ≠ 0 := by omega
  change 0 ≤ hilbertSequenceLinear (hilbertOne - limitProjection) k
  rw [map_sub]
  change 0 ≤ hilbertSequence hilbertOne k - hilbertSequence limitProjection k
  rw [hilbertOne_sequence]
  simp only [zeroAnchor, hk0, ↓reduceIte]
  linarith [hodd k hk hkodd]

theorem odd_limitProjection_le_one_iff_residual_zero :
    (∀ k : ℕ, 3 ≤ k → k % 2 = 1 → hilbertSequence limitProjection k ≤ 1) ↔
      limitResidual = 0 := by
  constructor
  · exact limitResidual_zero_of_odd_limitProjection_le_one
  · intro hz
    have hp : limitProjection = hilbertOne := by
      change hilbertOne - limitProjection = 0 at hz
      exact (sub_eq_zero.mp hz).symm
    intro k hk _
    rw [hp, hilbertOne_sequence]
    simp [zeroAnchor, show k ≠ 0 by omega]

/-- A useful contrapositive: a surviving defect must exhibit odd overshoot
at some physical coordinate ≥3. The coordinate is not uniformly bounded. -/
theorem odd_limitProjection_overshoot_of_residual_ne_zero
    (hne : limitResidual ≠ 0) :
    ∃ k : ℕ, 3 ≤ k ∧ k % 2 = 1 ∧ 1 < hilbertSequence limitProjection k := by
  by_contra hnone
  push Not at hnone
  exact hne (limitResidual_zero_of_odd_limitProjection_le_one hnone)

theorem riemannHypothesis_of_odd_limitProjection_le_one
    (hodd : ∀ k : ℕ, 3 ≤ k → k % 2 = 1 →
      hilbertSequence limitProjection k ≤ 1) : RiemannHypothesis :=
  riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_residual_zero.mpr
      (limitResidual_zero_of_odd_limitProjection_le_one hodd))

/-- The criterion can be supplied entirely as separate finite-optimizer
coordinate limits. Their limits automatically equal the actual limitProjection. -/
theorem riemannHypothesis_of_odd_projection_coordinate_limits_le_one
    (hodd : ∀ k : ℕ, 3 ≤ k → k % 2 = 1 → ∃ L : ℝ,
      Tendsto (fun n : ℕ => hilbertSequence (projection n) k) atTop (𝓝 L) ∧ L ≤ 1) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_odd_limitProjection_le_one
  intro k hk hkodd
  obtain ⟨L, hlim, hL⟩ := hodd k hk hkodd
  have hp : Tendsto (fun n : ℕ => hilbertSequence (projection n) k) atTop
      (𝓝 (hilbertSequence limitProjection k)) := by
    simpa only [Function.comp_def, anchoredEvaluationCLM_apply] using
      (anchoredEvaluationCLM k).continuous.tendsto limitProjection |>.comp projection_tendsto
  have he : L = hilbertSequence limitProjection k := tendsto_nhds_unique hlim hp
  simpa only [he] using hL

end RiemannResearch.RH.Pareto.CoefficientStabilization

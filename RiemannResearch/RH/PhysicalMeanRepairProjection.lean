/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PhysicalSourceLimits

/-!
# Exact ordinary-mean repair of the actual physical projection

The actual unconstrained physical optimizer is unique, and its charge is
monotone on nested legal packet sets. The constrained optimizer is its exact
signed repair along the actual ordinary-mean dual. The full mean mismatch
square gives the complete penalty, bounded by the remaining constrained-error
gap on the primorial chain. The existing PhysicalOptimizerLimits module supplies
the common error limit; its value is still unidentified.

Source: user-directed continuation of PhysicalSourceLimits20261008.md;
finite Gram completion and actual signed Schur source limits in the imports.
-/

noncomputable section
open Matrix Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.PhysicalMeanRepairProjection
open PhysicalPacketCore PhysicalSchurCoupling PhysicalSourceProjection PhysicalSourceLimits

/-- The ordinary mean mismatch retains the complete signed source. -/
theorem projection_totient_pairing (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    ramanujanTotientVector s ⬝ᵥ projectionCoefficients s =
      2 + 4 * Real.pi * (2 * Real.pi + mixedCharge s) / shiftedDeterminant s := by
  have hT := ne_of_gt (shiftedDeterminant_pos s hs ho)
  rw [projectionCoefficients]
  simp only [dotProduct_smul, dotProduct_sub, smul_eq_mul, coreLambda_totient_pair]
  change (2 / shiftedDeterminant s) *
    (logarithmicCharge s * inverseCharge s -
      (2 * Real.pi + mixedCharge s) * mixedCharge s) = _
  field_simp [hT]
  unfold shiftedDeterminant
  ring

theorem totientDual_pairing_pos (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    0 < ramanujanTotientVector s ⬝ᵥ totientDual s := by
  rw [totientDual_pairing]
  apply div_pos _ (shiftedDeterminant_pos s hs ho)
  nlinarith [Real.pi_pos, inverseCharge_neg s hs ho]

/-- Exact finite repair of the actual Gram projection, with the signed
coefficient retained before any squaring or absolute value. -/
theorem constrainedOptimizer_eq_projection_add_meanRepair (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    constrainedOptimizer s = projectionCoefficients s +
      ((2 * Real.pi + mixedCharge s) / inverseCharge s) • totientDual s := by
  have hC := ne_of_lt (inverseCharge_neg s hs ho)
  have hT := ne_of_gt (shiftedDeterminant_pos s hs ho)
  ext i
  change (2 / inverseCharge s) * coreTotient s i =
    (2 / shiftedDeterminant s) *
      (logarithmicCharge s * coreTotient s i -
        (2 * Real.pi + mixedCharge s) * coreLambda s i) +
    ((2 * Real.pi + mixedCharge s) / inverseCharge s) *
      ((2 / shiftedDeterminant s) *
        (inverseCharge s * coreLambda s i -
          (2 * Real.pi + mixedCharge s) * coreTotient s i))
  field_simp [hC, hT]
  unfold shiftedDeterminant
  ring

/-- The complete finite mean-one penalty is the ordinary mean mismatch
square divided by the actual ordinary-mean dual norm. -/
theorem meanOne_projection_error_gap_eq_mean_mismatch (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    paretoError (synthesis s (constrainedOptimizer s)) -
      paretoError (synthesis s (projectionCoefficients s)) =
      (2 - ramanujanTotientVector s ⬝ᵥ projectionCoefficients s) ^ 2 /
        (ramanujanTotientVector s ⬝ᵥ totientDual s) := by
  have hC := ne_of_lt (inverseCharge_neg s hs ho)
  have hT := ne_of_gt (shiftedDeterminant_pos s hs ho)
  rw [meanOne_projection_error_gap s hs ho, projection_totient_pairing s hs ho,
    totientDual_pairing]
  field_simp [hC, hT, Real.pi_ne_zero]
  ring

theorem projection_unique_minimum (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) (c : s → ℝ) :
    paretoError (synthesis s (projectionCoefficients s)) ≤ paretoError (synthesis s c) ∧
      (paretoError (synthesis s c) = paretoError (synthesis s (projectionCoefficients s)) ↔
        c = projectionCoefficients s) := by
  constructor
  · rw [projection_error s hs ho, projection_error_decomposition s hs ho c]
    exact le_add_of_nonneg_right (gram_quadratic_nonneg s _)
  · constructor
    · intro he
      by_contra hc
      have hp := PhysicalPacketCore.gram_quadratic_pos s hs
        (c - projectionCoefficients s) (sub_ne_zero.mpr hc)
      rw [projection_error s hs ho] at he
      have hd := projection_error_decomposition s hs ho c
      linarith
    · rintro rfl
      rfl

theorem sourceProjectionCharge_mono (s t : Finset ℕ) (hst : s ⊆ t)
    (hs : ∀ q ∈ s, 1 < q) (ht : ∀ q ∈ t, 1 < q)
    (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    sourceProjectionCharge s ≤ sourceProjectionCharge t := by
  have hot := PhysicalCoreMonotonicity.odd_prime_mono s t hst ho
  have h := (projection_unique_minimum t ht hot
    (PhysicalCoreMonotonicity.extendCoefficients s t (projectionCoefficients s))).1
  rw [PhysicalCoreMonotonicity.synthesis_extendCoefficients s t _ hst,
    projection_error t ht hot, projection_error s hs ho] at h
  linarith

theorem primorial_projectionCharge_monotone :
    Monotone (fun n => sourceProjectionCharge (primorialPackets n)) := by
  intro n m hnm
  exact sourceProjectionCharge_mono _ _ (primorialPackets_nested hnm)
    (primorialPackets_legal n) (primorialPackets_legal m) (primorialPackets_odd n)

theorem primorial_projectionCharge_le_limit (Cinf : ℝ) (hCneg : Cinf < 0)
    (hC : Tendsto (fun n => inverseCharge (primorialPackets n)) atTop (𝓝 Cinf)) (n : ℕ) :
    sourceProjectionCharge (primorialPackets n) ≤ 4 * Real.pi / (-Cinf) := by
  have hc := physical_source_limit_bound primorialPackets n Cinf
    (fun _ h => primorialPackets_nested h) primorialPackets_legal (primorialPackets_odd n)
    primorial_logarithmicCharge_tendsto_zero primorial_mixedCharge_tendsto_neg_two_pi hC
  change -Cinf ≤ sourceCorrectedCharge (primorialPackets n) at hc
  rw [sourceProjectionCharge_eq_div_corrected _ (primorialPackets_legal n)
    (primorialPackets_odd n)]
  exact div_le_div_of_nonneg_left (by positivity) (neg_pos.mpr hCneg) hc

/-- The left-hand side is exactly the full signed-source square penalty. -/
theorem primorial_meanOne_projection_gap_bound (Cinf : ℝ) (hCneg : Cinf < 0)
    (hC : Tendsto (fun n => inverseCharge (primorialPackets n)) atTop (𝓝 Cinf)) (n : ℕ) :
    paretoError (synthesis (primorialPackets n) (constrainedOptimizer (primorialPackets n))) -
      paretoError (synthesis (primorialPackets n) (projectionCoefficients (primorialPackets n))) ∈
        Set.Icc 0 (4 * Real.pi / inverseCharge (primorialPackets n) - 4 * Real.pi / Cinf) := by
  constructor
  · exact sub_nonneg.mpr
      (projection_unique_minimum _ (primorialPackets_legal n) (primorialPackets_odd n) _).1
  · have hq := primorial_projectionCharge_le_limit Cinf hCneg hC n
    rw [div_neg] at hq
    rw [constrainedOptimizer_error _ (primorialPackets_legal n) (primorialPackets_odd n),
      projection_error _ (primorialPackets_legal n) (primorialPackets_odd n)]
    linarith

end RiemannResearch.RH.Pareto.PhysicalMeanRepairProjection

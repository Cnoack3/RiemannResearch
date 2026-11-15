/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QReciprocalMetric
import RiemannResearch.RH.ParetoWeights
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Pareto-to-Q density multiplier

Source: user-provided argument, 8 November 2026, for the identity
B = (1 / zetaTwo) * (I + D), where D divides positive physical coordinates by n.

This module defines the density dQ/dP as a continuous linear operator and
checks both its physical-coordinate formula and the exact weight identity.
QDensityMetric.B is distinct from QShiftedReciprocal.B, whose physical
multiplier is 1 / (n + 1). The two operators keep their separate namespaces.

The density-augmented approximation application is in QDensityAugmentedSpan.
-/

noncomputable section
namespace RiemannResearch.RH.QDensityMetric
open ZetaTwoHilbert ZetaTwoProbability

def B : QHilbert →L[ℝ] QHilbert :=
  (1 / zetaTwo) • (ContinuousLinearMap.id ℝ QHilbert + QReciprocalMetric.D)

@[simp] theorem B_apply (f : QHilbert) (n : ℕ) :
    B f n = (1 / zetaTwo) * (f n + f n / ((n : ℝ) + 1)) := rfl

theorem qSequence_B (f : QHilbert) (k : ℕ) :
    qSequence (B f) k = (1 / zetaTwo) *
      (qSequence f k + qSequence f k / (k : ℝ)) := by
  cases k with
  | zero => simp
  | succ n =>
    simp only [qSequence_succ, B_apply, Nat.cast_add, Nat.cast_one]
    ring

/-- On every positive physical coordinate this is precisely dQ/dP. -/
theorem qSequence_B_physical (f : QHilbert) (k : ℕ) (hk : 0 < k) :
    qSequence (B f) k = (((k : ℝ) + 1) / (zetaTwo * (k : ℝ))) * qSequence f k := by
  rw [qSequence_B]
  have hkR : (k : ℝ) ≠ 0 := by positivity
  field_simp [hkR, ne_of_gt zetaTwo_pos]

theorem weight_mul_density (k : ℕ) (hk : 0 < k) :
    Pareto.positiveWeight k * (((k : ℝ) + 1) / (zetaTwo * (k : ℝ))) =
      positiveQWeight k := by
  have hkR : (k : ℝ) ≠ 0 := by positivity
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  unfold Pareto.positiveWeight positiveQWeight
  field_simp [hkR, hk1, ne_of_gt zetaTwo_pos]

/-- The positive density multiplier is symmetric in the Q inner product. -/
theorem B_symmetric (f g : QHilbert) :
    inner ℝ (B f) g = inner ℝ f (B g) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  change g n * (B f n) = (B g n) * f n
  simp only [B_apply]
  ring

end RiemannResearch.RH.QDensityMetric

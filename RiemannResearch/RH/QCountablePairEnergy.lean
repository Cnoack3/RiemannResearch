/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.AnchoredPairEnergy
import RiemannResearch.RH.QCountableJumpEnergy
import RiemannResearch.RH.QPairVariance
import Mathlib.Tactic.Finiteness

/-!
# Complete pair-energy regularity for the actual inverse-square law

Source: countable prime-resampling continuation, 27 October 2026.
The positive atom at one removes any prior L1 or L2 hypothesis.
-/

noncomputable section
open scoped BigOperators ENNReal
namespace RiemannResearch.RH.QCountableJumpEnergy
open ZetaTwoHilbert ZetaTwoProbability QPairVariance
open RiemannResearch.Analysis.CountableJumpEnergy
open RiemannResearch.Analysis.AnchoredPairEnergy

theorem qPairWeight_mass : (∑' n : ℕ, ENNReal.ofReal (positiveQWeight n)) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg positiveQWeight_nonneg positiveQWeight_summable,
    positiveQWeight_tsum]
  simp

theorem qPairWeight_anchor : ENNReal.ofReal zetaTwo *
    ENNReal.ofReal (positiveQWeight 1) = 1 := by
  rw [← ENNReal.ofReal_mul zetaTwo_pos.le]
  simp [positiveQWeight, zetaTwo_pos.ne']

theorem qSquareEnergy_le_pairEnergy_anchor (g : ℕ → ℝ) :
    (∑' n : ℕ, ENNReal.ofReal (positiveQWeight n * g n ^ 2)) ≤
      (4 * ENNReal.ofReal zetaTwo) * countableJumpEnergy pairFlow g +
        2 * ENNReal.ofReal (g 1 ^ 2) := by
  have h := squareEnergy_le_pairEnergy_anchor
    (fun n : ℕ => ENNReal.ofReal (positiveQWeight n)) qPairWeight_mass 1
    (ENNReal.ofReal zetaTwo) qPairWeight_anchor g
  change (∑' n : ℕ, ENNReal.ofReal (positiveQWeight n) * ENNReal.ofReal (g n ^ 2)) ≤
    (4 * ENNReal.ofReal zetaTwo) * countableJumpEnergy pairFlow g +
      2 * ENNReal.ofReal (g 1 ^ 2) at h
  have he : (∑' n : ℕ, ENNReal.ofReal (positiveQWeight n * g n ^ 2)) =
      ∑' n : ℕ, ENNReal.ofReal (positiveQWeight n) * ENNReal.ofReal (g n ^ 2) := by
    apply tsum_congr
    intro n
    exact ENNReal.ofReal_mul (positiveQWeight_nonneg n)
  rw [he]
  exact h

/-- Finite complete pair variance forces a finite second moment, without
assuming a first moment or square integrability beforehand. -/
theorem qSquare_summable_of_pairEnergy_ne_top (g : ℕ → ℝ)
    (hD : countableJumpEnergy pairFlow g ≠ ⊤) :
    Summable (fun n : ℕ => positiveQWeight n * g n ^ 2) := by
  have htotal : (∑' n : ℕ, ENNReal.ofReal (positiveQWeight n * g n ^ 2)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (qSquareEnergy_le_pairEnergy_anchor g)
    finiteness
  have hs := ENNReal.summable_toReal htotal
  simpa only [ENNReal.toReal_ofReal (mul_nonneg (positiveQWeight_nonneg _) (sq_nonneg _))]
    using hs

theorem qSquare_summable_of_energy_ne_top
    (W : ℕ → ℕ → ℝ≥0∞) (g : ℕ → ℝ)
    (hpoincare : countableJumpEnergy pairFlow g ≤ countableJumpEnergy W g)
    (hD : countableJumpEnergy W g ≠ ⊤) :
    Summable (fun n : ℕ => positiveQWeight n * g n ^ 2) :=
  qSquare_summable_of_pairEnergy_ne_top g (ne_top_of_le_ne_top hD hpoincare)

end RiemannResearch.RH.QCountableJumpEnergy

/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QHeadCrossMoments
import RiemannResearch.Analysis.PolylogAbelBudget
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# One-sided reciprocal envelopes for signed cumulative Q moments
Source: the user's cumulative-moment agenda. Only an upper bound is required;
negative cumulative moments are allowed without a separate lower envelope.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QHeadCrossMoments
open ZetaTwoHilbert QPolylogTailEnergy
open RiemannResearch.Analysis RiemannResearch.Analysis.LogTailWeights

/-- An upper bound on cumulative signed cross moments controls positive Abel
variation. There is no lower-bound assumption on the individual moments. -/
theorem positiveCrossVariation_le_of_reciprocal_envelope
    (H : ℕ) (f g : QHilbert) (C : ℝ) (hC : 0 ≤ C)
    (hM : ∀ t : ℕ, 0 < t → t < H →
      headCross t f g ≤ C / ((t : ℝ) + 1)) :
    positiveCrossVariation 2 H f g ≤ C * reciprocalCrossBudget := by
  let w : ℕ → ℝ := fun n => 1 / ((n : ℝ) * (6 + Real.log (n : ℝ)) ^ 2)
  have hw : Summable w := by
    simpa only [w, Real.rpow_two] using summable_shifted_log_square
  have hwpos (n : ℕ) : 0 ≤ w n := by dsimp [w]; positivity
  have hsum : (∑ t ∈ Finset.range H, w (t + 1)) ≤ reciprocalCrossBudget := by
    have hb := hw.sum_le_tsum (Finset.range (H + 1)) (fun n _ => hwpos n)
    have he : (∑ n ∈ Finset.range (H + 1), w n) =
        ∑ t ∈ Finset.range H, w (t + 1) := by
      rw [Finset.sum_range_succ']
      simp [w]
    rw [he] at hb
    exact hb
  calc
    positiveCrossVariation 2 H f g ≤ ∑ t ∈ Finset.range H, C * w (t + 1) := by
      apply Finset.sum_le_sum
      intro t ht
      have htH : t < H := Finset.mem_range.mp ht
      have hm : headCross t f g ≤ C / ((t : ℝ) + 1) := by
        by_cases ht0 : t = 0
        · subst t
          simpa [headCross, qSequence_zero] using hC
        · exact hM t (Nat.pos_of_ne_zero ht0) htH
      have hmax : max (headCross t f g) 0 ≤ C / ((t : ℝ) + 1) :=
        max_le hm (div_nonneg hC (by positivity))
      have hdelta : 0 ≤ polylogTailProfile 2 (t + 1) - polylogTailProfile 2 t :=
        sub_nonneg.mpr (polylogTailProfile_monotone 2 (Nat.le_succ t))
      calc
        _ ≤ (polylogTailProfile 2 (t + 1) - polylogTailProfile 2 t) *
            (C / ((t : ℝ) + 1)) := mul_le_mul_of_nonneg_left hmax hdelta
        _ = C * ((polylogTailProfile 2 (t + 1) - polylogTailProfile 2 t) /
            ((t : ℝ) + 1)) := by ring
        _ ≤ C * w (t + 1) := by
          apply mul_le_mul_of_nonneg_left _ hC
          simpa only [w, Nat.cast_add, Nat.cast_one] using
            polylogTwo_increment_div_succ_le t
    _ = C * ∑ t ∈ Finset.range H, w (t + 1) := by rw [Finset.mul_sum]
    _ ≤ C * reciprocalCrossBudget := mul_le_mul_of_nonneg_left hsum hC

theorem positiveCrossVariation_le_third_of_reciprocal_envelope
    (H : ℕ) (f g : QHilbert) (C : ℝ) (hC : 0 ≤ C)
    (hM : ∀ t : ℕ, 0 < t → t < H →
      headCross t f g ≤ C / ((t : ℝ) + 1)) :
    positiveCrossVariation 2 H f g ≤ C / 3 := by
  calc
    _ ≤ C * reciprocalCrossBudget :=
      positiveCrossVariation_le_of_reciprocal_envelope H f g C hC hM
    _ ≤ C * ((1 : ℝ) / 3) :=
      mul_le_mul_of_nonneg_left reciprocalCrossBudget_le_third hC
    _ = C / 3 := by ring

end RiemannResearch.RH.QHeadCrossMoments

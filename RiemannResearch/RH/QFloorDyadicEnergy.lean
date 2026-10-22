import RiemannResearch.RH.QFloorDilation
import RiemannResearch.RH.ZetaTwoParitySignal
import RiemannResearch.RH.ZetaTwoReciprocalCompactness
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact dyadic energy for the existing Q floor dilation

Source: the user's unit-signal/dilation continuation request, 18 October 2026,
for the two-scale consumer. This module reuses the existing physical operator
and proves its complete even/odd energy identity and a sharper bound directly
from the inverse-square weights. It supplies no scalar lower-bound hypothesis
about the actual optimizer.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QFloorDilation
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParitySignal

/-- Exact even/odd decomposition of the complete Q energy; no tail is truncated. -/
theorem floorDilation_two_norm_sq_exact (f : QHilbert) :
    ‖floorDilation 2 (by norm_num) f‖ ^ 2 =
      ∑' k : ℕ, (positiveQWeight (2 * k) + positiveQWeight (2 * k + 1)) *
        (qSequence f k) ^ 2 := by
  let F : ℕ → ℝ := fun k =>
    positiveQWeight k * (qSequence (floorDilation 2 (by norm_num) f) k) ^ 2
  have he : Summable (fun k => F (2 * k)) :=
    (qSequence_square_summable _).comp_injective (by intro a b h; change 2 * a = 2 * b at h; omega)
  have ho : Summable (fun k => F (2 * k + 1)) :=
    (qSequence_square_summable _).comp_injective (by
      intro a b h
      change 2 * a + 1 = 2 * b + 1 at h
      omega)
  rw [qNorm_weighted_sq]
  change (∑' k, F k) = _
  rw [← tsum_even_add_odd he ho, ← he.tsum_add ho]
  apply tsum_congr
  intro k
  have heven : 2 * k / 2 = k := by omega
  have hodd : (2 * k + 1) / 2 = k := by omega
  simp only [F, floorDilation_sequence, heven, hodd]
  ring

/-- Pairwise inverse-square comparison; the zero block uses the physical zero extension. -/
theorem floorDilation_two_block_le (f : QHilbert) (k : ℕ) :
    (positiveQWeight (2 * k) + positiveQWeight (2 * k + 1)) * (qSequence f k) ^ 2 ≤
      (1 / 2 : ℝ) * (positiveQWeight k * (qSequence f k) ^ 2) := by
  by_cases hk : k = 0
  · simp [hk]
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have hZ := zetaTwo_pos
  have hodd : positiveQWeight (2 * k + 1) ≤ positiveQWeight (2 * k) := by
    unfold positiveQWeight
    apply div_le_div_of_nonneg_left zero_le_one
    · positivity
    · push_cast
      nlinarith [mul_pos hZ hkR]
  rw [positiveQWeight_mul] at hodd ⊢
  norm_num at hodd ⊢
  nlinarith [mul_le_mul_of_nonneg_right hodd (sq_nonneg (qSequence f k))]

/-- A sharper bound for the existing physical dyadic operator, proved directly in Q. -/
theorem floorDilation_two_norm_sq_le_half (f : QHilbert) :
    ‖floorDilation 2 (by norm_num) f‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖f‖ ^ 2 := by
  rw [floorDilation_two_norm_sq_exact, qNorm_weighted_sq, ← tsum_mul_left]
  have hs := (qSequence_square_summable f).mul_left (1 / 2 : ℝ)
  apply Summable.tsum_le_tsum (floorDilation_two_block_le f) _ hs
  exact Summable.of_nonneg_of_le
    (fun k => mul_nonneg (add_nonneg (positiveQWeight_nonneg _) (positiveQWeight_nonneg _))
      (sq_nonneg _)) (floorDilation_two_block_le f) hs

/-- The exact boundary term in physical floor dilation of the constant. -/
theorem floorDilation_two_qOne :
    floorDilation 2 (by norm_num) qOne = qOne - qPoint 0 := by
  apply qSequence_injective
  rw [floorDilation_sequence]
  change (fun n => qSequence qOne (n / 2)) = qSequenceLinear (qOne - qPoint 0)
  rw [map_sub]
  change (fun n => qSequence qOne (n / 2)) = qSequence qOne - qSequence (qPoint 0)
  funext n
  simp only [Pi.sub_apply, qSequence_qOne, qSequence_qPoint, qPointSequence, qOneSequence]
  by_cases h0 : n = 0
  · simp [h0]
  by_cases h1 : n = 1
  · simp [h1]
  have hn : n / 2 ≠ 0 := by omega
  simp [h0, h1, hn]

end RiemannResearch.RH.QFloorDilation

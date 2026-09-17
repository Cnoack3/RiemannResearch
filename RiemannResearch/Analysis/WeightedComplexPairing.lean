/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ArithmeticCumulativeEnergy
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Data.Complex.Basic

/-! A signed complex pairing with the exact weighted dual square norm. -/
noncomputable section
open scoped BigOperators Topology
open Filter

namespace RiemannResearch.Analysis.WeightedPairing

/-- Weighted Young inequality, used only to justify absolute summability. -/
theorem norm_mul_le_dual_add_energy (w : ℝ) (hw : 0 < w) (b M : ℂ) :
    ‖b * M‖ ≤ ‖b‖ ^ 2 / w + w * ‖M‖ ^ 2 := by
  rw [norm_mul]
  have h : ‖b‖ * ‖M‖ * w ≤ ‖b‖ ^ 2 + (w * ‖M‖) ^ 2 := by
    nlinarith [sq_nonneg (‖b‖ - w * ‖M‖), sq_nonneg ‖b‖, sq_nonneg (w * ‖M‖)]
  calc
    ‖b‖ * ‖M‖ ≤ (‖b‖ ^ 2 + (w * ‖M‖) ^ 2) / w := (le_div_iff₀ hw).2 h
    _ = ‖b‖ ^ 2 / w + w * ‖M‖ ^ 2 := by
      field_simp

/-- Square-summability of both weighted factors gives an actual convergent complex series. -/
theorem summable_pairing (w : ℕ → ℝ) (hw : ∀ n, 0 < w n) (b M : ℕ → ℂ)
    (hb : Summable (fun n => ‖b n‖ ^ 2 / w n))
    (hM : Summable (fun n => w n * ‖M n‖ ^ 2)) :
    Summable (fun n => b n * M n) :=
  (hb.add hM).of_norm_bounded (fun n => norm_mul_le_dual_add_energy _ (hw n) _ _)

/-- Exact finite weighted Cauchy-Schwarz estimate; the complex signed sum is not replaced in the statement. -/
theorem finite_pairing_norm_sq_le (w : ℕ → ℝ) (hw : ∀ n, 0 < w n)
    (b M : ℕ → ℂ) (s : Finset ℕ) :
    ‖∑ n ∈ s, b n * M n‖ ^ 2 ≤
      (∑ n ∈ s, ‖b n‖ ^ 2 / w n) * ∑ n ∈ s, w n * ‖M n‖ ^ 2 := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul s
    (r := fun n => ‖b n * M n‖)
    (f := fun n => ‖b n‖ ^ 2 / w n) (g := fun n => w n * ‖M n‖ ^ 2)
    (fun n _ => div_nonneg (sq_nonneg _) (hw n).le)
    (fun n _ => mul_nonneg (hw n).le (sq_nonneg _))
    (fun n _ => by rw [norm_mul, mul_pow]; field_simp [(hw n).ne'] <;> ring)
  have hn := norm_sum_le s (fun n => b n * M n)
  have hsum : 0 ≤ ∑ n ∈ s, ‖b n * M n‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hs : ‖∑ n ∈ s, b n * M n‖ ^ 2 ≤ (∑ n ∈ s, ‖b n * M n‖) ^ 2 := by
    nlinarith [norm_nonneg (∑ n ∈ s, b n * M n)]
  exact hs.trans hcs

/-- The infinite signed pairing bound, with both summability requirements explicit. -/
theorem pairing_norm_sq_le (w : ℕ → ℝ) (hw : ∀ n, 0 < w n) (b M : ℕ → ℂ)
    (hb : Summable (fun n => ‖b n‖ ^ 2 / w n))
    (hM : Summable (fun n => w n * ‖M n‖ ^ 2)) :
    ‖∑' n : ℕ, b n * M n‖ ^ 2 ≤
      (∑' n : ℕ, ‖b n‖ ^ 2 / w n) * ∑' n : ℕ, w n * ‖M n‖ ^ 2 := by
  have hp := summable_pairing w hw b M hb hM
  have hbound (N : ℕ) :
      ‖∑ n ∈ Finset.range N, b n * M n‖ ^ 2 ≤
        (∑' n : ℕ, ‖b n‖ ^ 2 / w n) * ∑' n : ℕ, w n * ‖M n‖ ^ 2 := by
    apply (finite_pairing_norm_sq_le w hw b M (Finset.range N)).trans
    apply mul_le_mul
    · exact sum_le_hasSum _ (fun n _ => div_nonneg (sq_nonneg _) (hw n).le) hb.hasSum
    · exact sum_le_hasSum _ (fun n _ => mul_nonneg (hw n).le (sq_nonneg _)) hM.hasSum
    · exact Finset.sum_nonneg (fun n _ => mul_nonneg (hw n).le (sq_nonneg _))
    · exact tsum_nonneg (fun n => div_nonneg (sq_nonneg _) (hw n).le)
  exact le_of_tendsto (hp.hasSum.tendsto_sum_nat.norm.pow 2) (Eventually.of_forall hbound)

/-- A zero signed pairing forces either a prefix mismatch or tail energy.
The prefix mismatch and tail pairing are separated before Cauchy--Schwarz.
Source: the proof combines the two signed pairing bounds in this module. -/
theorem prefix_obstruction_of_pairing_zero
    (w : ℕ → ℝ) (hw : ∀ n, 0 < w n) (b M : ℕ → ℂ)
    (hb : Summable (fun n => ‖b n‖ ^ 2 / w n))
    (hM : Summable (fun n => w n * ‖M n‖ ^ 2))
    (hz : (∑' n : ℕ, b n * M n) = 0) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, b n‖ ^ 2 ≤
      2 * (∑' n : ℕ, ‖b n‖ ^ 2 / w n) *
        (∑ n ∈ Finset.range N, w n * ‖1 - M n‖ ^ 2) +
      2 * (∑' k : ℕ, ‖b (k + N)‖ ^ 2 / w (k + N)) *
        (∑' n : ℕ, w n * ‖M n‖ ^ 2) := by
  have hsplit := (summable_pairing w hw b M hb hM).sum_add_tsum_nat_add N
  rw [hz] at hsplit
  have heq : (∑ n ∈ Finset.range N, b n) =
      (∑ n ∈ Finset.range N, b n * (1 - M n)) -
        (∑' k : ℕ, b (k + N) * M (k + N)) := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    linear_combination hsplit
  have hn := norm_sub_le
    (∑ n ∈ Finset.range N, b n * (1 - M n))
    (∑' k : ℕ, b (k + N) * M (k + N))
  rw [← heq] at hn
  have hsq : ‖∑ n ∈ Finset.range N, b n‖ ^ 2 ≤
      2 * ‖∑ n ∈ Finset.range N, b n * (1 - M n)‖ ^ 2 +
      2 * ‖∑' k : ℕ, b (k + N) * M (k + N)‖ ^ 2 := by
    nlinarith [norm_nonneg (∑ n ∈ Finset.range N, b n),
      norm_nonneg (∑ n ∈ Finset.range N, b n * (1 - M n)),
      norm_nonneg (∑' k : ℕ, b (k + N) * M (k + N)),
      sq_nonneg (‖∑ n ∈ Finset.range N, b n * (1 - M n)‖ -
        ‖∑' k : ℕ, b (k + N) * M (k + N)‖)]
  have hhead := finite_pairing_norm_sq_le w hw b (fun n => 1 - M n) (Finset.range N)
  have hhead' : ‖∑ n ∈ Finset.range N, b n * (1 - M n)‖ ^ 2 ≤
      (∑' n : ℕ, ‖b n‖ ^ 2 / w n) *
        (∑ n ∈ Finset.range N, w n * ‖1 - M n‖ ^ 2) := by
    exact hhead.trans (mul_le_mul_of_nonneg_right
      (sum_le_hasSum _ (fun n _ => div_nonneg (sq_nonneg _) (hw n).le) hb.hasSum)
      (Finset.sum_nonneg (fun n _ => mul_nonneg (hw n).le (sq_nonneg _))))
  have hbTail : Summable (fun k => ‖b (k + N)‖ ^ 2 / w (k + N)) := hb.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hMTail : Summable (fun k => w (k + N) * ‖M (k + N)‖ ^ 2) := hM.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have htail := pairing_norm_sq_le (fun k => w (k + N)) (fun k => hw (k + N))
    (fun k => b (k + N)) (fun k => M (k + N)) hbTail hMTail
  have hesplit := hM.sum_add_tsum_nat_add N
  have hpre_nonneg : 0 ≤ ∑ n ∈ Finset.range N, w n * ‖M n‖ ^ 2 :=
    Finset.sum_nonneg (fun n _ => mul_nonneg (hw n).le (sq_nonneg _))
  have htail_le : (∑' k : ℕ, w (k + N) * ‖M (k + N)‖ ^ 2) ≤
      ∑' n : ℕ, w n * ‖M n‖ ^ 2 := by linarith
  have htail' := htail.trans (mul_le_mul_of_nonneg_left htail_le
    (tsum_nonneg (fun k => div_nonneg (sq_nonneg _) (hw (k + N)).le)))
  nlinarith

end RiemannResearch.Analysis.WeightedPairing

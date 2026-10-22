/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.NearbyDilationGram
import RiemannResearch.RH.ParetoDilation
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! # Signed complete-Q energy certificates

Exact signed energy differences, finite-prefix/infinite-tail splitting, and a
one-sided tail certificate using the telescoping Pareto majorant.
No physical tail or negative term is discarded.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSignedEnergyCertificate
open ZetaTwoHilbert ZetaTwoProbability Pareto

def signedEnergy (f g : QHilbert) (n : ℕ) : ℝ :=
  qSequence f n ^ 2 - qSequence g n ^ 2

private theorem weight_scale (n : ℕ) (x : ℝ) :
    zetaTwo * (positiveQWeight n * x) = x / (n : ℝ) ^ 2 := by
  by_cases hn : n = 0
  · simp [hn, positiveQWeight]
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    unfold positiveQWeight
    field_simp [hnR, zetaTwo_pos.ne']

theorem signedEnergy_summable (f g : QHilbert) :
    Summable (fun n : ℕ => signedEnergy f g n / (n : ℝ) ^ 2) := by
  have hs : Summable (fun n : ℕ => positiveQWeight n * signedEnergy f g n) := by
    simpa only [signedEnergy, mul_sub] using
      (qSequence_square_summable f).sub (qSequence_square_summable g)
  simpa only [weight_scale] using hs.mul_left zetaTwo

theorem energy_difference_series (f g : QHilbert) :
    zetaTwo * (‖f‖ ^ 2 - ‖g‖ ^ 2) =
      ∑' n : ℕ, signedEnergy f g n / (n : ℝ) ^ 2 := by
  rw [qNorm_weighted_sq, qNorm_weighted_sq,
    ← (qSequence_square_summable f).tsum_sub (qSequence_square_summable g),
    ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [← mul_sub, weight_scale]
  rfl

theorem energy_difference_prefix_tail (f g : QHilbert) (K : ℕ) :
    zetaTwo * (‖f‖ ^ 2 - ‖g‖ ^ 2) =
      (∑ n ∈ Finset.range (K + 1), signedEnergy f g n / (n : ℝ) ^ 2) +
      ∑' k : ℕ, signedEnergy f g (k + (K + 1)) /
        ((k + (K + 1) : ℕ) : ℝ) ^ 2 := by
  rw [energy_difference_series,
    ← (signedEnergy_summable f g).sum_add_tsum_nat_add (K + 1)]

theorem energy_difference_lower (f g : QHilbert) (K : ℕ) (hK : 0 < K)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n, K < n → -C ≤ signedEnergy f g n) :
    (∑ n ∈ Finset.range (K + 1), signedEnergy f g n / (n : ℝ) ^ 2) -
        C / (K : ℝ) ≤ zetaTwo * (‖f‖ ^ 2 - ‖g‖ ^ 2) := by
  have hs := (summable_nat_add_iff (K + 1)).mpr (signedEnergy_summable f g)
  have hp : Summable (fun k : ℕ => positiveWeight (k + K)) :=
    (summable_nat_add_iff K).mpr positiveWeight_summable
  have htail : -C / (K : ℝ) ≤
      ∑' k : ℕ, signedEnergy f g (k + (K + 1)) /
        ((k + (K + 1) : ℕ) : ℝ) ^ 2 := by
    calc
      _ = ∑' k : ℕ, (-C) * positiveWeight (k + K) := by
        rw [tsum_mul_left, positiveWeight_tail_tsum K hK]
        ring
      _ ≤ _ := by
        apply Summable.tsum_le_tsum _ (hp.mul_left (-C)) hs
        intro k
        have hx : (0 : ℝ) < (k + K : ℕ) := by exact_mod_cast (by omega : 0 < k + K)
        have hw : 1 / ((k + (K + 1) : ℕ) : ℝ) ^ 2 ≤ positiveWeight (k + K) := by
          unfold positiveWeight
          push_cast
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          nlinarith only [hx]
        calc
          _ ≤ (-C) * (1 / ((k + (K + 1) : ℕ) : ℝ) ^ 2) :=
            mul_le_mul_of_nonpos_left hw (neg_nonpos.mpr hC)
          _ = -C / ((k + (K + 1) : ℕ) : ℝ) ^ 2 := by ring
          _ ≤ _ := div_le_div_of_nonneg_right (hb _ (by omega)) (sq_nonneg _)
  rw [energy_difference_prefix_tail f g K]
  simpa only [sub_eq_add_neg, neg_div, add_comm] using
    add_le_add_left htail
      (∑ n ∈ Finset.range (K + 1), signedEnergy f g n / (n : ℝ) ^ 2)
end RiemannResearch.RH.QSignedEnergyCertificate

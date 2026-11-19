import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# First-moment tail bounds for a vanishing head

An error vanishes on a finite head, is small on a growing intermediate interval
and has a global bound. Two complete tails of the nonnegative weight bound the
whole pairing. Sending the interval ratio to infinity gives the scalar squeeze.
-/

namespace RiemannResearch.Analysis.WeightedTail

private def weightsAfter (a : ℕ → ℝ) (N j : ℕ) : ℝ := if N ≤ j then a j else 0

private theorem hasSum_weightsAfter (a : ℕ → ℝ) (ha : Summable a) (N : ℕ) :
    HasSum (weightsAfter a N) (∑' k, a (k + N)) := by
  have ht := ((summable_nat_add_iff (f := a) N).mpr ha).hasSum
  have hh : ∑ i ∈ Finset.range N, weightsAfter a N i = 0 :=
    Finset.sum_eq_zero fun i hi => if_neg (not_le.mpr (Finset.mem_range.mp hi))
  apply (hasSum_nat_add_iff' (f := weightsAfter a N) N).mp
  rw [hh, sub_zero]
  simpa [weightsAfter, Nat.le_add_left] using ht

theorem abs_tsum_le_two_tails (a e f : ℕ → ℝ) (N T : ℕ) (B C : ℝ)
    (ha : Summable a) (hn : ∀ j, 0 ≤ a j) (hB : 0 ≤ B)
    (hhead : ∀ j ≤ N, e j = 0)
    (hmiddle : ∀ j, N < j → j ≤ T → |e j| ≤ B)
    (hall : ∀ j, |e j| ≤ C)
    (hf : ∀ j, |f j| ≤ a j * |e j|) :
    |∑' j, f j| ≤ B * (∑' k, a (k + N)) + C * (∑' k, a (k + T)) := by
  have hC : 0 ≤ C := (abs_nonneg (e 0)).trans (hall 0)
  have hs := ((hasSum_weightsAfter a ha N).mul_left B).add
    ((hasSum_weightsAfter a ha T).mul_left C)
  refine (Real.norm_eq_abs _ ▸ tsum_of_norm_bounded hs ?_)
  intro j
  rw [Real.norm_eq_abs]
  apply (hf j).trans
  change a j * |e j| ≤ B * weightsAfter a N j + C * weightsAfter a T j
  have hpost (S : ℕ) : 0 ≤ weightsAfter a S j := by
    unfold weightsAfter
    split <;> simp_all
  by_cases hj : j ≤ N
  · rw [hhead j hj, abs_zero, mul_zero]
    exact add_nonneg (mul_nonneg hB (hpost N)) (mul_nonneg hC (hpost T))
  · by_cases hjt : j ≤ T
    · have hbound := mul_le_mul_of_nonneg_left (hmiddle j (lt_of_not_ge hj) hjt) (hn j)
      rw [weightsAfter, if_pos (le_of_lt (lt_of_not_ge hj))]
      linarith [mul_nonneg hC (hpost T), mul_comm (a j) B]
    · have hbound := mul_le_mul_of_nonneg_left (hall j) (hn j)
      have ht : weightsAfter a T j = a j := if_pos (le_of_lt (lt_of_not_ge hjt))
      rw [ht]
      linarith [mul_nonneg hB (hpost N), mul_comm (a j) C]

end RiemannResearch.Analysis.WeightedTail

open Filter
namespace RiemannResearch.Analysis

theorem weighted_tail_squeeze (r A : ℝ) (hA : 0 ≤ A) (hr : 0 ≤ r)
    (h : ∀ K : ℕ, 2 ≤ K → ∀ b : ℝ, 0 < b → ∀ᶠ N : ℕ in atTop,
      r ≤ (1 + b * (N : ℝ)) * (A / (N : ℝ)) +
        (1 + 2 * (N : ℝ)) * (A / ((K : ℝ) * (N : ℝ)))) : r = 0 := by
  by_contra hne
  have hr' : 0 < r := lt_of_le_of_ne hr (Ne.symm hne)
  obtain ⟨K, hK⟩ := exists_nat_gt (max (2 : ℝ) (5 * A / r))
  have hKtwo : (2 : ℝ) < (K : ℝ) := lt_of_le_of_lt (le_max_left _ _) hK
  have hKn : 2 ≤ K := by exact_mod_cast hKtwo.le
  have hKpos : 0 < (K : ℝ) := by linarith
  have hlarge : 5 * A < (K : ℝ) * r :=
    (div_lt_iff₀ hr').mp (lt_of_le_of_lt (le_max_right _ _) hK)
  obtain ⟨N, hbound, hNK⟩ := ((h K hKn (1 / K) (one_div_pos.mpr hKpos)).and
    (eventually_ge_atTop K)).exists
  have hNge : (K : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNK
  have hNpos : 0 < (N : ℝ) := hKpos.trans_le hNge
  have hNtwo : 1 ≤ (N : ℝ) := by linarith
  have hprod : (K : ℝ) ≤ (K : ℝ) * (N : ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hNtwo hKpos.le
  have h1 := div_le_div_of_nonneg_left hA hKpos hNge
  have h2 := div_le_div_of_nonneg_left hA hKpos hprod
  have he :
      (1 + 1 / (K : ℝ) * (N : ℝ)) * (A / (N : ℝ)) +
        (1 + 2 * (N : ℝ)) * (A / ((K : ℝ) * (N : ℝ))) =
      A / (N : ℝ) + A / ((K : ℝ) * (N : ℝ)) + 3 * (A / (K : ℝ)) := by
    field_simp [hKpos.ne', hNpos.ne']
    <;> ring
  rw [he] at hbound
  have hf : r ≤ 5 * A / (K : ℝ) := by
    rw [mul_div_assoc]
    linarith
  have hc := (le_div_iff₀ hKpos).mp hf
  linarith [mul_comm r (K : ℝ)]

end RiemannResearch.Analysis

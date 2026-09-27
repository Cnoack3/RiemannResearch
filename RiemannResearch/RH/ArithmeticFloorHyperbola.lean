/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.DampedMobiusSeed
import RiemannResearch.Analysis.PositiveArithmeticPrefix
import Mathlib.Tactic.LinearCombination

/-!
# Exact finite hyperbola decomposition of centered arithmetic floor prefixes

The finite identity is the classical Dirichlet hyperbola rearrangement.
Every signed endpoint and density-tail term is retained.  This module does
not assume, or assert, any estimate for the Mertens function.
-/

open scoped BigOperators
open RiemannResearch.Analysis

namespace RiemannResearch.RH.Pareto
noncomputable section

private theorem positiveArithmeticPrefix_eq_range (w : ℕ → ℝ)
    (hw0 : w 0 = 0) (N : ℕ) :
    positiveArithmeticPrefix w N = ∑ d ∈ Finset.range (N+1), w d := by
  rw [Finset.sum_range_succ']
  simp [positiveArithmeticPrefix, hw0]

/-- Summing on the other side of the integer hyperbola, with the zero
index harmless under the explicit zero-weight hypothesis. -/
theorem arithmeticFloorPrefix_eq_sum_prefix (w : ℕ → ℝ)
    (hw0 : w 0 = 0) (N : ℕ) :
    arithmeticFloorPrefix w N =
      ∑ k ∈ Finset.range (N+1), positiveArithmeticPrefix w (N/k) := by
  classical
  calc
    _ = ∑ d ∈ Finset.range (N+1), ∑ k ∈ Finset.range (N+1),
        if d*k ≤ N then (if k = 0 then 0 else w d) else 0 := by
      unfold arithmeticFloorPrefix
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hd0 : d = 0
      · simp [hd0, hw0]
      · simpa only [mul_comm] using
          (RiemannResearch.RH.sum_floor_weight N d hd0 (w d)).symm
    _ = ∑ k ∈ Finset.range (N+1), ∑ d ∈ Finset.range (N+1),
        if d*k ≤ N then (if k = 0 then 0 else w d) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hk0 : k = 0
      · simp [hk0]
      have hkp : 0 < k := Nat.pos_of_ne_zero hk0
      simp only [if_neg hk0]
      rw [positiveArithmeticPrefix_eq_range w hw0]
      calc
        _ = ∑ d ∈ Finset.range (N/k+1), if d*k ≤ N then w d else 0 := by
          symm
          apply Finset.sum_subset
            (Finset.range_mono (Nat.succ_le_succ (Nat.div_le_self N k)))
          intro d hd hdsmall
          have hlarge : N/k < d := by
            simp only [Finset.mem_range] at hdsmall
            omega
          have hprod : ¬ d*k ≤ N := by
            intro hp
            have := (Nat.le_div_iff_mul_le hkp).mpr hp
            omega
          simp [hprod]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro d hd
          have hdq : d ≤ N/k := by
            exact Nat.le_of_lt_succ (Finset.mem_range.mp hd)
          simp [(Nat.le_div_iff_mul_le hkp).mp hdq]

private def arithmeticTailWeight (w : ℕ → ℝ) (y d : ℕ) : ℝ :=
  if y < d then w d else 0

private theorem arithmeticTailWeight_zero (w : ℕ → ℝ) (y : ℕ) :
    arithmeticTailWeight w y 0 = 0 := by
  simp [arithmeticTailWeight]

private theorem prefix_tail_eq_zero (w : ℕ → ℝ) {y t : ℕ} (ht : t ≤ y) :
    positiveArithmeticPrefix (arithmeticTailWeight w y) t = 0 := by
  unfold positiveArithmeticPrefix
  apply Finset.sum_eq_zero
  intro d hd
  have hdy : ¬ y < d+1 := by
    have := Finset.mem_range.mp hd
    omega
  simp [arithmeticTailWeight, hdy]

private theorem prefix_tail_eq_sub (w : ℕ → ℝ) (hw0 : w 0 = 0)
    {y t : ℕ} (hyt : y ≤ t) :
    positiveArithmeticPrefix (arithmeticTailWeight w y) t =
      positiveArithmeticPrefix w t - positiveArithmeticPrefix w y := by
  rw [positiveArithmeticPrefix_eq_range _ (arithmeticTailWeight_zero w y),
    positiveArithmeticPrefix_eq_range w hw0,
    positiveArithmeticPrefix_eq_range w hw0]
  have hhead : (∑ d ∈ Finset.range (t+1), if d ≤ y then w d else 0) =
      ∑ d ∈ Finset.range (y+1), w d := by
    calc
      _ = ∑ d ∈ Finset.range (y+1), if d ≤ y then w d else 0 := by
        symm
        apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hyt))
        intro d hd hdy
        have hdy' : ¬ d ≤ y := by
          simp only [Finset.mem_range] at hdy
          omega
        simp [hdy']
      _ = _ := by
        apply Finset.sum_congr rfl
        intro d hd
        simp [Nat.le_of_lt_succ (Finset.mem_range.mp hd)]
  rw [← hhead, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdy : d ≤ y
  · simp [arithmeticTailWeight, hdy, show ¬ y < d by omega]
  · simp [arithmeticTailWeight, hdy, show y < d by omega]

/-- Exact hyperbola decomposition at an arbitrary positive integer cutoff.
There is no absolute-value estimate or loss of cancellation here. -/
theorem arithmeticFloorPrefix_hyperbola (w : ℕ → ℝ) (hw0 : w 0 = 0)
    {N y : ℕ} (hy : 0 < y) (hyN : y ≤ N) :
    arithmeticFloorPrefix w N =
      (∑ d ∈ Finset.range (y+1), w d * (N/d : ℕ)) +
      (∑ k ∈ Finset.range (N/y), positiveArithmeticPrefix w (N/(k+1))) -
      (N/y : ℕ) * positiveArithmeticPrefix w y := by
  classical
  have hsplit : arithmeticFloorPrefix w N =
      (∑ d ∈ Finset.range (y+1), w d * (N/d : ℕ)) +
        arithmeticFloorPrefix (arithmeticTailWeight w y) N := by
    have hhead : (∑ d ∈ Finset.range (N+1),
          if d ≤ y then w d * (N/d : ℕ) else 0) =
        ∑ d ∈ Finset.range (y+1), w d * (N/d : ℕ) := by
      calc
        _ = ∑ d ∈ Finset.range (y+1),
            if d ≤ y then w d * (N/d : ℕ) else 0 := by
          symm
          apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hyN))
          intro d hd hdy
          have hd' : ¬ d ≤ y := by simp only [Finset.mem_range] at hdy; omega
          simp [hd']
        _ = _ := by
          apply Finset.sum_congr rfl
          intro d hd
          simp [Nat.le_of_lt_succ (Finset.mem_range.mp hd)]
    rw [← hhead]
    unfold arithmeticFloorPrefix
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hdy : d ≤ y
    · simp [arithmeticTailWeight, hdy, show ¬ y < d by omega]
    · simp [arithmeticTailWeight, hdy, show y < d by omega]
  rw [hsplit, arithmeticFloorPrefix_eq_sum_prefix _ (arithmeticTailWeight_zero w y)]
  have hcut : (∑ k ∈ Finset.range (N+1),
      positiveArithmeticPrefix (arithmeticTailWeight w y) (N/k)) =
      ∑ k ∈ Finset.range (N/y+1),
        positiveArithmeticPrefix (arithmeticTailWeight w y) (N/k) := by
    symm
    apply Finset.sum_subset
      (Finset.range_mono (Nat.succ_le_succ (Nat.div_le_self N y)))
    intro k hk hkcut
    have hklarge : N/y < k := by simp only [Finset.mem_range] at hkcut; omega
    have hkpos : 0 < k := lt_of_le_of_lt (Nat.zero_le (N/y)) hklarge
    have hq : N/k ≤ y := by
      have hNk : N < k*y := (Nat.div_lt_iff_lt_mul hy).mp hklarge
      have hbound : N/k < y := (Nat.div_lt_iff_lt_mul hkpos).mpr (by simpa [mul_comm] using hNk)
      omega
    exact prefix_tail_eq_zero w hq
  rw [hcut, Finset.sum_range_succ'
    (fun k => positiveArithmeticPrefix (arithmeticTailWeight w y) (N/k)) (N/y)]
  simp only [Nat.div_zero, positiveArithmeticPrefix_zero, add_zero]
  have htail : (∑ k ∈ Finset.range (N/y),
      positiveArithmeticPrefix (arithmeticTailWeight w y) (N/(k+1))) =
      (∑ k ∈ Finset.range (N/y), positiveArithmeticPrefix w (N/(k+1))) -
        (N/y : ℕ) * positiveArithmeticPrefix w y := by
    calc
      _ = ∑ k ∈ Finset.range (N/y),
          (positiveArithmeticPrefix w (N/(k+1)) - positiveArithmeticPrefix w y) := by
        apply Finset.sum_congr rfl
        intro k hk
        apply prefix_tail_eq_sub w hw0
        have hkq : k+1 ≤ N/y := Finset.mem_range.mp hk
        have hprod : (k+1)*y ≤ N := (Nat.le_div_iff_mul_le hy).mp hkq
        exact (Nat.le_div_iff_mul_le (by omega : 0 < k+1)).mpr (by simpa [mul_comm] using hprod)
      _ = _ := by simp [Finset.sum_sub_distrib]
  rw [htail]
  ring

/-- Complete centered decomposition: the finite fractional residues,
the transposed summatory part, and the entire signed density tail. -/
theorem arithmeticFloorPrefix_centered_hyperbola (w : ℕ → ℝ) (hw0 : w 0 = 0)
    (C : ℝ) {N y : ℕ} (hy : 0 < y) (hyN : y ≤ N) :
    arithmeticFloorPrefix w N - (N : ℝ)*C =
      -(∑ d ∈ Finset.range (y+1), (w d / (d : ℝ)) * residue d N) +
      (∑ k ∈ Finset.range (N/y), positiveArithmeticPrefix w (N/(k+1))) -
      (N/y : ℕ) * positiveArithmeticPrefix w y -
      (N : ℝ)*(C - ∑ d ∈ Finset.range (y+1), w d / (d : ℝ)) := by
  rw [arithmeticFloorPrefix_hyperbola w hw0 hy hyN]
  have hhead : (∑ d ∈ Finset.range (y+1), w d * (N/d : ℕ)) =
      (N : ℝ) * (∑ d ∈ Finset.range (y+1), w d / (d : ℝ)) -
        ∑ d ∈ Finset.range (y+1), (w d / (d : ℝ)) * residue d N := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hd0 : d = 0
    · simp [hd0, hw0]
    have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
    have hdiv : (residue d N : ℝ) + (d : ℝ) * (N/d : ℕ) = N := by
      unfold residue
      exact_mod_cast Nat.mod_add_div N d
    field_simp [hdR]
    linear_combination (w d) * hdiv
  rw [hhead]
  ring

end
end RiemannResearch.RH.Pareto

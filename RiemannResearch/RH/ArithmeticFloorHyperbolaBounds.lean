/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ArithmeticFloorHyperbola

open scoped BigOperators
open RiemannResearch.Analysis
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- A sharp elementary summation bound, proved by square-root telescoping. -/
theorem sum_inverse_sqrt_nat_succ_le (N : ℕ) :
    (∑ k ∈ Finset.range N, 1 / Real.sqrt ((k+1 : ℕ) : ℝ)) ≤
      2 * Real.sqrt (N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hs : 0 < Real.sqrt ((N+1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have hsq1 := Real.sq_sqrt (show (0 : ℝ) ≤ ((N+1 : ℕ) : ℝ) by positivity)
    have hsq0 := Real.sq_sqrt (show (0 : ℝ) ≤ (N : ℝ) by positivity)
    have hterm : 1 / Real.sqrt ((N+1 : ℕ) : ℝ) ≤
        2 * Real.sqrt ((N+1 : ℕ) : ℝ) - 2 * Real.sqrt (N : ℝ) := by
      apply (div_le_iff₀ hs).mpr
      have hd := sq_nonneg (Real.sqrt ((N+1 : ℕ) : ℝ) - Real.sqrt (N : ℝ))
      norm_num only [Nat.cast_add, Nat.cast_one] at hsq1 hd ⊢
      nlinarith
    linarith

private theorem sqrt_nat_div_le (N k : ℕ) (hk : 0 < k) :
    Real.sqrt (N/k : ℕ) ≤ Real.sqrt (N : ℝ) / Real.sqrt (k : ℝ) := by
  have hkp : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hk)
  have hq := Real.sq_sqrt (show (0 : ℝ) ≤ (N/k : ℕ) by positivity)
  have hn := Real.sq_sqrt (show (0 : ℝ) ≤ (N : ℝ) by positivity)
  have hk' := Real.sq_sqrt (show (0 : ℝ) ≤ (k : ℝ) by positivity)
  have hprod : ((N/k : ℕ) : ℝ) * k ≤ N := by
    exact_mod_cast Nat.div_mul_le_self N k
  have hnonneg : 0 ≤ Real.sqrt (N/k : ℕ) * Real.sqrt (k : ℝ) := by positivity
  apply (le_div_iff₀ hkp).mpr
  nlinarith [Real.sqrt_nonneg (N : ℝ), sq_nonneg
    (Real.sqrt (N/k : ℕ) * Real.sqrt (k : ℝ) - Real.sqrt (N : ℝ)),
    show (Real.sqrt (N/k : ℕ) * Real.sqrt (k : ℝ))^2 ≤ (Real.sqrt (N : ℝ))^2 by
      rw [mul_pow, hq, hk', hn]; exact hprod]

private theorem residue_sum_abs_le (w : ℕ → ℝ) (hw0 : w 0 = 0)
    {W : ℝ} (hW : 0 ≤ W)
    (hw : ∀ d : ℕ, 0 < d → |w d| ≤ W / Real.sqrt (d : ℝ)) (N y : ℕ) :
    |∑ d ∈ Finset.range (y+1), (w d / (d : ℝ)) * residue d N| ≤
      2 * W * Real.sqrt (y : ℝ) := by
  calc
    _ ≤ ∑ d ∈ Finset.range (y+1), |(w d / (d : ℝ)) * residue d N| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.range (y+1), W * (1 / Real.sqrt (d : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      by_cases hd0 : d = 0
      · simp [hd0, hw0]
      have hdp : 0 < d := Nat.pos_of_ne_zero hd0
      have hdR : (0 : ℝ) < d := by exact_mod_cast hdp
      have hr0 : 0 ≤ residue d N := by unfold residue; positivity
      have hr : residue d N ≤ d := by
        unfold residue
        exact_mod_cast (Nat.mod_lt N hdp).le
      rw [abs_mul, abs_div, abs_of_pos hdR, abs_of_nonneg hr0]
      calc
        _ ≤ (|w d| / (d : ℝ)) * d :=
          mul_le_mul_of_nonneg_left hr (by positivity)
        _ = |w d| := div_mul_cancel₀ _ (ne_of_gt hdR)
        _ ≤ W / Real.sqrt (d : ℝ) := hw d hdp
        _ = _ := by ring
    _ = W * ∑ d ∈ Finset.range y, 1 / Real.sqrt ((d+1 : ℕ) : ℝ) := by
      rw [← Finset.mul_sum, Finset.sum_range_succ']
      simp
    _ ≤ W * (2 * Real.sqrt (y : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_inverse_sqrt_nat_succ_le y) hW
    _ = _ := by ring

/-- A quantitative form of the exact hyperbola decomposition for arbitrary
signed weights.  The input `hP` is only needed above the chosen cutoff;
the reciprocal tail `hD` keeps the actual centering `C` explicit. -/
theorem arithmeticFloorPrefix_centered_hyperbola_bound
    (w : ℕ → ℝ) (hw0 : w 0 = 0) (C : ℝ)
    {N y : ℕ} (hy : 0 < y) (hyN : y ≤ N)
    {W B D Q : ℝ} (hW : 0 ≤ W) (hB : 0 ≤ B) (_hD0 : 0 ≤ D) (hQ : 0 < Q)
    (hw : ∀ d : ℕ, 0 < d → |w d| ≤ W / Real.sqrt (d : ℝ))
    (hP : ∀ t : ℕ, y ≤ t →
      |positiveArithmeticPrefix w t| ≤ B * Real.sqrt (t : ℝ) / Q)
    (hD : |C - ∑ d ∈ Finset.range (y+1), w d / (d : ℝ)| ≤
      D / (Real.sqrt (y : ℝ) * Q)) :
    |arithmeticFloorPrefix w N - (N : ℝ) * C| ≤
      2 * W * Real.sqrt (y : ℝ) +
        (3*B+D) * (N : ℝ) / (Real.sqrt (y : ℝ) * Q) := by
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hsy : 0 < Real.sqrt (y : ℝ) := Real.sqrt_pos.mpr hyR
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hsN : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hsy2 := Real.sq_sqrt hyR.le
  have hsN2 := Real.sq_sqrt hN0
  have hprod : ((N/y : ℕ) : ℝ) * y ≤ N := by
    exact_mod_cast Nat.div_mul_le_self N y
  have hcross : Real.sqrt (N : ℝ) * Real.sqrt (N/y : ℕ) ≤
      (N : ℝ) / Real.sqrt (y : ℝ) := by
    have hquot := sqrt_nat_div_le N y hy
    calc
      _ ≤ Real.sqrt (N : ℝ) * (Real.sqrt (N : ℝ) / Real.sqrt (y : ℝ)) :=
        mul_le_mul_of_nonneg_left hquot hsN
      _ = _ := by rw [← mul_div_assoc, ← sq, hsN2]
  have hmiddle : |∑ k ∈ Finset.range (N/y), positiveArithmeticPrefix w (N/(k+1))| ≤
      2*B*(N : ℝ)/(Real.sqrt (y : ℝ)*Q) := by
    calc
      _ ≤ ∑ k ∈ Finset.range (N/y), |positiveArithmeticPrefix w (N/(k+1))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (N/y),
          (B*Real.sqrt (N : ℝ)/Q) * (1/Real.sqrt ((k+1 : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkq : k+1 ≤ N/y := Finset.mem_range.mp hk
        have ht : y ≤ N/(k+1) := by
          apply (Nat.le_div_iff_mul_le (by omega : 0 < k+1)).mpr
          simpa [mul_comm] using (Nat.le_div_iff_mul_le hy).mp hkq
        calc
          _ ≤ B * Real.sqrt (N/(k+1) : ℕ) / Q := hP _ ht
          _ ≤ B * (Real.sqrt (N : ℝ) / Real.sqrt ((k+1 : ℕ) : ℝ)) / Q :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left (sqrt_nat_div_le N (k+1) (by omega)) hB) hQ.le
          _ = _ := by ring
      _ = (B*Real.sqrt (N : ℝ)/Q) *
          (∑ k ∈ Finset.range (N/y), 1/Real.sqrt ((k+1 : ℕ) : ℝ)) := by
        rw [Finset.mul_sum]
      _ ≤ (B*Real.sqrt (N : ℝ)/Q) * (2*Real.sqrt (N/y : ℕ)) :=
        mul_le_mul_of_nonneg_left (sum_inverse_sqrt_nat_succ_le (N/y)) (by positivity)
      _ = (2*B/Q) * (Real.sqrt (N : ℝ)*Real.sqrt (N/y : ℕ)) := by ring
      _ ≤ (2*B/Q) * ((N : ℝ)/Real.sqrt (y : ℝ)) :=
        mul_le_mul_of_nonneg_left hcross (by positivity)
      _ = _ := by ring
  have hend : |(N/y : ℕ) * positiveArithmeticPrefix w y| ≤
      B*(N : ℝ)/(Real.sqrt (y : ℝ)*Q) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N/y : ℕ))]
    calc
      _ ≤ (N/y : ℕ) * (B*Real.sqrt (y : ℝ)/Q) :=
        mul_le_mul_of_nonneg_left (hP y le_rfl) (by positivity)
      _ = (B/(Real.sqrt (y : ℝ)*Q)) * (((N/y : ℕ) : ℝ) * y) := by
        field_simp [ne_of_gt hsy, ne_of_gt hQ]
        rw [hsy2]
      _ ≤ (B/(Real.sqrt (y : ℝ)*Q)) * N :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = _ := by ring
  have htail : |(N : ℝ)*(C - ∑ d ∈ Finset.range (y+1), w d / (d : ℝ))| ≤
      D*(N : ℝ)/(Real.sqrt (y : ℝ)*Q) := by
    rw [abs_mul, abs_of_nonneg hN0]
    calc
      _ ≤ (N : ℝ)*(D/(Real.sqrt (y : ℝ)*Q)) := mul_le_mul_of_nonneg_left hD hN0
      _ = _ := by ring
  rw [arithmeticFloorPrefix_centered_hyperbola w hw0 C hy hyN]
  have htri := abs_sub_le
    (-(∑ d ∈ Finset.range (y+1), (w d / (d : ℝ)) * residue d N) +
      (∑ k ∈ Finset.range (N/y), positiveArithmeticPrefix w (N/(k+1))) -
      (N/y : ℕ) * positiveArithmeticPrefix w y)
    0
    ((N : ℝ)*(C - ∑ d ∈ Finset.range (y+1), w d / (d : ℝ)))
  have htri2 := abs_sub_le
    (-(∑ d ∈ Finset.range (y+1), (w d / (d : ℝ)) * residue d N) +
      (∑ k ∈ Finset.range (N/y), positiveArithmeticPrefix w (N/(k+1))))
    0
    ((N/y : ℕ) * positiveArithmeticPrefix w y)
  simp only [sub_zero, zero_sub, abs_neg] at htri htri2
  have htri3 := abs_add_le
    (-(∑ d ∈ Finset.range (y+1), (w d / (d : ℝ)) * residue d N))
    (∑ k ∈ Finset.range (N/y), positiveArithmeticPrefix w (N/(k+1)))
  rw [abs_neg] at htri3
  have hh := residue_sum_abs_le w hw0 hW hw N y
  calc
    _ ≤ 2*W*Real.sqrt (y : ℝ) + 2*B*(N : ℝ)/(Real.sqrt (y : ℝ)*Q) +
        B*(N : ℝ)/(Real.sqrt (y : ℝ)*Q) + D*(N : ℝ)/(Real.sqrt (y : ℝ)*Q) := by
      linarith
    _ = _ := by ring

end
end RiemannResearch.RH.Pareto

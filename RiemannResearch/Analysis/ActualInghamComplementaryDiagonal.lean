/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MobiusLCMTotientExpansion
import Mathlib.Analysis.PSeries

/-!
# The diagonal of the actual truncated Möbius error

Complementary divisors constrain each progression in the square expansion.
Summing their inverse squares and applying the finite gcd diagonalization
estimates the actual Dirichlet diagonal uniformly in the truncation.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.InghamMollifier

private theorem interval_multiples_sum {d : ℕ} (_hd : 0 < d) (N : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 N, if d ∣ n then f n else 0) =
      ∑ i ∈ Finset.range (N / d), f (d*(i+1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hi : Finset.Icc 1 (N+1) = insert (N+1) (Finset.Icc 1 N) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hi, Finset.sum_insert (by simp), ih]
    by_cases hv : d ∣ N+1
    · have hx := Nat.succ_div_of_dvd hv
      have he : N+1 = d * (N/d+1) := by rw [← hx, Nat.mul_div_cancel' hv]
      rw [if_pos hv, hx, Finset.sum_range_succ, he, add_comm]
    · rw [if_neg hv, Nat.succ_div_of_not_dvd hv, zero_add]

/-- The inverse squares past an arbitrary threshold on one progression are
at most twice the reciprocal of the product of modulus and threshold. -/
theorem reciprocal_square_multiple_tail {d A : ℕ} (hd : 0 < d) (hA : 0 < A) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
      if d ∣ n ∧ A < n then 1 / (n:ℝ)^2 else 0) ≤ 2 / ((A:ℝ) * d) := by
  let g : ℕ → ℝ := fun i => (max (A:ℝ) (d*(i+1:ℕ):ℕ))⁻¹
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hAR : (0:ℝ) < A := by exact_mod_cast hA
  have hstep (i : ℕ) :
      (if A < d*(i+1) then 1 / ((d*(i+1):ℕ):ℝ)^2 else 0) ≤
        2/(d:ℝ) * (g i - g (i+1)) := by
    have hi : (0:ℝ) ≤ i := Nat.cast_nonneg _
    by_cases h : A < d*(i+1)
    · have hr : (A:ℝ) ≤ (d:ℝ)*(i+1) := by exact_mod_cast h.le
      have hr' : (A:ℝ) ≤ (d:ℝ)*((i:ℝ)+1+1) := by linarith
      rw [if_pos h]
      simp only [g, Nat.cast_mul, Nat.cast_add, Nat.cast_one, max_eq_right hr, max_eq_right hr']
      field_simp
      nlinarith [mul_nonneg hdR.le hi, mul_nonneg (sq_nonneg (d:ℝ)) hi]
    · rw [if_neg h]
      apply mul_nonneg (by positivity)
      apply sub_nonneg.mpr
      apply inv_anti₀ (lt_of_lt_of_le hAR (le_max_left _ _))
      apply max_le_max_left
      exact_mod_cast (Nat.mul_le_mul_left d (Nat.le_succ (i+1)))
  have hsum (M : ℕ) : (∑ i ∈ Finset.range M,
      if A < d*(i+1) then 1 / ((d*(i+1):ℕ):ℝ)^2 else 0) ≤ 2/(d:ℝ)*(g 0 - g M) := by
    induction M with
    | zero => simp
    | succ M ih => rw [Finset.sum_range_succ]; linarith [hstep M]
  have h0 : g 0 ≤ (A:ℝ)⁻¹ := inv_anti₀ hAR (le_max_left _ _)
  have hn : 0 ≤ g (N/d) := inv_nonneg.mpr (hAR.le.trans (le_max_left _ _))
  calc
    _ = ∑ n ∈ Finset.Icc 1 N, if d ∣ n then
        (if A < n then 1 / (n:ℝ)^2 else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro n _
      by_cases h : d ∣ n <;> simp [h]
    _ = _ := interval_multiples_sum hd N _
    _ ≤ 2/(d:ℝ) * (g 0 - g (N/d)) := hsum _
    _ ≤ 2/(d:ℝ) * (A:ℝ)⁻¹ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

private noncomputable def weight (n : ℕ) : ℝ := (n : ℝ) ^ (-(3/2 : ℝ))
private noncomputable def weightTotal : ℝ := ∑' n : ℕ, weight n
private theorem weight_nonneg (n : ℕ) : 0 ≤ weight n := by unfold weight; positivity
private theorem weight_sum : Summable weight := Real.summable_nat_rpow.mpr (by norm_num)

private theorem multiple_weight_le {k : ℕ} (hk : 0 < k) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, if k ∣ n then weight n else 0) ≤ weight k * weightTotal := by
  rw [interval_multiples_sum hk N]
  have hmul (j : ℕ) : weight (k*(j+1)) = weight k * weight (j+1) := by
    simp only [weight, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  simp only [hmul, ← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (weight_nonneg k)
  have h := (summable_nat_add_iff 1).mpr weight_sum
  have h' := h.sum_le_tsum (Finset.range (N/k)) (fun j _ => weight_nonneg (j+1))
  apply h'.trans
  have h0 := weight_sum.tsum_eq_zero_add
  change _ ≤ ∑' n, weight n
  linarith [weight_nonneg 0]

private theorem inv_pair_le_gcd_weight {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    1 / (((max a b : ℕ):ℝ) * Nat.lcm a b) ≤
      weight a * weight b * (Nat.gcd a b : ℝ) := by
  have haR : (0:ℝ) < a := by exact_mod_cast ha
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  have hM : (0:ℝ) < (max a b : ℕ) := by exact_mod_cast ha.trans_le (le_max_left a b)
  have hL : (0:ℝ) < Nat.lcm a b := by exact_mod_cast Nat.lcm_pos ha hb
  have hG : (0:ℝ) < Nat.gcd a b := by exact_mod_cast Nat.gcd_pos_of_pos_left b ha
  have hm : (Nat.gcd a b : ℝ)*(Nat.lcm a b : ℝ) = (a:ℝ)*b := by
    exact_mod_cast Nat.gcd_mul_lcm a b
  have hmax1 : (a:ℝ) ≤ (max a b : ℕ) := by exact_mod_cast le_max_left a b
  have hmax2 : (b:ℝ) ≤ (max a b : ℕ) := by exact_mod_cast le_max_right a b
  have hroot : Real.sqrt ((a:ℝ)*b) ≤ (max a b : ℕ) := by
    apply (Real.sqrt_le_iff).2
    exact ⟨hM.le, by simpa only [pow_two] using (mul_le_mul hmax1 hmax2 hbR.le hM.le)⟩
  have he (k : ℕ) (h : 0 < (k:ℝ)) :
      weight k = ((k:ℝ) * Real.sqrt k)⁻¹ := by
    rw [weight, Real.rpow_neg h.le, show (3/2:ℝ) = 1 + 1/2 by norm_num,
      Real.rpow_add h, Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [he a haR, he b hbR]
  have hsa := Real.sqrt_pos.mpr haR
  have hsb := Real.sqrt_pos.mpr hbR
  rw [Real.sqrt_mul haR.le] at hroot
  have heq : (Nat.gcd a b : ℝ)* (Nat.lcm a b : ℝ) * (max a b : ℕ) =
      ((a:ℝ)*b) * (max a b : ℕ) := by rw [hm]
  apply (div_le_iff₀ (mul_pos hM hL)).mpr
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left hroot (mul_nonneg haR.le hbR.le)]

private def pairConstant : ℝ := weightTotal^2 * ∑' n : ℕ, (n:ℝ) ^ (-(2:ℝ))

private theorem pair_sum_le (N : ℕ) :
    (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
      1 / (((max a b : ℕ):ℝ) * Nat.lcm a b)) ≤ pairConstant := by
  calc
    _ ≤ ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
          weight a * weight b * (Nat.gcd a b : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      exact Finset.sum_le_sum (fun b hb => inv_pair_le_gcd_weight
        (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hb).1)
    _ = _ := gcd_cutoff_energy N weight
    _ ≤ ∑ k ∈ Finset.Icc 1 N, (weightTotal^2 * (k:ℝ) ^ (-(2:ℝ))) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkR : 0 < (k:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).1
      have hnn : 0 ≤ ∑ d ∈ Finset.Icc 1 N, (if k ∣ d then weight d else 0) :=
        Finset.sum_nonneg (fun d _ => by split_ifs <;> first | exact weight_nonneg d | rfl)
      have hsq := pow_le_pow_left₀ hnn (multiple_weight_le (Finset.mem_Icc.mp hk).1 N) 2
      have ht : (Nat.totient k : ℝ) ≤ k := by exact_mod_cast Nat.totient_le k
      have hw : (k:ℝ) * (weight k)^2 = (k:ℝ)^(-(2:ℝ)) := by
        have h2 : (weight k)^2 = (k:ℝ)^(-(3:ℝ)) := by
          rw [weight, ← Real.rpow_natCast, ← Real.rpow_mul hkR.le]
          norm_num
        rw [h2]
        calc
          _ = (k:ℝ)^(1:ℝ) * (k:ℝ)^(-(3:ℝ)) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hkR]; norm_num
      calc
        _ ≤ (k:ℝ) * (weight k * weightTotal)^2 :=
          mul_le_mul ht hsq (sq_nonneg _) hkR.le
        _ = _ := by rw [mul_pow, ← mul_assoc, hw, mul_comm]
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact (Real.summable_nat_rpow.mpr (by norm_num : -(2:ℝ)< -1)).sum_le_tsum _
        (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

private def complementary (X n r : ℕ) : ℝ := if r ∣ n ∧ X*r<n then 1 else 0

private theorem complementary_nonneg (X n r : ℕ) : 0 ≤ complementary X n r := by
  unfold complementary
  split_ifs <;> norm_num

/-- Cancellation of the complete Möbius divisor sum converts the original
lower divisor cutoff into a restriction on its complementary divisor. -/
private theorem abs_truncated_le_complementary {X n N : ℕ} (hX : 1 ≤ X)
    (hXn : X < n) (hn : n ≤ N) :
    |truncatedMobiusDivisorSum X n| ≤ ∑ r ∈ Finset.Icc 1 N, complementary X n r := by
  have hpos : 0<n := by omega
  have hne : n ≠ 1 := by omega
  have hfull : (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ)) = 0 := by
    have h := truncatedMobiusDivisorSum_of_le (X := n) (n := n) le_rfl
    rw [if_neg hne] at h
    rw [← h, truncatedMobiusDivisorSum]
    apply Finset.sum_congr rfl
    intro d hd
    exact (if_pos (Nat.le_of_dvd hpos (Nat.dvd_of_mem_divisors hd))).symm
  let f (d : ℕ) : ℝ := if X<d then (ArithmeticFunction.moebius d : ℝ) else 0
  have hsplit : truncatedMobiusDivisorSum X n = -(∑ d ∈ n.divisors, f d) := by
    apply eq_neg_of_add_eq_zero_left
    calc
      _ = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) := by
        rw [truncatedMobiusDivisorSum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro d _
        by_cases hd : X < d
        · simp [f, hd, not_le.mpr hd]
        · simp [f, hd, le_of_not_gt hd]
      _ = 0 := hfull
  rw [hsplit, abs_neg, ← Nat.sum_div_divisors n f]
  have hsupport : n.divisors ⊆ Finset.Icc 1 N := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
      (Nat.le_of_dvd hpos (Nat.dvd_of_mem_divisors hd)).trans hn⟩
  calc
    _ ≤ ∑ r ∈ n.divisors, |f (n/r)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ n.divisors, complementary X n r := by
      apply Finset.sum_le_sum
      intro r hr
      have hrd := Nat.dvd_of_mem_divisors hr
      by_cases hj : X < n/r
      · have hpr : X*r < n := by
          simpa only [Nat.div_mul_cancel hrd] using
            (Nat.mul_lt_mul_of_pos_right hj (Nat.pos_of_mem_divisors hr))
        have both : r ∣ n ∧ X*r < n := ⟨hrd,hpr⟩
        simp only [f, if_pos hj, complementary, if_pos both]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n/r))
      · simp only [f, if_neg hj, abs_zero]
        exact complementary_nonneg _ _ _
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsupport
      (fun i _ _ => complementary_nonneg X n i)

private theorem finite_diagonal_bound {X : ℕ} (hX : 1 ≤ X) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, if X<n then (truncatedMobiusDivisorSum X n)^2 / (n:ℝ)^2 else 0) ≤
      2/(X:ℝ)*pairConstant := by
  let S := Finset.Icc 1 N
  let F := fun a b n : ℕ =>
    if Nat.lcm a b ∣ n ∧ X * max a b < n then 1/(n:ℝ)^2 else 0
  have hxR : 0 < (X:ℝ) := by exact_mod_cast hX
  have hf (n : ℕ) (hn : n ∈ S) :
      (if X<n then (truncatedMobiusDivisorSum X n)^2 / (n:ℝ)^2 else 0) ≤
        ∑ a ∈ S, ∑ b ∈ S, F a b n := by
    by_cases hXn : X<n
    · rw [if_pos hXn]
      have hs := pow_le_pow_left₀ (abs_nonneg _) (abs_truncated_le_complementary hX hXn
        (Finset.mem_Icc.mp hn).2) 2
      rw [sq_abs] at hs
      calc
        _ ≤ (∑ a ∈ S, complementary X n a)^2 / (n:ℝ)^2 :=
          div_le_div_of_nonneg_right hs (sq_nonneg _)
        _ = _ := by
          rw [pow_two]
          simp only [Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          have hg : (Nat.lcm a b ∣ n ∧ X * max a b < n) ↔
              (a ∣ n ∧ X*a<n) ∧ (b ∣ n ∧ X*b<n) := by
            have hmm : X * max a b = max (X*a) (X*b) := by
              rcases le_total a b with h | h
              · rw [max_eq_right h, max_eq_right (Nat.mul_le_mul_left X h)]
              · rw [max_eq_left h, max_eq_left (Nat.mul_le_mul_left X h)]
            rw [Nat.lcm_dvd_iff, hmm, max_lt_iff]
            tauto
          dsimp only [F]
          simp only [hg, complementary]
          by_cases ha : a ∣ n ∧ X*a<n <;> by_cases hb : b ∣ n ∧ X*b<n <;> simp [ha,hb]
    · rw [if_neg hXn]
      apply Finset.sum_nonneg
      intro a _
      apply Finset.sum_nonneg
      intro b _
      dsimp only [F]
      split_ifs <;> positivity
  calc
    _ ≤ ∑ n ∈ S, ∑ a ∈ S, ∑ b ∈ S, F a b n := Finset.sum_le_sum hf
    _ = ∑ a ∈ S, ∑ n ∈ S, ∑ b ∈ S, F a b n := Finset.sum_comm
    _ = ∑ a ∈ S, ∑ b ∈ S, ∑ n ∈ S, F a b n := by
      exact Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ ≤ ∑ a ∈ S, ∑ b ∈ S, 2/(X:ℝ) * (1/(((max a b : ℕ):ℝ) * Nat.lcm a b)) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      have hl := Nat.lcm_pos (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hb).1
      have hm : 0 < max a b := le_trans (Finset.mem_Icc.mp ha).1 (le_max_left a b)
      have h := reciprocal_square_multiple_tail hl (Nat.mul_pos hX hm) N
      change (∑ n ∈ S, F a b n) ≤ _ at h
      apply h.trans_eq
      push_cast
      ring
    _ ≤ _ := by
      simp only [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (pair_sum_le N) (by positivity)

/-- The actual diagonal at exponent two has order 1/X with an absolute
constant, uniformly in X. -/
theorem exists_truncatedMobiusDivisorSum_diagonal_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : ℕ}, 1 ≤ X →
      (∑' k : ℕ, (truncatedMobiusDivisorSum X (k+X+1))^2 *
        ((k+X+1 : ℕ):ℝ) ^ (-(2:ℝ))) ≤ C / X := by
  have hpc : 0 ≤ pairConstant := mul_nonneg (sq_nonneg _)
    (tsum_nonneg (fun n : ℕ => Real.rpow_nonneg (Nat.cast_nonneg _) _))
  refine ⟨2*pairConstant+1, by linarith, ?_⟩
  intro X hX
  have hx : (0:ℝ) < X := by exact_mod_cast hX
  let f (n : ℕ) := (truncatedMobiusDivisorSum X n)^2 / (n:ℝ)^2
  have he (M : ℕ) : (∑ k ∈ Finset.range M, f (k+X+1)) =
      ∑ n ∈ Finset.Icc 1 (X+M), if X<n then f n else 0 := by
    induction M with
    | zero =>
      simp only [Nat.add_zero, Finset.range_zero, Finset.sum_empty]
      symm
      exact Finset.sum_eq_zero (fun n hn => if_neg (not_lt_of_ge (Finset.mem_Icc.mp hn).2))
    | succ M ih =>
      have hi : Finset.Icc 1 (X + (M+1)) = insert (X+M+1) (Finset.Icc 1 (X+M)) := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [Finset.sum_range_succ, hi, Finset.sum_insert (by simp), ih,
        if_pos (by omega : X < X+M+1), Nat.add_comm M X, add_comm]
  have hp (n : ℕ) : (n:ℝ)^(-(2:ℝ)) = ((n:ℝ)^2)⁻¹ := by
    rw [Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_two]
  have hs := summable_truncatedMobiusDivisorSum_tail_energy X (by norm_num : 1 < (2:ℝ))
  apply le_of_tendsto hs.hasSum.tendsto_sum_nat
  apply Filter.Eventually.of_forall
  intro M
  simp only [hp, ← div_eq_mul_inv]
  change (∑ k ∈ Finset.range M, f (k+X+1)) ≤ _
  rw [he]
  refine (finite_diagonal_bound hX (X+M)).trans ?_
  apply (le_div_iff₀ hx).2
  field_simp
  linarith

/-- The same uniform bound for every exponent at least two, in the exact
signed lcm normalization appearing in the actual translated mean square. -/
theorem exists_lcm_diagonal_le_of_two_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : ℕ}, 1 ≤ X → ∀ {p : ℝ}, 2 ≤ p →
      ‖riemannZeta (p : ℂ)‖ * truncatedMobiusLCMForm X p - 1 ≤ C / X := by
  obtain ⟨C, hC, hD⟩ := exists_truncatedMobiusDivisorSum_diagonal_bound
  refine ⟨C, hC, ?_⟩
  intro X hX p hp
  have hp' : 1 < p := by linarith
  rw [← truncatedMobiusDivisorSum_tail_energy_eq_lcm hX hp']
  refine le_trans ?_ (hD hX)
  apply (summable_truncatedMobiusDivisorSum_tail_energy X hp').tsum_le_tsum _
    (summable_truncatedMobiusDivisorSum_tail_energy X (by norm_num : 1 < (2:ℝ)))
  intro k
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ k+X+1 by omega))
    (by linarith)

end RiemannResearch.Analysis.InghamMollifier

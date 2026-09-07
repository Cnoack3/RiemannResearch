import RiemannResearch.RH.NymanInverseMobius
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# An explicit weighted coefficient bound for the actual conductor inverse

This is the coefficient estimate (9.7) of the Nyman–Weil continuation.
The proof retains the exact Möbius recurrence, bounds |μ| by one, and
inducts on the cutoff after separating the multiples of the conductor.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH

private theorem sum_one_div_sqrt_range_le (M : ℕ) :
    (∑ k ∈ Finset.range (M+1), 1 / Real.sqrt (k : ℝ)) ≤ 2 * Real.sqrt M := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ]
      have hpos : 0 < Real.sqrt (M+1 : ℕ) := by positivity
      have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ (M+1 : ℕ) by positivity)
      have hsq' := Real.sq_sqrt (show (0 : ℝ) ≤ M by positivity)
      have hs : 1 / Real.sqrt (M+1 : ℕ) ≤
          2 * (Real.sqrt (M+1 : ℕ) - Real.sqrt M) := by
        apply (div_le_iff₀ hpos).mpr
        norm_num only [Nat.cast_add, Nat.cast_one] at hsq ⊢
        nlinarith [sq_nonneg (Real.sqrt ((M : ℝ)+1) - Real.sqrt M)]
      nlinarith [ih, hs]

/-- Reindexing all positive and zero multiples, with the half-density factor
proved from the actual square root of the product. -/
private theorem sum_dilation_div_sqrt (n M : ℕ) (hn : 0 < n) (F : ℕ → ℝ) :
    (∑ k ∈ Finset.range (M+1),
      (if n ∣ k then F (k/n) else 0) / Real.sqrt k) =
      (1 / Real.sqrt n) * ∑ r ∈ Finset.range (M/n+1), F r / Real.sqrt r := by
  classical
  simp only [ite_div, zero_div]
  rw [← Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_bij (fun k _ => k/n) ?_ ?_ ?_ ?_
  · intro k hk
    have hkm : k ≤ M := Nat.le_of_lt_succ (Finset.mem_range.mp
      (Finset.mem_filter.mp hk).1)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hkm))
  · intro k hk l hl he
    have hkdiv := Nat.div_mul_cancel (Finset.mem_filter.mp hk).2
    have hldiv := Nat.div_mul_cancel (Finset.mem_filter.mp hl).2
    calc
      k = (k/n)*n := hkdiv.symm
      _ = (l/n)*n := by rw [he]
      _ = l := hldiv
  · intro r hr
    have hrM : r*n ≤ M := (Nat.le_div_iff_mul_le hn).mp
      (Nat.le_of_lt_succ (Finset.mem_range.mp hr))
    have hd : n ∣ r*n := ⟨r, by ring⟩
    have hq : (r*n)/n = r := by
      apply Nat.eq_of_mul_eq_mul_left hn
      simpa only [Nat.mul_comm] using Nat.div_mul_cancel hd
    exact ⟨r*n, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hrM), hd⟩, hq⟩
  · intro k hk
    have hd := (Finset.mem_filter.mp hk).2
    have hs : Real.sqrt (k : ℝ) = Real.sqrt n * Real.sqrt (k/n : ℕ) := by
      calc
        _ = Real.sqrt (((k/n : ℕ) : ℝ) * n) := by
          congr 1
          exact_mod_cast (Nat.div_mul_cancel hd).symm
        _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg _)]; ring
    rw [hs]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

private def inverseCoefficientMass (n : ℕ) (hn : 2 ≤ n) (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M+1), |nymanConductorInverse n hn k| / Real.sqrt k

private theorem inverseCoefficientMass_recurrence_le (n M : ℕ) (hn : 2 ≤ n) :
    inverseCoefficientMass n hn M ≤
      (n : ℝ) * (∑ k ∈ Finset.range (M+1), 1 / Real.sqrt k) +
      Real.sqrt n * inverseCoefficientMass n hn (M/n) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp : 0 < Real.sqrt (n : ℝ) := by positivity
  have hpoint (k : ℕ) : |nymanConductorInverse n hn k| ≤
      (n : ℝ) + (n : ℝ) * (if n ∣ k then |nymanConductorInverse n hn (k/n)| else 0) := by
    rw [nymanConductorInverse_moebius_recurrence n hn k]
    have hμ : |((ArithmeticFunction.moebius k : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := k))
    calc
      _ ≤ |(n : ℝ) * (ArithmeticFunction.moebius k : ℤ)| +
        |(n : ℝ) * (if n ∣ k then nymanConductorInverse n hn (k/n) else 0)| :=
          abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul, abs_of_nonneg hn0, abs_mul, abs_of_nonneg hn0]
        by_cases hk : n ∣ k <;> simp only [hk, if_true, if_false, abs_zero, mul_zero]
        · exact add_le_add (by nlinarith [mul_le_mul_of_nonneg_left hμ hn0]) le_rfl
        · nlinarith [mul_le_mul_of_nonneg_left hμ hn0]
  calc
    inverseCoefficientMass n hn M ≤
        ∑ k ∈ Finset.range (M+1),
          ((n : ℝ) + (n : ℝ) *
            (if n ∣ k then |nymanConductorInverse n hn (k/n)| else 0)) / Real.sqrt k := by
      apply Finset.sum_le_sum
      intro k hk
      exact div_le_div_of_nonneg_right (hpoint k) (Real.sqrt_nonneg _)
    _ = (n : ℝ) * (∑ k ∈ Finset.range (M+1), 1 / Real.sqrt k) +
        (n : ℝ) * ∑ k ∈ Finset.range (M+1),
          (if n ∣ k then |nymanConductorInverse n hn (k/n)| else 0) / Real.sqrt k := by
      simp only [add_div, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro k hk <;> ring
    _ = _ := by
      rw [sum_dilation_div_sqrt n M (by omega)
        (fun r => |nymanConductorInverse n hn r|)]
      have he : (n : ℝ) * (1 / Real.sqrt n) = Real.sqrt n := by
        field_simp [hp.ne']
        nlinarith [Real.sq_sqrt hn0]
      rw [← mul_assoc, he]
      rfl

private theorem inverseCoefficientMass_le (n : ℕ) (hn : 2 ≤ n) (M : ℕ) :
    inverseCoefficientMass n hn M ≤
      2 * (n : ℝ) * Real.sqrt M * (1 + (Nat.log n M : ℝ)) := by
  induction M using Nat.strong_induction_on with
  | h M ih =>
      have hrec := inverseCoefficientMass_recurrence_le n M hn
      have hsum := mul_le_mul_of_nonneg_left (sum_one_div_sqrt_range_le M)
        (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      by_cases hMn : M < n
      · have hzero : inverseCoefficientMass n hn (M/n) = 0 := by
          simp [inverseCoefficientMass, Nat.div_eq_of_lt hMn]
        rw [hzero, mul_zero, add_zero] at hrec
        rw [Nat.log_of_lt hMn]
        norm_num
        nlinarith [hrec.trans hsum]
      · have hnM : n ≤ M := Nat.le_of_not_gt hMn
        have hlt : M/n < M := Nat.div_lt_self (by omega) (by omega)
        have hih := mul_le_mul_of_nonneg_left (ih (M/n) hlt) (Real.sqrt_nonneg (n : ℝ))
        have hsqrt : Real.sqrt n * Real.sqrt (M/n : ℕ) ≤ Real.sqrt M := by
          rw [← Real.sqrt_mul (Nat.cast_nonneg n)]
          apply Real.sqrt_le_sqrt
          have hmul : n*(M/n) ≤ M := by
            have hmod := Nat.mod_add_div M n
            omega
          exact_mod_cast hmul
        calc
          inverseCoefficientMass n hn M ≤
            (n : ℝ) * (2 * Real.sqrt M) + Real.sqrt n *
              (2 * (n : ℝ) * Real.sqrt (M/n : ℕ) * (1 + (Nat.log n (M/n) : ℝ))) :=
                hrec.trans (add_le_add hsum hih)
          _ = 2 * (n : ℝ) * Real.sqrt M +
              2 * (n : ℝ) * (Real.sqrt n * Real.sqrt (M/n : ℕ)) *
                (1 + (Nat.log n (M/n) : ℝ)) := by ring
          _ ≤ 2 * (n : ℝ) * Real.sqrt M +
              2 * (n : ℝ) * Real.sqrt M * (1 + (Nat.log n (M/n) : ℝ)) := by
            gcongr
          _ = _ := by
            rw [Nat.log_of_one_lt_of_le (by omega : 1 < n) hnM]
            push_cast
            ring

/-- The note's explicit coefficient bound for the actual constructive inverse. -/
theorem sum_abs_nymanConductorInverse_div_sqrt_le (n M : ℕ)
    (hn : 2 ≤ n) (_hM : 1 ≤ M) :
    (∑ k ∈ Finset.Icc 1 M, |nymanConductorInverse n hn k| / Real.sqrt k) ≤
      2 * (n : ℝ) * Real.sqrt M * (1 + (Nat.log n M : ℝ)) := by
  have he : (∑ k ∈ Finset.Icc 1 M,
      |nymanConductorInverse n hn k| / Real.sqrt k) = inverseCoefficientMass n hn M := by
    apply Finset.sum_subset
    · intro k hk
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hk).2)
    · intro k hk hnot
      have hk0 : k = 0 := by
        simp only [Finset.mem_range, Finset.mem_Icc, not_and] at hk hnot
        omega
      simp [hk0]
  rw [he]
  exact inverseCoefficientMass_le n hn M

end RiemannResearch.RH

import RiemannResearch.RH.NymanConductorArithmetic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Closed Möbius/power coefficients of the actual conductor inverse

Möbius inversion turns the actual conductor coefficients into a first-order
arithmetic dilation recurrence. Iterating that exact recurrence gives the
finite geometric formula for the already constructed Dirichlet inverse.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH

private def arithmeticDilation (n : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ where
  toFun k := if n ∣ k then f (k / n) else 0
  map_zero' := by simp

private theorem arithmeticDilation_apply (n k : ℕ) (f : ArithmeticFunction ℝ) :
    arithmeticDilation n f k = if n ∣ k then f (k/n) else 0 := rfl

private theorem mobius_restrictedDivisors {n k : ℕ} (hk : k ≠ 0) (hnk : n ∣ k) :
    k.divisors.filter (fun d => n ∣ k/d) = (k/n).divisors := by
  have hquot : k/n ∣ k := ⟨n, (Nat.div_mul_cancel hnk).symm⟩
  calc
    k.divisors.filter (fun d => n ∣ k/d) = k.divisors.filter (fun d => d ∣ k/n) := by
      apply Finset.filter_congr
      intro d hd
      rw [Nat.dvd_div_iff_mul_dvd (Nat.dvd_of_mem_divisors hd),
        Nat.dvd_div_iff_mul_dvd hnk, Nat.mul_comm d n]
    _ = (k/n).divisors := Nat.divisors_filter_dvd_of_dvd hk hquot

/-- Actual Dirichlet convolution commutes with arithmetic dilation. -/
private theorem mul_arithmeticDilation (f g : ArithmeticFunction ℝ) (n : ℕ) :
    f * arithmeticDilation n g = arithmeticDilation n (f*g) := by
  ext k
  by_cases hk : k = 0
  · subst k
    simp
  rw [arithmeticDilation_apply, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => f a * arithmeticDilation n g b)]
  by_cases hnk : n ∣ k
  · rw [if_pos hnk]
    calc
      (∑ d ∈ k.divisors, f d * arithmeticDilation n g (k/d)) =
          ∑ d ∈ k.divisors.filter (fun d => n ∣ k/d), f d * g ((k/n)/d) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro d hd
        by_cases hnd : n ∣ k/d
        · simp [arithmeticDilation_apply, hnd, Nat.div_div_eq_div_mul, Nat.mul_comm]
        · simp [arithmeticDilation_apply, hnd]
      _ = (f*g) (k/n) := by
        rw [mobius_restrictedDivisors hk hnk, ArithmeticFunction.mul_apply,
          Nat.sum_divisorsAntidiagonal (fun a b => f a * g b)]
  · rw [if_neg hnk]
    apply Finset.sum_eq_zero
    intro d hd
    have hnd : ¬ n ∣ k/d := by
      intro h
      have hquot : k/d ∣ k := ⟨d, (Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)).symm⟩
      exact hnk (h.trans hquot)
    simp [arithmeticDilation_apply, hnd]

private theorem nymanConductorBeta_eq_zeta_dilation (n : ℕ) :
    nymanConductorBeta n =
      (1/(n:ℝ)) • (ArithmeticFunction.zeta : ArithmeticFunction ℝ) -
        arithmeticDilation n (ArithmeticFunction.zeta : ArithmeticFunction ℝ) := by
  ext k
  by_cases hk : k = 0
  · subst k
    simp
  rw [nymanConductorBeta_apply hk]
  change 1/(n:ℝ) - (if n ∣ k then 1 else 0) =
    ((1/(n:ℝ)) • (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) k -
      arithmeticDilation n (ArithmeticFunction.zeta : ArithmeticFunction ℝ) k
  simp only [ArithmeticFunction.smul_map, smul_eq_mul,
    arithmeticDilation_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply_ne hk, Nat.cast_one, mul_one]
  by_cases hnk : n ∣ k
  · have hq : k/n ≠ 0 := by
      intro h
      exact hk (by simpa [h] using (Nat.div_mul_cancel hnk).symm)
    simp [hnk, ArithmeticFunction.zeta_apply_ne hq]
  · simp [hnk]

private theorem moebius_mul_nymanConductorBeta (n : ℕ) :
    (ArithmeticFunction.moebius : ArithmeticFunction ℝ) * nymanConductorBeta n =
      (1/(n:ℝ)) • (1 : ArithmeticFunction ℝ) - arithmeticDilation n 1 := by
  rw [nymanConductorBeta_eq_zeta_dilation, mul_sub, mul_smul_comm,
    mul_arithmeticDilation, ArithmeticFunction.coe_moebius_mul_coe_zeta]

/-- Exact scalar recurrence satisfied by the actual constructive inverse. -/
theorem nymanConductorInverse_moebius_recurrence (n : ℕ) (hn : 2 ≤ n) (k : ℕ) :
    nymanConductorInverse n hn k =
      (n : ℝ) * (ArithmeticFunction.moebius k : ℤ) +
        (n : ℝ) * (if n ∣ k then nymanConductorInverse n hn (k/n) else 0) := by
  let b := nymanConductorInverse n hn
  have he : (1/(n:ℝ)) • b - arithmeticDilation n b =
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) := by
    calc
      _ = ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) * nymanConductorBeta n) * b := by
        rw [moebius_mul_nymanConductorBeta, sub_mul, smul_mul_assoc, one_mul,
          mul_comm (arithmeticDilation n 1) b, mul_arithmeticDilation, mul_one]
      _ = _ := by
        rw [mul_assoc, nymanConductorBeta_mul_inverse, mul_one]
  have hk := congrArg (fun f : ArithmeticFunction ℝ => f k) he
  change ((1/(n:ℝ)) • b) k - arithmeticDilation n b k =
    (ArithmeticFunction.moebius : ArithmeticFunction ℝ) k at hk
  simp only [ArithmeticFunction.smul_map, smul_eq_mul, arithmeticDilation_apply,
    ArithmeticFunction.intCoe_apply] at hk
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  change (1/(n:ℝ)) * nymanConductorInverse n hn k -
    (if n ∣ k then nymanConductorInverse n hn (k/n) else 0) =
      (ArithmeticFunction.moebius k : ℤ) at hk
  field_simp at hk
  nlinarith [hk]

/-- The exact summand in the closed Möbius/power formula. -/
def nymanMobiusPowerTerm (n k j : ℕ) : ℝ :=
  if n^j ∣ k then (n : ℝ)^j * (ArithmeticFunction.moebius (k/n^j) : ℤ) else 0

private theorem inverse_remainder_step (n : ℕ) (hn : 2 ≤ n) (k j : ℕ) :
    (if n^j ∣ k then (n : ℝ)^j * nymanConductorInverse n hn (k/n^j) else 0) =
      (n : ℝ) * nymanMobiusPowerTerm n k j +
        (if n^(j+1) ∣ k then
          (n : ℝ)^(j+1) * nymanConductorInverse n hn (k/n^(j+1)) else 0) := by
  by_cases hj : n^j ∣ k
  · rw [if_pos hj, nymanConductorInverse_moebius_recurrence]
    have hd : n ∣ k/n^j ↔ n^(j+1) ∣ k := by
      rw [Nat.dvd_div_iff_mul_dvd hj, pow_succ]
    have hq : (k/n^j)/n = k/n^(j+1) := by
      rw [Nat.div_div_eq_div_mul, pow_succ]
    simp only [nymanMobiusPowerTerm, if_pos hj, hd, hq]
    simp only [pow_succ]
    split_ifs <;> ring
  · have hj' : ¬ n^(j+1) ∣ k := by
      intro h
      have hpow : n^j ∣ n^(j+1) := ⟨n, by rw [pow_succ]⟩
      exact hj (hpow.trans h)
    simp only [nymanMobiusPowerTerm, hj, hj', if_false, mul_zero, add_zero]

/-- A finite geometric expansion with its exact arithmetic remainder retained. -/
theorem nymanConductorInverse_eq_prefix_add_remainder (n : ℕ) (hn : 2 ≤ n)
    (k J : ℕ) :
    nymanConductorInverse n hn k =
      (n : ℝ) * (∑ j ∈ Finset.range J, nymanMobiusPowerTerm n k j) +
        (if n^J ∣ k then
          (n : ℝ)^J * nymanConductorInverse n hn (k/n^J) else 0) := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [Finset.sum_range_succ]
      calc
        nymanConductorInverse n hn k =
          (n : ℝ) * (∑ j ∈ Finset.range J, nymanMobiusPowerTerm n k j) +
            (if n^J ∣ k then
              (n : ℝ)^J * nymanConductorInverse n hn (k/n^J) else 0) := ih
        _ = _ := by rw [inverse_remainder_step]; ring

private theorem exponent_lt_conductor_power (n : ℕ) (hn : 2 ≤ n) (j : ℕ) :
    j+1 ≤ n^j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ]
      have hmul := Nat.mul_le_mul_right (n^j) hn
      nlinarith

/-- The Möbius/power sum is genuinely finite for every positive coefficient. -/
theorem nymanMobiusPowerTerm_zero_of_large_exponent (n : ℕ) (hn : 2 ≤ n)
    {k j : ℕ} (hk : k ≠ 0) (hj : k < j) : nymanMobiusPowerTerm n k j = 0 := by
  have hpow : k < n^j := lt_of_lt_of_le (Nat.lt_succ_of_lt hj)
    (exponent_lt_conductor_power n hn j)
  have hnd : ¬ n^j ∣ k := by
    intro h
    exact (not_le_of_gt hpow) (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) h)
  simp only [nymanMobiusPowerTerm, hnd, if_false]

/-- Identification with the actual constructive inverse, in finite form. -/
theorem nymanConductorInverse_eq_mobius_sum (n : ℕ) (hn : 2 ≤ n)
    (k : ℕ) (hk : k ≠ 0) :
    nymanConductorInverse n hn k =
      (n : ℝ) * ∑ j ∈ Finset.range (k+1),
        if n^j ∣ k then (n : ℝ)^j * (ArithmeticFunction.moebius (k/n^j) : ℤ) else 0 := by
  have hpow : k < n^(k+1) := lt_of_lt_of_le (by omega : k < (k+1)+1)
    (exponent_lt_conductor_power n hn (k+1))
  have hnd : ¬ n^(k+1) ∣ k := by
    intro h
    exact (not_le_of_gt hpow) (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) h)
  simpa only [nymanMobiusPowerTerm, hnd, if_false, add_zero] using
    nymanConductorInverse_eq_prefix_add_remainder n hn k (k+1)

/-- The note's infinite-looking sum is exactly the proved finite sum. -/
theorem nymanConductorInverse_eq_mobius_tsum (n : ℕ) (hn : 2 ≤ n)
    (k : ℕ) (hk : k ≠ 0) :
    nymanConductorInverse n hn k =
      (n : ℝ) * ∑' j : ℕ,
        if n^j ∣ k then (n : ℝ)^j * (ArithmeticFunction.moebius (k/n^j) : ℤ) else 0 := by
  rw [nymanConductorInverse_eq_mobius_sum n hn k hk]
  congr 1
  symm
  apply tsum_eq_sum
  intro j hj
  exact nymanMobiusPowerTerm_zero_of_large_exponent n hn hk
    (by simp only [Finset.mem_range] at hj; omega)

end RiemannResearch.RH

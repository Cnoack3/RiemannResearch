import RiemannResearch.RH.ReciprocalChargeDilationArithmetic
import RiemannResearch.RH.ReciprocalChargeDilationSeries
import RiemannResearch.Analysis.BoundedSquareEnergy
import RiemannResearch.NumberTheory.SquarefreeEulerSeries

/-!
# Exact reciprocal Möbius correlation at a prime dilation

Source: the arithmetic dilation extension developed from the user-provided
`ReciprocalChargeNormLimit20260924.md`. No novelty claim is made.

The proof removes one prime by an exact finite partition. It uses the
already evaluated squarefree reciprocal-square series and does not require
another Euler-product argument.
-/

noncomputable section
open Filter
open RiemannResearch.Analysis.BoundedSquareEnergy RiemannResearch.NumberTheory
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto

/-- Square energy remaining after excluding multiples of `p`. -/
def primeRoughSquare (p n : ℕ) : ℝ :=
  if p ∣ n then 0 else (mobiusReciprocalCoefficient n) ^ 2

@[simp] theorem primeRoughSquare_zero (p : ℕ) : primeRoughSquare p 0 = 0 := by
  simp [primeRoughSquare]

theorem mobiusReciprocalCoefficient_prime_mul (p n : ℕ) (hp : Nat.Prime p) :
    mobiusReciprocalCoefficient (p * n) =
      if p ∣ n then 0 else -(1 / (p : ℝ)) * mobiusReciprocalCoefficient n := by
  by_cases hn : p ∣ n
  · have hmu : ArithmeticFunction.moebius (p * n) = 0 := by
      apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
      intro hs
      exact (hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs)) hn
    simp [hn, mobiusReciprocalCoefficient, hmu]
  · have hmu : (ArithmeticFunction.moebius (p * n) : ℝ) =
        -(ArithmeticFunction.moebius n : ℝ) := by
      have he := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
        (hp.coprime_iff_not_dvd.mpr hn)
      rw [ArithmeticFunction.moebius_apply_prime hp] at he
      have he' : ArithmeticFunction.moebius (p * n) = -ArithmeticFunction.moebius n := by
        simpa only [neg_one_mul] using he
      exact_mod_cast he'
    rw [if_neg hn]
    simp only [mobiusReciprocalCoefficient, hmu, Nat.cast_mul,
      div_eq_mul_inv, mul_inv_rev]
    ring

theorem mobiusReciprocalCoefficient_prime_mul_sq (p n : ℕ) (hp : Nat.Prime p) :
    (mobiusReciprocalCoefficient (p * n)) ^ 2 =
      (1 / (p : ℝ) ^ 2) * primeRoughSquare p n := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  by_cases hn : p ∣ n
  · simp [mobiusReciprocalCoefficient_prime_mul p n hp, primeRoughSquare, hn]
  · rw [mobiusReciprocalCoefficient_prime_mul p n hp, if_neg hn]
    simp only [primeRoughSquare, if_neg hn]
    field_simp [hp0] <;> ring

theorem mobiusReciprocalCoefficient_prime_mul_cross (p n : ℕ) (hp : Nat.Prime p) :
    mobiusReciprocalCoefficient (p * n) * mobiusReciprocalCoefficient n =
      -(1 / (p : ℝ)) * primeRoughSquare p n := by
  by_cases hn : p ∣ n
  · simp [mobiusReciprocalCoefficient_prime_mul p n hp, primeRoughSquare, hn]
  · rw [mobiusReciprocalCoefficient_prime_mul p n hp, if_neg hn]
    simp only [primeRoughSquare, if_neg hn]
    ring

theorem primeRoughSquare_summable (p : ℕ) : Summable (primeRoughSquare p) := by
  have hs : Summable (fun n => (mobiusReciprocalCoefficient n) ^ 2) :=
    summable_square_of_reciprocal_bound mobiusReciprocalCoefficient
      mobiusReciprocalCoefficient_zero 1 (by norm_num)
      (fun n _ => mobiusReciprocalCoefficient_abs_le n)
  apply hs.of_norm_bounded
  intro n
  by_cases hn : p ∣ n
  · simp [primeRoughSquare, hn, sq_nonneg]
  · simp [primeRoughSquare, hn, Real.norm_eq_abs, abs_sq]

/-- Split the full square energy into numbers prime to `p` and positive multiples. -/
theorem mobiusReciprocalCoefficient_sq_prime_partition (p n : ℕ) (hp : Nat.Prime p) :
    (mobiusReciprocalCoefficient n) ^ 2 = primeRoughSquare p n +
      (1 / (p : ℝ) ^ 2) * (if p ∣ n then primeRoughSquare p (n / p) else 0) := by
  by_cases hn : p ∣ n
  · have he : p * (n / p) = n := by
      simpa only [Nat.mul_comm] using Nat.div_mul_cancel hn
    rw [if_pos hn]
    have hrough : primeRoughSquare p n = 0 := by simp [primeRoughSquare, hn]
    rw [hrough, zero_add]
    simpa only [he] using mobiusReciprocalCoefficient_prime_mul_sq p (n / p) hp
  · simp [primeRoughSquare, hn]

theorem mobiusReciprocalCoefficient_sq_prime_partition_sum (p M : ℕ)
    (hp : Nat.Prime p) :
    (∑ n ∈ Finset.Icc 1 M, (mobiusReciprocalCoefficient n) ^ 2) =
      (∑ n ∈ Finset.Icc 1 M, primeRoughSquare p n) +
      (1 / (p : ℝ) ^ 2) * ∑ d ∈ Finset.Icc 1 (M / p), primeRoughSquare p d := by
  simp_rw [mobiusReciprocalCoefficient_sq_prime_partition p _ hp]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    positive_dilation_sum M p hp.pos]

/-- Exact infinite partition; the prime-complement series is an actual summable series. -/
theorem primeRoughSquare_partition_tsum (p : ℕ) (hp : Nat.Prime p) :
    (∑' n : ℕ, (mobiusReciprocalCoefficient n) ^ 2) =
      (∑' n : ℕ, primeRoughSquare p n) +
      (1 / (p : ℝ) ^ 2) * ∑' n : ℕ, primeRoughSquare p n := by
  have hs : Summable (fun n => (mobiusReciprocalCoefficient n) ^ 2) :=
    summable_square_of_reciprocal_bound mobiusReciprocalCoefficient
      mobiusReciprocalCoefficient_zero 1 (by norm_num)
      (fun n _ => mobiusReciprocalCoefficient_abs_le n)
  have hf := summable_tendsto_sum_Icc _ hs (by simp)
  have hr := summable_tendsto_sum_Icc _ (primeRoughSquare_summable p)
    (primeRoughSquare_zero p)
  have hdiv : Tendsto (fun M : ℕ => M / p) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b * p)] with M hM
    exact (Nat.le_div_iff_mul_le hp.pos).mpr hM
  have hright : Tendsto
      (fun M => ∑ n ∈ Finset.Icc 1 M, (mobiusReciprocalCoefficient n) ^ 2)
      atTop (𝓝 ((∑' n : ℕ, primeRoughSquare p n) +
        (1 / (p : ℝ) ^ 2) * ∑' n : ℕ, primeRoughSquare p n)) := by
    convert hr.add ((hr.comp hdiv).const_mul (1 / (p : ℝ) ^ 2)) using 1
    funext M
    exact mobiusReciprocalCoefficient_sq_prime_partition_sum p M hp
  exact tendsto_nhds_unique hf hright

theorem primeRoughSquare_tsum_eq_factor (p : ℕ) (hp : Nat.Prime p) :
    (∑' n : ℕ, primeRoughSquare p n) =
      (p : ℝ) ^ 2 * (∑' n : ℕ, (mobiusReciprocalCoefficient n) ^ 2) /
        ((p : ℝ) ^ 2 + 1) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hden : (p : ℝ) ^ 2 + 1 ≠ 0 := by positivity
  have he := primeRoughSquare_partition_tsum p hp
  have he' :
      (∑' n : ℕ, (mobiusReciprocalCoefficient n) ^ 2) * (p : ℝ) ^ 2 =
        (∑' n : ℕ, primeRoughSquare p n) * (p : ℝ) ^ 2 +
          (∑' n : ℕ, primeRoughSquare p n) := by
    calc
      _ = ((∑' n : ℕ, primeRoughSquare p n) +
          (1 / (p : ℝ) ^ 2) * ∑' n : ℕ, primeRoughSquare p n) * (p : ℝ) ^ 2 := by
        rw [he]
      _ = _ := by field_simp [hp0] <;> ring
  apply (eq_div_iff hden).mpr
  nlinarith [he']

/-- Signed prime-dilation correlation, expressed by the original square energy. -/
theorem prime_dilation_mobius_mixed_tsum (p : ℕ) (hp : Nat.Prime p) :
    (∑' n : ℕ, mobiusReciprocalCoefficient (p * n) * mobiusReciprocalCoefficient n) =
      -((p : ℝ) / ((p : ℝ) ^ 2 + 1)) *
        ∑' n : ℕ, (mobiusReciprocalCoefficient n) ^ 2 := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hden : (p : ℝ) ^ 2 + 1 ≠ 0 := by positivity
  simp_rw [mobiusReciprocalCoefficient_prime_mul_cross p _ hp]
  rw [tsum_mul_left, primeRoughSquare_tsum_eq_factor p hp]
  field_simp [hp0, hden] <;> ring

/-- The prime-dilation correlation is evaluated unconditionally. -/
theorem prime_dilation_mobius_mixed_tsum_exact (p : ℕ) (hp : Nat.Prime p) :
    (∑' n : ℕ, mobiusReciprocalCoefficient (p * n) * mobiusReciprocalCoefficient n) =
      -(15 * (p : ℝ)) / (((p : ℝ) ^ 2 + 1) * Real.pi ^ 2) := by
  have hS : (∑' n : ℕ, (mobiusReciprocalCoefficient n) ^ 2) = 15 / Real.pi ^ 2 := by
    simpa only [mobiusReciprocalCoefficient, div_pow] using
      RiemannResearch.NumberTheory.squarefree_reciprocal_square_sum
  rw [prime_dilation_mobius_mixed_tsum p hp, hS]
  have hden : (p : ℝ) ^ 2 + 1 ≠ 0 := by positivity
  field_simp [Real.pi_ne_zero, hden] <;> ring

theorem two_dilation_mobius_mixed_tsum :
    (∑' n : ℕ, mobiusReciprocalCoefficient (2 * n) * mobiusReciprocalCoefficient n) =
      -6 / Real.pi ^ 2 := by
  rw [prime_dilation_mobius_mixed_tsum_exact 2 (by decide)]
  norm_num <;> ring

theorem three_dilation_mobius_mixed_tsum :
    (∑' n : ℕ, mobiusReciprocalCoefficient (3 * n) * mobiusReciprocalCoefficient n) =
      -9 / (2 * Real.pi ^ 2) := by
  rw [prime_dilation_mobius_mixed_tsum_exact 3 (by decide)]
  norm_num <;> ring

end RiemannResearch.RH.Pareto

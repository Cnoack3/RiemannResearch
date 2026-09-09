import RiemannResearch.RH.DivisorComponentNormBound

/-!
# Closed uniform error floor for arbitrary bounded seed exponents

The divisor norm bound is specialized by the multiplicativity of the squared
totient ratio and an exact prime-power divisor sum.  The result applies to the
actual signed seed generators, all complementary prime powers, and their full
infinite Pareto error.
-/

namespace RiemannResearch.RH.DivisorComponentJumpRow

open scoped BigOperators
open PositiveSeedCone

noncomputable section

private def normOne : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else 1, by simp⟩

private def squaredTotientRatio : ArithmeticFunction ℝ :=
  ⟨fun n => ((Nat.totient n : ℝ) / (n : ℝ)) ^ 2, by simp⟩

theorem totient_ratio_mul (m n : ℕ) (hc : Nat.Coprime m n) :
    (Nat.totient (m * n) : ℝ) / (m * n : ℕ) =
      ((Nat.totient m : ℝ) / (m : ℝ)) * ((Nat.totient n : ℝ) / (n : ℝ)) := by
  rw [Nat.totient_mul hc]
  simp only [Nat.cast_mul]
  ring

private theorem normOne_multiplicative : normOne.IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  constructor
  · simp [normOne]
  · intro m n hm hn _hc
    simp [normOne, hm, hn, mul_ne_zero hm hn]

private theorem squaredTotientRatio_multiplicative : squaredTotientRatio.IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  constructor
  · norm_num [squaredTotientRatio]
  · intro m n _hm _hn hc
    change ((Nat.totient (m * n) : ℝ) / (m * n : ℕ)) ^ 2 =
      ((Nat.totient m : ℝ) / (m : ℝ)) ^ 2 * ((Nat.totient n : ℝ) / (n : ℝ)) ^ 2
    rw [totient_ratio_mul m n hc, mul_pow]

private theorem norm_convolution (D : ℕ) :
    (normOne * squaredTotientRatio) D = totientDivisorNorm D := by
  by_cases hDz : D = 0
  · subst D
    simp [totientDivisorNorm]
  have hD := Nat.pos_of_ne_zero hDz
  rw [mul_comm, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y => squaredTotientRatio x * normOne y)]
  unfold totientDivisorNorm
  apply Finset.sum_congr rfl
  intro d hd
  have hquot : 0 < D / d := Nat.div_pos
    (Nat.le_of_dvd hD (Nat.dvd_of_mem_divisors hd)) (Nat.pos_of_mem_divisors hd)
  simp [normOne, squaredTotientRatio, ne_of_gt hquot]

theorem totientDivisorNorm_mul (m n : ℕ) (hc : Nat.Coprime m n) :
    totientDivisorNorm (m * n) = totientDivisorNorm m * totientDivisorNorm n := by
  rw [← norm_convolution (m * n), ← norm_convolution m, ← norm_convolution n]
  exact (normOne_multiplicative.mul squaredTotientRatio_multiplicative).map_mul_of_coprime hc

theorem totient_ratio_prime_pow_succ (p n : ℕ) (hp : Nat.Prime p) :
    (Nat.totient (p ^ (n + 1)) : ℝ) / (p ^ (n + 1) : ℕ) =
      ((p - 1 : ℕ) : ℝ) / (p : ℝ) := by
  rw [Nat.totient_prime_pow_succ hp, pow_succ]
  simp only [Nat.cast_mul]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpowR : ((p ^ n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (pow_ne_zero n hp.ne_zero)
  field_simp

theorem totientDivisorNorm_prime_pow (p A : ℕ) (hp : Nat.Prime p) :
    totientDivisorNorm (p ^ A) =
      1 + (A : ℝ) * (((p - 1 : ℕ) : ℝ) / (p : ℝ)) ^ 2 := by
  unfold totientDivisorNorm
  rw [Nat.divisors_prime_pow hp A, Finset.sum_map]
  change (∑ j ∈ Finset.range (A + 1),
    ((Nat.totient (p ^ j) : ℝ) / (p ^ j : ℕ)) ^ 2) = _
  rw [Finset.sum_range_succ']
  simp_rw [totient_ratio_prime_pow_succ p _ hp]
  simp [Finset.sum_const, nsmul_eq_mul, add_comm]

theorem totientDivisorNorm_smooth (A B : ℕ) :
    totientDivisorNorm (2 ^ A * 3 ^ B) =
      (1 + (A : ℝ) / 4) * (1 + 4 * (B : ℝ) / 9) := by
  rw [totientDivisorNorm_mul (2 ^ A) (3 ^ B)
    (Nat.Coprime.pow A B (by decide : Nat.Coprime 2 3)),
    totientDivisorNorm_prime_pow 2 A (by decide),
    totientDivisorNorm_prime_pow 3 B (by decide)]
  norm_num
  ring

theorem totient_ratio_smooth (A B : ℕ) (hA : 0 < A) (hB : 0 < B) :
    (Nat.totient (2 ^ A * 3 ^ B) : ℝ) / (2 ^ A * 3 ^ B : ℕ) = (1 / 3 : ℝ) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hA)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hB)
  rw [totient_ratio_mul (2 ^ (a + 1)) (3 ^ (b + 1))
    (Nat.Coprime.pow (a + 1) (b + 1) (by decide : Nat.Coprime 2 3)),
    totient_ratio_prime_pow_succ 2 a (by decide),
    totient_ratio_prime_pow_succ 3 b (by decide)]
  norm_num

/-- The closed floor for all actual signed combinations with bounded seed
exponents.  Other prime factors and their exponents are unrestricted. -/
theorem smooth_seed_fullError_lower {ι : Type*}
    (A B r : ℕ) (hA : 0 < A) (hB : 0 < B) (hr : Nat.Coprime 6 r)
    (s : Finset ι) (a m : ι → ℕ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3)
    (hm : ∀ i ∈ s, 0 < m i)
    (hperiod : ∀ i ∈ s, a i * m i ∣ (2 ^ A * 3 ^ B) * r) :
    2 / (((A : ℝ) + 4) * (4 * (B : ℝ) + 9)) ≤
      ∑' k : ℕ, weightedError (seedCombination s a m c) k := by
  have h := divisorComponent_totient_fullError_lower (2 ^ A * 3 ^ B) r
    (by positivity) hr s a m c ha hm hperiod
  rw [totient_ratio_smooth A B hA hB, totientDivisorNorm_smooth A B] at h
  have he : (1 / 3 : ℝ) ^ 2 /
      (2 * ((1 + (A : ℝ) / 4) * (1 + 4 * (B : ℝ) / 9))) =
      2 / (((A : ℝ) + 4) * (4 * (B : ℝ) + 9)) := by
    have ha₁ : (A : ℝ) + 4 ≠ 0 := by positivity
    have hb₁ : 4 * (B : ℝ) + 9 ≠ 0 := by positivity
    have ha₂ : 1 + (A : ℝ) / 4 ≠ 0 := by positivity
    have hb₂ : 1 + 4 * (B : ℝ) / 9 ≠ 0 := by positivity
    field_simp
    ring
  rwa [he] at h

end
end RiemannResearch.RH.DivisorComponentJumpRow

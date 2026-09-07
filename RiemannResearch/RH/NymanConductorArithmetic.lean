import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Exact Nyman conductor arithmetic and finite inverse prefixes

Source: `RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md`,
equation (4.7) and the coefficient calculation in Theorem 9.1.

The arithmetic function is the concrete beta_n(k) = 1/n - 1_{n | k}
for positive k, extended by zero at k = 0 to match Mathlib's convention.
All prime powers are retained through Mathlib's actual von Mangoldt function.
The inverse is Mathlib's constructive Dirichlet inverse, specialized using
the explicit inverse n of beta_n(1). No assumed arithmetic identities occur.
The separate closed Möbius/power expression in (9.1) is not asserted here.

-/

open scoped BigOperators

namespace RiemannResearch.RH

/-- Actual normalized arithmetic return coefficients, with the standard
zero-at-zero arithmetic-function convention. -/
noncomputable def nymanConductorBeta (n : ℕ) : ArithmeticFunction ℝ where
  toFun k := if k = 0 then 0 else 1 / (n : ℝ) - if n ∣ k then 1 else 0
  map_zero' := by simp

theorem nymanConductorBeta_apply {n k : ℕ} (hk : k ≠ 0) :
    nymanConductorBeta n k = 1 / (n : ℝ) - if n ∣ k then 1 else 0 := by
  simp [nymanConductorBeta, hk]

theorem nymanConductorBeta_one {n : ℕ} (hn : 2 ≤ n) :
    nymanConductorBeta n 1 = 1 / (n : ℝ) := by
  have hn1 : n ≠ 1 := ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2) hn)
  simp [nymanConductorBeta, Nat.dvd_one, hn1]

private theorem conductor_restrictedDivisors {n k : ℕ} (hk : k ≠ 0)
    (hnk : n ∣ k) :
    k.divisors.filter (fun d => n ∣ k / d) = (k / n).divisors := by
  have hquot : k / n ∣ k := ⟨n, (Nat.div_mul_cancel hnk).symm⟩
  calc
    k.divisors.filter (fun d => n ∣ k / d) =
        k.divisors.filter (fun d => d ∣ k / n) := by
      apply Finset.filter_congr
      intro d hd
      rw [Nat.dvd_div_iff_mul_dvd (Nat.dvd_of_mem_divisors hd),
        Nat.dvd_div_iff_mul_dvd hnk, Nat.mul_comm d n]
    _ = (k / n).divisors := Nat.divisors_filter_dvd_of_dvd hk hquot

private theorem conductor_restrictedMangoldtSum {n k : ℕ} (hk : k ≠ 0) :
    (∑ d ∈ k.divisors, if n ∣ k / d then ArithmeticFunction.vonMangoldt d else 0) =
      if n ∣ k then Real.log (k / n : ℕ) else 0 := by
  by_cases hnk : n ∣ k
  · rw [if_pos hnk, ← Finset.sum_filter, conductor_restrictedDivisors hk hnk]
    exact ArithmeticFunction.vonMangoldt_sum
  · rw [if_neg hnk]
    apply Finset.sum_eq_zero
    intro d hd
    have hnd : ¬ n ∣ k / d := by
      intro h
      have hquot : k / d ∣ k :=
        ⟨d, (Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)).symm⟩
      exact hnk (h.trans hquot)
    simp [hnd]

/-- Exact evaluation of every forward prime-power channel. In particular no
prime-square or higher-power term has been omitted. -/
theorem vonMangoldt_mul_nymanConductorBeta {n k : ℕ} (hk : k ≠ 0) :
    (ArithmeticFunction.vonMangoldt * nymanConductorBeta n) k =
      Real.log k / (n : ℝ) - if n ∣ k then Real.log (k / n : ℕ) else 0 := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (f := fun d e =>
      ArithmeticFunction.vonMangoldt d * nymanConductorBeta n e)]
  calc
    (∑ d ∈ k.divisors,
        ArithmeticFunction.vonMangoldt d * nymanConductorBeta n (k / d)) =
      ∑ d ∈ k.divisors,
        ArithmeticFunction.vonMangoldt d *
          (1 / (n : ℝ) - if n ∣ k / d then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hkd : k / d ≠ 0 := by
        intro h
        have heq := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)
        exact hk (by simpa [h] using heq.symm)
      rw [nymanConductorBeta_apply hkd]
    _ = (∑ d ∈ k.divisors, ArithmeticFunction.vonMangoldt d) / (n : ℝ) -
        ∑ d ∈ k.divisors,
          if n ∣ k / d then ArithmeticFunction.vonMangoldt d else 0 := by
      simp_rw [mul_sub, mul_one_div, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_sub_distrib]
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = Real.log k / (n : ℝ) - if n ∣ k then Real.log (k / n : ℕ) else 0 := by
      rw [ArithmeticFunction.vonMangoldt_sum, conductor_restrictedMangoldtSum hk]

/-- At coefficient 1 the inverse is explicitly n. -/
@[instance_reducible]
noncomputable def nymanConductorInvertibleOne (n : ℕ) (hn : 2 ≤ n) :
    Invertible (nymanConductorBeta n 1) where
  invOf := (n : ℝ)
  invOf_mul_self := by
    rw [nymanConductorBeta_one hn]
    have hn0 : (n : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hn))
    simp [div_eq_mul_inv, hn0]
  mul_invOf_self := by
    rw [nymanConductorBeta_one hn]
    have hn0 : (n : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hn))
    simp [div_eq_mul_inv, hn0]

/-- The actual Dirichlet inverse, constructed recursively by Mathlib from
the explicit inverse n of the leading coefficient. -/
noncomputable def nymanConductorInverse (n : ℕ) (hn : 2 ≤ n) :
    ArithmeticFunction ℝ :=
  ArithmeticFunction.dirichletInverse (nymanConductorBeta n)
    (nymanConductorInvertibleOne n hn)

theorem nymanConductorBeta_mul_inverse (n : ℕ) (hn : 2 ≤ n) :
    nymanConductorBeta n * nymanConductorInverse n hn = 1 :=
  ArithmeticFunction.self_mul_dirichletInverse (nymanConductorBeta n)
    (nymanConductorInvertibleOne n hn)

theorem nymanConductorInverse_mul_beta (n : ℕ) (hn : 2 ≤ n) :
    nymanConductorInverse n hn * nymanConductorBeta n = 1 := by
  rw [mul_comm, nymanConductorBeta_mul_inverse]

/-- Truncation of the concrete inverse to a prescribed finite prefix. -/
noncomputable def nymanConductorInversePrefix (n M : ℕ) (hn : 2 ≤ n) :
    ArithmeticFunction ℝ where
  toFun k := if k ≤ M then nymanConductorInverse n hn k else 0
  map_zero' := by simp

/-- Truncation cannot change any convolution coefficient at or below M.
This is the exact arithmetic input to the remote-tail support calculation. -/
theorem nymanConductorInversePrefix_exact {n M k : ℕ} (hn : 2 ≤ n) (hk : k ≤ M) :
    (nymanConductorBeta n * nymanConductorInversePrefix n M hn) k =
      if k = 1 then 1 else 0 := by
  calc
    (nymanConductorBeta n * nymanConductorInversePrefix n M hn) k =
        (nymanConductorBeta n * nymanConductorInverse n hn) k := by
      rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
      apply Finset.sum_congr rfl
      intro d hd
      have hdM : d.2 ≤ M :=
        (Nat.divisor_le (Nat.snd_mem_divisors_of_mem_antidiagonal hd)).trans hk
      simp [nymanConductorInversePrefix, hdM]
    _ = if k = 1 then 1 else 0 := by
      rw [nymanConductorBeta_mul_inverse, ArithmeticFunction.one_apply]

/-- Concrete feasibility of the two-conductor finite matching constraints.
The second conductor can subsequently be used to optimize the tail. -/
theorem nymanTwoThree_prefix_feasible (M : ℕ) :
    ∃ d₂ d₃ : ArithmeticFunction ℝ,
      (∀ k, M < k → d₂ k = 0 ∧ d₃ k = 0) ∧
      ∀ k, k ≤ M →
        (nymanConductorBeta 2 * d₂ + nymanConductorBeta 3 * d₃) k =
          if k = 1 then 1 else 0 := by
  refine ⟨nymanConductorInversePrefix 2 M (by decide), 0, ?_, ?_⟩
  · intro k hk
    simp [nymanConductorInversePrefix, Nat.not_le.mpr hk]
  · intro k hk
    simpa using nymanConductorInversePrefix_exact (n := 2) (by decide) hk

end RiemannResearch.RH

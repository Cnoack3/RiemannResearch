import RiemannResearch.NumberTheory.PrimeNumberTheorem.MobiusLogarithmicRateBridge

/-! A finite cubic logarithmic-kernel estimate for the classical logarithmic
Möbius mean route. Source: direct comparison with the existing square-log kernel. -/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis

/-- The existing square-log estimate gains a vanishing factor when the kernel
has one extra logarithm and the quotient is bounded below by K. -/
theorem finite_reciprocal_cube_log_sum_le
    (x K : ℝ) (M : ℕ) (hM : 0 < M) (hK : 1 ≤ K)
    (hMK : (M : ℝ) * K ≤ x) :
    (∑ k ∈ Finset.range M,
      1 / (((k : ℝ) + 1) * (1 + Real.log (x / ((k : ℝ) + 1))) ^ 3)) ≤
      3 / (1 + Real.log K) := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hMx : (M : ℝ) ≤ x :=
    (le_mul_of_one_le_right (Nat.cast_nonneg M) hK).trans hMK
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hdenK : 0 < 1 + Real.log K := by linarith
  have hterm (k : ℕ) (hk : k ∈ Finset.range M) :
      1 / (((k : ℝ) + 1) * (1 + Real.log (x / ((k : ℝ) + 1))) ^ 3) ≤
        (1 / (1 + Real.log K)) *
          (1 / (((k : ℝ) + 1) * (1 + Real.log (x / ((k : ℝ) + 1))) ^ 2)) := by
    have hkM : (k : ℝ) + 1 ≤ (M : ℝ) := by
      exact_mod_cast (show k + 1 ≤ M by have := Finset.mem_range.mp hk; omega)
    have hkpos : 0 < (k : ℝ) + 1 := by positivity
    have hquot : K ≤ x / ((k : ℝ) + 1) := by
      apply (le_div_iff₀ hkpos).2
      have hprod : K * ((k : ℝ) + 1) ≤ (M : ℝ) * K := by
        simpa only [mul_comm] using (mul_le_mul_of_nonneg_right hkM hK0.le)
      exact hprod.trans hMK
    have hlog : Real.log K ≤ Real.log (x / ((k : ℝ) + 1)) :=
      Real.log_le_log hK0 hquot
    have hden : 0 < 1 + Real.log (x / ((k : ℝ) + 1)) := by linarith
    have hinv : 1 / (1 + Real.log (x / ((k : ℝ) + 1))) ≤
        1 / (1 + Real.log K) :=
      one_div_le_one_div_of_le hdenK (by linarith)
    calc
      _ = (1 / (1 + Real.log (x / ((k : ℝ) + 1)))) *
          (1 / (((k : ℝ) + 1) * (1 + Real.log (x / ((k : ℝ) + 1))) ^ 2)) := by
        field_simp [hkpos.ne', hden.ne']
        <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hinv (by positivity)
  calc
    _ ≤ ∑ k ∈ Finset.range M, (1 / (1 + Real.log K)) *
        (1 / (((k : ℝ) + 1) * (1 + Real.log (x / ((k : ℝ) + 1))) ^ 2)) :=
      Finset.sum_le_sum hterm
    _ = (1 / (1 + Real.log K)) * ∑ k ∈ Finset.range M,
        1 / (((k : ℝ) + 1) * (1 + Real.log (x / ((k : ℝ) + 1))) ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / (1 + Real.log K)) * 3 :=
      mul_le_mul_of_nonneg_left (RiemannResearch.NumberTheory.PrimeNumberTheorem.finite_reciprocal_square_log_sum_le x M hM hMx)
        (one_div_nonneg.mpr hdenK.le)
    _ = _ := by ring

end RiemannResearch.Analysis

namespace RiemannResearch.NumberTheory
open RiemannResearch.Analysis

/-- Uniform control of the small-divisor part of a reciprocal arithmetic
convolution. The envelope is stated explicitly; its intended provider is the
Abel remainder of the quantitative von-Mangoldt harmonic sum. -/
theorem reciprocal_log_cube_quotient_head_bound
    (a e : ℕ → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (ha : ∀ d, 0 < d → |a d| ≤ 1 / (d : ℝ))
    (he : ∀ q, 0 < q → |e q| ≤ D / (1 + Real.log ((q : ℝ) + 1)) ^ 3)
    (N K : ℕ) (hK : 0 < K) :
    |∑ k ∈ Finset.range (N / K), a (k + 1) * e (N / (k + 1))| ≤
      3 * D / (1 + Real.log (K : ℝ)) := by
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hlogK : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg hKR
  have hdenK : 0 < 1 + Real.log (K : ℝ) := by linarith
  by_cases hM : N / K = 0
  · simp only [hM, Finset.range_zero, Finset.sum_empty, abs_zero]
    positivity
  have hMpos : 0 < N / K := Nat.pos_of_ne_zero hM
  have hNK : ((N / K : ℕ) : ℝ) * (K : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self N K
  have hterm (k : ℕ) (hk : k ∈ Finset.range (N / K)) :
      |a (k + 1) * e (N / (k + 1))| ≤
        D * (1 / (((k : ℝ) + 1) *
          (1 + Real.log ((N : ℝ) / ((k : ℝ) + 1))) ^ 3)) := by
    have hd : 0 < k + 1 := by omega
    have hdNK : k + 1 ≤ N / K := by have := Finset.mem_range.mp hk; omega
    have hdK : (k + 1) * K ≤ N := (Nat.le_div_iff_mul_le hK).mp hdNK
    have hqK : K ≤ N / (k + 1) :=
      (Nat.le_div_iff_mul_le hd).mpr (by simpa [Nat.mul_comm] using hdK)
    have hq : 0 < N / (k + 1) := lt_of_lt_of_le hK hqK
    have hdR : 0 < (k : ℝ) + 1 := by positivity
    have hxK : (K : ℝ) ≤ (N : ℝ) / ((k : ℝ) + 1) := by
      apply (le_div_iff₀ hdR).2
      have hprod : ((k : ℝ) + 1) * K ≤ (N : ℝ) := by exact_mod_cast hdK
      simpa [mul_comm] using hprod
    have hx1 : 1 ≤ (N : ℝ) / ((k : ℝ) + 1) := hKR.trans hxK
    have hxpos : 0 < (N : ℝ) / ((k : ℝ) + 1) := lt_of_lt_of_le zero_lt_one hx1
    have hquot : (N : ℝ) / ((k : ℝ) + 1) <
        ((N / (k + 1) : ℕ) : ℝ) + 1 := by
      apply (div_lt_iff₀ hdR).2
      have hn := (Nat.div_lt_iff_lt_mul hd).mp
        (Nat.lt_succ_self (N / (k + 1)))
      exact_mod_cast hn
    have hlog : Real.log ((N : ℝ) / ((k : ℝ) + 1)) ≤
        Real.log (((N / (k + 1) : ℕ) : ℝ) + 1) :=
      Real.log_le_log hxpos hquot.le
    have hdenx : 0 < 1 + Real.log ((N : ℝ) / ((k : ℝ) + 1)) := by
      have := Real.log_nonneg hx1
      linarith
    have he' : |e (N / (k + 1))| ≤
        D / (1 + Real.log ((N : ℝ) / ((k : ℝ) + 1))) ^ 3 := by
      apply (he _ hq).trans
      apply div_le_div_of_nonneg_left hD (by positivity)
      gcongr
    have ha' : |a (k + 1)| ≤ 1 / ((k : ℝ) + 1) := by
      simpa only [Nat.cast_add, Nat.cast_one] using ha (k + 1) hd
    rw [abs_mul]
    calc
      _ ≤ (1 / ((k : ℝ) + 1)) *
          (D / (1 + Real.log ((N : ℝ) / ((k : ℝ) + 1))) ^ 3) :=
        mul_le_mul ha' he' (abs_nonneg _) (by positivity)
      _ = _ := by
        field_simp [hdR.ne', hdenx.ne']
  calc
    _ ≤ ∑ k ∈ Finset.range (N / K), |a (k + 1) * e (N / (k + 1))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (N / K), D *
        (1 / (((k : ℝ) + 1) *
          (1 + Real.log ((N : ℝ) / ((k : ℝ) + 1))) ^ 3)) :=
      Finset.sum_le_sum hterm
    _ = D * ∑ k ∈ Finset.range (N / K),
        1 / (((k : ℝ) + 1) *
          (1 + Real.log ((N : ℝ) / ((k : ℝ) + 1))) ^ 3) := by
      rw [Finset.mul_sum]
    _ ≤ D * (3 / (1 + Real.log (K : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (finite_reciprocal_cube_log_sum_le N K (N / K) hMpos hKR hNK) hD
    _ = _ := by ring

end RiemannResearch.NumberTheory

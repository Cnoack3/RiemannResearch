import RiemannResearch.NumberTheory.DirichletExponentialLocalFactors
import RiemannResearch.NumberTheory.DirichletExponentialLocalTail
import RiemannResearch.NumberTheory.DirichletExponentialTail
import Mathlib.Analysis.Complex.Exponential

/-!
# A factorial bound for generalized-divisor moments

Source: the user-provided Pareto argument, conversation of 2026-11-13.
Split the finite Euler product at twice the convolution-power index, bound
small primes by the odd-integer product and large primes by the integer tail,
then use a single term of the scalar exponential series to obtain a factorial.
-/

open scoped BigOperators

namespace RiemannResearch.NumberTheory.DirichletExponential

private theorem tailFactor_den_pos {r n : ℕ} (hn : 2 * r < n) :
    (0 : ℝ) < (n : ℝ) ^ 2 - (r : ℝ) ^ 2 := by
  have hnr : (r : ℝ) < n := by exact_mod_cast (show r < n by omega)
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  nlinarith

private theorem one_le_tailFactor {r n : ℕ} (hn : 2 * r < n) :
    (1 : ℝ) ≤ (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - (r : ℝ) ^ 2) := by
  apply (le_div_iff₀ (tailFactor_den_pos hn)).2
  nlinarith [sq_nonneg (r : ℝ)]

private theorem divisorMomentTerm_prime_local_large {p r : ℕ} (hp : p.Prime)
    (hrp : 2 * r < p) :
    (∑' a : ℕ, divisorMomentTerm r (p ^ a)) ≤
      (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - (r : ℝ) ^ 2) := by
  have h := zetaReal_pow_prime_pow_sq_tsum_le hp (show r < p by omega)
  change (∑' a : ℕ, divisorMomentTerm r (p ^ a)) ≤ _ at h
  have hratio : 1 / (1 - (r : ℝ) ^ 2 / (p : ℝ) ^ 2) =
      (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - (r : ℝ) ^ 2) := by
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hd := ne_of_gt (tailFactor_den_pos hrp)
    field_simp [hp0, hd]
  rwa [hratio] at h

/-- The finite Euler product is bounded uniformly in its prime cutoff. -/
theorem divisorMomentTerm_finite_euler_bound (r : ℕ) (hr : 1 ≤ r) (N : ℕ) :
    (∏ p ∈ N.primesBelow, ∑' a : ℕ, divisorMomentTerm r (p ^ a)) ≤
      (12 * (r : ℝ)) ^ r * Real.exp r := by
  classical
  let s := N.primesBelow
  let small := s.filter (fun p => p ≤ 2 * r)
  let large := s.filter (fun p => ¬ p ≤ 2 * r)
  have hlocal0 (p : ℕ) : 0 ≤ ∑' a : ℕ, divisorMomentTerm r (p ^ a) :=
    tsum_nonneg fun a => divisorMomentTerm_nonneg r _
  have hsmall : (∏ p ∈ small, ∑' a : ℕ, divisorMomentTerm r (p ^ a)) ≤
      (12 * (r : ℝ)) ^ r := by
    calc
      _ ≤ ∏ p ∈ small, (((p : ℝ) / ((p : ℝ) - 1)) ^ 2) ^ r := by
        apply Finset.prod_le_prod (fun p _ => hlocal0 p)
        intro p hp
        obtain ⟨hps, hpr⟩ := Finset.mem_filter.mp hp
        exact (divisorMomentTerm_prime_local_small
          (Nat.prime_of_mem_primesBelow hps) r hr).2
      _ = ((∏ p ∈ small, (p : ℝ) / ((p : ℝ) - 1)) ^ 2) ^ r := by
        rw [Finset.prod_pow, Finset.prod_pow]
      _ ≤ (12 * (r : ℝ)) ^ r := by
        apply pow_le_pow_left₀ (sq_nonneg _)
        apply small_prime_euler_product_sq_le r hr small
        intro p hp
        obtain ⟨hps, hpr⟩ := Finset.mem_filter.mp hp
        exact ⟨Nat.prime_of_mem_primesBelow hps, hpr⟩
  have hlarge : (∏ p ∈ large, ∑' a : ℕ, divisorMomentTerm r (p ^ a)) ≤
      Real.exp r := by
    have hsubset : large ⊆ Finset.Icc (2 * r + 1) N := by
      intro p hp
      obtain ⟨hps, hpr⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_Icc.mpr ⟨by omega, (Nat.lt_of_mem_primesBelow hps).le⟩
    calc
      _ ≤ ∏ p ∈ large, (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - (r : ℝ) ^ 2) := by
        apply Finset.prod_le_prod (fun p _ => hlocal0 p)
        intro p hp
        obtain ⟨hps, hpr⟩ := Finset.mem_filter.mp hp
        exact divisorMomentTerm_prime_local_large
          (Nat.prime_of_mem_primesBelow hps) (by omega)
      _ ≤ ∏ n ∈ Finset.Icc (2 * r + 1) N,
          (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - (r : ℝ) ^ 2) := by
        apply Finset.prod_le_prod_of_subset_of_one_le hsubset
        · intro p hp
          exact zero_le_one.trans
            (one_le_tailFactor (by have := (Finset.mem_filter.mp hp).2; omega))
        · intro n hn _
          exact one_le_tailFactor (by have := (Finset.mem_Icc.mp hn).1; omega)
      _ ≤ Real.exp r := euler_tail_product_le r N (by omega)
  have hsplit : (∏ p ∈ N.primesBelow, ∑' a : ℕ, divisorMomentTerm r (p ^ a)) =
      (∏ p ∈ small, ∑' a : ℕ, divisorMomentTerm r (p ^ a)) *
        (∏ p ∈ large, ∑' a : ℕ, divisorMomentTerm r (p ^ a)) := by
    exact (Finset.prod_filter_mul_prod_filter_not s (fun p => p ≤ 2 * r)
      (fun p => ∑' a : ℕ, divisorMomentTerm r (p ^ a))).symm
  rw [hsplit]
  exact mul_le_mul hsmall hlarge (Finset.prod_nonneg fun p _ => hlocal0 p)
    (by positivity)

/-- The generalized-divisor moment bound before converting to a factorial. -/
theorem divisorMomentTerm_summable_and_bound (r : ℕ) (hr : 1 ≤ r) :
    Summable (divisorMomentTerm r) ∧
      (∑' n : ℕ, divisorMomentTerm r n) ≤
        (12 * (r : ℝ)) ^ r * Real.exp r := by
  apply summable_and_tsum_le_of_finite_euler_bound
    (divisorMomentTerm_zero r) (divisorMomentTerm_one r)
    (divisorMomentTerm_nonneg r) (divisorMomentTerm_mul r)
  · intro p hp
    exact (divisorMomentTerm_prime_local_small hp r hr).1
  · exact divisorMomentTerm_finite_euler_bound r hr

/-- The elementary exponential-series inequality supplies a factorial bound. -/
theorem moment_bound_le_factorial (r : ℕ) :
    (12 * (r : ℝ)) ^ r * Real.exp r ≤
      (12 * Real.exp 2) ^ r * (r.factorial : ℝ) := by
  have hf : (0 : ℝ) < (r.factorial : ℝ) := by positivity
  have hrpow : (r : ℝ) ^ r ≤ Real.exp r * (r.factorial : ℝ) :=
    (div_le_iff₀ hf).mp
      (Real.pow_div_factorial_le_exp (r : ℝ) (Nat.cast_nonneg r) r)
  have he : Real.exp (r : ℝ) = Real.exp 1 ^ r := by
    simpa using Real.exp_nat_mul (1 : ℝ) r
  have he2 : Real.exp (2 : ℝ) = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  calc
    (12 * (r : ℝ)) ^ r * Real.exp r =
        (12 : ℝ) ^ r * (r : ℝ) ^ r * Real.exp r := by rw [mul_pow]
    _ ≤ (12 : ℝ) ^ r * (Real.exp r * (r.factorial : ℝ)) * Real.exp r := by
      gcongr
    _ = (12 * Real.exp 2) ^ r * (r.factorial : ℝ) := by
      rw [he, he2, mul_pow, mul_pow]
      ring

/-- A uniform factorial moment bound for every convolution power, including
the degree-zero convolution identity `δ₁`. -/
theorem zetaReal_pow_square_summable_and_bound (r : ℕ) :
    Summable (fun n : ℕ => ((zetaReal ^ r) n) ^ 2 / (n : ℝ) ^ 2) ∧
      (∑' n : ℕ, ((zetaReal ^ r) n) ^ 2 / (n : ℝ) ^ 2) ≤
        (12 * Real.exp 2) ^ r * (r.factorial : ℝ) := by
  change Summable (divisorMomentTerm r) ∧
    (∑' n : ℕ, divisorMomentTerm r n) ≤ _
  by_cases hr : r = 0
  · subst r
    have hzero : divisorMomentTerm 0 = (fun n : ℕ => if n = 1 then (1 : ℝ) else 0) := by
      funext n
      by_cases hn : n = 1 <;> simp [divisorMomentTerm, ArithmeticFunction.one_apply, hn]
    rw [hzero]
    constructor
    · apply summable_of_sum_range_le
        (fun n => by split_ifs <;> norm_num) (c := (1 : ℝ))
      intro N
      by_cases hN : (1 : ℕ) ∈ Finset.range N <;> simp [hN]
    · simp
  · obtain ⟨hs, hb⟩ := divisorMomentTerm_summable_and_bound r (by omega)
    exact ⟨hs, hb.trans (moment_bound_le_factorial r)⟩

end RiemannResearch.NumberTheory.DirichletExponential

import RiemannResearch.NumberTheory.PositiveDilationSum
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MobiusReciprocal
import RiemannResearch.NumberTheory.PrimeNumberTheorem.Consequences
import RiemannResearch.RH.DampedMobiusSeed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Finite arithmetic identities for the logarithmic Möbius mean

Source: direct finite divisor-convolution derivation.

The finite convolution identities below support the
classical limit recorded in NIST DLMF 27.11.15. They are elementary identities;
the quantitative prime-error and limiting estimates are separate obligations.
The intended route uses B_N = sum_{n <= N} (Lambda(n)-1)/n, its convergent Abel
expansion, and mu * (Lambda-1) = -mu log - delta. It does not assume RH or an
unproved logarithmic Mertens estimate.

The positive-multiple reindexing provider is shared through the general
`NumberTheory/PositiveDilationSum` foundation.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.NumberTheory

/-- Summation of a finite Dirichlet convolution over positive integers. -/
theorem positive_divisor_convolution_sum (a b : ℕ → ℝ) (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N,
      a d * ∑ k ∈ Finset.Icc 1 (N / d), b k) =
    ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, a d * b (n / d) := by
  classical
  calc
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        if d ∣ n then a d * b (n / d) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← positive_dilation_sum N d (Finset.mem_Icc.mp hd).1 b,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      split_ifs <;> simp
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N,
        if d ∣ n then a d * b (n / d) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      obtain ⟨hnpos, hnN⟩ := Finset.mem_Icc.mp hn
      have he : (Finset.Icc 1 N).filter (fun d => d ∣ n) = n.divisors := by
        ext d
        simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
        constructor
        · rintro ⟨⟨hdpos, hdN⟩, hdvd⟩
          exact ⟨hdvd, Nat.ne_of_gt hnpos⟩
        · rintro ⟨hdvd, hn0⟩
          have hd0 : d ≠ 0 := by
            intro hzero
            subst d
            have : n = 0 := by simpa using hdvd
            exact hn0 this
          exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hd0,
            (Nat.le_of_dvd hnpos hdvd).trans hnN⟩, hdvd⟩
      rw [← Finset.sum_filter, he]

/-- The reciprocal weight factors exactly through multiplication. -/
theorem reciprocal_divisor_convolution_sum (a b : ℕ → ℝ) (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N,
      (a d / (d : ℝ)) * ∑ k ∈ Finset.Icc 1 (N / d), b k / (k : ℝ)) =
    ∑ n ∈ Finset.Icc 1 N,
      (∑ d ∈ n.divisors, a d * b (n / d)) / (n : ℝ) := by
  rw [positive_divisor_convolution_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  rw [div_mul_div_comm]
  have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hmul : (d : ℝ) * ((n / d : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' hdvd
  rw [hmul]

/-- A pointwise divisor-convolution identity gives its exact weighted finite
sum. In the Möbius application the pointwise identity is already arithmetic,
not an asymptotic cancellation hypothesis. -/
theorem reciprocal_convolution_sum_of_divisor_identity
    (a b t : ℕ → ℝ)
    (hid : ∀ n, 0 < n → ∑ d ∈ n.divisors, a d * b (n / d) = t n)
    (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N,
      (a d / (d : ℝ)) * ∑ k ∈ Finset.Icc 1 (N / d), b k / (k : ℝ)) =
      ∑ n ∈ Finset.Icc 1 N, t n / (n : ℝ) := by
  rw [reciprocal_divisor_convolution_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [hid n (Finset.mem_Icc.mp hn).1]

end RiemannResearch.NumberTheory

namespace RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- Actual Möbius/von-Mangoldt divisor convolution, with its sign retained. -/
theorem moebius_vonMangoldt_divisor_sum (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) *
      ArithmeticFunction.vonMangoldt (n / d)) =
        -(ArithmeticFunction.moebius n : ℝ) * Real.log n := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    mu_log_eq_mu_mul_neg_lambda
  simp only [mu_log_apply, ArithmeticFunction.mul_apply,
    ArithmeticFunction.neg_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.log_apply] at h
  rw [Nat.sum_divisorsAntidiagonal
    (fun d k => (ArithmeticFunction.moebius d : ℝ) *
      -ArithmeticFunction.vonMangoldt k)] at h
  simp only [mul_neg, Finset.sum_neg_distrib] at h
  linarith

/-- The renormalized harmonic von-Mangoldt sum. Its limiting constant is not
evaluated or postulated by the finite identities in this module. -/
def mangoldtHarmonicDefect (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n - 1) / (n : ℝ)

def logarithmicMobiusMean (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    (ArithmeticFunction.moebius n : ℝ) * Real.log n / (n : ℝ)

/-- Exact finite identity behind the logarithmic mean limit. The constant one
comes from the Möbius divisor sum and is not an asymptotic approximation. -/
theorem logarithmicMobiusMean_convolution (N : ℕ) (hN : 0 < N) :
    (∑ d ∈ Finset.Icc 1 N,
      ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) *
        mangoldtHarmonicDefect (N / d)) = -logarithmicMobiusMean N - 1 := by
  unfold mangoldtHarmonicDefect
  rw [RiemannResearch.NumberTheory.reciprocal_divisor_convolution_sum]
  have hdiv (n : ℕ) :
      (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) *
        (ArithmeticFunction.vonMangoldt (n / d) - 1)) =
      -(ArithmeticFunction.moebius n : ℝ) * Real.log n -
        (if n = 1 then 1 else 0) := by
    simp_rw [mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, moebius_vonMangoldt_divisor_sum,
      RiemannResearch.RH.Pareto.moebius_real_divisor_sum]
  simp_rw [hdiv, sub_div, neg_mul, neg_div]
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have hdelta : (∑ n ∈ Finset.Icc 1 N,
      (if n = 1 then (1 : ℝ) else 0) / (n : ℝ)) = 1 := by
    rw [Finset.sum_eq_single 1]
    · norm_num
    · intro n hn hn1
      simp [hn1]
    · intro hn
      exact False.elim (hn (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩))
  rw [hdelta]
  rfl

/-- Exact subtraction of an arbitrary limiting constant. -/
theorem logarithmicMobiusMean_remainder_identity
    (β : ℝ) (N : ℕ) (hN : 0 < N) :
    logarithmicMobiusMean N + 1 =
      -β * RiemannResearch.RH.Pareto.mobiusReciprocalSum N -
        ∑ d ∈ Finset.Icc 1 N,
          ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) *
            (mangoldtHarmonicDefect (N / d) - β) := by
  have h := logarithmicMobiusMean_convolution N hN
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  change logarithmicMobiusMean N + 1 =
    -β * RiemannResearch.RH.Pareto.mobiusReciprocalSum N -
      ((∑ d ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) *
          mangoldtHarmonicDefect (N / d)) -
        RiemannResearch.RH.Pareto.mobiusReciprocalSum N * β)
  linarith

end RiemannResearch.NumberTheory.PrimeNumberTheorem

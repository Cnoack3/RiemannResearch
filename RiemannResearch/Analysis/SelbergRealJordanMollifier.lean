/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.SelbergMollifierOptimization
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Real-order Jordan weights for the Selberg mollifier

The finite arithmetic step in Simonic, arXiv:1910.08274, Section 4.1:
https://arxiv.org/abs/1910.08274 .

These are unconditional finite identities. They supply positive real-order
weights and the gcd-power kernel required by the optimized mollifier.
They are not a uniform mollified zeta moment or a zero-density theorem.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.SelbergMollifier

/-- Real powers as an arithmetic function, with the required value zero at zero. -/
def realPower (a : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else (n : ℝ) ^ a, by simp⟩

theorem realPower_apply (a : ℝ) {n : ℕ} (hn : n ≠ 0) :
    realPower a n = (n : ℝ) ^ a := by simp [realPower, hn]

theorem realPower_one (a : ℝ) : realPower a 1 = 1 := by simp [realPower]

theorem realPower_mul (a : ℝ) (m n : ℕ) :
    realPower a (m * n) = realPower a m * realPower a n := by
  by_cases hm : m = 0
  · subst m; simp [realPower]
  by_cases hn : n = 0
  · subst n; simp [realPower]
  rw [realPower_apply a (Nat.mul_ne_zero hm hn), realPower_apply a hm,
    realPower_apply a hn, Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]

theorem realPower_isMultiplicative (a : ℝ) : (realPower a).IsMultiplicative :=
  ⟨realPower_one a, fun {_ _} _ => realPower_mul a _ _⟩

/-- Jordan's divisor weight for an arbitrary real order. -/
def realJordan (a : ℝ) : ArithmeticFunction ℝ :=
  realPower a * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)

theorem realJordan_one (a : ℝ) : realJordan a 1 = 1 := by
  simp [realJordan, realPower_one]

/-- Exact divisor identity, proved by Dirichlet-convolution inversion. -/
theorem sum_realJordan_divisors (a : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, realJordan a d) = (n : ℝ) ^ a := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply, realJordan, mul_assoc,
    ArithmeticFunction.coe_moebius_mul_coe_zeta, mul_one, realPower_apply a hn]

theorem realJordan_moebius_sum (a : ℝ) {n : ℕ} (hn : n ≠ 0) :
    realJordan a n = (n : ℝ) ^ a *
      ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-a) := by
  rw [realJordan, mul_comm, ArithmeticFunction.mul_apply]
  simp only [ArithmeticFunction.intCoe_apply]
  rw [Nat.sum_divisorsAntidiagonal (fun d e =>
      (ArithmeticFunction.moebius d : ℝ) * realPower a e), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hnd0 : n / d ≠ 0 := (Nat.div_pos
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdn) (Nat.pos_of_ne_zero hd0)).ne'
  rw [realPower_apply a hnd0,
    Nat.cast_div hdn (by exact_mod_cast hd0),
    Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity)]
  ring

/-- General Euler--Mobius identity. The pinned mathlib supplies the squarefree
case; this extension follows the upstream mathlib argument (Moebius.lean,
generalization dated 2026-09-14), retaining all nonsquarefree divisors. -/
theorem product_one_sub_eq_moebius_sum (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) {n : ℕ} (hn : n ≠ 0) :
    (∏ p ∈ n.primeFactors, (1 - f p)) =
      ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * f d := by
  let P := ∏ p ∈ n.primeFactors, p
  have hP : Squarefree P := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp q hq hpq
      exact Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
          (Nat.prime_of_mem_primeFactors hq)).mpr hpq)
    · intro p hp
      exact (Nat.prime_of_mem_primeFactors hp).squarefree
  calc
    _ = ∏ p ∈ P.primeFactors, (1 - f p) := by
      rw [Nat.primeFactors_prod_primeFactors]
    _ = ∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ) * f d :=
      ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree f hf hP
    _ = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * f d := by
      refine Finset.sum_subset
        (Nat.divisors_subset_of_dvd hn n.prod_primeFactors_dvd) ?_
      intro d hd hdP
      suffices hns : ¬ Squarefree d by
        simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns]
      intro hsq
      apply hdP
      apply Nat.mem_divisors.mpr
      refine ⟨?_, hP.ne_zero⟩
      rw [← Nat.prod_primeFactors_of_squarefree hsq]
      exact Finset.prod_dvd_prod_of_subset _ _ _
        (Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hn)

/-- Euler product, including every prime divisor and the complete power factor. -/
theorem realJordan_eq_product (a : ℝ) {n : ℕ} (hn : n ≠ 0) :
    realJordan a n = (n : ℝ) ^ a *
      ∏ p ∈ n.primeFactors, (1 - (p : ℝ) ^ (-a)) := by
  rw [realJordan_moebius_sum a hn]
  congr 1

  calc
    _ = ∑ d ∈ n.divisors,
        (ArithmeticFunction.moebius d : ℝ) * realPower (-a) d := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [realPower_apply (-a) (Nat.pos_of_mem_divisors hd).ne']
    _ = ∏ p ∈ n.primeFactors, (1 - realPower (-a) p) :=
      (product_one_sub_eq_moebius_sum (realPower (-a))
        (realPower_isMultiplicative (-a)) hn).symm
    _ = ∏ p ∈ n.primeFactors, (1 - (p : ℝ) ^ (-a)) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [realPower_apply (-a) (Nat.mem_primeFactors.mp hp).1.ne_zero]

theorem realJordan_pos {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : n ≠ 0) :
    0 < realJordan a n := by
  rw [realJordan_eq_product a hn]
  apply mul_pos
  · exact Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) _
  · apply Finset.prod_pos
    intro p hp
    have hp1 : (1 : ℝ) < p := by
      exact_mod_cast (Nat.mem_primeFactors.mp hp).1.one_lt
    exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg hp1 (neg_neg_of_pos ha))

/-- The full gcd-power kernel has exactly the real-Jordan diagonalization. -/
theorem gcd_rpow_energy_eq (a : ℝ) (L : ℕ) (coeff : ℕ → ℝ) :
    (∑ d ∈ L.divisors, ∑ e ∈ L.divisors,
      coeff d * coeff e * (Nat.gcd d e : ℝ) ^ a) =
        divisorEnergy L (realJordan a) coeff := by
  rw [← gcdKernel_energy_eq L (realJordan a) coeff]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  rw [sum_realJordan_divisors a
    (Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left d e) (Nat.pos_of_mem_divisors hd)).ne']

/-- The mass includes its exact n=1 contribution. -/
theorem one_le_cutoffMass_realJordan {a : ℝ} (ha : 0 < a)
    (L X : ℕ) (hL : L ≠ 0) (hX : 1 ≤ X) :
    1 ≤ cutoffMass L X (realJordan a) := by
  have h1 : 1 ∈ cutoffSet L X :=
    Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨one_dvd L, hL⟩, hX⟩
  have h := Finset.single_le_sum
    (s := cutoffSet L X)
    (f := fun r => (ArithmeticFunction.moebius r : ℝ) ^ 2 / realJordan a r)
    (fun r hr => div_nonneg (sq_nonneg _) (realJordan_pos ha
      (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hr).1).ne').le) h1
  simpa [cutoffMass, diagonalMass, realJordan_one] using h

theorem cutoffMass_realJordan_pos {a : ℝ} (ha : 0 < a)
    (L X : ℕ) (hL : L ≠ 0) (hX : 1 ≤ X) :
    0 < cutoffMass L X (realJordan a) :=
  lt_of_lt_of_le (by norm_num) (one_le_cutoffMass_realJordan ha L X hL hX)

/-- Exact optimization with all squared residuals, now without abstract
weight-positivity or nonzero-capacity hypotheses. -/
theorem gcd_rpow_cutoff_completion {a : ℝ} (ha : 0 < a)
    (L X : ℕ) (hL : L ≠ 0) (hX : 1 ≤ X) (coeff : ℕ → ℝ)
    (hsupport : ∀ d, X < d → coeff d = 0) (h1 : coeff 1 = 1) :
    (∑ d ∈ L.divisors, ∑ e ∈ L.divisors,
      coeff d * coeff e * (Nat.gcd d e : ℝ) ^ a) =
      1 / cutoffMass L X (realJordan a) +
        ∑ r ∈ cutoffSet L X, realJordan a r *
          (divisorCoordinate L coeff r - (ArithmeticFunction.moebius r : ℝ) /
            (realJordan a r * cutoffMass L X (realJordan a))) ^ 2 := by
  rw [gcd_rpow_energy_eq]
  exact cutoffEnergy_completion L X hL (realJordan a) coeff
    (fun r hr => (realJordan_pos ha
      (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hr).1).ne').ne')
    (cutoffMass_realJordan_pos ha L X hL hX).ne' hsupport h1

/-- An actual normalized mollifier with prescribed support attains the
reciprocal capacity. Factorial embedding adds no nonzero coefficients. -/
theorem exists_realJordan_cutoff_optimizer {a : ℝ} (ha : 0 < a)
    (X : ℕ) (hX : 1 ≤ X) :
    ∃ coeff : ℕ → ℝ, coeff 1 = 1 ∧
      (∀ d, X < d → coeff d = 0) ∧
      (∑ d ∈ (Nat.factorial X).divisors, ∑ e ∈ (Nat.factorial X).divisors,
        coeff d * coeff e * (Nat.gcd d e : ℝ) ^ a) =
        1 / (∑ r ∈ Finset.Icc 1 X,
          (ArithmeticFunction.moebius r : ℝ) ^ 2 / realJordan a r) := by
  let L := Nat.factorial X
  have hL : L ≠ 0 := (Nat.factorial_pos X).ne'
  have hG := (cutoffMass_realJordan_pos ha L X hL hX).ne'
  refine ⟨cutoffOptimizer L X (realJordan a),
    cutoffOptimizer_one L X (realJordan a) hG,
    cutoffOptimizer_eq_zero_above L X (realJordan a), ?_⟩
  rw [gcd_rpow_energy_eq]
  rw [cutoffEnergy_optimizer L X hL (realJordan a)
    (fun r hr => (realJordan_pos ha
      (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hr).1).ne').ne') hG]
  rw [cutoffMass_factorial]


end RiemannResearch.Analysis.SelbergMollifier

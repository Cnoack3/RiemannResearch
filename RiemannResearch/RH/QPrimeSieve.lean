import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.Analysis.NoorLogarithmDensity
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Divisor sieves, actual residue atoms, and the inverse-square head obstruction

There are no proof placeholders. Compilation and project integration remain
required before any declaration below is described as kernel verified.

Source: user-requested investigation of the prime structure of the zeta-two
law. Finite inclusion-exclusion is supplied by the existing `Noor.moebius_sift`.
The elementary Wallis product estimate is proved directly below.

The finite product-to-divisor-density identification is proved for squarefree
conductors. Neither this draft nor pointwise sieve convergence proves RH.
In fact the uncorrected primorial sieve has a fixed positive inverse-square
approximation error, with an explicit conductor family in the last theorem.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace RiemannResearch.RH.QPrimeSieve
open ArithmeticCumulative
open ZetaTwoProbability

/-- Natural-density coefficient of a finite divisor inclusion-exclusion sieve. -/
def divisorDensity (L : ℕ) : ℝ :=
  ∑ d ∈ L.divisors, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)

def reciprocalFunction : ArithmeticFunction ℝ :=
  ⟨fun n => (n : ℝ)⁻¹, by simp⟩

theorem reciprocalFunction_multiplicative : reciprocalFunction.IsMultiplicative := by
  constructor
  · norm_num [reciprocalFunction]
  · intro m n _
    change ((m * n : ℕ) : ℝ)⁻¹ = (m : ℝ)⁻¹ * (n : ℝ)⁻¹
    simp [Nat.cast_mul, mul_inv_rev, mul_comm]

/-- The exact finite prime Euler product for a squarefree conductor. -/
theorem divisorDensity_euler (L : ℕ) (hL : Squarefree L) :
    divisorDensity L = ∏ p ∈ L.primeFactors, (1 - 1 / (p : ℝ)) := by
  simpa [divisorDensity, reciprocalFunction, div_eq_mul_inv] using
    (ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
      reciprocalFunction reciprocalFunction_multiplicative hL).symm

/-- A legal finite residue combination; nonsquarefree coefficients vanish. -/
def divisorSieve (L n : ℕ) : ℝ :=
  -(∑ d ∈ L.divisors,
    (ArithmeticFunction.moebius d : ℝ) * residueFraction d n)

/-- Number of positive integers at most n coprime to L, as a real number. -/
def coprimeCount (L n : ℕ) : ℝ :=
  cumulative (fun k => if Nat.Coprime k L then (1 : ℝ) else 0) n

theorem divisor_sift (L k : ℕ) (hL : L ≠ 0) :
    (∑ d ∈ L.divisors,
      (ArithmeticFunction.moebius d : ℝ) * divisorIndicator d k) =
      if Nat.Coprime k L then 1 else 0 := by
  simp only [divisorIndicator, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  exact RiemannResearch.Analysis.Noor.moebius_sift L k hL

/-- Exact sieve-to-atom identity, retaining the entire linear density term. -/
theorem divisorSieve_eq_count_sub_linear (L n : ℕ) (hL : L ≠ 0) :
    divisorSieve L n = coprimeCount L n - (n : ℝ) * divisorDensity L := by
  have hcum :
      (∑ d ∈ L.divisors, (ArithmeticFunction.moebius d : ℝ) *
        cumulative (balancedDivisor d) n) = divisorSieve L n := by
    unfold divisorSieve
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [cumulative_balancedDivisor d n (Nat.pos_of_mem_divisors hd)]
    ring
  have hcum' :
      (∑ d ∈ L.divisors, (ArithmeticFunction.moebius d : ℝ) *
        cumulative (balancedDivisor d) n) =
      cumulative (fun k => ∑ d ∈ L.divisors,
        (ArithmeticFunction.moebius d : ℝ) * balancedDivisor d k) n := by
    simp only [cumulative, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hpoint (k : ℕ) :
      (∑ d ∈ L.divisors,
        (ArithmeticFunction.moebius d : ℝ) * balancedDivisor d k) =
      (if Nat.Coprime k L then (1 : ℝ) else 0) - divisorDensity L := by
    simp only [balancedDivisor, mul_sub, Finset.sum_sub_distrib]
    rw [divisor_sift L k hL]
    simp [divisorDensity, div_eq_mul_inv]
  rw [← hcum, hcum']
  simp_rw [hpoint]
  rw [cumulative_sub, cumulative_const]
  rfl

/-- A covered head contains exactly the single surviving integer 1. -/
theorem coprimeCount_head (L M n : ℕ) (hn : 0 < n) (hnM : n ≤ M)
    (hcover : ∀ k, 2 ≤ k → k ≤ M → ¬ Nat.Coprime k L) :
    coprimeCount L n = 1 := by
  have he : coprimeCount L n =
      cumulative (fun k => if k = 1 then (1 : ℝ) else 0) n := by
    unfold coprimeCount cumulative
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hk0 : k = 0
    · simp [hk0]
    · have hk2 : 2 ≤ k + 1 := by omega
      have hkM : k + 1 ≤ M := by
        have := Finset.mem_range.mp hk
        omega
      simp [hcover (k + 1) hk2 hkM, hk0]
  rw [he, cumulative_delta_one n hn]

theorem divisorSieve_head (L M n : ℕ) (hL : L ≠ 0)
    (hn : 0 < n) (hnM : n ≤ M)
    (hcover : ∀ k, 2 ≤ k → k ≤ M → ¬ Nat.Coprime k L) :
    divisorSieve L n = 1 - (n : ℝ) * divisorDensity L := by
  rw [divisorSieve_eq_count_sub_linear L n hL,
    coprimeCount_head L M n hn hnM hcover]

/-- Factorials supply a completely explicit covered head. Möbius coefficients
still restrict the residue combination to squarefree conductors. -/
theorem factorial_covers_head (M k : ℕ) (hk2 : 2 ≤ k) (hkM : k ≤ M) :
    ¬ Nat.Coprime k M.factorial := by
  have hd : k ∣ M.factorial := Nat.dvd_factorial (by omega) hkM
  simpa only [Nat.coprime_iff_gcd_eq_one, Nat.gcd_eq_left hd] using
    (show k ≠ 1 by omega)

theorem divisorSieve_factorial_head (M n : ℕ) (hn : 0 < n) (hnM : n ≤ M) :
    divisorSieve M.factorial n = 1 - (n : ℝ) * divisorDensity M.factorial :=
  divisorSieve_head M.factorial M n (Nat.factorial_ne_zero M) hn hnM
    (factorial_covers_head M)

/-- A finite part of the literal squared L²(Q) error. -/
def headError (M : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range M,
    (1 - f (k + 1)) ^ 2 / (zetaTwo * ((k + 1 : ℕ) : ℝ) ^ 2)

theorem headError_eq (M : ℕ) (f : ℕ → ℝ) (α : ℝ)
    (hhead : ∀ n, 0 < n → n ≤ M → f n = 1 - (n : ℝ) * α) :
    headError M f = (M : ℝ) * α ^ 2 / zetaTwo := by
  unfold headError
  have he : (∑ k ∈ Finset.range M,
      (1 - f (k + 1)) ^ 2 / (zetaTwo * ((k + 1 : ℕ) : ℝ) ^ 2)) =
      ∑ _k ∈ Finset.range M, α ^ 2 / zetaTwo := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hhead (k + 1) (by omega) (by have := Finset.mem_range.mp hk; omega)]
    have hkR : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hkR, ne_of_gt zetaTwo_pos]
    ring
  rw [he]
  simp [mul_div_assoc]

/-- Exact growing-head error, before any estimate on the prime product. -/
theorem divisorSieve_headError (L M : ℕ) (hL : L ≠ 0)
    (hcover : ∀ k, 2 ≤ k → k ≤ M → ¬ Nat.Coprime k L) :
    headError M (divisorSieve L) =
      (M : ℝ) * divisorDensity L ^ 2 / zetaTwo :=
  headError_eq M (divisorSieve L) (divisorDensity L)
    (fun n hn hnM => divisorSieve_head L M n hL hn hnM hcover)

/-- The Wallis comparison product over all odd integers 3 through 2m+1. -/
def oddComparison (m : ℕ) : ℝ :=
  ∏ j ∈ Finset.range m, (2 * (j : ℝ) + 2) / (2 * (j : ℝ) + 3)

theorem oddComparison_nonneg (m : ℕ) : 0 ≤ oddComparison m := by
  unfold oddComparison
  exact Finset.prod_nonneg (fun _ _ => by positivity)

/-- Elementary telescope inequality; no prime number theorem is used. -/
theorem oddComparison_sq_bound (m : ℕ) :
    1 ≤ (2 * (m : ℝ) + 1) * oddComparison m ^ 2 := by
  induction m with
  | zero => simp [oddComparison]
  | succ m ih =>
    have hstep : oddComparison (m + 1) =
        oddComparison m * ((2 * (m : ℝ) + 2) / (2 * (m : ℝ) + 3)) := by
      simp only [oddComparison, Finset.prod_range_succ]
    have hC : 0 < 2 * (m : ℝ) + 3 := by positivity
    have he : (2 * ((m + 1 : ℕ) : ℝ) + 1) * oddComparison (m + 1) ^ 2 =
        oddComparison m ^ 2 * (2 * (m : ℝ) + 2) ^ 2 / (2 * (m : ℝ) + 3) := by
      rw [hstep]
      push_cast
      field_simp [ne_of_gt hC]
      ring
    change 1 ≤ (2 * ((m + 1 : ℕ) : ℝ) + 1) * oddComparison (m + 1) ^ 2
    rw [he]
    apply (le_div_iff₀ hC).2
    have hm := mul_le_mul_of_nonneg_right ih hC.le
    nlinarith [sq_nonneg (oddComparison m)]

/-- The exact finite Euler product at odd cutoff 2m+1, written with primality
flags so that removing composite odd integers is explicit. At m=0 it is 1/2. -/
def oddPrimeDensity (m : ℕ) : ℝ :=
  (1 / 2) * ∏ j ∈ Finset.range m,
    if Nat.Prime (2 * j + 3) then
      (2 * (j : ℝ) + 2) / (2 * (j : ℝ) + 3) else 1

theorem oddPrimeDensity_ge_comparison (m : ℕ) :
    oddComparison m / 2 ≤ oddPrimeDensity m := by
  have hp : oddComparison m ≤
      ∏ j ∈ Finset.range m,
        if Nat.Prime (2 * j + 3) then
          (2 * (j : ℝ) + 2) / (2 * (j : ℝ) + 3) else 1 := by
    unfold oddComparison
    apply Finset.prod_le_prod
    · intro j _
      positivity
    · intro j _
      split_ifs
      · exact le_rfl
      · apply (div_le_one₀ (by positivity : 0 < 2 * (j : ℝ) + 3)).2
        linarith
  unfold oddPrimeDensity
  linarith

theorem oddPrimeDensity_nonneg (m : ℕ) : 0 ≤ oddPrimeDensity m :=
  (div_nonneg (oddComparison_nonneg m) (by norm_num)).trans
    (oddPrimeDensity_ge_comparison m)

/-- Uniform elementary obstruction for the uncorrected prime product. -/
theorem oddPrimeDensity_sq_bound (m : ℕ) :
    (1 / 4 : ℝ) ≤ (2 * (m : ℝ) + 1) * oddPrimeDensity m ^ 2 := by
  have hp := oddPrimeDensity_ge_comparison m
  have hW := oddComparison_nonneg m
  have hsq : oddComparison m * oddComparison m ≤
      (2 * oddPrimeDensity m) * (2 * oddPrimeDensity m) := by
    exact mul_self_le_mul_self hW (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ 2 * (m : ℝ) + 1 by positivity)
  nlinarith [oddComparison_sq_bound m]

/-- Assembly with the finite Euler-product identity displayed as a hypothesis.
This bridge must be proved for the chosen primorial/factorial conductor before
the theorem is advertised as a specialized result about that conductor. -/
theorem divisorSieve_headError_ge_quarter (L m : ℕ) (hL : L ≠ 0)
    (hcover : ∀ k, 2 ≤ k → k ≤ 2 * m + 1 → ¬ Nat.Coprime k L)
    (hdensity : divisorDensity L = oddPrimeDensity m) :
    1 / (4 * zetaTwo) ≤ headError (2 * m + 1) (divisorSieve L) := by
  rw [divisorSieve_headError L (2 * m + 1) hL hcover, hdensity]
  have hb := oddPrimeDensity_sq_bound m
  have hdiv := div_le_div_of_nonneg_right hb zetaTwo_pos.le
  push_cast
  calc
    1 / (4 * zetaTwo) = (1 / 4 : ℝ) / zetaTwo := by ring
    _ ≤ (2 * (m : ℝ) + 1) * oddPrimeDensity m ^ 2 / zetaTwo := hdiv

/-- Actual primes through odd cutoff 2m+1, with the prime 2 always included. -/
def primeSet (m : ℕ) : Finset ℕ :=
  insert 2 (((Finset.range m).filter (fun j => Nat.Prime (2 * j + 3))).image
    (fun j => 2 * j + 3))

def primeConductor (m : ℕ) : ℕ := ∏ p ∈ primeSet m, p

theorem primeSet_prime (m p : ℕ) (hp : p ∈ primeSet m) : Nat.Prime p := by
  rcases Finset.mem_insert.mp hp with rfl | hp
  · exact Nat.prime_two
  · rcases Finset.mem_image.mp hp with ⟨j, hj, rfl⟩
    exact (Finset.mem_filter.mp hj).2

theorem primeConductor_squarefree (m : ℕ) : Squarefree (primeConductor m) := by
  unfold primeConductor
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (primeSet_prime m p hp) (primeSet_prime m q hq)).mpr hpq)
  · intro p hp
    exact (primeSet_prime m p hp).squarefree

theorem primeConductor_primeFactors (m : ℕ) :
    (primeConductor m).primeFactors = primeSet m := by
  unfold primeConductor
  exact Nat.primeFactors_prod (fun p hp => primeSet_prime m p hp)

theorem primeConductor_density (m : ℕ) :
    divisorDensity (primeConductor m) = oddPrimeDensity m := by
  rw [divisorDensity_euler _ (primeConductor_squarefree m),
    primeConductor_primeFactors]
  have htwo : 2 ∉ (((Finset.range m).filter (fun j => Nat.Prime (2 * j + 3))).image
      (fun j => 2 * j + 3)) := by
    intro h
    rcases Finset.mem_image.mp h with ⟨j, hj, he⟩
    omega
  unfold primeSet oddPrimeDensity
  rw [Finset.prod_insert htwo, Finset.prod_image (by
    intro a ha b hb hab
    change 2 * a + 3 = 2 * b + 3 at hab
    omega), Finset.prod_filter]
  norm_num only [Nat.cast_ofNat]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  split_ifs
  · push_cast
    have hjR : (2 * (j : ℝ) + 3) ≠ 0 := by positivity
    field_simp [hjR]
    ring
  · rfl

theorem primeConductor_covers_head (m k : ℕ) (hk2 : 2 ≤ k)
    (hkM : k ≤ 2 * m + 1) : ¬ Nat.Coprime k (primeConductor m) := by
  obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd (show k ≠ 1 by omega)
  have hple : p ≤ k := Nat.le_of_dvd (by omega) hpk
  have hmem : p ∈ primeSet m := by
    rcases hp.eq_two_or_odd' with hp2 | ⟨j, hj⟩
    · simp [primeSet, hp2]
    · have hjpos : 0 < j := by have := hp.two_le; omega
      have hjm : j - 1 < m := by omega
      have he : 2 * (j - 1) + 3 = p := by omega
      apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      refine ⟨j - 1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjm, ?_⟩, he⟩
      simpa only [he] using hp
  have hpL : p ∣ primeConductor m := by
    unfold primeConductor
    exact Finset.dvd_prod_of_mem (fun p : ℕ => p) hmem
  exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hpk, hpL⟩

/-- The fully specified squarefree prime-sieve family has a fixed positive
inverse-square head error. It cannot approximate the constant in L²(Q). -/
theorem primeConductor_headError_ge_quarter (m : ℕ) :
    1 / (4 * zetaTwo) ≤
      headError (2 * m + 1) (divisorSieve (primeConductor m)) := by
  exact divisorSieve_headError_ge_quarter (primeConductor m) m
    (primeConductor_squarefree m).ne_zero (primeConductor_covers_head m)
    (primeConductor_density m)

/-- The complete literal squared error for Q, indexed by positive integers. -/
def fullError (f : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, (1 - f (k + 1)) ^ 2 /
    (zetaTwo * ((k + 1 : ℕ) : ℝ) ^ 2)

private theorem residueFraction_abs_le (d n : ℕ) (hd : 0 < d) :
    |residueFraction d n| ≤ 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hm : ((n % d : ℕ) : ℝ) ≤ d := by
    exact_mod_cast (Nat.mod_lt n hd).le
  unfold residueFraction
  rw [abs_of_nonneg (by positivity)]
  exact (div_le_one₀ hdR).mpr hm

theorem divisorSieve_abs_le (L n : ℕ) :
    |divisorSieve L n| ≤ (L.divisors.card : ℝ) := by
  calc
    |divisorSieve L n| =
        |∑ d ∈ L.divisors, (ArithmeticFunction.moebius d : ℝ) *
          residueFraction d n| := by simp [divisorSieve]
    _ ≤ ∑ d ∈ L.divisors,
        |(ArithmeticFunction.moebius d : ℝ) * residueFraction d n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ L.divisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul]
      have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      have hg := residueFraction_abs_le d n (Nat.pos_of_mem_divisors hd)
      exact (mul_le_mul hmu hg (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq
        (by norm_num)
    _ = (L.divisors.card : ℝ) := by simp

theorem fullError_summable_of_abs_le (f : ℕ → ℝ) (C : ℝ)
    (hf : ∀ n, |f n| ≤ C) :
    Summable (fun k : ℕ => (1 - f (k + 1)) ^ 2 /
      (zetaTwo * ((k + 1 : ℕ) : ℝ) ^ 2)) := by
  have hZ : 0 < zetaTwo := zetaTwo_pos
  have hs0 : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))
  have hs : Summable (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).mpr hs0
  have hsmajor : Summable (fun k : ℕ =>
      ((1 + C) ^ 2 / zetaTwo) * (1 / ((k + 1 : ℕ) : ℝ) ^ 2)) :=
    hs.mul_left _
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hsmajor
  intro k
  have herr : |1 - f (k + 1)| ≤ 1 + C := by
    calc
      _ ≤ |(1 : ℝ)| + |f (k + 1)| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (1 : ℝ) (-f (k + 1))
      _ ≤ 1 + C := by simpa using add_le_add_left (hf (k + 1)) 1
  have hsq : (1 - f (k + 1)) ^ 2 ≤ (1 + C) ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg (1 - f (k + 1))) herr
    simpa only [← pow_two, sq_abs] using h
  calc
    _ ≤ (1 + C) ^ 2 / (zetaTwo * ((k + 1 : ℕ) : ℝ) ^ 2) :=
      div_le_div_of_nonneg_right hsq (by positivity)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev, one_mul]; ring

theorem divisorSieve_fullError_summable (L : ℕ) :
    Summable (fun k : ℕ => (1 - divisorSieve L (k + 1)) ^ 2 /
      (zetaTwo * ((k + 1 : ℕ) : ℝ) ^ 2)) :=
  fullError_summable_of_abs_le (divisorSieve L) (L.divisors.card : ℝ)
    (divisorSieve_abs_le L)

theorem headError_le_fullError (M : ℕ) (f : ℕ → ℝ)
    (hs : Summable (fun k : ℕ => (1 - f (k + 1)) ^ 2 /
      (zetaTwo * ((k + 1 : ℕ) : ℝ) ^ 2))) :
    headError M f ≤ fullError f := by
  have hZ : 0 < zetaTwo := zetaTwo_pos
  unfold headError fullError
  exact Summable.sum_le_tsum _ (fun _ _ => by positivity) hs

/-- The lower bound applies to the complete Q error, with its summability proved. -/
theorem primeConductor_fullError_ge_quarter (m : ℕ) :
    1 / (4 * zetaTwo) ≤ fullError (divisorSieve (primeConductor m)) :=
  (primeConductor_headError_ge_quarter m).trans
    (headError_le_fullError (2 * m + 1) (divisorSieve (primeConductor m))
      (divisorSieve_fullError_summable (primeConductor m)))

/-- The canonical uncorrected primorial sieve fails the intended L²(Q)
approximation. This is unconditional and does not assume the negation of RH. -/
theorem primeConductor_fullError_not_tendsto_zero :
    ¬ Tendsto (fun m : ℕ => fullError (divisorSieve (primeConductor m)))
      atTop (𝓝 0) := by
  intro ht
  have hZ : 0 < zetaTwo := zetaTwo_pos
  have hpos : (0 : ℝ) < 1 / (4 * zetaTwo) := by positivity
  have hsmall := (tendsto_order.mp ht).2 (1 / (4 * zetaTwo)) hpos
  obtain ⟨m, hm⟩ := hsmall.exists
  exact (not_lt_of_ge (primeConductor_fullError_ge_quarter m)) hm

end RiemannResearch.RH.QPrimeSieve

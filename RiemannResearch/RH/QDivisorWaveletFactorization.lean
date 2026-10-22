import RiemannResearch.RH.QDivisibilityResidueCoefficients
import RiemannResearch.RH.QPrimePowerOrthogonal
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Arithmetic factorization of Q divisor wavelets

Source: direct finite multiplicative-function calculation. The arithmetic
Möbius wavelet factors into the actual independent prime-valuation wavelets.
This supplies the scalar Gram provider for their complete Hilbert-space basis.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RiemannResearch.RH.ZetaTwoHilbert
open RiemannResearch.RH.ZetaTwoProbability

/-- The scaled divisibility tail, as an arithmetic function of its conductor. -/
def scaledDivisorAF (n : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => (d : ℝ) ^ 2 * (if d ∣ n then 1 else 0), by simp⟩

theorem scaledDivisorAF_multiplicative (n : ℕ) :
    (scaledDivisorAF n).IsMultiplicative := by
  constructor
  · norm_num [scaledDivisorAF]
  · intro a b hab
    have hd : a * b ∣ n ↔ a ∣ n ∧ b ∣ n := by
      constructor
      · intro h
        exact ⟨(dvd_mul_right a b).trans h, (dvd_mul_left b a).trans h⟩
      · intro h
        exact hab.mul_dvd_of_dvd_of_dvd h.1 h.2
    by_cases ha : a ∣ n <;> by_cases hb : b ∣ n <;>
      simp [scaledDivisorAF, hd, ha, hb, Nat.cast_mul, mul_pow]

/-- Dirichlet convolution gives the full signed divisor wavelet. -/
def divisorWaveletAF (n : ℕ) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℝ) * scaledDivisorAF n

theorem divisorWaveletAF_multiplicative (n : ℕ) :
    (divisorWaveletAF n).IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_moebius.intCast.mul
    (scaledDivisorAF_multiplicative n)

theorem divisorWaveletAF_apply (r n : ℕ) :
    divisorWaveletAF n r = qDivisorWavelet r n := by
  rw [divisorWaveletAF, ArithmeticFunction.mul_apply]
  trans ∑ d ∈ r.divisors,
    ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) (r / d)) * scaledDivisorAF n d
  · exact Nat.sum_divisorsAntidiagonal'
      (fun a b => ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) a) *
        scaledDivisorAF n b)
  unfold qDivisorWavelet qScaledDivisibilitySum
  apply Finset.sum_congr rfl
  intro d hd
  simp only [ArithmeticFunction.intCoe_apply, scaledDivisorAF, ArithmeticFunction.coe_mk]
  ring

/-- Exact finite Möbius inversion, before specializing to one prime. -/
theorem sum_divisorWaveletAF (r n : ℕ) :
    (∑ d ∈ r.divisors, divisorWaveletAF n d) = scaledDivisorAF n r := by
  have he : (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * divisorWaveletAF n =
      scaledDivisorAF n := by
    unfold divisorWaveletAF
    rw [← mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, one_mul]
  have h := congrArg (fun f : ArithmeticFunction ℝ => f r) he
  simpa only [ArithmeticFunction.coe_zeta_mul_apply] using h

/-- Prime-power Möbius inversion is exactly one adjacent difference. -/
theorem divisorWaveletAF_prime_pow_succ (p a n : ℕ) (hp : p.Prime) :
    divisorWaveletAF n (p ^ (a + 1)) =
      scaledDivisorAF n (p ^ (a + 1)) - scaledDivisorAF n (p ^ a) := by
  have h0 := sum_divisorWaveletAF (p ^ a) n
  have h1 := sum_divisorWaveletAF (p ^ (a + 1)) n
  rw [Nat.sum_divisors_prime_pow hp] at h0 h1
  rw [Finset.sum_range_succ] at h1
  linarith

theorem divisorWaveletAF_prime_pow (p a : ℕ) (hp : p.Prime) (n : ℕ+) :
    divisorWaveletAF (n : ℕ) (p ^ a) = valuationWavelet p a n := by
  cases a with
  | zero =>
    simpa only [pow_zero, valuationWavelet_zero] using
      (divisorWaveletAF_multiplicative (n : ℕ)).map_one
  | succ a =>
    rw [divisorWaveletAF_prime_pow_succ p a (n : ℕ) hp, valuationWavelet_succ]
    have hdiv (j : ℕ) : p ^ j ∣ (n : ℕ) ↔ j ≤ primeValuation p n :=
      hp.pow_dvd_iff_le_factorization (ne_of_gt n.pos)
    simp [scaledDivisorAF, scaledValuationTail, valuationIndicator, Nat.cast_pow, hdiv]

/-- Exact bridge from the divisor formula to independent prime coordinates. -/
theorem qDivisorWavelet_eq_prime_product (r : ℕ) (hr : r ≠ 0) (n : ℕ+) :
    qDivisorWavelet r (n : ℕ) =
      ∏ p ∈ r.primeFactors, valuationWavelet p (r.factorization p) n := by
  rw [← divisorWaveletAF_apply]
  calc
    divisorWaveletAF (n : ℕ) r =
        divisorWaveletAF (n : ℕ) (∏ p ∈ r.primeFactors, p ^ r.factorization p) := by
      rw [← Nat.prod_primeFactors_pow_factorization hr]
    _ = ∏ p ∈ r.primeFactors,
        divisorWaveletAF (n : ℕ) (p ^ r.factorization p) := by
      apply ArithmeticFunction.IsMultiplicative.map_prod
        (fun p => p ^ r.factorization p) (divisorWaveletAF_multiplicative (n : ℕ))
      intro p hp q hq hpq
      exact Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hq) hpq
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      exact divisorWaveletAF_prime_pow p (r.factorization p)
        (Nat.prime_of_mem_primeFactors hp) n

theorem qFactorization_zero_of_notmem (r p : ℕ) (hp : p ∉ r.primeFactors) :
    r.factorization p = 0 := by
  by_contra h
  have hs : p ∈ r.factorization.support := Finsupp.mem_support_iff.mpr h
  exact hp (by simpa only [Nat.support_factorization] using hs)

/-- Zero exponents allow every conductor to be placed in a common prime set. -/
theorem qDivisorWavelet_eq_product_of_support_subset (r : ℕ) (hr : r ≠ 0)
    (S : Finset ℕ) (hS : r.primeFactors ⊆ S) (n : ℕ+) :
    qDivisorWavelet r (n : ℕ) = ∏ p ∈ S, valuationWavelet p (r.factorization p) n := by
  rw [qDivisorWavelet_eq_prime_product r hr n]
  apply Finset.prod_subset hS
  intro p hp hpnot
  rw [qFactorization_zero_of_notmem r p hpnot, valuationWavelet_zero]

/-- Jordan's order-two weight, with zero conductor excluded explicitly. -/
def qJordanTwo (r : ℕ) : ℝ :=
  if r = 0 then 0 else
    ∏ p ∈ r.primeFactors, valuationWaveletWeight p (r.factorization p)

theorem qValuationWaveletWeight_pos (p a : ℕ) (hp : p.Prime) :
    0 < valuationWaveletWeight p a := by
  cases a with
  | zero => norm_num [valuationWaveletWeight]
  | succ a =>
    rw [valuationWaveletWeight_succ]
    have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    apply mul_pos
    · exact sq_pos_of_pos (pow_pos (by linarith) a)
    · nlinarith

theorem qJordanTwo_pos (r : ℕ) (hr : 0 < r) : 0 < qJordanTwo r := by
  rw [qJordanTwo, if_neg (ne_of_gt hr)]
  exact Finset.prod_pos (fun p hp =>
    qValuationWaveletWeight_pos p (r.factorization p) (Nat.prime_of_mem_primeFactors hp))

/-- Every divisor pair has the diagonal Gram law under the actual measure Q. -/
theorem qDivisorWavelet_inner_integral (r s : ℕ) (hr : r ≠ 0) (hs : s ≠ 0) :
    (∫ n : ℕ+, qDivisorWavelet r (n : ℕ) * qDivisorWavelet s (n : ℕ) ∂Q) =
      if r = s then qJordanTwo r else 0 := by
  classical
  let S : Finset ℕ := r.primeFactors ∪ s.primeFactors
  let p : S → ℕ := fun i => i.val
  have hp : ∀ i, (p i).Prime := by
    intro i
    rcases Finset.mem_union.mp i.property with hi | hi
    · exact Nat.prime_of_mem_primeFactors hi
    · exact Nat.prime_of_mem_primeFactors hi
  have hinj : Function.Injective p := by
    intro a b hab
    exact Subtype.ext hab
  have hpoint (t : ℕ) (ht : t ≠ 0) (hsub : t.primeFactors ⊆ S) (n : ℕ+) :
      qDivisorWavelet t (n : ℕ) =
        primePowerTensor p (fun i => t.factorization (p i)) n := by
    rw [qDivisorWavelet_eq_product_of_support_subset t ht S hsub n]
    exact (Finset.prod_coe_sort S
      (fun q => valuationWavelet q (t.factorization q) n)).symm
  simp_rw [hpoint r hr Finset.subset_union_left,
    hpoint s hs Finset.subset_union_right]
  rw [integral_primePowerTensor_mul p hp hinj]
  have heq : (fun i : S => r.factorization (p i)) =
      (fun i : S => s.factorization (p i)) ↔ r = s := by
    constructor
    · intro hab
      apply Nat.eq_of_factorization_eq hr hs
      intro q
      by_cases hq : q ∈ S
      · exact congrFun hab ⟨q, hq⟩
      · have hqr : q ∉ r.primeFactors := fun h => hq (Finset.mem_union_left _ h)
        have hqs : q ∉ s.primeFactors := fun h => hq (Finset.mem_union_right _ h)
        rw [qFactorization_zero_of_notmem r q hqr, qFactorization_zero_of_notmem s q hqs]
    · rintro rfl
      rfl
  by_cases hrs : r = s
  · rw [if_pos (heq.mpr hrs), if_pos hrs]
    subst s
    calc
      (∏ i : S, valuationWaveletWeight (p i) (r.factorization (p i))) =
          ∏ q ∈ S, valuationWaveletWeight q (r.factorization q) :=
        Finset.prod_coe_sort S (fun q => valuationWaveletWeight q (r.factorization q))
      _ = qJordanTwo r := by simp [qJordanTwo, hr, S]
  · have hcoords : (fun i : S => r.factorization (p i)) ≠
        (fun i : S => s.factorization (p i)) := fun h => hrs (heq.mp h)
    rw [if_neg hcoords, if_neg hrs]

end RiemannResearch.RH.ZetaTwoHilbert

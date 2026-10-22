import RiemannResearch.RH.MultiRangeFloorCoordinates
import RiemannResearch.RH.DampedMobiusCoefficients
import Mathlib.Data.Nat.Squarefree

/-! Exact primorial and Euler-product data for the original divisor correction
presentation in Section 2. No analytic energy bound is asserted. -/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

/-- Exactly the primes at most the prescribed head length. -/
def correctionPrimes (Y : ℕ) : Finset ℕ := (Finset.range (Y + 1)).filter Nat.Prime

def correctionPrimorial (Y : ℕ) : ℕ := ∏ p ∈ correctionPrimes Y, p

def correctionAlpha (Y : ℕ) : ℝ := ∏ p ∈ correctionPrimes Y, (1 - 1 / (p : ℝ))

def correctionSieve (Y n : ℕ) : ℝ :=
  ∑ d ∈ (correctionPrimorial Y).divisors, (ArithmeticFunction.moebius d : ℝ) * (n / d : ℕ)

theorem correctionPrimorial_pos (Y : ℕ) : 0 < correctionPrimorial Y := by
  unfold correctionPrimorial
  exact Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.pos)

theorem correctionPrimorial_primeFactors (Y : ℕ) :
    (correctionPrimorial Y).primeFactors = correctionPrimes Y := by
  exact Nat.primeFactors_prod (fun p hp => (Finset.mem_filter.mp hp).2)

/-- Every squarefree integer in the head divides the actual primorial. -/
theorem squarefree_head_dvd_correctionPrimorial (Y n : ℕ)
    (hn : Squarefree n) (hnY : n ≤ Y) : n ∣ correctionPrimorial Y := by
  rw [← Nat.prod_primeFactors_of_squarefree hn]
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpn : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn.ne_zero) (Nat.dvd_of_mem_primeFactors hp)
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpp⟩

/-- The signed low sieve coefficient is exactly μ(n), including nonsquarefree n. -/
theorem correctionPrimorial_low_moebius (Y n : ℕ) (_hn : 0 < n) (hnY : n ≤ Y) :
    (if n ∈ (correctionPrimorial Y).divisors then (ArithmeticFunction.moebius n : ℝ) else 0) =
      (ArithmeticFunction.moebius n : ℝ) := by
  classical
  by_cases hs : Squarefree n
  · rw [if_pos (Nat.mem_divisors.mpr
      ⟨squarefree_head_dvd_correctionPrimorial Y n hs hnY, ne_of_gt (correctionPrimorial_pos Y)⟩)]
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
    simp

/-- Exact reciprocal balance constant, with its original product and signs. -/
theorem correctionAlpha_eq_divisor_sum (Y : ℕ) :
    correctionAlpha Y = ∑ d ∈ (correctionPrimorial Y).divisors,
      (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) := by
  have h := dampedDivisorCoefficient_eq_prime_product (1 : ℝ)
    (ne_of_gt (correctionPrimorial_pos Y))
  rw [correctionPrimorial_primeFactors] at h
  simpa only [dampedDivisorCoefficient, dampedMobiusWeight, Real.rpow_neg_one,
    div_eq_mul_inv, one_mul, correctionAlpha] using h.symm

/-- The actual primorial sieve is exactly one throughout the initial head. -/
theorem correctionSieve_exact (Y n : ℕ) (hn : 0 < n) (hnY : n ≤ Y) :
    correctionSieve Y n = 1 := by
  classical
  let t := (correctionPrimorial Y).divisors.filter (fun d => d ≤ Y)
  have hsub : t ⊆ Finset.Icc 1 Y := by
    intro d hd
    obtain ⟨hdQ, hdY⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdQ, hdY⟩
  have hlow : (∑ d ∈ t, (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ)) =
      ∑ d ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ) := by
    apply Finset.sum_subset hsub
    intro d hd hdt
    have hd0 := (Finset.mem_Icc.mp hd).1
    have hdY := (Finset.mem_Icc.mp hd).2
    have hdQ : d ∉ (correctionPrimorial Y).divisors := by
      intro hh
      exact hdt (Finset.mem_filter.mpr ⟨hh, hdY⟩)
    have hm := correctionPrimorial_low_moebius Y d hd0 hdY
    rw [if_neg hdQ] at hm
    rw [← hm, zero_mul]
  have hhigh : (∑ d ∈ t, (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ)) =
      correctionSieve Y n := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hdt
    have hdY : Y < d := by
      by_contra h
      exact hdt (Finset.mem_filter.mpr ⟨hd, by omega⟩)
    rw [Nat.div_eq_of_lt (by omega : n < d)]
    simp
  rw [← hhigh, hlow]
  exact finite_mobius_floor_sum Y n hn hnY

end RiemannResearch.RH.Pareto

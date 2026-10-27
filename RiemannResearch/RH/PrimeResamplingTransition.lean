/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PrimeResamplingKernel

/-!
# Actual normalized one-prime transition, including self-loops

Each positive row resamples one valuation with total mass one. The
countable Dirichlet form uses the corresponding off-diagonal conductance.
-/

noncomputable section
open scoped BigOperators ENNReal
namespace RiemannResearch.RH.PrimeResampling
open ZetaTwoHilbert

/-- The complete stochastic transition for one actual prime resampling. -/
def primeTransition (p n m : ℕ) : ℝ :=
  if p.Prime ∧ n ≠ 0 ∧ m ≠ 0 ∧ primeCore p n = primeCore p m then
    geometricMass p (m.factorization p)
  else 0

theorem primeTransition_nonneg (p n m : ℕ) : 0 ≤ primeTransition p n m := by
  unfold primeTransition
  split_ifs with h
  · exact geometricMass_nonneg p _ h.1
  · exact le_rfl

@[simp] theorem primeTransition_zero_left (p m : ℕ) : primeTransition p 0 m = 0 := by
  simp [primeTransition]

@[simp] theorem primeTransition_zero_right (p n : ℕ) : primeTransition p n 0 = 0 := by
  simp [primeTransition]

theorem primeTransition_replaceValuation (p n k : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    primeTransition p n (replaceValuation p n k) = geometricMass p k := by
  simp [primeTransition, hp, hn, replaceValuation_ne_zero p n k hp hn,
    primeCore_replaceValuation p n k hp hn, factorization_replaceValuation p n k hp hn]

/-- Every signed observable is averaged against the genuine geometric law. -/
theorem primeTransition_weighted_row (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0)
    (h : ℕ → ℝ) :
    (∑' m : ℕ, primeTransition p n m * h m) =
      ∑' k : ℕ, geometricMass p k * h (replaceValuation p n k) := by
  have hs (m : ℕ) : primeTransition p n m * h m =
      if primeCore p m = primeCore p n then primeTransition p n m * h m else 0 := by
    by_cases hc : primeCore p m = primeCore p n
    · rw [if_pos hc]
    · have hc' := Ne.symm hc
      simp [primeTransition, hc, hc']
  calc
    _ = ∑' m : ℕ, if primeCore p m = primeCore p n then
        primeTransition p n m * h m else 0 := tsum_congr hs
    _ = ∑' k : ℕ, primeTransition p n (replaceValuation p n k) *
        h (replaceValuation p n k) := tsum_primeFiber p n hp hn _
    _ = _ := by simp_rw [primeTransition_replaceValuation p n _ hp hn]

/-- A positive integer's complete one-prime replacement row has mass one. -/
theorem primeTransition_row_tsum (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    (∑' m : ℕ, primeTransition p n m) = 1 := by
  have h := primeTransition_weighted_row p n hp hn (fun _ => 1)
  simpa only [mul_one, geometricMass_tsum p hp] using h

theorem primeTransition_row_summable (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    Summable (primeTransition p n) := by
  by_contra hs
  have hzero := tsum_eq_zero_of_not_summable hs
  rw [primeTransition_row_tsum p n hp hn] at hzero
  exact one_ne_zero hzero

theorem primeTransition_row_tsum_ennreal (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    (∑' m : ℕ, ENNReal.ofReal (primeTransition p n m)) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => primeTransition_nonneg p n m)
    (primeTransition_row_summable p n hp hn), primeTransition_row_tsum p n hp hn,
    ENNReal.ofReal_one]

/-- Exact detailed balance, including the stationary self-loop. -/
theorem primeTransition_detailed_balance (p n m : ℕ) :
    positiveQWeight n * primeTransition p n m =
      positiveQWeight m * primeTransition p m n := by
  unfold primeTransition
  by_cases h : p.Prime ∧ n ≠ 0 ∧ m ≠ 0 ∧ primeCore p n = primeCore p m
  · have h' : p.Prime ∧ m ≠ 0 ∧ n ≠ 0 ∧ primeCore p m = primeCore p n :=
      ⟨h.1, h.2.2.1, h.2.1, h.2.2.2.symm⟩
    rw [if_pos h, if_pos h']
    exact geometric_detailed_balance p n m h.2.2.2
  · have h' : ¬(p.Prime ∧ m ≠ 0 ∧ n ≠ 0 ∧ primeCore p m = primeCore p n) := by
      rintro ⟨hp, hm, hn, hc⟩
      exact h ⟨hp, hn, hm, hc.symm⟩
    rw [if_neg h, if_neg h', mul_zero, mul_zero]

/-- The actual inverse-square Q law is stationary for each normalized
prime-resampling transition, with the entire countable column retained. -/
theorem primeTransition_stationary (p : ℕ) (hp : p.Prime) (m : ℕ) :
    (∑' n : ℕ, positiveQWeight n * primeTransition p n m) = positiveQWeight m := by
  by_cases hm : m = 0
  · subst m
    simp [positiveQWeight]
  calc
    _ = ∑' n : ℕ, positiveQWeight m * primeTransition p m n :=
      tsum_congr (fun n => primeTransition_detailed_balance p n m)
    _ = positiveQWeight m * (∑' n : ℕ, primeTransition p m n) := tsum_mul_left
    _ = _ := by rw [primeTransition_row_tsum p m hp hm, mul_one]

/-- The energy conductance is exactly Q times this transition, with its
stationary self-loop deleted before the sum over primes. -/
theorem primeConductance_eq_transition (p n m : ℕ) :
    primeConductance p n m = if n = m then 0 else positiveQWeight n * primeTransition p n m := by
  by_cases hnm : n = m
  · subst m
    simp
  rw [if_neg hnm]
  unfold primeConductance primeTransition
  by_cases h : p.Prime ∧ n ≠ 0 ∧ m ≠ 0 ∧ primeCore p n = primeCore p m
  · have h' : p.Prime ∧ n ≠ 0 ∧ m ≠ 0 ∧ n ≠ m ∧ primeCore p n = primeCore p m :=
      ⟨h.1, h.2.1, h.2.2.1, hnm, h.2.2.2⟩
    rw [if_pos h, if_pos h']
  · have h' : ¬(p.Prime ∧ n ≠ 0 ∧ m ≠ 0 ∧ n ≠ m ∧ primeCore p n = primeCore p m) := by
      rintro ⟨hp, hn, hm, _, hc⟩
      exact h ⟨hp, hn, hm, hc⟩
    rw [if_neg h, if_neg h', mul_zero]

end RiemannResearch.RH.PrimeResampling

/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PrimeResamplingGeometric
import RiemannResearch.RH.PrimeResamplingExitBound
import RiemannResearch.Analysis.ReversibleJumpEnergy
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.Linarith

/-!
# The actual countable prime-resampling conductance on Q

The diagonal is removed before summing primes. At each prime, the p-free
part is kept fixed and the new exponent has its actual geometric Q law.
-/

noncomputable section
open scoped BigOperators ENNReal
namespace RiemannResearch.RH.PrimeResampling
open ZetaTwoHilbert

/-- Real symmetric conductance for resampling one actual prime valuation.
Zero has zero flow, and stationary self-loops are explicitly deleted. -/
def primeConductance (p n m : ℕ) : ℝ :=
  if p.Prime ∧ n ≠ 0 ∧ m ≠ 0 ∧ n ≠ m ∧ primeCore p n = primeCore p m then
    positiveQWeight n * geometricMass p (m.factorization p)
  else 0

theorem primeConductance_nonneg (p n m : ℕ) : 0 ≤ primeConductance p n m := by
  unfold primeConductance
  split_ifs with h
  · exact mul_nonneg (positiveQWeight_nonneg n)
      (geometricMass_nonneg p _ h.1)
  · exact le_rfl

@[simp] theorem primeConductance_self (p n : ℕ) : primeConductance p n n = 0 := by
  simp [primeConductance]

@[simp] theorem primeConductance_zero_left (p m : ℕ) : primeConductance p 0 m = 0 := by
  simp [primeConductance]

@[simp] theorem primeConductance_zero_right (p n : ℕ) : primeConductance p n 0 = 0 := by
  simp [primeConductance]

@[simp] theorem primeConductance_nonprime (p n m : ℕ) (hp : ¬p.Prime) :
    primeConductance p n m = 0 := by simp [primeConductance, hp]

theorem primeConductance_symm (p n m : ℕ) :
    primeConductance p n m = primeConductance p m n := by
  unfold primeConductance
  by_cases h : p.Prime ∧ n ≠ 0 ∧ m ≠ 0 ∧ n ≠ m ∧ primeCore p n = primeCore p m
  · have h' : p.Prime ∧ m ≠ 0 ∧ n ≠ 0 ∧ m ≠ n ∧ primeCore p m = primeCore p n :=
      ⟨h.1, h.2.2.1, h.2.1, Ne.symm h.2.2.2.1, h.2.2.2.2.symm⟩
    rw [if_pos h, if_pos h']
    exact geometric_detailed_balance p n m h.2.2.2.2
  · have h' : ¬(p.Prime ∧ m ≠ 0 ∧ n ≠ 0 ∧ m ≠ n ∧ primeCore p m = primeCore p n) := by
      rintro ⟨hp, hm, hn, hmn, hc⟩
      exact h ⟨hp, hn, hm, Ne.symm hmn, hc.symm⟩
    rw [if_neg h, if_neg h']

/-- On a replacement fiber, the only removed exponent is the current exponent. -/
theorem primeConductance_replaceValuation
    (p n k : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    primeConductance p n (replaceValuation p n k) =
      if k = n.factorization p then 0 else positiveQWeight n * geometricMass p k := by
  have hm := replaceValuation_ne_zero p n k hp hn
  have hc := primeCore_replaceValuation p n k hp hn
  by_cases hk : k = n.factorization p
  · subst k
    simp
  · have hneq : n ≠ replaceValuation p n k := by
      intro he
      exact hk ((replaceValuation_eq_self_iff p n k hp hn).mp he.symm)
    simp [primeConductance, hp, hn, hm, hneq, hc, hk,
      factorization_replaceValuation p n k hp hn]

/-- The full row is precisely the geometric replacement law with its current
exponent deleted. This identity is a complete countable sum. -/
theorem primeConductance_row (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    (∑' m : ℕ, ENNReal.ofReal (primeConductance p n m)) =
      ENNReal.ofReal (positiveQWeight n) *
        ∑' k : ℕ, ENNReal.ofReal (geometricOffDiagonal p (n.factorization p) k) := by
  have he (m : ℕ) : ENNReal.ofReal (primeConductance p n m) =
      if primeCore p m = primeCore p n then
        ENNReal.ofReal (positiveQWeight n) *
          ENNReal.ofReal (geometricOffDiagonal p (n.factorization p) (m.factorization p))
      else 0 := by
    by_cases hc : primeCore p m = primeCore p n
    · have hm := ne_zero_of_primeCore_eq p n m hn hc
      by_cases hnm : n = m
      · subst m
        simp [geometricOffDiagonal]
      · have hv : m.factorization p ≠ n.factorization p := by
          intro hval
          have hmrep := replaceValuation_of_primeCore_eq p n m hc.symm
          rw [hval, replaceValuation_self] at hmrep
          exact hnm hmrep
        have hcon : p.Prime ∧ n ≠ 0 ∧ m ≠ 0 ∧ n ≠ m ∧ primeCore p n = primeCore p m :=
          ⟨hp, hn, hm, hnm, hc.symm⟩
        rw [primeConductance, if_pos hcon, if_pos hc, geometricOffDiagonal, if_neg hv]
        exact ENNReal.ofReal_mul (positiveQWeight_nonneg n)
    · have hc' : primeCore p n ≠ primeCore p m := Ne.symm hc
      simp [primeConductance, hc, hc']
  calc
    _ = ∑' m : ℕ, if primeCore p m = primeCore p n then
        ENNReal.ofReal (positiveQWeight n) *
          ENNReal.ofReal (geometricOffDiagonal p (n.factorization p) (m.factorization p))
        else 0 := tsum_congr he
    _ = ∑' k : ℕ, ENNReal.ofReal (positiveQWeight n) *
        ENNReal.ofReal (geometricOffDiagonal p (n.factorization p)
          ((replaceValuation p n k).factorization p)) :=
      tsum_primeFiber_ennreal p n hp hn _
    _ = _ := by
      simp_rw [factorization_replaceValuation p n _ hp hn]
      rw [ENNReal.tsum_mul_left]

/-- A nonnegative observable vanishing on the current state can be summed
against the genuine one-prime flow by independent geometric replacement. -/
theorem primeConductance_weighted_row
    (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0)
    (h : ℕ → ℝ≥0∞) (hdiag : h n = 0) :
    (∑' m : ℕ, ENNReal.ofReal (primeConductance p n m) * h m) =
      ENNReal.ofReal (positiveQWeight n) *
        ∑' k : ℕ, ENNReal.ofReal (geometricMass p k) * h (replaceValuation p n k) := by
  have hs (m : ℕ) : ENNReal.ofReal (primeConductance p n m) * h m =
      if primeCore p m = primeCore p n then
        ENNReal.ofReal (primeConductance p n m) * h m else 0 := by
    by_cases hc : primeCore p m = primeCore p n
    · rw [if_pos hc]
    · have hc' := Ne.symm hc
      simp [primeConductance, hc, hc']
  calc
    _ = ∑' m : ℕ, if primeCore p m = primeCore p n then
        ENNReal.ofReal (primeConductance p n m) * h m else 0 := tsum_congr hs
    _ = ∑' k : ℕ, ENNReal.ofReal (primeConductance p n (replaceValuation p n k)) *
        h (replaceValuation p n k) := tsum_primeFiber_ennreal p n hp hn _
    _ = ∑' k : ℕ, ENNReal.ofReal (positiveQWeight n) *
        (ENNReal.ofReal (geometricMass p k) * h (replaceValuation p n k)) := by
      apply tsum_congr
      intro k
      rw [primeConductance_replaceValuation p n k hp hn]
      by_cases hk : k = n.factorization p
      · subst k
        simp [hdiag]
      · rw [if_neg hk, ENNReal.ofReal_mul (positiveQWeight_nonneg n), mul_assoc]
    _ = _ := ENNReal.tsum_mul_left

/-- Signed scalar version of the exact complete geometric replacement row. -/
theorem primeConductance_weighted_row_real
    (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0)
    (h : ℕ → ℝ) (hdiag : h n = 0) :
    (∑' m : ℕ, primeConductance p n m * h m) =
      positiveQWeight n *
        ∑' k : ℕ, geometricMass p k * h (replaceValuation p n k) := by
  have hs (m : ℕ) : primeConductance p n m * h m =
      if primeCore p m = primeCore p n then primeConductance p n m * h m else 0 := by
    by_cases hc : primeCore p m = primeCore p n
    · rw [if_pos hc]
    · have hc' := Ne.symm hc
      simp [primeConductance, hc, hc']
  calc
    _ = ∑' m : ℕ, if primeCore p m = primeCore p n then
        primeConductance p n m * h m else 0 := tsum_congr hs
    _ = ∑' k : ℕ, primeConductance p n (replaceValuation p n k) *
        h (replaceValuation p n k) := tsum_primeFiber p n hp hn _
    _ = ∑' k : ℕ, positiveQWeight n *
        (geometricMass p k * h (replaceValuation p n k)) := by
      apply tsum_congr
      intro k
      rw [primeConductance_replaceValuation p n k hp hn]
      by_cases hk : k = n.factorization p
      · subst k
        simp [hdiag]
      · rw [if_neg hk, mul_assoc]
    _ = _ := tsum_mul_left

/-- A single prime has exit probability at most one. -/
theorem primeConductance_row_le_Q (p n : ℕ) :
    (∑' m : ℕ, ENNReal.ofReal (primeConductance p n m)) ≤
      ENNReal.ofReal (positiveQWeight n) := by
  by_cases hn : n = 0
  · subst n
    simp [positiveQWeight]
  by_cases hp : p.Prime
  · rw [primeConductance_row p n hp hn]
    have h := ENNReal.ofReal_le_ofReal
      (geometricOffDiagonal_tsum_le_one p (n.factorization p) hp)
    rw [ENNReal.ofReal_tsum_of_nonneg
      (fun k => geometricOffDiagonal_nonneg p (n.factorization p) k hp)
      (geometricOffDiagonal_summable p (n.factorization p) hp), ENNReal.ofReal_one] at h
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h zero_le
  · simp [primeConductance_nonprime p n _ hp]

theorem primeConductance_row_summable (p n : ℕ) :
    Summable (primeConductance p n) := by
  let f : ℕ → NNReal := fun m => ⟨primeConductance p n m, primeConductance_nonneg p n m⟩
  have ht : (∑' m : ℕ, (f m : ℝ≥0∞)) ≠ ⊤ := by
    have he : (fun m : ℕ => (f m : ℝ≥0∞)) =
        (fun m : ℕ => ENNReal.ofReal (primeConductance p n m)) := by
      funext m
      exact ENNReal.coe_nnreal_eq (f m)
    rw [he]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (primeConductance_row_le_Q p n)
  exact ENNReal.tsum_coe_ne_top_iff_summable_coe.mp ht

theorem primeConductance_row_real_le_Q (p n : ℕ) :
    (∑' m : ℕ, primeConductance p n m) ≤ positiveQWeight n := by
  have h := primeConductance_row_le_Q p n
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => primeConductance_nonneg p n m)
    (primeConductance_row_summable p n)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (positiveQWeight_nonneg n)).mp h

theorem primeConductance_row_le (p n : ℕ) (hn : n ≠ 0) :
    (∑' m : ℕ, ENNReal.ofReal (primeConductance p n m)) ≤
      ENNReal.ofReal (positiveQWeight n) *
        (if p.Prime then
          ENNReal.ofReal ((if p ∣ n then (1 : ℝ) else 0) + 1 / (p : ℝ) ^ 2)
        else 0) := by
  by_cases hp : p.Prime
  · rw [if_pos hp, primeConductance_row p n hp hn]
    have hi : (if n.factorization p = 0 then (0 : ℝ) else 1) =
        (if p ∣ n then (1 : ℝ) else 0) := by
      by_cases hd : p ∣ n
      · have hv : n.factorization p ≠ 0 := by
          have h := (hp.dvd_iff_one_le_factorization hn).mp hd
          omega
        simp [hv, hd]
      · have hv := Nat.factorization_eq_zero_of_not_dvd hd
        simp [hv, hd]
    have h := geometricOffDiagonal_tsum_ennreal_le p (n.factorization p) hp
    rw [hi] at h
    exact mul_le_mul_of_nonneg_left h zero_le
  · simp [primeConductance_nonprime p n _ hp, hp]

/-- Sum over all actual primes; ENNReal preserves possibly infinite energies. -/
def primeFlow (n m : ℕ) : ℝ≥0∞ :=
  ∑' p : ℕ, ENNReal.ofReal (primeConductance p n m)

theorem primeFlow_symm (n m : ℕ) : primeFlow n m = primeFlow m n := by
  unfold primeFlow
  apply tsum_congr
  intro p
  rw [primeConductance_symm]

@[simp] theorem primeFlow_self (n : ℕ) : primeFlow n n = 0 := by
  simp [primeFlow]

@[simp] theorem primeFlow_zero_left (m : ℕ) : primeFlow 0 m = 0 := by
  simp [primeFlow]

@[simp] theorem primeFlow_zero_right (n : ℕ) : primeFlow n 0 = 0 := by
  simp [primeFlow]

/-- The total actual prime exit flow is at most Q(n)(n+1). -/
theorem primeFlow_row_bound (n : ℕ) :
    (∑' m : ℕ, primeFlow n m) ≤
      ENNReal.ofReal (positiveQWeight n * ((n : ℝ) + 1)) := by
  by_cases hn : n = 0
  · subst n
    simp [positiveQWeight]
  unfold primeFlow
  rw [ENNReal.tsum_comm]
  calc
    _ ≤ ∑' p : ℕ, ENNReal.ofReal (positiveQWeight n) *
        (if p.Prime then
          ENNReal.ofReal ((if p ∣ n then (1 : ℝ) else 0) + 1 / (p : ℝ) ^ 2)
        else 0) := ENNReal.tsum_le_tsum (fun p => primeConductance_row_le p n hn)
    _ = ENNReal.ofReal (positiveQWeight n) *
        ∑' p : ℕ, (if p.Prime then
          ENNReal.ofReal ((if p ∣ n then (1 : ℝ) else 0) + 1 / (p : ℝ) ^ 2)
        else 0) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (positiveQWeight n) * ENNReal.ofReal ((n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (prime_exit_majorant_tsum_le n hn) zero_le
    _ = _ := (ENNReal.ofReal_mul (positiveQWeight_nonneg n)).symm

/-- Every individual coefficient of the actual countable flow is finite. -/
theorem primeFlow_coeff_ne_top (n m : ℕ) : primeFlow n m ≠ ⊤ := by
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    ((ENNReal.le_tsum m).trans (primeFlow_row_bound n))

end RiemannResearch.RH.PrimeResampling

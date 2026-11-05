/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MertensOddSquareSieve

/-! # The root and the first-prime-2 Möbius subtree

The exact odd-part recursion transfers bounds in both directions at every dyadic
power `q > 1`. Taking every `q > √2` gives the classical square-root-plus-epsilon
Mertens criterion. Its analytic equivalence to RH is Titchmarsh, Theorem 14.25(c).
-/

noncomputable section
namespace RiemannResearch.NumberTheory.PrimeNumberTheorem.RoughMertensSubtree

/-- The sum of μ over odd positive integers at most `n`. -/
def oddAt (n : ℕ) : ℝ := oddMertensPrefix ((n + 1) / 2)

/-- The signed charge in the prime-2 cylinder below cutoff `n`.
Even squarefree integers are uniquely `2k` with `k` odd squarefree,
and `μ(2k) = - μ(k)`. The cutoff for `k` is `n / 2`. -/
def twoBranch (n : ℕ) : ℝ := - oddAt (n / 2)

/-- Deleting the prime-2 cylinder from the root recovers exactly the odd part. -/
theorem root_decomposition (n : ℕ) : M (n : ℝ) = oddAt n + twoBranch n := by
  rw [M_nat_eq_oddMertensPrefix_sub]
  have h : (n + 2) / 4 = (n / 2 + 1) / 2 := by omega
  simp only [oddAt, twoBranch, h, sub_eq_add_neg]

theorem oddAt_rec (n : ℕ) : oddAt n = M (n : ℝ) + oddAt (n / 2) := by
  rw [root_decomposition]
  unfold twoBranch
  ring

/-- A power bound on the cutoffs `n < 2^j`, with growth factor `q` per scale. -/
def DyadicBound (q : ℝ) (f : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ j n : ℕ, n < 2 ^ j → |f n| ≤ C * q ^ j

/-- Iterating exact odd-part deletion transfers a root bound to a fixed rough subtree. -/
theorem root_to_odd {q : ℝ} (hq : 1 < q)
    (h : DyadicBound q (fun n => M (n : ℝ))) : DyadicBound q oddAt := by
  obtain ⟨C, hC, hM⟩ := h
  let K := C * q / (q - 1)
  have hden : 0 < q - 1 := sub_pos.mpr hq
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hK : 0 ≤ K := div_nonneg (mul_nonneg hC hq0.le) hden.le
  have hbalance : C * q + K = K * q := by
    dsimp [K]
    field_simp [ne_of_gt hden]
    ring
  refine ⟨K, hK, ?_⟩
  intro j
  induction j with
  | zero =>
    intro n hn
    have hn0 : n = 0 := by
      simp only [pow_zero] at hn
      omega
    subst n
    simpa [oddAt, oddMertensPrefix] using hK
  | succ j ih =>
    intro n hn
    have hn' : n / 2 < 2 ^ j := by
      rw [pow_succ] at hn
      omega
    calc |oddAt n| = |M (n : ℝ) + oddAt (n / 2)| := by rw [← oddAt_rec]
         _ ≤ |M (n : ℝ)| + |oddAt (n / 2)| := abs_add_le _ _
         _ ≤ C * q ^ (j + 1) + K * q ^ j := add_le_add (hM _ _ hn) (ih _ hn')
         _ = (C * q + K) * q ^ j := by rw [pow_succ]; ring
         _ = K * q ^ (j + 1) := by rw [hbalance, pow_succ]; ring

/-- The entire root bound is equivalent to the identical bound on the single
prime-2 subtree. The implicit constants may depend on the dyadic rate. -/
theorem root_iff_twoBranch {q : ℝ} (hq : 1 < q) :
    DyadicBound q (fun n => M (n : ℝ)) ↔ DyadicBound q twoBranch := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  constructor
  · intro h
    obtain ⟨K, hK, hodd⟩ := root_to_odd hq h
    refine ⟨K, hK, ?_⟩
    intro j n hn
    have hn' := (Nat.div_le_self n 2).trans_lt hn
    simpa [twoBranch] using hodd j (n / 2) hn'
  · rintro ⟨K, hK, hs⟩
    refine ⟨K * q + K, add_nonneg (mul_nonneg hK hq0.le) hK, ?_⟩
    intro j n hn
    have h2n : 2 * n < 2 ^ (j + 1) := by rw [pow_succ]; omega
    have he : (2 * n) / 2 = n := by omega
    have hodd : |oddAt n| ≤ K * q ^ (j + 1) := by
      simpa [twoBranch, he] using hs (j + 1) (2 * n) h2n
    calc |M (n : ℝ)| = |oddAt n + twoBranch n| := by rw [root_decomposition]
         _ ≤ |oddAt n| + |twoBranch n| := abs_add_le _ _
         _ ≤ K * q ^ (j + 1) + K * q ^ j := add_le_add hodd (hs j n hn)
         _ = (K * q + K) * q ^ j := by rw [pow_succ]; ring

/-- Only the published Littlewood criterion is a premise here. The transfer
from the root to this fixed subtree is proved in both directions above. -/
theorem riemannHypothesis_iff_twoBranch_of_littlewood
    (hLittlewood : RiemannHypothesis ↔ ∀ q : ℝ, Real.sqrt 2 < q →
      DyadicBound q (fun n => M (n : ℝ))) :
    RiemannHypothesis ↔ ∀ q : ℝ, Real.sqrt 2 < q → DyadicBound q twoBranch := by
  rw [hLittlewood]
  have hone : (1 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  exact forall_congr' fun q => forall_congr' fun hq => root_iff_twoBranch (hone.trans hq)

end RiemannResearch.NumberTheory.PrimeNumberTheorem.RoughMertensSubtree

/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoPrimeRefinementCancellation

/-!
# Exact cross-stage structure of prime cancellation

Source: continuation of the user-provided Pareto capacity handoff
(2026-09-21). This module formalizes the cross-stage orthogonality and
finite telescoping argument developed from the preceding refinement module.

The Schur innovations and factorial refinements are each pairwise orthogonal.
Their cross-Gram matrix is lower triangular after shifting the innovation
index by one. Its prime diagonal is the positive fresh-prime source.
The actual signed Schur numerator is exactly a fixed base pairing plus a
finite row sum, retaining every signed off-diagonal term.

These structural identities are unconditional. A lower bound preventing
cancellation in the row sums remains open; no RH proof is asserted.
-/

noncomputable section
open scoped BigOperators


namespace RiemannResearch.RH.Pareto.IntegerDPP

open RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity

theorem tailInnovation_inner_of_lt (i j : ℕ) (hij : i < j) :
    inner ℝ (tailInnovation i) (tailInnovation j) = 0 := by
  calc
    inner ℝ (tailInnovation i) (tailInnovation j) =
        inner ℝ (tailAtom i) (tailInnovation j) :=
      tailInnovation_inner_of_old_observation_zero i (tailInnovation j) (by
        intro k
        exact tailInnovation_old_observation j ⟨k.val, by omega⟩)
    _ = 0 := tailInnovation_old_observation j ⟨i, hij⟩

theorem tailInnovation_pairwise_orthogonal :
    Pairwise (fun i j : ℕ =>
      inner ℝ (tailInnovation i) (tailInnovation j) = 0) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact tailInnovation_inner_of_lt i j h
  · rw [real_inner_comm]
    exact tailInnovation_inner_of_lt j i h

end RiemannResearch.RH.Pareto.IntegerDPP

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity

open RiemannResearch.RH.Pareto.IntegerDPP
open RiemannResearch.Analysis.FiniteGramCapacity
open RiemannResearch.Analysis.FiniteHilbertGram


theorem infiniteCoprimeCertificate_inner_factorialPrimeRefinement
    {n m : ℕ} (hnm : n ≤ m) :
    inner ℝ (infiniteCoprimeCertificate (n + 2).factorial)
      (factorialPrimeRefinement m) = 0 := by
  have htop := infiniteCoprimeCertificate_inner_of_dvd
    (P := (n + 2).factorial) (Q := (m + 3).factorial)
    (Nat.factorial_ne_zero _)
    (Nat.dvd_factorial (by decide) (by omega))
    (Nat.factorial_ne_zero _)
    (Nat.factorial_dvd_factorial (by omega))
  have hbase := infiniteCoprimeCertificate_inner_of_dvd
    (P := (n + 2).factorial) (Q := (m + 2).factorial)
    (Nat.factorial_ne_zero _)
    (Nat.dvd_factorial (by decide) (by omega))
    (Nat.factorial_ne_zero _)
    (Nat.factorial_dvd_factorial (by omega))
  rw [factorialPrimeRefinement, inner_sub_right, htop, hbase, sub_self]

theorem factorialPrimeRefinement_inner_of_lt
    {n m : ℕ} (hnm : n < m) :
    inner ℝ (factorialPrimeRefinement n) (factorialPrimeRefinement m) = 0 := by
  change inner ℝ
    (infiniteCoprimeCertificate (n + 3).factorial -
      infiniteCoprimeCertificate (n + 2).factorial)
    (factorialPrimeRefinement m) = 0
  have hnext :
      inner ℝ (infiniteCoprimeCertificate (n + 3).factorial)
        (factorialPrimeRefinement m) = 0 := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      (infiniteCoprimeCertificate_inner_factorialPrimeRefinement
        (n := n + 1) (m := m) (by omega))
  rw [inner_sub_left, hnext,
    infiniteCoprimeCertificate_inner_factorialPrimeRefinement (by omega : n ≤ m),
    sub_self]

theorem factorialPrimeRefinement_pairwise_orthogonal :
    Pairwise (fun n m : ℕ =>
      inner ℝ (factorialPrimeRefinement n) (factorialPrimeRefinement m) = 0) := by
  intro n m hnm
  rcases lt_or_gt_of_ne hnm with h | h
  · exact factorialPrimeRefinement_inner_of_lt h
  · rw [real_inner_comm]
    exact factorialPrimeRefinement_inner_of_lt h

/-- Cross-stage pairings of Schur innovations with factorial refinements. -/
def factorialPrimeCrossGram (n m : ℕ) : ℝ :=
  inner ℝ (tailInnovation (n + 1)) (factorialPrimeRefinement m)

theorem factorialPrimeCrossGram_eq_zero_of_lt
    {n m : ℕ} (hnm : n < m) : factorialPrimeCrossGram n m = 0 := by
  unfold factorialPrimeCrossGram
  rw [tailInnovation_inner_of_old_observation_zero (n + 1)
    (factorialPrimeRefinement m)
    (fun i => factorialPrimeRefinement_old_observation_zero m ⟨i.val, by omega⟩)]
  exact factorialPrimeRefinement_old_observation_zero m ⟨n + 1, by omega⟩

theorem factorialPrimeCrossGram_diag (n : ℕ) (hp : Nat.Prime (n + 3)) :
    factorialPrimeCrossGram n n = factorialPrimeDelta n :=
  tailInnovation_inner_factorialPrimeRefinement n hp

theorem factorialCoprimeCertificate_eq_base_add_refinements (n : ℕ) :
    infiniteCoprimeCertificate (n + 2).factorial =
      infiniteCoprimeCertificate (Nat.factorial 2) +
        ∑ j ∈ Finset.range n, factorialPrimeRefinement j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hstep :
          infiniteCoprimeCertificate (n + 1 + 2).factorial =
            infiniteCoprimeCertificate (n + 2).factorial +
              factorialPrimeRefinement n := by
        simp only [factorialPrimeRefinement, Nat.add_assoc, Nat.reduceAdd]
        abel
      rw [hstep, ih]
      exact add_assoc _ _ _

theorem factorialPrimeError_eq_base_add_crossGram (n : ℕ) :
    factorialPrimeError n =
      inner ℝ (tailInnovation (n + 1)) (infiniteCoprimeCertificate (Nat.factorial 2)) +
        ∑ j ∈ Finset.range n, factorialPrimeCrossGram n j := by
  rw [factorialPrimeError, inner_sub_right, tailInnovation_inner_minimum, sub_zero,
    factorialCoprimeCertificate_eq_base_add_refinements]
  simp only [inner_add_right, inner_sum, factorialPrimeCrossGram]

/-- Exact finite signed expansion at every stage, including composite moduli. -/
theorem schurEta_eq_base_add_crossGram (n : ℕ) :
    schurEta (n+1) =
      inner ℝ (tailInnovation (n+1)) (infiniteCoprimeCertificate (Nat.factorial 2)) +
        ∑ j ∈ Finset.range (n+1), factorialPrimeCrossGram n j := by
  let z := infiniteCoprimeCertificate (n+3).factorial
  have hz (i : Fin (n+2)) :
      inner ℝ (tailAtom i.val) z = reciprocalSource (n+2) i :=
    infiniteCoprimeCertificate_observation (n+2) (n+3).factorial
      (Nat.factorial_ne_zero _)
      (Nat.dvd_factorial (by decide) (by omega))
      (fun i => Nat.dvd_factorial (by omega) (by omega)) i
  have hold (i : Fin (n+1)) :
      inner ℝ (tailAtom i.val) (z - tailMinimum (n+1)) = 0 := by
    have hi := hz i.castSucc
    simp only [Fin.val_castSucc, reciprocalSource] at hi
    rw [inner_sub_right, hi, tailMinimum_observation]
    simp [reciprocalSource]
  have he := tailInnovation_inner_of_old_observation_zero (n+1)
    (z - tailMinimum (n+1)) hold
  have hlast := hz (Fin.last (n+1))
  simp only [Fin.val_last, reciprocalSource] at hlast
  rw [inner_sub_right, tailInnovation_inner_minimum, sub_zero,
    inner_sub_right, hlast] at he
  change inner ℝ (tailInnovation (n+1)) z = schurEta (n+1) at he
  rw [← he]
  dsimp [z]
  rw [show n+3 = (n+1)+2 by omega,
    factorialCoprimeCertificate_eq_base_add_refinements]
  simp only [inner_add_right, inner_sum, factorialPrimeCrossGram,
    show Nat.factorial 2 = 2 by decide]
end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity

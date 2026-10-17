/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteWeightedVariance
import RiemannResearch.Analysis.FiniteHilbertGram
import RiemannResearch.RH.CanonicalMobiusQuotientCells
import RiemannResearch.RH.QCanonicalWindowSchurArithmetic
import RiemannResearch.RH.QCanonicalWindowCapacity
import RiemannResearch.RH.QCanonicalWindowMinimum
import RiemannResearch.RH.QCanonicalMovingCovariance
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith

/-!
# Common-quotient variance caps for complete Q screened gains

Source: independently developed from the checked quotient-cell and Schur
identities in the user's sparse-power-cost research, 17 October 2026.
Screening leaves the common Mertens profile with coefficient equal to the
signed source defect. The exact complete Q energy is its defect-squared
variance, a nonnegative mean square, and the entire infinite complement.
Consequently a positive cell variance caps the gain by its reciprocal.
No upper energy estimate or lower gain certificate is claimed.

The statements concern actual canonical Q windows. They do not assert
squarefree legality of every member of a contiguous window. In particular,
they apply to screening one legal squarefree anchor against another via
N=M and squarefree N+1 and T+1. The full sparse squarefree target stays open.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.QCanonicalWindowCapacity
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QCanonicalWindowMinimum QCanonicalMovingCovariance
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteWeightedVariance

theorem schur_quotient_variance_full_energy
    (N M T q : ℕ) (hN : 0 < N) (hNM : N ≤ M) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 0 < n)
    (hT : ∀ n ∈ s, n / (T + 1) = q)
    (hcell : ∀ n ∈ s, ∀ i : Fin (M - N + 1), n / (N + i.val + 1) = q)
    (hW : mass s positiveQWeight ≠ 0) :
    schur N M T =
      (defect N M hN hNM T) ^ 2 * variance s positiveQWeight (mobiusQuotientProfile q) +
      mass s positiveQWeight *
        (defect N M hN hNM T * mean s positiveQWeight (mobiusQuotientProfile q) +
          (q : ℝ) * screenedOffset N M T) ^ 2 +
      ∑' n : {n : ℕ // n ∉ s}, positiveQWeight n.val *
        qSequence (screenedVector (windowFamily N M) (residual T)) n.val ^ 2 := by
  rw [schur_quotient_cell_full_energy N M T q hN hNM s hs hT hcell,
    affine_energy s positiveQWeight (mobiusQuotientProfile q)
      (defect N M hN hNM T) ((q : ℝ) * screenedOffset N M T) hW]

theorem schur_quotient_variance_le
    (N M T q : ℕ) (hN : 0 < N) (hNM : N ≤ M) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 0 < n)
    (hT : ∀ n ∈ s, n / (T + 1) = q)
    (hcell : ∀ n ∈ s, ∀ i : Fin (M - N + 1), n / (N + i.val + 1) = q)
    (hW : mass s positiveQWeight ≠ 0) :
    (defect N M hN hNM T) ^ 2 * variance s positiveQWeight (mobiusQuotientProfile q)
      ≤ schur N M T := by
  rw [schur_quotient_variance_full_energy N M T q hN hNM s hs hT hcell hW]
  have hm : 0 ≤ mass s positiveQWeight *
        (defect N M hN hNM T * mean s positiveQWeight (mobiusQuotientProfile q) +
          (q : ℝ) * screenedOffset N M T) ^ 2 :=
    mul_nonneg (Finset.sum_nonneg (fun n _ => positiveQWeight_nonneg n)) (sq_nonneg _)
  have ht : 0 ≤ ∑' n : {n : ℕ // n ∉ s}, positiveQWeight n.val *
        qSequence (screenedVector (windowFamily N M) (residual T)) n.val ^ 2 :=
    tsum_nonneg (fun n => mul_nonneg (positiveQWeight_nonneg _) (sq_nonneg _))
  linarith only [hm, ht]

theorem schur_gain_le_inverse_quotient_variance
    (N M T q : ℕ) (hN : 0 < N) (hNM : N ≤ M) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 0 < n)
    (hT : ∀ n ∈ s, n / (T + 1) = q)
    (hcell : ∀ n ∈ s, ∀ i : Fin (M - N + 1), n / (N + i.val + 1) = q)
    (hW : mass s positiveQWeight ≠ 0)
    (hV : 0 < variance s positiveQWeight (mobiusQuotientProfile q)) :
    (defect N M hN hNM T) ^ 2 / schur N M T ≤
      (variance s positiveQWeight (mobiusQuotientProfile q))⁻¹ := by
  have hb := schur_quotient_variance_le N M T q hN hNM s hs hT hcell hW
  by_cases he : schur N M T = 0
  · simp only [he, div_zero]
    exact inv_nonneg.mpr hV.le
  · have hp : 0 < schur N M T := lt_of_le_of_ne (sq_nonneg _) (Ne.symm he)
    rw [← one_div]
    apply (div_le_div_iff₀ hp hV).mpr
    simpa only [one_mul] using hb
end RiemannResearch.RH.QCanonicalWindowCapacity

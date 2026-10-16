/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCanonicalWindowCapacity
import RiemannResearch.RH.CanonicalMobiusQuotientCells
import RiemannResearch.RH.CanonicalMobiusConditionalHead
import RiemannResearch.RH.QCanonicalMovingCovariance
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.Analysis.FiniteGramOneStepCapacity
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Ring

/-!
# Complete Q Schur energy and its common quotient-cell arithmetic

Source: the user's 15 October 2026 request and the exact quotient identities
in CanonicalMobiusQuotientCells.lean. The common Mertens-profile coefficient
of the screened residual is precisely the signed Schur source defect.
The full infinite complement is retained in the energy identity.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.QCanonicalWindowCapacity
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QCanonicalWindowMinimum QCanonicalMovingCovariance
open RiemannResearch.Analysis.FiniteHilbertGram

theorem screened_sequence (N M T n : ℕ) :
    qSequence (screenedVector (windowFamily N M) (residual T)) n =
      qSequence (residual T) n -
        ∑ i, screening N M T i * qSequence (residual (N + i.val)) n := by
  change qSequenceLinear (residual T -
    Fintype.linearCombination ℝ (windowFamily N M) (screening N M T)) n = _
  simp only [map_sub, Fintype.linearCombination_apply, map_sum, map_smul,
    Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, windowFamily]
  rfl

/-- An explicit full infinite-energy form of the Schur denominator. -/
theorem schur_weighted (N M T : ℕ) :
    schur N M T = ∑' n : ℕ, positiveQWeight n *
      (qSequence (residual T) n -
        ∑ i, screening N M T i * qSequence (residual (N + i.val)) n) ^ 2 := by
  rw [schur, qNorm_weighted_sq]
  apply tsum_congr
  intro n
  rw [screened_sequence]

def screenedOffset (N M T : ℕ) : ℝ :=
  mobiusCellOffset T - ∑ i, screening N M T i * mobiusCellOffset (N + i.val)

/-- Screening changes the common profile's coefficient to the actual signed
source defect. Every reciprocal-Möbius boundary correction remains. -/
theorem screened_quotient_cell (N M T q n : ℕ) (hN : 0 < N) (hNM : N ≤ M)
    (hn : 0 < n) (hT : n / (T + 1) = q)
    (hcell : ∀ i : Fin (M - N + 1), n / (N + i.val + 1) = q) :
    qSequence (screenedVector (windowFamily N M) (residual T)) n =
      defect N M hN hNM T * mobiusQuotientProfile q n +
        (q : ℝ) * screenedOffset N M T := by
  have hr (Y : ℕ) (hY : n / (Y + 1) = q) :
      qSequence (residual Y) n = mobiusQuotientProfile q n +
        (q : ℝ) * mobiusCellOffset Y := by
    rw [residual_sequence]
    change qOneSequence n - canonicalMobiusHead Y n = _
    rw [show qOneSequence n = 1 by simp [qOneSequence, Nat.ne_of_gt hn],
      canonicalMobiusResidual_quotient_identity Y n hn, hY]
  have hold : ∀ i : Fin (M - N + 1), qSequence (residual (N + i.val)) n =
      mobiusQuotientProfile q n + (q : ℝ) * mobiusCellOffset (N + i.val) :=
    fun i => hr (N + i.val) (hcell i)
  rw [screened_sequence, hr T hT]
  simp_rw [hold]
  have hs : (∑ i : Fin (M - N + 1), screening N M T i *
      (mobiusQuotientProfile q n + (q : ℝ) * mobiusCellOffset (N + i.val))) =
      (∑ i, screening N M T i) * mobiusQuotientProfile q n +
        (q : ℝ) * ∑ i, screening N M T i * mobiusCellOffset (N + i.val) := by
    calc
      _ = ∑ i : Fin (M - N + 1),
          (screening N M T i * mobiusQuotientProfile q n +
            (q : ℝ) * (screening N M T i * mobiusCellOffset (N + i.val))) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [hs, defect_eq_one_sub_sum]
  unfold screenedOffset
  ring

/-- Exact local arithmetic energy plus the entire infinite complement.
The complement is not a finite-period or unsigned covariance replacement. -/
theorem schur_quotient_cell_full_energy
    (N M T q : ℕ) (hN : 0 < N) (hNM : N ≤ M) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 0 < n)
    (hT : ∀ n ∈ s, n / (T + 1) = q)
    (hcell : ∀ n ∈ s, ∀ i : Fin (M - N + 1), n / (N + i.val + 1) = q) :
    schur N M T =
      (∑ n ∈ s, positiveQWeight n *
        (defect N M hN hNM T * mobiusQuotientProfile q n +
          (q : ℝ) * screenedOffset N M T) ^ 2) +
      ∑' n : {n : ℕ // n ∉ s}, positiveQWeight n.val *
        qSequence (screenedVector (windowFamily N M) (residual T)) n.val ^ 2 := by
  rw [schur, qNorm_weighted_sq,
    ← (qSequence_square_summable
      (screenedVector (windowFamily N M) (residual T))).sum_add_tsum_subtype_compl s]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [screened_quotient_cell N M T q n hN hNM (hs n hn) (hT n hn) (hcell n hn)]

end RiemannResearch.RH.QCanonicalWindowCapacity

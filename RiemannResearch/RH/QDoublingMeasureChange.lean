/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QArgumentDoubling
import RiemannResearch.RH.QShiftedReciprocalBounds
import Lean.Elab.Tactic.Omega
import RiemannResearch.RH.ArgumentDoublingGenerators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact change of the physical doubling adjoint formulas

Source: independently derived from the user's dQ/dP and doubling request,
27 October 2026. The formulas are justified by pointwise detailed balance.
Their discrepancy is physically bounded and recovers the actual multiplier B
under doubling. This module does not formalize the abstract adjoint pairing,
nor claim that projection of the bounded discrepancy remains bounded.
-/

noncomputable section
namespace RiemannResearch.RH.QDoublingMeasureChange
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QShiftedReciprocal

/-- Detailed balance for the Q-adjoint of f(n) ↦ f(2n). -/
theorem q_doubling_balance (n : ℕ) :
    positiveQWeight (2 * n) * 4 = positiveQWeight n := by
  by_cases hn : n = 0
  · simp [hn, positiveQWeight]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  unfold positiveQWeight
  push_cast
  field_simp [hnR, ne_of_gt zetaTwo_pos]
  <;> ring

/-- Detailed balance for the Pareto-adjoint of f(n) ↦ f(2n). -/
theorem pareto_doubling_balance (n : ℕ) :
    positiveWeight (2 * n) * (4 - 2 / ((n : ℝ) + 1)) =
      positiveWeight n := by
  simpa only [mul_comm] using (Pareto.doubling_weight_identity n).symm

def qAdjointSequence (u : ℕ → ℝ) (k : ℕ) : ℝ :=
  if 2 ∣ k then 4 * u (k / 2) else 0

def paretoAdjointSequence (u : ℕ → ℝ) (k : ℕ) : ℝ :=
  if 2 ∣ k then (4 - 2 / (((k / 2 : ℕ) : ℝ) + 1)) * u (k / 2) else 0

/-- Physical change of measure changes the adjoint by exactly B/2. -/
theorem adjoint_change_exact (f : QHilbert) (k : ℕ) :
    paretoAdjointSequence (qSequence f) k =
      qAdjointSequence
        (fun n => qSequence f n - (1 / 2 : ℝ) * qSequence (B f) n) k := by
  by_cases hk : 2 ∣ k
  · simp only [paretoAdjointSequence, qAdjointSequence, if_pos hk, qSequence_B]
    ring
  · simp [paretoAdjointSequence, qAdjointSequence, hk]

theorem adjoint_defect_exact (f : QHilbert) (k : ℕ) :
    qAdjointSequence (qSequence f) k -
        paretoAdjointSequence (qSequence f) k =
      if 2 ∣ k then 2 * qSequence (B f) (k / 2) else 0 := by
  by_cases hk : 2 ∣ k
  · simp only [paretoAdjointSequence, qAdjointSequence, if_pos hk, qSequence_B]
    ring
  · simp [paretoAdjointSequence, qAdjointSequence, hk]

/-- The entire adjoint change is physically bounded, for every Hilbert vector. -/
theorem adjoint_defect_physically_bounded (f : QHilbert) (k : ℕ) :
    |qAdjointSequence (qSequence f) k -
      paretoAdjointSequence (qSequence f) k| ≤
        2 * (Real.sqrt zetaTwo * ‖f‖) := by
  rw [adjoint_defect_exact]
  by_cases hk : 2 ∣ k
  · rw [if_pos hk, abs_mul]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (B_physical_bound f (k / 2)) (by norm_num)
  · simp only [if_neg hk, abs_zero]
    positivity

/-- Applying physical doubling to the adjoint discrepancy recovers 2 B. -/
theorem doubled_adjoint_defect (f : QHilbert) (n : ℕ) :
    qAdjointSequence (qSequence f) (2 * n) -
        paretoAdjointSequence (qSequence f) (2 * n) =
      2 * qSequence (B f) n := by
  rw [adjoint_defect_exact]
  simp

/-- Exact smoothing commutator; no projection or span assumption is used. -/
theorem physical_B_doubling_commutator (f : QHilbert) (n : ℕ) :
    qSequence f (2 * n) / ((n : ℝ) + 1) - qSequence (B f) (2 * n) =
      (n : ℝ) / (((n : ℝ) + 1) * (2 * (n : ℝ) + 1)) *
        qSequence f (2 * n) := by
  rw [qSequence_B]
  push_cast
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [h1, h2]
  <;> ring

def adjointDefectSequence (f : QHilbert) (k : ℕ) : ℝ :=
  qAdjointSequence (qSequence f) k - paretoAdjointSequence (qSequence f) k

theorem adjointDefectSequence_zero (f : QHilbert) :
    adjointDefectSequence f 0 = 0 := by
  simp [adjointDefectSequence, qAdjointSequence, paretoAdjointSequence]

theorem adjointDefectSequence_square_summable (f : QHilbert) :
    Summable (fun k => positiveQWeight k * (adjointDefectSequence f k) ^ 2) :=
  boundedQ_square_summable _ (2 * (Real.sqrt zetaTwo * ‖f‖)) (by positivity)
    (adjoint_defect_physically_bounded f)

def adjointDefect (f : QHilbert) : QHilbert :=
  encodeQ (adjointDefectSequence f) (adjointDefectSequence_square_summable f)

@[simp] theorem qSequence_adjointDefect (f : QHilbert) :
    qSequence (adjointDefect f) = adjointDefectSequence f :=
  qSequence_encodeQ _ _ (adjointDefectSequence_zero f)

theorem adjointDefectSequence_even (f : QHilbert) (n : ℕ) :
    adjointDefectSequence f (2 * n) = 2 * qSequence (B f) n :=
  doubled_adjoint_defect f n

theorem adjointDefectSequence_odd (f : QHilbert) (n : ℕ) :
    adjointDefectSequence f (2 * n + 1) = 0 := by
  change qAdjointSequence (qSequence f) (2 * n + 1) -
    paretoAdjointSequence (qSequence f) (2 * n + 1) = 0
  rw [adjoint_defect_exact]
  have hn : ¬ 2 ∣ 2 * n + 1 := by omega
  simp [hn]

/-- Complete weighted energy; the full odd tail is zero and the even tail
is an exact reindexing of the full energy of B f. -/
theorem adjointDefect_norm_sq (f : QHilbert) :
    ‖adjointDefect f‖ ^ 2 = ‖B f‖ ^ 2 := by
  rw [qNorm_weighted_sq, qSequence_adjointDefect, qNorm_weighted_sq]
  have hsum := adjointDefectSequence_square_summable f
  have heven : Summable (fun n => positiveQWeight (2 * n) *
      (adjointDefectSequence f (2 * n)) ^ 2) :=
    hsum.comp_injective (by intro i j hij; change 2 * i = 2 * j at hij; omega)
  have hodd : Summable (fun n => positiveQWeight (2 * n + 1) *
      (adjointDefectSequence f (2 * n + 1)) ^ 2) :=
    hsum.comp_injective (by intro i j hij; change 2 * i + 1 = 2 * j + 1 at hij; omega)
  have hsplit := tsum_even_add_odd
    (f := fun k => positiveQWeight k * (adjointDefectSequence f k) ^ 2)
    heven hodd
  have heq : (fun n => positiveQWeight (2 * n) *
      (adjointDefectSequence f (2 * n)) ^ 2) =
      (fun n => positiveQWeight n * (qSequence (B f) n) ^ 2) := by
    funext n
    rw [adjointDefectSequence_even]
    calc
      positiveQWeight (2 * n) * (2 * qSequence (B f) n) ^ 2 =
          (positiveQWeight (2 * n) * 4) * (qSequence (B f) n) ^ 2 := by ring
      _ = positiveQWeight n * (qSequence (B f) n) ^ 2 := by
        rw [q_doubling_balance]
  have hoq : (fun n => positiveQWeight (2 * n + 1) *
      (adjointDefectSequence f (2 * n + 1)) ^ 2) = (fun _ : ℕ => (0 : ℝ)) := by
    funext n
    rw [adjointDefectSequence_odd]
    ring
  rw [heq, hoq] at hsplit
  simp only [tsum_zero, add_zero] at hsplit
  first | exact hsplit | exact hsplit.symm

theorem adjointDefect_norm (f : QHilbert) :
    ‖adjointDefect f‖ = ‖B f‖ := by
  nlinarith [adjointDefect_norm_sq f, norm_nonneg (adjointDefect f), norm_nonneg (B f)]

/-- Exact norm control for the difference of the weighted-adjoint formulas. -/
theorem adjointDefect_norm_le_half (f : QHilbert) :
    ‖adjointDefect f‖ ≤ (1 / 2 : ℝ) * ‖f‖ := by
  rw [adjointDefect_norm]
  exact QShiftedReciprocal.B_norm_le_half f

/-- The actual bounded physical doubling recovers the inverse-density multiplier. -/
theorem doubling_adjointDefect (f : QHilbert) :
    QArgumentDoubling.doubling (adjointDefect f) = (2 : ℝ) • B f := by
  apply qSequence_injective
  funext n
  simp only [QArgumentDoubling.doubling_sequence, qSequence_adjointDefect,
    adjointDefectSequence_even]
  change _ = qSequenceLinear ((2 : ℝ) • B f) n
  rw [map_smul]
  rfl

end RiemannResearch.RH.QDoublingMeasureChange

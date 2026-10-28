/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.OddReciprocalSquare
import RiemannResearch.RH.QSquarefreeResponseSeries
import RiemannResearch.RH.QCanonicalInnovation
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.ZetaTwoParitySignal
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact first-innovation smoothing energy

Source: user-provided argument and
https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/InfiniteSquarefreeResponseResearch20261027.md
for the proposed arithmetic evaluation. The proof below uses complete
infinite physical-coordinate Q sums. The relation between the first
canonical direction and qOdd is obtained from the existing exact projection
update, avoiding a change of Gram--Schmidt normalization or indexing.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QCanonicalInnovation
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParitySignal ZetaTwoOptimizerStage
open QShiftedReciprocal QSquarefreeSmoothedProjection
open RiemannResearch.Analysis.ExhaustiveWalk

/-- Every positive odd integer occurs once, with the complete infinite tail. -/
theorem odd_reciprocal_square_tsum :
    (∑' k : ℕ, 1 / ((2 * (k : ℝ) + 1) ^ 2 * (2 * (k : ℝ) + 2) ^ 2)) =
      zetaTwo - 2 * Real.log 2 := by
  rw [zetaTwo_eq_nat_sum]
  exact RiemannResearch.Analysis.OddReciprocalSquare.odd_reciprocal_square_tsum

/-- Smoothing energy of the unnormalized odd indicator in the actual Q space. -/
theorem B_qOdd_norm_sq :
    ‖B qOdd‖ ^ 2 = (zetaTwo - 2 * Real.log 2) / zetaTwo := by
  let f : ℕ → ℝ := fun n => positiveQWeight n * (qSequence (B qOdd) n) ^ 2
  have hs : Summable f := qSequence_square_summable (B qOdd)
  have he : Summable (fun k => f (2 * k)) :=
    hs.comp_injective (fun a b h => by omega)
  have ho : Summable (fun k => f (2 * k + 1)) :=
    hs.comp_injective (fun a b h => by omega)
  have heval (k : ℕ) : f (2 * k) = 0 := by
    dsimp only [f]
    rw [qSequence_B, qSequence_qOdd, if_pos (dvd_mul_right 2 k)]
    simp
  have hoval (k : ℕ) : f (2 * k + 1) =
      (1 / zetaTwo) *
        (1 / ((2 * (k : ℝ) + 1) ^ 2 * (2 * (k : ℝ) + 2) ^ 2)) := by
    have hn : ¬ 2 ∣ 2 * k + 1 := by omega
    dsimp only [f]
    rw [qSequence_B, qSequence_qOdd, if_neg hn]
    simp only [positiveQWeight, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one, div_pow]
    have hZ : zetaTwo ≠ 0 := ne_of_gt zetaTwo_pos
    have h1 : 2 * (k : ℝ) + 1 ≠ 0 := by positivity
    have h2 : 2 * (k : ℝ) + 2 ≠ 0 := by positivity
    have h2' : 2 * (k : ℝ) + 1 + 1 ≠ 0 := by positivity
    field_simp [hZ, h1, h2, h2']
    ring
  calc
    ‖B qOdd‖ ^ 2 = ∑' n, f n := qNorm_weighted_sq (B qOdd)
    _ = (∑' k, f (2 * k)) + ∑' k, f (2 * k + 1) :=
      (tsum_even_add_odd he ho).symm
    _ = ∑' k : ℕ, (1 / zetaTwo) *
        (1 / ((2 * (k : ℝ) + 1) ^ 2 * (2 * (k : ℝ) + 2) ^ 2)) := by
      simp only [heval, hoval, tsum_zero, zero_add]
    _ = (zetaTwo - 2 * Real.log 2) / zetaTwo := by
      rw [tsum_mul_left, odd_reciprocal_square_tsum]
      ring

/-- The first projection update identifies its canonical normalized direction. -/
theorem targetCoefficient_zero_smul :
    qOdd = targetCoefficient 0 • direction 0 := by
  have hz : (stage 0).starProjection qOne = 0 := by
    simp [stage, walkSpan]
  have hp := projection_succ 0 qOne
  change optimizer 1 = (stage 0).starProjection qOne +
    targetCoefficient 0 • direction 0 at hp
  simpa only [optimizer_one, hz, zero_add] using hp

theorem direction_zero_ne_zero : direction 0 ≠ 0 := by
  intro hz
  have hp := targetCoefficient_zero_smul
  rw [hz, smul_zero] at hp
  have hn := qOdd_norm_sq
  rw [hp, norm_zero] at hn
  norm_num at hn

theorem targetCoefficient_zero_sq : (targetCoefficient 0) ^ 2 = (3 / 4 : ℝ) := by
  have h := qOdd_norm_sq
  rw [targetCoefficient_zero_smul, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs, direction_norm 0 direction_zero_ne_zero] at h
  simpa only [one_pow, mul_one] using h

/-- Exact arithmetic value of the discarded parity smoothing energy. -/
theorem B_direction_zero_norm_sq :
    ‖B (direction 0)‖ ^ 2 =
      4 * (zetaTwo - 2 * Real.log 2) / (3 * zetaTwo) := by
  have h := congrArg (fun v : QHilbert => ‖B v‖ ^ 2) targetCoefficient_zero_smul
  rw [map_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    targetCoefficient_zero_sq] at h
  calc
    ‖B (direction 0)‖ ^ 2 = (4 / 3 : ℝ) * ‖B qOdd‖ ^ 2 := by linarith
    _ = 4 * (zetaTwo - 2 * Real.log 2) / (3 * zetaTwo) := by
      rw [B_qOdd_norm_sq]
      field_simp [ne_of_gt zetaTwo_pos]

theorem B_direction_zero_norm_sq_pos : 0 < ‖B (direction 0)‖ ^ 2 := by
  have hne : B qOdd ≠ 0 := by
    intro hz
    have hval : qSequence (B qOdd) 1 = (1 / 2 : ℝ) := by
      rw [qSequence_B, qSequence_qOdd]
      norm_num
    have hzero : qSequence (B qOdd) 1 = 0 := by
      rw [hz]
      simp [qSequence]
    linarith
  have hpos : 0 < ‖B qOdd‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
  have h := congrArg (fun v : QHilbert => ‖B v‖ ^ 2) targetCoefficient_zero_smul
  rw [map_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    targetCoefficient_zero_sq] at h
  nlinarith

/-- The complete squarefree variation bound with a fully explicit constant. -/
theorem movingCorrection_variation_explicit_parity :
    (∑' n, ‖movingCorrection (n + 1) - movingCorrection n‖ ^ 2) ≤
      (zetaTwo - 1 -
        4 * (zetaTwo - 2 * Real.log 2) / (3 * zetaTwo)) / 4 := by
  simpa only [B_direction_zero_norm_sq] using movingCorrection_variation_excluding_parity

theorem explicit_parity_bound_lt_basic :
    (zetaTwo - 1 -
      4 * (zetaTwo - 2 * Real.log 2) / (3 * zetaTwo)) / 4 <
      (zetaTwo - 1) / 4 := by
  have h := B_direction_zero_norm_sq_pos
  rw [B_direction_zero_norm_sq] at h
  linarith

end RiemannResearch.RH.QCanonicalInnovation

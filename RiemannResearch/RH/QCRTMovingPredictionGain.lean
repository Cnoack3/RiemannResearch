/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTMinimumHeadCost
import RiemannResearch.RH.QCRTPeriodHeadBalance
import RiemannResearch.RH.QSquarefreeHeadStep
import RiemannResearch.RH.QSquarefreeGapHeadCost
import RiemannResearch.RH.QResidueHeadSpace
import RiemannResearch.RH.QCRTMinimumEnergy
import RiemannResearch.RH.QCRTCoprimeApproximation
import RiemannResearch.Analysis.FiniteHilbertGram
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Actual moving predictions and signed dictionary gains

Source: user-provided continuation of a4911d47, 29 October 2026.
The full compensated tangent Gram system gives the prediction after enlargement.
Completing the enlargement displacement at the next physical site cancels
its observed square against the head cost, leaving an exact signed bilinear
term and a nonnegative unobserved remainder. No growth estimate is assumed
or proved; all vectors and norms use the complete Q Hilbert space.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCRTMovingPredictionGain
open ZetaTwoHilbert QSquarefreeLatticePackets QResidueHeadSpace
open QSquarefreeAffineHead QCRTPeriodHeadBalance QSquarefreeHeadStep
open QCRTMinimumHeadCost QCRTMinimumEnergy QCRTCoprimeApproximation
open QSquarefreeEnergyTransitions QSquarefreeGapHeadCost
open RiemannResearch.Analysis.FiniteHilbertGram

/-- Reuse the old actual minimum as the seed in the enlarged dictionary. -/
theorem minimumAt_enlargement_inverseGram (i j H r : ℕ)
    (hij : i ≤ j) (hH : H ≤ i + 1) (hHpos : 0 < H)
    (hr : r ∈ conductors (primorial (j + 2))) (hrH : H < r) :
    let s := conductors (primorial (j + 2))
    let v := fun d : freeConductors s H r => compensatedResidue (d : ℕ) r
    let hv := compensated_linearIndependent s (conductor_gt_one _) H r hr
    minimumAt j H = minimumAt i H -
      Fintype.linearCombination ℝ v (inverseCoeff hv (minimumAt i H)) := by
  dsimp only
  have hF : minimumAt i H ∈ dictionary (conductors (primorial (j + 2))) := by
    rw [← divisorStage_eq_dictionary _ (primorial_pos _)]
    exact divisorStage_mono
      (primorial_dvd_primorial (Nat.add_le_add_right hij 2)) (minimumAt_mem i H)
  have he : minimumAt j H =
      exactHeadAdjustment (conductors (primorial (j + 2))) H (minimumAt i H) := by
    exact exactHeadAdjustment_seed_independent _ H (minimumAt i H) (approximant j)
      hF (seed_mem_dictionary j) (fun k hk hkH => by
        rw [approximant_exact_head j k hk (by omega), minimumAt_head i H hH k hk hkH])
  rw [he, exactHeadAdjustment]
  simp only [inf_headNull_eq_zeroHeadSpan _ (conductor_gt_one _) H r hHpos hr hrH]
  rw [synthesis_inverseCoeff_eq_projection]
  rfl

/-- Exact prediction from the full Gram solve. At this site the source
has only the conductor n entry, equal to minus one. -/
theorem minimumAt_enlargement_prediction (i j n r : ℕ)
    (hij : i ≤ j) (hn : 1 < n) (hH : n - 1 ≤ i + 1)
    (hr : r ∈ conductors (primorial (j + 2))) (hrn : n < r) :
    let s := conductors (primorial (j + 2))
    let hv := compensated_linearIndependent s (conductor_gt_one _) (n - 1) r hr
    1 - qSequence (minimumAt j (n - 1)) n =
      (1 - qSequence (minimumAt i (n - 1)) n) +
      ∑ d, inverseCoeff hv (minimumAt i (n - 1)) d *
        stepSource n (primorial (j + 2)) r d := by
  dsimp only
  rw [minimumAt_enlargement_inverseGram i j (n - 1) r hij hH (by omega) hr (by omega)]
  change 1 - qSequenceLinear (_ - _) n = _
  rw [map_sub, Pi.sub_apply]
  change 1 - (qSequence (minimumAt i (n - 1)) n -
    qSequence (Fintype.linearCombination ℝ _ _) n) = _
  rw [step_sequence n (primorial (j + 2)) r (by omega) hrn]
  ring


/-- Scalar coefficient form of the actual prediction. The distinguished
index is conductor n in the full compensated tangent dictionary. -/
theorem minimumAt_enlargement_prediction_coefficient (i j n r : ℕ)
    (hij : i ≤ j) (hn : 1 < n) (hH : n - 1 ≤ i + 1)
    (hr : r ∈ conductors (primorial (j + 2))) (hrn : n < r)
    (dn : freeConductors (conductors (primorial (j + 2))) (n - 1) r)
    (hdn : (dn : ℕ) = n) :
    let hv := compensated_linearIndependent (conductors (primorial (j + 2)))
      (conductor_gt_one _) (n - 1) r hr
    1 - qSequence (minimumAt j (n - 1)) n =
      (1 - qSequence (minimumAt i (n - 1)) n) -
        inverseCoeff hv (minimumAt i (n - 1)) dn := by
  classical
  dsimp only
  rw [minimumAt_enlargement_prediction i j n r hij hn hH hr hrn]
  have hs :
      (∑ d, inverseCoeff
        (compensated_linearIndependent _ (conductor_gt_one _) (n - 1) r hr)
          (minimumAt i (n - 1)) d * stepSource n (primorial (j + 2)) r d) =
      -inverseCoeff
        (compensated_linearIndependent _ (conductor_gt_one _) (n - 1) r hr)
          (minimumAt i (n - 1)) dn := by
    rw [Finset.sum_eq_single dn]
    · simp [stepSource, hdn]
    · intro d _ hne
      have hv : (d : ℕ) ≠ n := fun e => hne (Subtype.ext (e.trans hdn.symm))
      simp [stepSource, hv]
    · simp
  rw [hs]
  ring

/-- Complete gain decomposition: observed displacement plus every unobserved
direction. No tail or signed term is omitted. -/
theorem minimumAt_enlargement_gain_completion (i j n r : ℕ)
    (hij : i ≤ j) (hn : 1 < n) (hH : n - 1 ≤ i + 1)
    (hnL : n ∣ primorial (j + 2))
    (hr : r ∈ conductors (primorial (j + 2))) (hrn : n < r) :
    let a := 1 - qSequence (minimumAt i (n - 1)) n
    let b := 1 - qSequence (minimumAt j (n - 1)) n
    let D := minimumAt i (n - 1) - minimumAt j (n - 1)
    let κ := stepCapacity n (primorial (j + 2)) r hr
    ‖D‖ ^ 2 = (b - a) ^ 2 / κ +
      ‖D - ((b - a) / κ) • stepNormal n (primorial (j + 2)) r hr‖ ^ 2 := by
  dsimp only
  apply correction_completion n (primorial (j + 2)) r hn (primorial_pos _) hnL hr hrn
  · apply (exact_head_iff_sub_mem_zeroHeadSpan _ (conductor_gt_one _) (n - 1) r
      (by omega) hr (by omega) (minimumAt j (n - 1)) ?_ ?_ _).mp
    · constructor
      · rw [← divisorStage_eq_dictionary _ (primorial_pos _)]
        exact divisorStage_mono
          (primorial_dvd_primorial (Nat.add_le_add_right hij 2)) (minimumAt_mem i _)
      · exact minimumAt_head i (n - 1) hH
    · rw [← divisorStage_eq_dictionary _ (primorial_pos _)]
      exact minimumAt_mem j _
    · exact minimumAt_head j (n - 1) (by omega)
  · change qSequenceLinear (_ - _) n = _
    rw [map_sub, Pi.sub_apply]
    change qSequence (minimumAt i (n - 1)) n - qSequence (minimumAt j (n - 1)) n =
      (1 - qSequence (minimumAt j (n - 1)) n) -
        (1 - qSequence (minimumAt i (n - 1)) n)
    ring

/-- The moving prediction cannot shift independently of enlargement gain. -/
theorem minimumAt_prediction_shift_sq_le_gain (i j n r : ℕ)
    (hij : i ≤ j) (hn : 1 < n) (hH : n - 1 ≤ i + 1)
    (hnL : n ∣ primorial (j + 2))
    (hr : r ∈ conductors (primorial (j + 2))) (hrn : n < r) :
    (qSequence (minimumAt i (n - 1)) n -
      qSequence (minimumAt j (n - 1)) n) ^ 2 ≤
      ‖minimumAt i (n - 1) - minimumAt j (n - 1)‖ ^ 2 *
        stepCapacity n (primorial (j + 2)) r hr := by
  have he := minimumAt_enlargement_gain_completion i j n r hij hn hH hnL hr hrn
  dsimp only at he
  have hcap := stepCapacity_pos n (primorial (j + 2)) r hn (primorial_pos _) hnL hr hrn
  apply (div_le_iff₀ hcap).mp
  have halg : (1 - qSequence (minimumAt j (n - 1)) n -
      (1 - qSequence (minimumAt i (n - 1)) n)) =
      qSequence (minimumAt i (n - 1)) n -
        qSequence (minimumAt j (n - 1)) n := by ring
  rw [halg] at he
  linarith [sq_nonneg ‖minimumAt i (n - 1) - minimumAt j (n - 1) -
    ((qSequence (minimumAt i (n - 1)) n - qSequence (minimumAt j (n - 1)) n) /
      stepCapacity n (primorial (j + 2)) r hr) •
        stepNormal n (primorial (j + 2)) r hr‖]

/-- Exact cancellation in the net energy transition, retaining its remainder. -/
theorem minimumAt_signed_prediction_transition (i j n r : ℕ)
    (hij : i ≤ j) (hn : 1 < n) (hH : n - 1 ≤ i + 1) (hnj : n ≤ j + 1)
    (hnL : n ∣ primorial (j + 2))
    (hr : r ∈ conductors (primorial (j + 2))) (hrn : n < r) :
    let a := 1 - qSequence (minimumAt i (n - 1)) n
    let b := 1 - qSequence (minimumAt j (n - 1)) n
    let D := minimumAt i (n - 1) - minimumAt j (n - 1)
    let κ := stepCapacity n (primorial (j + 2)) r hr
    ‖minimumAt j n‖ ^ 2 - ‖minimumAt i (n - 1)‖ ^ 2 =
      a * (2 * b - a) / κ -
        ‖D - ((b - a) / κ) • stepNormal n (primorial (j + 2)) r hr‖ ^ 2 := by
  have hc := minimumAt_single_head_cost j n r hn hnj hnL hr hrn
  have hg := minimumAt_period_gain i j (n - 1) hij hH
  have hd := minimumAt_enlargement_gain_completion i j n r hij hn hH hnL hr hrn
  dsimp only at hd ⊢
  have halg (a b κ : ℝ) : b ^ 2 / κ - (b - a) ^ 2 / κ = a * (2 * b - a) / κ := by ring
  have ha := halg (1 - qSequence (minimumAt i (n - 1)) n)
    (1 - qSequence (minimumAt j (n - 1)) n)
    (stepCapacity n (primorial (j + 2)) r hr)
  linarith

def oldMismatch (i : ℕ) : ℝ :=
  1 - qSequence (minimumAt (denseSchedule i) (i + 1)) (i + 2)

theorem denseAnchor_mem (i : ℕ) :
    squarefreeAnchor i ∈ conductors (primorial (denseSchedule (i + 1) + 2)) := by
  have hd := dvd_trans (squarefreeAnchor_spec i).2.dvd_primorial
    (primorial_dvd_primorial (show squarefreeAnchor i ≤ denseSchedule (i + 1) + 2 by
      have := squarefreeAnchor_le_two_mul i
      dsimp [denseSchedule]
      omega))
  exact Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨hd, primorial_ne_zero _⟩, by
      have := (squarefreeAnchor_spec i).1
      omega⟩

def denseCapacity (i : ℕ) : ℝ :=
  stepCapacity (i + 2) (primorial (denseSchedule (i + 1) + 2))
    (squarefreeAnchor i) (denseAnchor_mem i)

def enlargementRemainder (i : ℕ) : QHilbert :=
  (minimumAt (denseSchedule i) (i + 1) -
    minimumAt (denseSchedule (i + 1)) (i + 1)) -
  ((nextMismatch i - oldMismatch i) / denseCapacity i) •
    stepNormal (i + 2) (primorial (denseSchedule (i + 1) + 2))
      (squarefreeAnchor i) (denseAnchor_mem i)

theorem dense_signed_prediction_transition (i : ℕ) (hsf : Squarefree (i + 2)) :
    stageEnergy denseSchedule (i + 1) - stageEnergy denseSchedule i =
      oldMismatch i * (2 * nextMismatch i - oldMismatch i) / denseCapacity i -
        ‖enlargementRemainder i‖ ^ 2 := by
  have hnL : i + 2 ∣ primorial (denseSchedule (i + 1) + 2) :=
    dvd_trans hsf.dvd_primorial
      (primorial_dvd_primorial (by dsimp [denseSchedule]; omega))
  have he := minimumAt_signed_prediction_transition (denseSchedule i)
    (denseSchedule (i + 1)) (i + 2) (squarefreeAnchor i)
    (denseSchedule_monotone (Nat.le_succ i)) (by omega)
    (by dsimp [denseSchedule]; omega) (by dsimp [denseSchedule]; omega)
    hnL (denseAnchor_mem i) (squarefreeAnchor_spec i).1
  simpa only [show i + 2 - 1 = i + 1 by omega, stageEnergy,
    Nat.add_assoc, oldMismatch, nextMismatch, denseCapacity, enlargementRemainder] using he

/-- A signed upper bound that can be negative; neither prediction is bounded here. -/
theorem dense_signed_prediction_bound (i : ℕ) (hsf : Squarefree (i + 2)) :
    stageEnergy denseSchedule (i + 1) - stageEnergy denseSchedule i ≤
      oldMismatch i * (2 * nextMismatch i - oldMismatch i) / denseCapacity i := by
  rw [dense_signed_prediction_transition i hsf]
  exact sub_le_self _ (sq_nonneg _)

end RiemannResearch.RH.QCRTMovingPredictionGain

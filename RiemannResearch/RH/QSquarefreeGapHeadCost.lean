/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCompensatedResidueGap
import RiemannResearch.RH.QSquarefreeEnergyTransitions
import RiemannResearch.RH.QCRTMinimumHeadCost
import RiemannResearch.RH.QCRTPeriodHeadBalance
import RiemannResearch.RH.QSquarefreeHeadStep
import RiemannResearch.RH.QSquarefreeAffineHead
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.QCRTPredictionBudget
import RiemannResearch.RH.QExactHeadSubpolynomial
import RiemannResearch.Analysis.SubpolynomialWindowGrowth
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Actual minimum - energy costs using the nearest squarefree anchor

Source: the user - provided minimum - energy remaining - obligations handoff,
29 October 2026. This applies QCompensatedResidueGap to the actual
minimumAt vectors and the dense primorial schedule. The anchor is the
least squarefree integer strictly above the next physical site.
Bertrand supplies existence and membership in the actual dictionary.

The literal gapBudget takes the smaller of the prior reciprocal - head
cost and the new conductor - gap cost at every stage. Its signed energy
bound retains every dictionary - enlargement gain. The final RH theorem is
a conditional research reduction: subpolynomial growth of this actual
budget remains Open. No external squarefree short - interval theorem is
assumed or represented as a checked declaration here.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeGapHeadCost
open ZetaTwoHilbert QSquarefreeLatticePackets
open QCompensatedResidueGap

open ZetaTwoProbability QSquarefreeHeadStep QCRTMinimumHeadCost QCRTPeriodHeadBalance
open QSquarefreeAffineHead QSquarefreeEnergyTransitions

def gapWeight (n r : ℕ) : ℝ :=
  (1 / zetaTwo) * (((r : ℝ) - n) / (n : ℝ) ^ 2 * ((21 / 4 : ℝ) + Real.log ((n : ℝ) / ((r : ℝ) - n))))

theorem minimumAt_single_head_gap_bound (j n r : ℕ) (hn : 1 < n)
    (hnj : n ≤ j + 1) (hnL : n ∣ primorial (j + 2))
    (hr : r ∈ conductors (primorial (j + 2))) (hrn : n < r) (hr2 : r ≤ 2 * n) :
    ‖minimumAt j n‖^2 ≤ ‖minimumAt j (n - 1)‖^2 + (1 - qSequence (minimumAt j (n - 1)) n) ^ 2 * gapWeight n r := by
  have hb := compensatedResidue_gap_log_bound n r hn hrn hr2
  have hi := (inverse_stepCapacity_le_trial_energy n (primorial (j + 2)) r
    hn (primorial_pos _) hnL hr hrn).trans hb
  rw [minimumAt_single_head_cost j n r hn hnj hnL hr hrn]
  apply add_le_add le_rfl
  calc
    _ = (1 - qSequence (minimumAt j (n - 1)) n) ^ 2 * (1 / stepCapacity n (primorial (j + 2)) r hr) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hi (sq_nonneg _)

theorem dense_headCost_gap_bound (i r : ℕ) (hrsf : Squarefree r)
    (hrlower : i + 2 < r) (hrupper : r ≤ 2 * (i + 2)) :
    headCost denseSchedule i ≤ nextMismatch i ^ 2 * gapWeight (i + 2) r := by
  by_cases hsf : Squarefree (i + 2)
  · have hnL : i + 2 ∣ primorial (denseSchedule (i + 1) + 2) :=
      dvd_trans hsf.dvd_primorial
        (primorial_dvd_primorial (by dsimp [denseSchedule]; omega))
    have hrL : r ∣ primorial (denseSchedule (i + 1) + 2) :=
      dvd_trans hrsf.dvd_primorial
        (primorial_dvd_primorial (by dsimp [denseSchedule]; omega))
    have hr : r ∈ conductors (primorial (denseSchedule (i + 1) + 2)) :=
      Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hrL, primorial_ne_zero _⟩, by omega⟩
    have hb := minimumAt_single_head_gap_bound (denseSchedule (i + 1)) (i + 2) r
      (by omega) (by dsimp [denseSchedule]; omega) hnL hr hrlower hrupper
    simp only [show i + 2 - 1 = i + 1 by omega] at hb
    have hc := minimumAt_head_cost (denseSchedule (i + 1)) (i + 1) (i + 2) (by omega)
    change ‖minimumAt (denseSchedule (i + 1)) (i + 2) - minimumAt (denseSchedule (i + 1)) (i + 1)‖^2 ≤ _
    change _ ≤ (1 - qSequence (minimumAt (denseSchedule (i + 1)) (i + 1)) (i + 2)) ^ 2 * gapWeight (i + 2) r
    linarith only [hb, hc]
  · rw [headCost_eq_zero_of_nonsquarefree denseSchedule i
        (denseSchedule_head (i + 1)) hsf,
      nextMismatch_eq_zero_of_nonsquarefree i hsf]
    simp

theorem dense_energy_gap_signed_bound (ρ : ℕ → ℕ)
    (hρ : ∀ i, Squarefree (ρ i) ∧ i + 2 < ρ i ∧ ρ i ≤ 2 * (i + 2)) (N : ℕ) :
    stageEnergy denseSchedule N ≤ stageEnergy denseSchedule 0 + (∑ i ∈ Finset.range N, nextMismatch i ^ 2 * gapWeight (i + 2) (ρ i)) -
      ∑ i ∈ Finset.range N, periodGain denseSchedule i := by
  rw [stageEnergy_telescope denseSchedule denseSchedule_monotone denseSchedule_head]
  have hs := Finset.sum_le_sum (s := Finset.range N) (fun i _ =>
    sub_le_sub_right (dense_headCost_gap_bound i (ρ i) (hρ i).1
      (hρ i).2.1 (hρ i).2.2) (periodGain denseSchedule i))
  simp only [Finset.sum_sub_distrib] at hs ⊢
  linarith

private theorem squarefree_after (i : ℕ) :
    ∃ r : ℕ, i + 2 < r ∧ Squarefree r := by
  obtain ⟨r, hr, hlo, _⟩ := Nat.exists_prime_lt_and_le_two_mul (i + 2) (by omega)
  exact ⟨r, hlo, hr.squarefree⟩

def squarefreeAnchor (i : ℕ) : ℕ := Nat.find (squarefree_after i)

theorem squarefreeAnchor_spec (i : ℕ) :
    i + 2 < squarefreeAnchor i ∧ Squarefree (squarefreeAnchor i) :=
  Nat.find_spec (squarefree_after i)

theorem squarefreeAnchor_le (i r : ℕ) (hrn : i + 2 < r) (hrsf : Squarefree r) :
    squarefreeAnchor i ≤ r :=
  Nat.find_min' (squarefree_after i) ⟨hrn, hrsf⟩

theorem squarefreeAnchor_le_two_mul (i : ℕ) : squarefreeAnchor i ≤ 2 * (i + 2) := by
  obtain ⟨r, hr, hlo, hup⟩ := Nat.exists_prime_lt_and_le_two_mul (i + 2) (by omega)
  exact (squarefreeAnchor_le i r hlo hr.squarefree).trans hup


def gapBudget (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, min
    ((4 / zetaTwo) * (nextMismatch i ^ 2 / (i + 1 : ℕ)))
    (nextMismatch i ^ 2 * gapWeight (i + 2) (squarefreeAnchor i))

theorem gapWeight_nonneg (n r : ℕ) (hn : 1 < n) (hnr : n < r) (hr2 : r ≤ 2 * n) :
    0 ≤ gapWeight n r :=
  (sq_nonneg _).trans (compensatedResidue_gap_log_bound n r hn hnr hr2)

theorem gapBudget_nonneg (N : ℕ) : 0 ≤ gapBudget N := by
  apply Finset.sum_nonneg
  intro i hi
  apply le_min
  · positivity [zetaTwo_pos]
  · exact mul_nonneg (sq_nonneg _)
      (gapWeight_nonneg (i + 2) (squarefreeAnchor i) (by omega)
        (squarefreeAnchor_spec i).1 (squarefreeAnchor_le_two_mul i))

theorem gapBudget_le_predictionBudget (N : ℕ) :
    gapBudget N ≤ (4 / zetaTwo) * predictionBudget N := by
  unfold gapBudget predictionBudget
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => min_le_left _ _)

theorem dense_energy_gapBudget_signed_bound (N : ℕ) :
    stageEnergy denseSchedule N ≤ stageEnergy denseSchedule 0 + gapBudget N -
      ∑ i ∈ Finset.range N, periodGain denseSchedule i := by
  have hp (i : ℕ) : headCost denseSchedule i ≤
      min ((4 / zetaTwo) * (nextMismatch i ^ 2 / (i + 1 : ℕ)))
        (nextMismatch i ^ 2 * gapWeight (i + 2) (squarefreeAnchor i)) := by
    apply le_min
    · calc
        headCost denseSchedule i ≤ nextMismatch i ^ 2 * ((1 / zetaTwo) * (4 / (i + 1 : ℕ))) := dense_headCost_bound i
        _ = (4 / zetaTwo) * (nextMismatch i ^ 2 / (i + 1 : ℕ)) := by ring
    · exact dense_headCost_gap_bound i (squarefreeAnchor i)
        (squarefreeAnchor_spec i).2 (squarefreeAnchor_spec i).1
        (squarefreeAnchor_le_two_mul i)
  rw [stageEnergy_telescope denseSchedule denseSchedule_monotone denseSchedule_head]
  have hs := Finset.sum_le_sum (s := Finset.range N) (fun i _ =>
    sub_le_sub_right (hp i) (periodGain denseSchedule i))
  simp only [Finset.sum_sub_distrib] at hs ⊢
  change _ ≤ gapBudget N - _ at hs
  linarith

theorem dense_energy_le_gapBudget (N : ℕ) :
    stageEnergy denseSchedule N ≤ stageEnergy denseSchedule 0 + gapBudget N := by
  have he := dense_energy_gapBudget_signed_bound N
  have hg : 0 ≤ ∑ i ∈ Finset.range N, periodGain denseSchedule i :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  linarith

open QCRTPredictionBudget Filter
open scoped Topology

theorem trial_error_le_gapBudget (N : ℕ) :
    ‖qOne - trial N‖^2 ≤ 2 + 2 * stageEnergy denseSchedule 0 + 2 * gapBudget N := by
  have hnorm := norm_sub_le qOne (trial N)
  rw [qOne_norm] at hnorm
  have he := dense_energy_le_gapBudget N
  change ‖trial N‖^2 ≤ _ at he
  nlinarith [norm_nonneg (qOne - trial N), norm_nonneg (trial N),
    sq_nonneg (‖trial N‖-1)]

/-- Conditional research reduction: the actual gap budget remains Open. -/
theorem riemannHypothesis_of_subpolynomial_gapBudget
    (hsub : Tendsto (fun N => Real.log (1 + gapBudget N) / Real.log ((N + 2 : ℕ) : ℝ)) atTop (𝓝 0)) : RiemannHypothesis := by
  let E : ℕ → ℝ := fun N => 1 + 2 * stageEnergy denseSchedule 0 + 2 * gapBudget N
  let A : ℝ := 4 + 2 * stageEnergy denseSchedule 0
  have he0 : 0 ≤ stageEnergy denseSchedule 0 := sq_nonneg _
  have hA : 1 ≤ A := by dsimp [A]; linarith
  have hE : ∀ N, 0 ≤ E N := by
    intro N
    dsimp [E]
    positivity [gapBudget_nonneg N]
  have hn : Tendsto (fun N : ℕ => ((N + 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hscaled :=
    RiemannResearch.Analysis.SubpolynomialWindow.relativeLog_tendsto_zero_of_scaled_budget
    E gapBudget (fun N => ((N + 2 : ℕ) : ℝ)) A hA hE gapBudget_nonneg hn
    (Eventually.of_forall (fun N => by
      dsimp [A, E]
      nlinarith [gapBudget_nonneg N, mul_nonneg he0 (gapBudget_nonneg N)])) hsub
  apply QExactHeadSubpolynomial.riemannHypothesis_of_cofinal_exact_head_subpolynomial
    trial (fun N => N + 2) E hn trial_legal trial_head hE
  · intro N
    have h := trial_error_le_gapBudget N
    dsimp [E]
    linarith
  · exact hscaled


end RiemannResearch.RH.QSquarefreeGapHeadCost

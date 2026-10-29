/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTConductorGap
import RiemannResearch.RH.QCRTPeriodHeadBalance
import RiemannResearch.RH.QCRTMinimumEnergy
import RiemannResearch.RH.QResidueHeadSpace
import RiemannResearch.RH.QSquarefreeAffineHead
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.QCRTCoprimeApproximation
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Exact plateaux and conductor comparisons for delayed-head CRT schedules

Source: the user-provided period-first research task, 28 October 2026.
The generic result identifies the complete zero-head subspaces across a
conductor gap, so it identifies the actual minimizers, not merely their
first coordinates or a finite truncation of their energies.

The existing signed period/head balance is reused. No complete-energy
numerical upper certificate or uniform cofinal bound is assumed here.
-/

noncomputable section
namespace RiemannResearch.RH.QCRTDelayedSchedule
open ZetaTwoHilbert QSquarefreeLatticePackets QResidueHeadSpace
open QSquarefreeAffineHead QCRTConductorGap QCRTCoprimeApproximation
open QCRTPeriodHeadBalance

/-- A conductor gap makes the entire zero-head subspace constant. -/
theorem dictionary_headNull_eq_of_gap (s : Finset ℕ)
    (hs : ∀ d ∈ s, 1 < d) (H K r : ℕ) (hH : 0 < H) (hHK : H ≤ K)
    (hr : r ∈ s) (hHr : H < r)
    (hgap : ∀ d ∈ s, H < d → K < d) :
    dictionary s ⊓ headNull H = dictionary s ⊓ headNull K := by
  apply le_antisymm
  · intro f hf
    refine ⟨hf.1, ?_⟩
    have hz (n : ℕ) : qSequence (0 : QHilbert) n = 0 := by
      change qSequenceLinear 0 n = 0
      simp
    have he := dictionary_head_agreement_of_gap s hs H K r hH hr hHr hgap
      f 0 hf.1 (dictionary s).zero_mem (by
        intro n hn hnH
        rw [hf.2 n hn hnH, hz])
    intro n hn hnK
    exact (he n hn hnK).trans (hz n)
  · intro f hf
    exact ⟨hf.1, fun n hn hnH => hf.2 n hn (hnH.trans hHK)⟩

/-- The complete minimum-norm adjustment is unchanged across the gap,
for any seed and hence any prescribed feasible physical head. -/
theorem exactHeadAdjustment_eq_of_gap (s : Finset ℕ)
    (hs : ∀ d ∈ s, 1 < d) (H K r : ℕ) (hH : 0 < H) (hHK : H ≤ K)
    (hr : r ∈ s) (hHr : H < r)
    (hgap : ∀ d ∈ s, H < d → K < d) (F : QHilbert) :
    exactHeadAdjustment s H F = exactHeadAdjustment s K F := by
  simp only [exactHeadAdjustment,
    dictionary_headNull_eq_of_gap s hs H K r hH hHK hr hHr hgap]

/-- Primorial minimizers plateau between consecutive available conductors.
No extra head-legality restriction is needed for this equality of adjustments;
the exact-one interpretation uses the existing `minimumAt_head` hypotheses. -/
theorem minimumAt_eq_of_gap (j H K : ℕ) (hH : 0 < H) (hHK : H ≤ K)
    (hHL : H < primorial (j + 2))
    (hgap : ∀ d, d ∣ primorial (j + 2) → H < d → K < d) :
    minimumAt j H = minimumAt j K := by
  apply exactHeadAdjustment_eq_of_gap _ (conductor_gt_one _) H K
    (primorial (j + 2)) hH hHK _ hHL _
  · exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨dvd_refl _, primorial_ne_zero _⟩, by omega⟩
  · intro d hd hdH
    exact hgap d (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1 hdH

/-- At period 510510, prescribing coordinate 16 adds no constraint to head 15. -/
theorem period510510_head15_eq_head16 : minimumAt 15 15 = minimumAt 15 16 := by
  have hp : primorial (15 + 2) = 510510 := by decide +kernel
  apply minimumAt_eq_of_gap 15 15 16 (by norm_num) (by norm_num)
  · rw [hp]
    norm_num
  · rw [hp]
    intro d hd hdH
    by_contra hnot
    have he : d = 16 := by omega
    subst d
    norm_num at hd

/-- At period 9699690, prescribing coordinate 18 adds no constraint to head 17. -/
theorem period9699690_head17_eq_head18 : minimumAt 17 17 = minimumAt 17 18 := by
  have hp : primorial (17 + 2) = 9699690 := by decide +kernel
  apply minimumAt_eq_of_gap 17 17 18 (by norm_num) (by norm_num)
  · rw [hp]
    norm_num
  · rw [hp]
    intro d hd hdH
    by_contra hnot
    have he : d = 18 := by omega
    subst d
    norm_num at hd

/-- The direction 17 is genuinely new relative to period 30030. -/
theorem conductor17_enters : ¬17 ∣ 30030 ∧ 17 ∣ 510510 := by norm_num

/-- The next primorial adds the still-missing prime 19. -/
theorem conductor19_enters : ¬19 ∣ 510510 ∧ 19 ∣ 9699690 := by norm_num

/-- The old rigid interval (15,20] is not a conductor gap after adjoining 17. -/
theorem period510510_old_gap_fails :
    ¬(∀ d : ℕ, d ∣ 510510 → 15 < d → 20 < d) := by
  intro h
  have := h 17 (by norm_num) (by norm_num)
  omega

/-- Exact complete-energy comparison with the obstructed old period.
The squared distance is the actual benefit of all added directions. -/
theorem period30030_to510510_head15_energy :
    ‖minimumAt 14 15‖ ^ 2 = ‖minimumAt 15 15‖ ^ 2 +
      ‖minimumAt 14 15 - minimumAt 15 15‖ ^ 2 :=
  minimumAt_period_gain 14 15 15 (by norm_num) (by norm_num)

/-- Reuse the existing canonical obstruction without modifying it. -/
theorem period30030_head15_minimum_gt_one : 1 < ‖minimumAt 14 15‖ ^ 2 := by
  simpa only [minimumAt, QCRTMinimumEnergy.minimumEnergyApproximant] using
    minimumEnergyApproximant_fourteen_gt_one

end RiemannResearch.RH.QCRTDelayedSchedule

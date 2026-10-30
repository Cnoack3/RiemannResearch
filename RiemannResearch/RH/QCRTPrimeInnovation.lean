/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.OrthogonalObservationInnovation
import RiemannResearch.RH.QResidueAnchorScreening
import RiemannResearch.RH.QCRTInnovationGain
import RiemannResearch.RH.QFloorDilation
import RiemannResearch.RH.QSquarefreeEnergyTransitions
import RiemannResearch.RH.QSquarefreeAffineHead
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.QResidueHeadSpace
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Complete energy estimates for the actual screened prime-conductor family

Source: independently developed from the user-provided capacity-increment
agenda, 29 October 2026, Priority A. Bertrand supplies an old prime anchor
at every stage, so the bounds have no missing arithmetic anchor hypothesis.
The trace bound and explicit raw-to-screened ratio do not bound the actual
inverse-Gram source. Primality is needed to identify a family as an enlargement,
but not for the energy estimates themselves.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCRTPrimeInnovation
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeLatticePackets QResidueHeadSpace
open QSquarefreeAffineHead QCRTInnovationGain QSquarefreeEnergyTransitions
open QResidueAnchorScreening
open RiemannResearch.Analysis.OrthogonalObservationInnovation

theorem exists_old_prime_anchor (i : ℕ) :
    ∃ r : ℕ, Nat.Prime r ∧ i + 1 < r ∧ r ≤ 2 * i + 2 := by
  obtain ⟨r, hp, hl, hu⟩ := Nat.exists_prime_lt_and_le_two_mul (i + 1) (by omega)
  exact ⟨r, hp, hl, by omega⟩

def shortAnchor (i : ℕ) : ℕ := Classical.choose (exists_old_prime_anchor i)
theorem shortAnchor_spec (i : ℕ) :
    Nat.Prime (shortAnchor i) ∧ i + 1 < shortAnchor i ∧ shortAnchor i ≤ 2 * i + 2 :=
  Classical.choose_spec (exists_old_prime_anchor i)

def oldPeriod (i : ℕ) : ℕ := primorial (denseSchedule i + 2)

theorem shortAnchor_mem (i : ℕ) : shortAnchor i ∈ conductors (oldPeriod i) := by
  have hs := shortAnchor_spec i
  have hd := dvd_trans hs.1.squarefree.dvd_primorial
    (primorial_dvd_primorial (show shortAnchor i ≤ denseSchedule i + 2 by
      simpa [denseSchedule] using hs.2.2))
  exact Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨hd, primorial_ne_zero _⟩, hs.1.one_lt⟩

theorem oldPeriod_mem (i : ℕ) : oldPeriod i ∈ conductors (oldPeriod i) := by
  have hs := shortAnchor_spec i
  have hd := (Nat.mem_divisors.mp (Finset.mem_filter.mp (shortAnchor_mem i)).1).1
  have hle := Nat.le_of_dvd (primorial_pos _) hd
  change shortAnchor i ≤ oldPeriod i at hle
  exact Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨dvd_rfl, primorial_ne_zero _⟩, by omega⟩

theorem head_lt_oldPeriod (i : ℕ) : i + 1 < oldPeriod i := by
  have hd := (Nat.mem_divisors.mp (Finset.mem_filter.mp (shortAnchor_mem i)).1).1
  exact lt_of_lt_of_le (shortAnchor_spec i).2.1 (Nat.le_of_dvd (primorial_pos _) hd)

def rawDirection (i d : ℕ) : QHilbert :=
  compensatedResidue ((2 * i + 3) * d) (oldPeriod i)
def screenedDirection (i d : ℕ) : QHilbert :=
  innovation (oldTangent i) (rawDirection i d)

theorem screened_anchor_change (i d : ℕ) :
    screenedDirection i d = innovation (oldTangent i)
      (compensatedResidue ((2 * i + 3) * d) (shortAnchor i)) := by
  apply innovation_eq_of_sub_mem
  exact anchor_change_mem _ (i + 1) _ _ _ (oldPeriod_mem i) (shortAnchor_mem i)
    (head_lt_oldPeriod i) (shortAnchor_spec i).2.1

theorem screened_energy_bound (i d : ℕ) (hd : 0 < d) :
    ‖screenedDirection i d‖ ^ 2 ≤
      2 / (zetaTwo * (((2 * i + 3) * d : ℕ) : ℝ)) +
      2 * shortAnchor i / (zetaTwo * (((2 * i + 3) * d : ℕ) : ℝ) ^ 2) := by
  rw [screened_anchor_change]
  exact (innovation_energy_le _ _).trans
    (compensated_energy_upper _ _ (by nlinarith) (shortAnchor_spec i).1.two_le)

theorem screened_energy_le_four (i d : ℕ) (hd : 0 < d) :
    ‖screenedDirection i d‖ ^ 2 ≤
      4 / (zetaTwo * (((2 * i + 3) * d : ℕ) : ℝ)) := by
  have hm : (0 : ℝ) < (((2 * i + 3) * d : ℕ) : ℝ) := by positivity
  have hr : (shortAnchor i : ℝ) ≤ (((2 * i + 3) * d : ℕ) : ℝ) := by
    exact_mod_cast (show shortAnchor i ≤ (2 * i + 3) * d by
      have := (shortAnchor_spec i).2.2
      nlinarith)
  have hb := screened_energy_bound i d hd
  have h := mul_le_mul_of_nonneg_left hr
    (show 0 ≤ 2 / (zetaTwo * (((2 * i + 3) * d : ℕ) : ℝ) ^ 2) by positivity [zetaTwo_pos])
  have he : (2 / (zetaTwo * (((2 * i + 3) * d : ℕ) : ℝ) ^ 2)) *
      (((2 * i + 3) * d : ℕ) : ℝ) =
      2 / (zetaTwo * (((2 * i + 3) * d : ℕ) : ℝ)) := by field_simp
  rw [he] at h
  have h' : 2 * shortAnchor i / (zetaTwo * (((2 * i + 3) * d : ℕ) : ℝ) ^ 2) ≤
      2 / (zetaTwo * (((2 * i + 3) * d : ℕ) : ℝ)) := by
    calc
      _ = (2 / (zetaTwo * (((2 * i + 3) * d : ℕ) : ℝ) ^ 2)) * shortAnchor i := by ring
      _ ≤ _ := h
  calc
    _ ≤ _ := hb
    _ ≤ 2 / (zetaTwo * (((2 * i + 3) * d : ℕ) : ℝ)) +
        2 / (zetaTwo * (((2 * i + 3) * d : ℕ) : ℝ)) := by nlinarith
    _ = _ := by ring

theorem screened_trace_bound (i : ℕ) :
    (∑ d ∈ (oldPeriod i).divisors, ‖screenedDirection i d‖ ^ 2) ≤
      (4 / (zetaTwo * (2 * i + 3 : ℕ))) *
        ∑ d ∈ (oldPeriod i).divisors, (1 : ℝ) / d := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  have hdp := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 (primorial_pos _)
  calc
    _ ≤ _ := screened_energy_le_four i d hdp
    _ = _ := by
      rw [Nat.cast_mul]
      simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
      ring


theorem actual_raw_energy_lower (i : ℕ) :
    ((oldPeriod i : ℝ) - 8 * (2 * i + 3 : ℕ)) /
        (4 * zetaTwo * (2 * i + 3 : ℕ) ^ 2) ≤ ‖rawDirection i 1‖ ^ 2 := by
  have hL := conductor_gt_one _ _ (oldPeriod_mem i)
  simpa only [rawDirection, Nat.mul_one] using raw_energy_lower (2 * i + 3)
    (oldPeriod i) (by omega) (by omega)

theorem actual_screening_ratio (i : ℕ) (hlarge : 16 * (2 * i + 3) ≤ oldPeriod i) :
    ‖screenedDirection i 1‖ ^ 2 ≤
      (32 * (2 * i + 3 : ℕ) / (oldPeriod i : ℝ)) * ‖rawDirection i 1‖ ^ 2 := by
  have hp : (0 : ℝ) < (2 * i + 3 : ℕ) := by positivity
  have hL : (0 : ℝ) < oldPeriod i := by exact_mod_cast primorial_pos _
  have hz := zetaTwo_pos
  have hl : 16 * (2 * i + 3 : ℕ) ≤ (oldPeriod i : ℝ) := by exact_mod_cast hlarge
  have hu := screened_energy_le_four i 1 (by omega)
  simp only [Nat.mul_one] at hu
  have hlo := actual_raw_energy_lower i
  have hlow : (oldPeriod i : ℝ) / (8 * zetaTwo * (2 * i + 3 : ℕ) ^ 2) ≤
      ‖rawDirection i 1‖ ^ 2 := by
    apply le_trans _ hlo
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_nonneg (show 0 ≤ zetaTwo * (2 * i + 3 : ℕ) ^ 2 by positivity)
      (sub_nonneg.mpr hl)]
  have hh := mul_le_mul_of_nonneg_left hlow
    (show 0 ≤ (32 * (2 * i + 3 : ℕ) / (oldPeriod i : ℝ)) by positivity)
  have hid : (32 * (2 * i + 3 : ℕ) / (oldPeriod i : ℝ)) *
      ((oldPeriod i : ℝ) / (8 * zetaTwo * (2 * i + 3 : ℕ) ^ 2)) =
        4 / (zetaTwo * (2 * i + 3 : ℕ)) := by
    field_simp
    ring
  rw [hid] at hh
  exact hu.trans hh

end RiemannResearch.RH.QCRTPrimeInnovation


namespace RiemannResearch.RH.QCRTPrimeInnovation
open QFloorDilation ZetaTwoHilbert QSquarefreeLatticePackets QCRTInnovationGain
open RiemannResearch.Analysis.OrthogonalObservationInnovation
/-- Exact arithmetic change of coordinates for EVERY positive old divisor d.
Together with d=1 this retains the entire new-conductor block. -/
theorem rawDirection_floor_block (i d : ℕ) (hd : 0 < d) :
    rawDirection i d =
      floorDilation (2 * i + 3) (by omega) (qResidue d) +
        (1 / (d : ℝ)) • rawDirection i 1 := by
  rw [floorDilation_qResidue (2 * i + 3) d (by omega) hd]
  have hc : (oldPeriod i : ℝ) / (((2 * i + 3) * d : ℕ) : ℝ) =
      (1 / (d : ℝ)) * ((oldPeriod i : ℝ) / (2 * i + 3 : ℕ)) := by
    simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  simp only [rawDirection, Nat.mul_one, compensatedResidue]
  rw [hc]
  module

/-- Screening preserves that full arithmetic decomposition and all cross terms. -/
theorem screenedDirection_floor_block (i d : ℕ) (hd : 0 < d) :
    screenedDirection i d =
      innovation (oldTangent i)
        (floorDilation (2 * i + 3) (by omega) (qResidue d)) +
        (1 / (d : ℝ)) • screenedDirection i 1 := by
  unfold screenedDirection
  rw [rawDirection_floor_block i d hd]
  simp only [innovation, map_add, map_smul]
  module
end RiemannResearch.RH.QCRTPrimeInnovation

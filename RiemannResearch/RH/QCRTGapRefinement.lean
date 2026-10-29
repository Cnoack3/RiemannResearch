/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTConductorGap
import RiemannResearch.RH.QResidueHeadSpace
import RiemannResearch.RH.QSquarefreeAffineHead
import RiemannResearch.RH.SquarefreeRadicalDifference
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Refinement of the first conductor-gap obstruction after adjoining 17

Source: user-directed delayed-period schedule investigation, 28 October 2026.
The first twenty coordinates give an exact signed square completion. This is
a lower bound on every feasible complete-Q vector, not a trial-vector estimate.
It is below one, so it does not establish or obstruct an upper certificate.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCRTGapRefinement
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative
open QSquarefreeLatticePackets QResidueHeadSpace QSquarefreeAffineHead
open SquarefreeRadicalDifference QCRTConductorGap QFiniteEnergyBounds

/-- Matching divisor events make the physical jumps agree on the entire dictionary. -/
theorem dictionary_difference_eq (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (m a : ℕ) (hm : 0 < m) (ha : 0 < a)
    (hdiv : ∀ d ∈ s, d ∣ m ↔ d ∣ a)
    (f : QHilbert) (hf : f ∈ dictionary s) :
    qDifference f m = qDifference f a := by
  obtain ⟨c, rfl⟩ := (mem_dictionary_iff s f).mp hf
  calc
    _ = ∑ d ∈ s, c d * (residueFraction d m - residueFraction d (m - 1)) := by
      simp only [qDifference, synthesis_sequence, mul_sub, Finset.sum_sub_distrib]
    _ = ∑ d ∈ s, c d * (residueFraction d a - residueFraction d (a - 1)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [residueFraction_difference_eq_of_dvd_iff d m a (hs d hd) hm ha (hdiv d hd)]
    _ = _ := by
      simp only [qDifference, synthesis_sequence, mul_sub, Finset.sum_sub_distrib]

/-- With no conductor dividing the site, its jump is precisely the first coordinate. -/
theorem dictionary_difference_of_no_divisor (s : Finset ℕ)
    (hs : ∀ d ∈ s, 1 < d) (m : ℕ) (hm : 0 < m)
    (hdiv : ∀ d ∈ s, ¬ d ∣ m)
    (f : QHilbert) (hf : f ∈ dictionary s) :
    qDifference f m = qSequence f 1 := by
  obtain ⟨c, rfl⟩ := (mem_dictionary_iff s f).mp hf
  calc
    _ = ∑ d ∈ s, c d * (residueFraction d m - residueFraction d (m - 1)) := by
      simp only [qDifference, synthesis_sequence, mul_sub, Finset.sum_sub_distrib]
    _ = ∑ d ∈ s, c d * residueFraction d 1 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [residueFraction_difference d m (hs d hd) hm, if_neg (hdiv d hd), sub_zero]
      simp only [residueFraction, Nat.mod_eq_of_lt (hs d hd), Nat.cast_one]
    _ = _ := (synthesis_sequence s c 1).symm

private theorem conductor_dvd_period {d : ℕ} (hd : d ∈ conductors 510510) :
    d ∣ 510510 := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1

private theorem events16 (d : ℕ) (hd : d ∈ conductors 510510) :
    d ∣ 16 ↔ d ∣ 2 := by
  have hdL := conductor_dvd_period hd
  constructor
  · intro h
    have hdle := Nat.le_of_dvd (by norm_num : 0 < 16) h
    interval_cases d <;> norm_num at *
  · intro h
    exact dvd_trans h (by norm_num)

private theorem events18 (d : ℕ) (hd : d ∈ conductors 510510) :
    d ∣ 18 ↔ d ∣ 6 := by
  have hdL := conductor_dvd_period hd
  constructor
  · intro h
    have hdle := Nat.le_of_dvd (by norm_num : 0 < 18) h
    interval_cases d <;> norm_num at *
  · intro h
    exact dvd_trans h (by norm_num)

private theorem events20 (d : ℕ) (hd : d ∈ conductors 510510) :
    d ∣ 20 ↔ d ∣ 10 := by
  have hdL := conductor_dvd_period hd
  constructor
  · intro h
    have hdle := Nat.le_of_dvd (by norm_num : 0 < 20) h
    interval_cases d <;> norm_num at *
  · intro h
    exact dvd_trans h (by norm_num)

private theorem no_event19 (d : ℕ) (hd : d ∈ conductors 510510) :
    ¬ d ∣ 19 := by
  have hdL := conductor_dvd_period hd
  have hd1 := conductor_gt_one 510510 d hd
  intro h
  have hdle := Nat.le_of_dvd (by norm_num : 0 < 19) h
  interval_cases d <;> norm_num at *

/-- The new conductor 17 releases one parameter in the old rigid twenty-site head. -/
theorem period510510_head15_forced (f : QHilbert)
    (hf : f ∈ divisorStage 510510)
    (hh : ∀ n, 0 < n → n ≤ 15 → qSequence f n = 1) :
    qSequence f 16 = 1 ∧ qSequence f 18 = qSequence f 17 ∧
      qSequence f 19 = qSequence f 17 + 1 ∧
      qSequence f 20 = qSequence f 17 + 1 := by
  rw [divisorStage_eq_dictionary 510510 (by norm_num)] at hf
  have h16 := dictionary_difference_eq _ (conductor_gt_one 510510) 16 2
    (by norm_num) (by norm_num) events16 f hf
  have h18 := dictionary_difference_eq _ (conductor_gt_one 510510) 18 6
    (by norm_num) (by norm_num) events18 f hf
  have h19 := dictionary_difference_of_no_divisor _ (conductor_gt_one 510510) 19
    (by norm_num) no_event19 f hf
  have h20 := dictionary_difference_eq _ (conductor_gt_one 510510) 20 10
    (by norm_num) (by norm_num) events20 f hf
  norm_num only [qDifference] at h16 h18 h19 h20
  rw [hh 15 (by norm_num) (by norm_num), hh 2 (by norm_num) (by norm_num),
    hh 1 (by norm_num) (by norm_num)] at h16
  rw [hh 6 (by norm_num) (by norm_num), hh 5 (by norm_num) (by norm_num)] at h18
  rw [hh 1 (by norm_num) (by norm_num)] at h19
  rw [hh 10 (by norm_num) (by norm_num), hh 9 (by norm_num) (by norm_num)] at h20
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

def headModel (x : ℝ) (n : ℕ) : ℝ :=
  if n ≤ 16 then 1 else if n ≤ 18 then x else x + 1

theorem headModel_square_completion (x : ℝ) :
    (∑ n ∈ Finset.range 20, (headModel x (n + 1)) ^ 2 / (n + 1 : ℝ) ^ 2) =
      32932869651286797001 / 20748169979939001600 +
        (39943549 / 3380259600) * (x + 17814249 / 39943549) ^ 2 := by
  norm_num [headModel, Finset.sum_range_succ]
  ring

theorem period510510_head20_energy_identity (f : QHilbert)
    (hf : f ∈ divisorStage 510510)
    (hh : ∀ n, 0 < n → n ≤ 15 → qSequence f n = 1) :
    (∑ n ∈ Finset.range 20, (qSequence f (n + 1)) ^ 2 / (n + 1 : ℝ) ^ 2) =
      32932869651286797001 / 20748169979939001600 +
        (39943549 / 3380259600) *
          (qSequence f 17 + 17814249 / 39943549) ^ 2 := by
  obtain ⟨h16, h18, h19, h20⟩ := period510510_head15_forced f hf hh
  have hm (n : ℕ) (hn : n ∈ Finset.range 20) :
      qSequence f (n + 1) = headModel (qSequence f 17) (n + 1) := by
    have hnlt := Finset.mem_range.mp hn
    by_cases hlow : n + 1 ≤ 15
    · rw [hh (n + 1) (by omega) hlow]
      simp [headModel, show n + 1 ≤ 16 by omega]
    · have hnlo : 15 ≤ n := by omega
      interval_cases n
      · change qSequence f 16 = 1
        exact h16
      · change qSequence f 17 = qSequence f 17
        rfl
      · change qSequence f 18 = qSequence f 17
        exact h18
      · change qSequence f 19 = qSequence f 17 + 1
        exact h19
      · change qSequence f 20 = qSequence f 17 + 1
        exact h20
  calc
    _ = ∑ n ∈ Finset.range 20,
        (headModel (qSequence f 17) (n + 1)) ^ 2 / (n + 1 : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hm n hn]
    _ = _ := headModel_square_completion _

/-- The entire infinite norm is above the optimized twenty-coordinate certificate. -/
theorem period510510_head15_energy_lower (f : QHilbert)
    (hf : f ∈ divisorStage 510510)
    (hh : ∀ n, 0 < n → n ≤ 15 → qSequence f n = 1) :
    (1 / zetaTwo) * (32932869651286797001 / 20748169979939001600) ≤ ‖f‖ ^ 2 := by
  have hraw : (32932869651286797001 : ℝ) / 20748169979939001600 ≤
      ∑ n ∈ Finset.range 20, (qSequence f (n + 1)) ^ 2 / (n + 1 : ℝ) ^ 2 := by
    rw [period510510_head20_energy_identity f hf hh]
    exact le_add_of_nonneg_right (by positivity)
  exact (mul_le_mul_of_nonneg_left hraw (one_div_pos.mpr zetaTwo_pos).le).trans
    (finite_raw_energy_le f 20)

/-- A small rational display bound, using the existing checked zeta normalization. -/
theorem period510510_head15_energy_gt_rational (f : QHilbert)
    (hf : f ∈ divisorStage 510510)
    (hh : ∀ n, 0 < n → n ≤ 15 → qSequence f n = 1) :
    (9649 : ℝ) / 10000 < ‖f‖ ^ 2 := by
  have h := period510510_head15_energy_lower f hf hh
  rw [one_div_mul_eq_div] at h
  have hb : ((9649 : ℝ) / 10000) * zetaTwo <
      32932869651286797001 / 20748169979939001600 := by
    calc
      _ < ((9649 : ℝ) / 10000) * (329 / 200) :=
        mul_lt_mul_of_pos_left zetaTwo_rational_bounds.2 (by norm_num)
      _ < _ := by norm_num
  exact ((lt_div_iff₀ zetaTwo_pos).mpr hb).trans_le h

end RiemannResearch.RH.QCRTGapRefinement

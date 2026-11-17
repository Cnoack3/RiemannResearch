import RiemannResearch.RH.ExactHeadOccurrenceRational
import RiemannResearch.RH.ExactHeadOccurrenceStageFive
import RiemannResearch.RH.ExactHeadOccurrenceReuseCertificates
import RiemannResearch.RH.ExactHeadOccurrenceCoefficientIntervals
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Complete cutoff-seven occurrence-energy certificate

Source: the general rational occurrence enclosure and exact finite replay.
All 209 nonterminal residues and every infinite progression tail are retained.
The comparison with cutoff five concerns only these two specific stages.
-/
noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 40000000
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadOccurrenceStageSeven
open ExactHeadOccurrenceProjection

private def boundary (i : ℕ) : ℕ :=
  [10,14,15,20,21,28,30,35,40,42,45,50,
    56,60,63,70,75,80,84,90,98,100,105,110,
    112,120,126,130,135,140,147,150,154,160,165,168,
    170,175,180,182,189,190,195,196,200].getD i 210

private theorem free_card : (freePositions 210 7).card = 45 := by decide

private theorem boundary_actual (i : ℕ) : occurrenceBoundary 210 7 i = boundary i := by
  have hm : ∀ j : Fin 45, boundary j.val ∈ freePositions 210 7 := by decide
  have hs : StrictMono (fun j : Fin 45 => boundary j.val) := by decide
  have heq := Finset.orderEmbOfFin_unique free_card hm hs
  by_cases hi : i < 45
  · have hi' : i < (freePositions 210 7).card := by rw [free_card]; exact hi
    simp only [occurrenceBoundary, dif_pos hi']
    calc
      _ = (freePositions 210 7).orderEmbOfFin free_card ⟨i,hi⟩ :=
        Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr rfl
      _ = _ := (congrFun heq ⟨i,hi⟩).symm
  · rw [occurrenceBoundary_terminal 210 7 i (by rw [free_card]; omega)]
    simp [boundary, List.getD_eq_getElem?_getD, List.getD_getElem?, hi]

private def countData (r : ℕ) : ℕ :=
  if r < 1 then 0 else
  if r < 11 then 1 else
  if r < 13 then 2 else
  if r < 17 then 3 else
  if r < 19 then 4 else
  if r < 23 then 5 else
  if r < 29 then 6 else
  if r < 31 then 7 else
  if r < 37 then 8 else
  if r < 41 then 9 else
  if r < 43 then 10 else
  if r < 47 then 11 else
  if r < 53 then 12 else
  if r < 59 then 13 else
  if r < 61 then 14 else
  if r < 67 then 15 else
  if r < 71 then 16 else
  if r < 73 then 17 else
  if r < 79 then 18 else
  if r < 83 then 19 else
  if r < 89 then 20 else
  if r < 97 then 21 else
  if r < 101 then 22 else
  if r < 103 then 23 else
  if r < 107 then 24 else
  if r < 109 then 25 else
  if r < 113 then 26 else
  if r < 121 then 27 else
  if r < 127 then 28 else
  if r < 131 then 29 else
  if r < 137 then 30 else
  if r < 139 then 31 else
  if r < 143 then 32 else
  if r < 149 then 33 else
  if r < 151 then 34 else
  if r < 157 then 35 else
  if r < 163 then 36 else
  if r < 167 then 37 else
  if r < 169 then 38 else
  if r < 173 then 39 else
  if r < 179 then 40 else
  if r < 181 then 41 else
  if r < 187 then 42 else
  if r < 191 then 43 else
  if r < 193 then 44 else
  if r < 197 then 45 else
  if r < 199 then 46 else
  if r < 209 then 47 else
  48

set_option maxHeartbeats 5000000 in
-- Kernel reduction checks all 210 finite coprime-count entries.
private theorem count_check : ∀ r : Fin 210,
    ((Finset.Icc 1 r.val).filter (fun n => Nat.gcd n 210 = 1)).card = countData r.val := by decide

private theorem target_data (r : ℕ) (hr : r < 210) :
    rationalTarget 210 r = (countData r : ℚ) - 1 := by
  unfold rationalTarget
  rw [count_check ⟨r,hr⟩]

set_option maxHeartbeats 40000000 in
-- Exact rational replay retains all 209 residues and every complete progression tail.
set_option maxRecDepth 200000 in
private theorem energy_endpoint_checks :
    (212 / 6250 : ℚ) ≤
      rationalOccurrenceEnergy 210 7 (fun r => (elementaryProgressionInterval 210 r 2).lo) ∧
    rationalOccurrenceEnergy 210 7 (fun r => (elementaryProgressionInterval 210 r 2).hi) ≤
      (853 / 25000 : ℚ) := by
  norm_num (config := { maxSteps := 10000000 })
    [rationalOccurrenceEnergy, free_card, boundary_actual, boundary,
    Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ, elementaryProgressionInterval,
    target_data, countData]

/-- Complete occurrence-energy certificate at cutoff seven, with all infinite tails. -/
theorem occurrence_energy_seven_interval :
    (212 / 6250 : ℝ) ≤ occurrenceEnergy 210 7 ∧
      occurrenceEnergy 210 7 ≤ (853 / 25000 : ℝ) := by
  have h := rationalOccurrenceEnergy_enclosure 210 7 2 (by norm_num)
  have he := energy_endpoint_checks
  constructor
  · exact (show (212 / 6250 : ℝ) ≤
        (rationalOccurrenceEnergy 210 7
          (fun r => (elementaryProgressionInterval 210 r 2).lo) : ℝ) by
          simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 he.1).trans h.1
  · exact h.2.trans (by
      simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 he.2)

/-- A certified comparison of two particular changing-period stages. -/
theorem occurrence_energy_seven_lt_five :
    occurrenceEnergy 210 7 < occurrenceEnergy 30 5 := by
  have h7 := occurrence_energy_seven_interval.2
  have h5 := ExactHeadOccurrenceStageFive.occurrence_energy_five_interval.1
  linarith

end RiemannResearch.RH.Pareto.ExactHeadOccurrenceStageSeven

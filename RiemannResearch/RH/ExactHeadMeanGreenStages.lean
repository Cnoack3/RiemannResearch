import RiemannResearch.RH.ExactHeadOccurrenceMeanBudget
import RiemannResearch.RH.ExactHeadGcdAtoms
import RiemannResearch.RH.ExactHeadOccurrencePartition
import RiemannResearch.RH.ExactHeadOccurrenceProjection
import RiemannResearch.RH.ParetoProgressionTails
import RiemannResearch.RH.ExactHeadOccurrenceStageSeven
import RiemannResearch.RH.ExactHeadOccurrenceStageFive
import RiemannResearch.RH.ExactHeadAtomStageFive
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
/-!
# Endpoint loss reverses the two-stage occurrence comparison

Source: the actual occurrence blocks and the repository's kernel certificates
at cutoffs five and seven. The endpoint remainder, rather than the smaller
occurrence energy alone, determines the comparison of these mean budgets.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
open RiemannResearch.Analysis.FiniteProfileEnergy
open ExactHeadAtomOptimizer
open RiemannResearch.RH.ExactHeadGcdAtoms

private def count (P r : ℕ) : ℕ :=
  ((Finset.Icc 1 r).filter (fun n => Nat.gcd n P = 1)).card

private theorem target_eq_count (P r : ℕ) : target P r = (count P r : ℝ) - 1 := by
  simp [target, atom, count]
set_option maxHeartbeats 5000000 in
-- Kernel reduction checks the finite block-by-residue table.
/-- At cutoff five every target in each free block equals one of its two
endpoint values, so the endpoint loss vanishes exactly. -/
theorem endpoint_remainder_five_zero : occurrenceEndpointRemainder 30 5 = 0 := by
  have hc : (freePositions 30 5).card = 7 := by decide
  have hq : ∀ i : Fin 7, ∀ r : Fin 30,
      r.val ∈ Finset.Ico (ExactHeadOccurrenceStageFive.boundary i.val)
        (ExactHeadOccurrenceStageFive.boundary (i.val+1)) →
      count 30 r.val = count 30 (ExactHeadOccurrenceStageFive.boundary i.val) ∨
        count 30 r.val = count 30 (ExactHeadOccurrenceStageFive.boundary (i.val+1)-1) := by
    decide
  unfold occurrenceEndpointRemainder
  rw [hc]
  apply Finset.sum_eq_zero
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [ExactHeadOccurrenceStageFive.boundary_actual i (by omega),
    ExactHeadOccurrenceStageFive.boundary_actual (i+1) (by omega)]
  apply Finset.sum_eq_zero
  intro r hr
  have hb : ExactHeadOccurrenceStageFive.boundary (i+1) ≤ 30 := by
    rw [← ExactHeadOccurrenceStageFive.boundary_actual (i+1) (by omega)]
    exact occurrenceBoundary_le_period 30 5 (i+1)
  have hr' : r < 30 := by have := Finset.mem_Ico.mp hr; omega
  simp only [target_eq_count]
  rcases hq ⟨i,hi'⟩ ⟨r,hr'⟩ hr with hl | hu
  · simp [hl]
  · simp [hu]

/-- The first free block alone contributes w(11)+w(12)>=2/143.
All other nonnegative terms and complete progression tails remain present. -/
theorem endpoint_remainder_seven_lower :
    (2 / 143 : ℝ) ≤ occurrenceEndpointRemainder 210 7 := by
  have hc : 1 < (freePositions 210 7).card := by decide
  have hsmall : ∀ n : Fin 14, n.val ∈ freePositions 210 7 → n.val = 10 := by decide
  have hb0 : occurrenceBoundary 210 7 0 = 10 := by
    have hle := occurrenceBoundary_first 210 7 10 (by decide)
    have hm := occurrenceBoundary_mem 210 7 0 (by omega)
    exact hsmall ⟨occurrenceBoundary 210 7 0, by omega⟩ hm
  have hb1 : occurrenceBoundary 210 7 1 = 14 := by
    have hstrict := occurrenceBoundary_strict 210 7 0 (by omega)
    rw [hb0] at hstrict
    change 10 < occurrenceBoundary 210 7 1 at hstrict
    obtain ⟨j, hj, he⟩ := exists_occurrenceBoundary 210 7 14 (by decide)
    have hj1 : 1 ≤ j := by
      by_contra hh
      have hj0 : j = 0 := by omega
      rw [hj0, hb0] at he
      omega
    have hle := occurrenceBoundary_mono 210 7 hj1
    rw [he] at hle
    by_contra hne
    have hlt : occurrenceBoundary 210 7 1 < 14 := by omega
    have h := hsmall ⟨occurrenceBoundary 210 7 1, hlt⟩
      (occurrenceBoundary_mem 210 7 1 hc)
    change occurrenceBoundary 210 7 1 = 10 at h
    omega
  have ht : target 210 10 = 0 ∧ target 210 11 = 1 ∧ target 210 12 = 1 ∧ target 210 13 = 2 := by
    have h : count 210 10 = 1 ∧ count 210 11 = 2 ∧
        count 210 12 = 2 ∧ count 210 13 = 3 := by decide
    norm_num [target_eq_count, h.1, h.2.1, h.2.2.1, h.2.2.2]
  have hb : progressionWeight 210 11 + progressionWeight 210 12 ≤
      occurrenceEndpointRemainder 210 7 := by
    have h := Finset.single_le_sum
      (s := Finset.range (freePositions 210 7).card)
      (f := fun i => ∑ r ∈ Finset.Ico (occurrenceBoundary 210 7 i)
          (occurrenceBoundary 210 7 (i+1)),
        progressionWeight 210 r *
          (target 210 (occurrenceBoundary 210 7 (i+1)-1) - target 210 r) *
          (target 210 r - target 210 (occurrenceBoundary 210 7 i)))
      (fun i hi => Finset.sum_nonneg (fun r hr => by
        have hr' := Finset.mem_Ico.mp hr
        exact mul_nonneg (mul_nonneg (progressionWeight_nonneg 210 r)
          (sub_nonneg.mpr (occurrence_target_mono 210 (by omega))))
          (sub_nonneg.mpr (occurrence_target_mono 210 hr'.1))))
      (show 0 ∈ Finset.range (freePositions 210 7).card by decide)
    change _ ≤ occurrenceEndpointRemainder 210 7 at h
    norm_num [hb0, hb1, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ,
      ht.1, ht.2.1, ht.2.2.1, ht.2.2.2] at h
    exact h
  have hw11 : (1 / 132 : ℝ) ≤ progressionWeight 210 11 := by
    rw [progressionWeight_split 210 11 (by norm_num)]
    have h := progressionWeight_nonneg 210 (11+210)
    norm_num [positiveWeight]
    linarith
  have hw12 : (1 / 156 : ℝ) ≤ progressionWeight 210 12 := by
    rw [progressionWeight_split 210 12 (by norm_num)]
    have h := progressionWeight_nonneg 210 (12+210)
    norm_num [positiveWeight]
    linarith
  linarith

/-- A lower bound valid for every shared correction at cutoff seven. -/
theorem meanGreenBudget_seven_lower (u : ℕ → ℝ) :
    (212 / 6250 + 2 / 143 : ℝ) ≤ meanGreenBudget 210 7 u := by
  have hm := meanGreenBudget_minimizes 210 7 (by norm_num) u
  have ho := ExactHeadOccurrenceStageSeven.occurrence_energy_seven_interval.1
  have ha := occurrenceEnergy_le_atomEnergy 210 7
  have he := endpoint_remainder_seven_lower
  linarith

/-- The best combined budget at five is smaller than every combined budget
at seven. This finite comparison makes no asymptotic claim. -/
theorem optimal_meanGreenBudget_five_lt_seven (u : ℕ → ℝ) :
    meanGreenBudget 30 5 (atomNormalCoefficients 30 5) < meanGreenBudget 210 7 u := by
  rw [meanGreenBudget_optimal 30 5 (by norm_num), endpoint_remainder_five_zero, add_zero]
  have h5 := ExactHeadAtomStageFive.primorial_five_energy_interval.2
  have hP : MobiusHeadGreen.greenPeriod 5 = 30 := by decide
  rw [hP] at h5
  have h7 := meanGreenBudget_seven_lower u
  linarith
end RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection

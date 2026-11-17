import RiemannResearch.RH.ExactHeadOccurrenceRational
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

/-!
# Complete cutoff-five occurrence certificates

Source: exact rational endpoint proposals checked here in Lean. The theorem
`blockMeanCertificate_sound` transfers them to the actual normal optimizer.
All 29 nonterminal residues and all infinite progression tails are retained.
These finite certificates make no uniform or asymptotic claim.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadOccurrenceStageFive
open ExactHeadOccurrenceProjection
open ExactHeadAtomOptimizer

theorem freePositions_five : freePositions 30 5 = {6,10,12,15,18,20,24} := by decide

def boundary : ℕ → ℕ
  | 0 => 6 | 1 => 10 | 2 => 12 | 3 => 15
  | 4 => 18 | 5 => 20 | 6 => 24 | _ => 30

theorem boundary_actual (i : ℕ) (hi : i ≤ 7) :
    occurrenceBoundary 30 5 i = boundary i := by
  have hc : (freePositions 30 5).card = 7 := by rw [freePositions_five]; decide
  have hm : ∀ j : Fin 7, boundary j.val ∈ freePositions 30 5 := by
    rw [freePositions_five]
    decide
  have hs : StrictMono (fun j : Fin 7 => boundary j.val) := by decide
  have heq := Finset.orderEmbOfFin_unique hc hm hs
  by_cases hi7 : i < 7
  · have hi' : i < (freePositions 30 5).card := by omega
    simp only [occurrenceBoundary, dif_pos hi']
    calc
      _ = (freePositions 30 5).orderEmbOfFin hc ⟨i,hi7⟩ :=
        Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr rfl
      _ = _ := (congrFun heq ⟨i,hi7⟩).symm
  · have hi7 : i = 7 := by omega
    subst i
    rw [occurrenceBoundary_terminal 30 5 7 (by omega)]
    rfl

private def countData (r : ℕ) : ℕ :=
  if r = 0 then 0 else if r < 7 then 1 else if r < 11 then 2 else if r < 13 then 3 else
  if r < 17 then 4 else if r < 19 then 5 else if r < 23 then 6 else if r < 29 then 7 else 8

private theorem count_check : ∀ r : Fin 30,
    ((Finset.Icc 1 r.val).filter (fun n => Nat.gcd n 30 = 1)).card = countData r.val := by decide

private theorem target_data (r : ℕ) (hr : r < 30) :
    rationalTarget 30 r = (countData r : ℚ) - 1 := by
  unfold rationalTarget
  rw [count_check ⟨r,hr⟩]

def meanLower : ℕ → ℚ
  | 0 => 6494/10000 | 1 => 14587/10000 | 2 => 26215/10000 | 3 => 32997/10000
  | 4 => 44776/10000 | 5 => 52233/10000 | 6 => 61441/10000 | _ => 0

def meanUpper : ℕ → ℚ
  | 0 => 6499/10000 | 1 => 14596/10000 | 2 => 26227/10000 | 3 => 33012/10000
  | 4 => 44796/10000 | 5 => 52252/10000 | 6 => 61458/10000 | _ => 0

set_option maxHeartbeats 20000000 in
-- Exact rational replay expands every residue and all eight finite prefix terms.
set_option maxRecDepth 100000 in
theorem mean_endpoint_checks (i : ℕ) (hi : i < 7) :
    blockMeanCertificate 30 8 (boundary i) (boundary (i+1)) (meanLower i) (meanUpper i) := by
  interval_cases i <;>
    norm_num [blockMeanCertificate, boundary, meanLower, meanUpper,
      Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ,
      elementaryProgressionInterval, target_data, countData]


/-- All seven actual block means are enclosed by exact rational endpoint tests. -/
theorem means_five_interval (i : ℕ) (hi : i < 7) :
    (meanLower i : ℝ) ≤ occurrenceBlockMean 30 5 i ∧
      occurrenceBlockMean 30 5 i ≤ (meanUpper i : ℝ) := by
  have hc : (freePositions 30 5).card = 7 := by rw [freePositions_five]; decide
  have hi' : i < (freePositions 30 5).card := by omega
  have ht := mean_endpoint_checks i hi
  rw [← boundary_actual i (by omega), ← boundary_actual (i+1) (by omega)] at ht
  have h := blockMeanCertificate_sound 30 5 8 _ _
    (occurrenceBoundary_mem 30 5 i hi') (occurrenceBoundary_strict 30 5 i hi')
    (occurrenceBoundary_le_period 30 5 (i+1)) (occurrenceBoundary_next 30 5 i)
    (occurrenceBoundary_gap 30 5 i) (meanLower i) (meanUpper i) ht
  simpa only [occurrence_fit_boundary_eq_mean 30 5 i hi'] using h

/-- Certified intervals for every active actual occurrence coefficient at cutoff five. -/
theorem coefficients_five_interval (i : ℕ) (hi : i < 7) :
    (meanLower i : ℝ) - (if i = 0 then 0 else (meanUpper (i-1) : ℝ)) ≤
        occurrenceCoefficients 30 5 (boundary i) ∧
      occurrenceCoefficients 30 5 (boundary i) ≤
        (meanUpper i : ℝ) - (if i = 0 then 0 else (meanLower (i-1) : ℝ)) := by
  have hc : (freePositions 30 5).card = 7 := by rw [freePositions_five]; decide
  have h := occurrenceCoefficients_enclosure 30 5 (by norm_num)
    (fun j => (meanLower j : ℝ)) (fun j => (meanUpper j : ℝ))
    (fun j hj => means_five_interval j (by omega)) i (by omega)
  simpa only [boundary_actual i (by omega)] using h

/-- Strict positivity of these particular coefficients, certified by rational arithmetic. -/
theorem coefficients_five_pos (n : ℕ) (hn : n ∈ freePositions 30 5) :
    0 < occurrenceCoefficients 30 5 n := by
  obtain ⟨i,hi,rfl⟩ := exists_occurrenceBoundary 30 5 n hn
  have hc : (freePositions 30 5).card = 7 := by rw [freePositions_five]; decide
  have hi' : i < 7 := by omega
  rw [boundary_actual i (by omega)]
  have h := (coefficients_five_interval i hi').1
  interval_cases i <;> norm_num [meanLower, meanUpper] at h ⊢ <;> linarith

set_option maxHeartbeats 20000000 in
-- Exact rational replay expands every residue and all eight finite prefix terms.
set_option maxRecDepth 100000 in
private theorem energy_endpoint_checks :
    (342 / 10000 : ℚ) ≤
      rationalOccurrenceEnergy 30 5 (fun r => (elementaryProgressionInterval 30 r 8).lo) ∧
    rationalOccurrenceEnergy 30 5 (fun r => (elementaryProgressionInterval 30 r 8).hi) ≤
      (3427 / 100000 : ℚ) := by
  norm_num [rationalOccurrenceEnergy, freePositions_five, boundary_actual, boundary,
    Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ, elementaryProgressionInterval,
    target_data, countData]

/-- The complete optimized occurrence energy at cutoff five, including all infinite tails. -/
theorem occurrence_energy_five_interval :
    (342 / 10000 : ℝ) ≤ occurrenceEnergy 30 5 ∧
      occurrenceEnergy 30 5 ≤ (3427 / 100000 : ℝ) := by
  have h := rationalOccurrenceEnergy_enclosure 30 5 8 (by norm_num)
  have he := energy_endpoint_checks
  constructor
  · exact (show (342 / 10000 : ℝ) ≤
        (rationalOccurrenceEnergy 30 5
          (fun r => (elementaryProgressionInterval 30 r 8).lo) : ℝ) by
          simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 he.1).trans h.1
  · exact h.2.trans (by
      simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 he.2)

end RiemannResearch.RH.Pareto.ExactHeadOccurrenceStageFive

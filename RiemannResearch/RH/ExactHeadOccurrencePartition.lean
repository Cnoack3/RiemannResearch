import RiemannResearch.RH.ExactHeadOccurrenceBlocks
import RiemannResearch.RH.ExactHeadOccurrenceCertificates
import RiemannResearch.RH.ExactHeadOccurrenceCriterion
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Canonical occurrence blocks and a complete finite gap budget

Source: the repository's actual occurrence normal equations, finite variance
identities, and signed Green criterion. Sorting the actual free positions
supplies every block endpoint, including the fixed initial interval and the
terminal endpoint P. No partition or optimizer oracle is assumed.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
open RiemannResearch.Analysis
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.Analysis.FiniteWeightedVariance
open RiemannResearch.RH.ExactHeadGcdAtoms
open ExactHeadAtomOptimizer MobiusHeadGreen

/-- Sorted actual free positions, followed by the terminal endpoint P. -/
def occurrenceBoundary (P x i : ℕ) : ℕ :=
  if hi : i < (freePositions P x).card then
    (freePositions P x).orderEmbOfFin rfl ⟨i,hi⟩
  else P

theorem occurrenceBoundary_mem (P x i : ℕ) (hi : i < (freePositions P x).card) :
    occurrenceBoundary P x i ∈ freePositions P x := by
  simpa [occurrenceBoundary, hi] using
    (freePositions P x).orderEmbOfFin_mem rfl ⟨i,hi⟩

theorem occurrenceBoundary_terminal (P x i : ℕ) (hi : (freePositions P x).card ≤ i) :
    occurrenceBoundary P x i = P := by
  simp [occurrenceBoundary, show ¬ i < (freePositions P x).card by omega]

theorem occurrenceBoundary_le_period (P x i : ℕ) :
    occurrenceBoundary P x i ≤ P := by
  by_cases hi : i < (freePositions P x).card
  · have h := (Finset.mem_Icc.mp
      (Finset.mem_filter.mp (occurrenceBoundary_mem P x i hi)).1).2
    omega
  · rw [occurrenceBoundary_terminal P x i (by omega)]

theorem occurrenceBoundary_mono (P x : ℕ) : Monotone (occurrenceBoundary P x) := by
  intro i j hij
  by_cases hj : j < (freePositions P x).card
  · have hi : i < (freePositions P x).card := lt_of_le_of_lt hij hj
    simp only [occurrenceBoundary, dif_pos hi, dif_pos hj]
    exact (freePositions P x).orderEmbOfFin rfl |>.monotone
      (show (⟨i,hi⟩ : Fin _) ≤ ⟨j,hj⟩ from hij)
  · rw [occurrenceBoundary_terminal P x j (by omega)]
    exact occurrenceBoundary_le_period P x i

theorem occurrenceBoundary_strict (P x i : ℕ) (hi : i < (freePositions P x).card) :
    occurrenceBoundary P x i < occurrenceBoundary P x (i + 1) := by
  by_cases hj : i + 1 < (freePositions P x).card
  · simp only [occurrenceBoundary, dif_pos hi, dif_pos hj]
    exact (freePositions P x).orderEmbOfFin rfl |>.strictMono
      (show (⟨i,hi⟩ : Fin _) < ⟨i+1,hj⟩ from Nat.lt_succ_self i)
  · rw [occurrenceBoundary_terminal P x (i+1) (by omega)]
    have h := Finset.mem_Icc.mp
      (Finset.mem_filter.mp (occurrenceBoundary_mem P x i hi)).1
    omega

theorem occurrenceBoundary_pos (P x i : ℕ) (hP : 0 < P) :
    1 ≤ occurrenceBoundary P x i := by
  by_cases hi : i < (freePositions P x).card
  · exact (Finset.mem_Icc.mp (Finset.mem_filter.mp
      (occurrenceBoundary_mem P x i hi)).1).1
  · rw [occurrenceBoundary_terminal P x i (by omega)]
    exact hP

theorem exists_occurrenceBoundary (P x n : ℕ) (hn : n ∈ freePositions P x) :
    ∃ i < (freePositions P x).card, occurrenceBoundary P x i = n := by
  have h : n ∈ Set.range ((freePositions P x).orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hn
  obtain ⟨i,hi⟩ := h
  refine ⟨i.val,i.isLt,?_⟩
  simpa [occurrenceBoundary, i.isLt] using hi

theorem occurrenceBoundary_first (P x n : ℕ) (hn : n ∈ freePositions P x) :
    occurrenceBoundary P x 0 ≤ n := by
  obtain ⟨i,hi,rfl⟩ := exists_occurrenceBoundary P x n hn
  exact occurrenceBoundary_mono P x (Nat.zero_le i)

theorem occurrenceBoundary_gap (P x i n : ℕ) (hn : n ∈ freePositions P x)
    (hlo : occurrenceBoundary P x i < n)
    (hhi : n < occurrenceBoundary P x (i + 1)) : False := by
  obtain ⟨j,hj,rfl⟩ := exists_occurrenceBoundary P x n hn
  have hij : i < j := by
    by_contra h
    have hm := occurrenceBoundary_mono P x (show j ≤ i by omega)
    omega
  have hm := occurrenceBoundary_mono P x (show i+1 ≤ j by omega)
  omega

theorem occurrenceBoundary_next (P x i : ℕ) :
    occurrenceBoundary P x (i + 1) ∈ freePositions P x ∨
      occurrenceBoundary P x (i + 1) = P := by
  by_cases hi : i+1 < (freePositions P x).card
  · exact Or.inl (occurrenceBoundary_mem P x (i+1) hi)
  · exact Or.inr (occurrenceBoundary_terminal P x (i+1) (by omega))

/-- Exact sum over the canonical disjoint intervals. -/
theorem occurrence_partition_sum (P x : ℕ) (hP : 0 < P) (f : ℕ → ℝ) :
    (∑ r ∈ Finset.Icc 1 (P - 1), f r) =
      (∑ r ∈ Finset.Ico 1 (occurrenceBoundary P x 0), f r) +
      ∑ i ∈ Finset.range (freePositions P x).card,
        ∑ r ∈ Finset.Ico (occurrenceBoundary P x i) (occurrenceBoundary P x (i+1)), f r := by
  have htel (k : ℕ) :
      (∑ i ∈ Finset.range k,
        ∑ r ∈ Finset.Ico (occurrenceBoundary P x i) (occurrenceBoundary P x (i+1)), f r) =
      ∑ r ∈ Finset.Ico (occurrenceBoundary P x 0) (occurrenceBoundary P x k), f r := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      exact Finset.sum_Ico_consecutive f
        (occurrenceBoundary_mono P x (Nat.zero_le k))
        (occurrenceBoundary_mono P x (Nat.le_succ k))
  rw [htel, occurrenceBoundary_terminal P x _ le_rfl,
    Finset.sum_Ico_consecutive f (occurrenceBoundary_pos P x 0 hP)
      (occurrenceBoundary_le_period P x 0)]
  congr 1

/-- Full actual occurrence error, including the constrained initial block. -/
theorem occurrenceEnergy_eq_block_variances (P x : ℕ) (hP : 0 < P) :
    occurrenceEnergy P x =
      energy (Finset.Ico 1 (occurrenceBoundary P x 0)) (progressionWeight P) (target P) +
      ∑ i ∈ Finset.range (freePositions P x).card,
        variance (Finset.Ico (occurrenceBoundary P x i) (occurrenceBoundary P x (i+1)))
          (progressionWeight P) (target P) := by
  unfold occurrenceEnergy energy
  rw [occurrence_partition_sum P x hP]
  congr 1
  · exact occurrence_initial_energy P x (occurrenceBoundary P x 0) (occurrenceBoundary_first P x)
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    exact occurrence_block_energy_eq_variance P x _ _
      (occurrenceBoundary_mem P x i hi') (occurrenceBoundary_strict P x i hi')
      (occurrenceBoundary_le_period P x (i+1)) (occurrenceBoundary_next P x i)
      (occurrenceBoundary_gap P x i)

/-- A finite arithmetic statistic: complete block mass times actual coprime oscillation. -/
def occurrenceGapBudget (P x : ℕ) : ℝ :=
  energy (Finset.Ico 1 (occurrenceBoundary P x 0)) (progressionWeight P) (target P) +
  ∑ i ∈ Finset.range (freePositions P x).card,
    FiniteWeightedVariance.mass
      (Finset.Ico (occurrenceBoundary P x i) (occurrenceBoundary P x (i+1)))
      (progressionWeight P) *
      (target P (occurrenceBoundary P x (i+1) - 1) -
        target P (occurrenceBoundary P x i)) ^ 2 / 4

/-- No smooth-gap, equidistribution, or asymptotic premise is required. -/
theorem occurrenceEnergy_le_gapBudget (P x : ℕ) (hP : 0 < P) :
    occurrenceEnergy P x ≤ occurrenceGapBudget P x := by
  rw [occurrenceEnergy_eq_block_variances P x hP]
  unfold occurrenceGapBudget
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [← occurrence_block_energy_eq_variance P x _ _
    (occurrenceBoundary_mem P x i hi') (occurrenceBoundary_strict P x i hi')
    (occurrenceBoundary_le_period P x (i+1)) (occurrenceBoundary_next P x i)
    (occurrenceBoundary_gap P x i)]
  exact occurrence_block_energy_le_oscillation P x _ _
    (occurrenceBoundary_mem P x i hi') (occurrenceBoundary_strict P x i hi')
    (occurrenceBoundary_le_period P x (i+1)) (occurrenceBoundary_next P x i)
    (occurrenceBoundary_gap P x i)

/-- Integrate the explicit block bound with the full signed Green trial. -/
theorem atomEnergy_le_gapBudget_add_green (P x : ℕ) (hP : 0 < P) (u : ℕ → ℝ) :
    atomEnergy P x ≤ occurrenceGapBudget P x +
      energy (Finset.Icc 1 (P-1)) (progressionWeight P)
        (fit P x (occurrenceCoefficients P x) - synthesis P (upperDivisors P x) u) := by
  rw [atomEnergy_eq_occurrence_add_reuse]
  exact add_le_add (occurrenceEnergy_le_gapBudget P x hP) (reuseEnergy_le_trial P x u)

/-- Conditional RH reduction. Only the uniform cofinal bound below remains
analytic: all block endpoints and occurrence coefficients are the actual ones. -/
theorem riemannHypothesis_of_cofinal_gap_green_budget (B : ℝ) (u : ℕ → ℕ → ℝ)
    (hdata : ∀ J : ℕ, ∃ x, J ≤ x ∧
      occurrenceGapBudget (greenPeriod x) x +
        energy (Finset.Icc 1 (greenPeriod x - 1)) (progressionWeight (greenPeriod x))
          (fit (greenPeriod x) x (occurrenceCoefficients (greenPeriod x) x) -
            synthesis (greenPeriod x) (upperDivisors (greenPeriod x) x) (u x)) ≤ B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_bounded_atomEnergy B
  intro J
  obtain ⟨x,hx,hbound⟩ := hdata J
  exact ⟨x,hx,(atomEnergy_le_gapBudget_add_green (greenPeriod x) x
    (lt_of_le_of_lt (Nat.zero_le x) (greenPeriod_gt x)) (u x)).trans hbound⟩

/-- The explicit level on the i-th free block. -/
def occurrenceBlockMean (P x i : ℕ) : ℝ :=
  mean (Finset.Ico (occurrenceBoundary P x i) (occurrenceBoundary P x (i+1)))
    (progressionWeight P) (target P)

theorem occurrence_fit_boundary_eq_mean (P x i : ℕ) (hi : i < (freePositions P x).card) :
    fit P x (occurrenceCoefficients P x) (occurrenceBoundary P x i) =
      occurrenceBlockMean P x i :=
  occurrence_fit_eq_block_mean P x _ _
    (occurrenceBoundary_mem P x i hi) (occurrenceBoundary_strict P x i hi)
    (occurrenceBoundary_le_period P x (i+1)) (occurrenceBoundary_next P x i)
    (occurrenceBoundary_gap P x i)

/-- Every active coefficient is an explicit difference of adjacent weighted means. -/
theorem occurrenceCoefficients_boundary (P x i : ℕ) (hP : 0 < P)
    (hi : i < (freePositions P x).card) :
    occurrenceCoefficients P x (occurrenceBoundary P x i) =
      occurrenceBlockMean P x i - if i = 0 then 0 else occurrenceBlockMean P x (i-1) := by
  rw [← fit_jump P x _ (occurrenceCoefficients P x) (occurrenceBoundary_mem P x i hi),
    occurrence_fit_boundary_eq_mean P x i hi]
  congr 1
  by_cases hi0 : i = 0
  · subst i
    rw [if_pos rfl]
    apply occurrence_fit_zero_before_first
    intro n hn
    have hn' := occurrenceBoundary_first P x n hn
    have hp := occurrenceBoundary_pos P x 0 hP
    omega
  · rw [if_neg hi0]
    have him : i - 1 < (freePositions P x).card := by omega
    have he : i-1+1 = i := by omega
    have hlt := occurrenceBoundary_strict P x (i-1) him
    rw [he] at hlt
    calc
      _ = fit P x (occurrenceCoefficients P x) (occurrenceBoundary P x (i-1)) := by
        have hg : ∀ n ∈ freePositions P x,
            occurrenceBoundary P x (i-1) < n → n < occurrenceBoundary P x i → False := by
          simpa only [he] using occurrenceBoundary_gap P x (i-1)
        apply fit_constant_on_gap P x (occurrenceBoundary P x (i-1))
          (occurrenceBoundary P x i) (occurrenceCoefficients P x) hg
          (occurrenceBoundary P x i - 1)
        have hp := occurrenceBoundary_pos P x i hP
        exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
      _ = _ := occurrence_fit_boundary_eq_mean P x (i-1) him

/-- Every explicit block level lies between its actual endpoint target values. -/
theorem occurrenceBlockMean_bounds (P x i : ℕ) (hi : i < (freePositions P x).card) :
    target P (occurrenceBoundary P x i) ≤ occurrenceBlockMean P x i ∧
      occurrenceBlockMean P x i ≤ target P (occurrenceBoundary P x (i+1)-1) := by
  let s := Finset.Ico (occurrenceBoundary P x i) (occurrenceBoundary P x (i+1))
  have hm : 0 < FiniteWeightedVariance.mass s (progressionWeight P) :=
    occurrence_block_mass_pos P _ _
      (Finset.mem_Icc.mp (Finset.mem_filter.mp (occurrenceBoundary_mem P x i hi)).1).1
      (occurrenceBoundary_strict P x i hi) (occurrenceBoundary_le_period P x (i+1))
  change target P (occurrenceBoundary P x i) ≤
      (∑ r ∈ s, progressionWeight P r * target P r) /
        FiniteWeightedVariance.mass s (progressionWeight P) ∧
    (∑ r ∈ s, progressionWeight P r * target P r) /
        FiniteWeightedVariance.mass s (progressionWeight P) ≤
      target P (occurrenceBoundary P x (i+1)-1)
  constructor
  · apply (le_div_iff₀ hm).mpr
    calc
      _ = ∑ r ∈ s, progressionWeight P r * target P (occurrenceBoundary P x i) := by
        rw [FiniteWeightedVariance.mass, ← Finset.sum_mul]
        ring
      _ ≤ _ := Finset.sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left
        (occurrence_target_mono P (Finset.mem_Ico.mp hr).1) (progressionWeight_nonneg P r))
  · apply (div_le_iff₀ hm).mpr
    calc
      _ ≤ ∑ r ∈ s,
          progressionWeight P r * target P (occurrenceBoundary P x (i+1)-1) := by
        apply Finset.sum_le_sum
        intro r hr
        apply mul_le_mul_of_nonneg_left _ (progressionWeight_nonneg P r)
        apply occurrence_target_mono P
        have := Finset.mem_Ico.mp hr
        omega
      _ = _ := by rw [FiniteWeightedVariance.mass, ← Finset.sum_mul]; ring

theorem occurrence_target_nonneg (P r : ℕ) (hr : 1 ≤ r) : 0 ≤ target P r := by
  have h := Finset.single_le_sum (s := Finset.Icc 1 r)
    (f := fun n => if Nat.gcd n P = 1 then (1 : ℝ) else 0)
    (fun n hn => by split_ifs <;> norm_num) (Finset.mem_Icc.mpr ⟨le_rfl,hr⟩)
  simp only [Nat.gcd_one_left, if_true] at h
  exact sub_nonneg.mpr h

/-- Nonnegativity is proved for the actual optimizer, not imposed as a constraint. -/
theorem occurrenceCoefficients_nonneg (P x : ℕ) (hP : 0 < P)
    (n : ℕ) (hn : n ∈ freePositions P x) :
    0 ≤ occurrenceCoefficients P x n := by
  obtain ⟨i,hi,rfl⟩ := exists_occurrenceBoundary P x n hn
  rw [occurrenceCoefficients_boundary P x i hP hi]
  have hnow := (occurrenceBlockMean_bounds P x i hi).1
  by_cases hi0 : i = 0
  · rw [if_pos hi0, sub_zero]
    exact (occurrence_target_nonneg P _ (occurrenceBoundary_pos P x i hP)).trans hnow
  · rw [if_neg hi0]
    have him : i-1 < (freePositions P x).card := by omega
    have he : i-1+1 = i := by omega
    have hprev := (occurrenceBlockMean_bounds P x (i-1) him).2
    rw [he] at hprev
    have ht := occurrence_target_mono P (Nat.sub_le (occurrenceBoundary P x i) 1)
    exact sub_nonneg.mpr (hprev.trans (ht.trans hnow))

/-- The actual occurrence fit is monotone as a consequence of its explicit solution. -/
theorem occurrence_fit_mono (P x : ℕ) (hP : 0 < P) :
    Monotone (fit P x (occurrenceCoefficients P x)) := by
  intro r s hrs
  apply Finset.sum_le_sum
  intro n hn
  apply mul_le_mul_of_nonneg_left _ (occurrenceCoefficients_nonneg P x hP n hn)
  unfold step
  split_ifs <;> norm_num <;> omega

end RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection

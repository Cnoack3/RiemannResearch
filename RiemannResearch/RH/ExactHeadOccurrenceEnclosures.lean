import RiemannResearch.RH.ExactHeadOccurrencePartition
import RiemannResearch.Analysis.FiniteWeightedVarianceCertificates
import RiemannResearch.RH.ParetoRationalWeightIntervals
import Mathlib.Tactic.Positivity

/-!
# Complete-weight enclosures for the actual occurrence optimizer

Source: the canonical occurrence block formula and finite weighted-variance
certificates. Lower and upper weight tables bound the optimized energy itself.
Signed centered sums certify block means and hence all active coefficients.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
open RiemannResearch.Analysis
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.Analysis.FiniteWeightedVariance
open ExactHeadAtomOptimizer

/-- The canonical block formula evaluated at any proposed weight vector. -/
def occurrenceWeightEnergy (P x : ℕ) (w : ℕ → ℝ) : ℝ :=
  energy (Finset.Ico 1 (occurrenceBoundary P x 0)) w (target P) +
  ∑ i ∈ Finset.range (freePositions P x).card,
    variance (Finset.Ico (occurrenceBoundary P x i) (occurrenceBoundary P x (i+1)))
      w (target P)

theorem occurrenceWeightEnergy_actual (P x : ℕ) (hP : 0 < P) :
    occurrenceWeightEnergy P x (progressionWeight P) = occurrenceEnergy P x :=
  (occurrenceEnergy_eq_block_variances P x hP).symm

/-- Monotonicity includes the change in every weighted mean, not only the weights in a fixed fit. -/
theorem occurrenceWeightEnergy_mono (P x : ℕ) (hP : 0 < P) (w v : ℕ → ℝ)
    (hw : ∀ r ∈ Finset.Icc 1 (P-1), 0 < w r)
    (hwv : ∀ r ∈ Finset.Icc 1 (P-1), w r ≤ v r) :
    occurrenceWeightEnergy P x w ≤ occurrenceWeightEnergy P x v := by
  unfold occurrenceWeightEnergy
  apply add_le_add
  · apply Finset.sum_le_sum
    intro r hr
    have hrI : r ∈ Finset.Icc 1 (P-1) := by
      have := Finset.mem_Ico.mp hr
      have := occurrenceBoundary_le_period P x 0
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    exact mul_le_mul_of_nonneg_right (hwv r hrI) (sq_nonneg _)
  · apply Finset.sum_le_sum
    intro i hi
    have hi' := Finset.mem_range.mp hi
    let s := Finset.Ico (occurrenceBoundary P x i) (occurrenceBoundary P x (i+1))
    have hs : ∀ r ∈ s, r ∈ Finset.Icc 1 (P-1) := by
      intro r hr
      have := Finset.mem_Ico.mp hr
      have := occurrenceBoundary_pos P x i hP
      have := occurrenceBoundary_le_period P x (i+1)
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hmass : 0 < FiniteWeightedVariance.mass s w := by
      apply Finset.sum_pos
      · exact fun r hr => hw r (hs r hr)
      · exact ⟨occurrenceBoundary P x i, Finset.mem_Ico.mpr
          ⟨le_rfl, occurrenceBoundary_strict P x i hi'⟩⟩
    exact variance_le_of_weights s w v (target P) (fun r hr => (hw r (hs r hr)).le)
      hmass.ne' (fun r hr => hwv r (hs r hr))

/-- Finite lower/upper weight tables certify the complete optimized energy. -/
theorem occurrenceEnergy_weight_enclosure (P x : ℕ) (hP : 0 < P)
    (lower upper : ℕ → ℝ)
    (hlower : ∀ r ∈ Finset.Icc 1 (P-1), 0 < lower r)
    (hw : ∀ r ∈ Finset.Icc 1 (P-1),
      lower r ≤ progressionWeight P r ∧ progressionWeight P r ≤ upper r) :
    occurrenceWeightEnergy P x lower ≤ occurrenceEnergy P x ∧
      occurrenceEnergy P x ≤ occurrenceWeightEnergy P x upper := by
  rw [← occurrenceWeightEnergy_actual P x hP]
  exact ⟨occurrenceWeightEnergy_mono P x hP lower (progressionWeight P) hlower
      (fun r hr => (hw r hr).1),
    occurrenceWeightEnergy_mono P x hP (progressionWeight P) upper
      (fun r hr => progressionWeight_pos P r hP (Finset.mem_Icc.mp hr).1)
      (fun r hr => (hw r hr).2)⟩

/-- A signed centered-sum certificate encloses the actual fitted value on a complete block. -/
theorem occurrence_block_fit_enclosure (P x a b : ℕ)
    (ha : a ∈ freePositions P x) (hab : a < b) (hbP : b ≤ P)
    (hb : b ∈ freePositions P x ∨ b = P)
    (hgap : ∀ n ∈ freePositions P x, a < n → n < b → False)
    (lower upper : ℕ → ℝ)
    (hw : ∀ r ∈ Finset.Ico a b,
      lower r ≤ progressionWeight P r ∧ progressionWeight P r ≤ upper r)
    (lo hi : ℝ)
    (hlo : 0 ≤ ∑ r ∈ Finset.Ico a b,
      min (lower r * (target P r - lo)) (upper r * (target P r - lo)))
    (hhi : (∑ r ∈ Finset.Ico a b,
      max (lower r * (target P r - hi)) (upper r * (target P r - hi))) ≤ 0) :
    lo ≤ fit P x (occurrenceCoefficients P x) a ∧
      fit P x (occurrenceCoefficients P x) a ≤ hi := by
  rw [occurrence_fit_eq_block_mean P x a b ha hab hbP hb hgap]
  exact mean_enclosure_of_weight_bounds _ _ _ lower upper
    (occurrence_block_mass_pos P a b
      (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1 hab hbP) hw lo hi hlo hhi

/-- The same certificate for the canonical i-th free block. -/
theorem occurrenceBlockMean_enclosure (P x i : ℕ)
    (hi : i < (freePositions P x).card) (lower upper : ℕ → ℝ)
    (hw : ∀ r ∈ Finset.Ico (occurrenceBoundary P x i) (occurrenceBoundary P x (i+1)),
      lower r ≤ progressionWeight P r ∧ progressionWeight P r ≤ upper r)
    (lo up : ℝ)
    (hlo : 0 ≤ ∑ r ∈ Finset.Ico (occurrenceBoundary P x i) (occurrenceBoundary P x (i+1)),
      min (lower r * (target P r - lo)) (upper r * (target P r - lo)))
    (hup : (∑ r ∈ Finset.Ico (occurrenceBoundary P x i) (occurrenceBoundary P x (i+1)),
      max (lower r * (target P r - up)) (upper r * (target P r - up))) ≤ 0) :
    lo ≤ occurrenceBlockMean P x i ∧ occurrenceBlockMean P x i ≤ up := by
  rw [← occurrence_fit_boundary_eq_mean P x i hi]
  exact occurrence_block_fit_enclosure P x _ _
    (occurrenceBoundary_mem P x i hi) (occurrenceBoundary_strict P x i hi)
    (occurrenceBoundary_le_period P x (i+1)) (occurrenceBoundary_next P x i)
    (occurrenceBoundary_gap P x i) lower upper hw lo up hlo hup

/-- Differences of certified adjacent means certify every active actual coefficient. -/
theorem occurrenceCoefficients_enclosure (P x : ℕ) (hP : 0 < P)
    (lower upper : ℕ → ℝ)
    (hm : ∀ i < (freePositions P x).card,
      lower i ≤ occurrenceBlockMean P x i ∧ occurrenceBlockMean P x i ≤ upper i)
    (i : ℕ) (hi : i < (freePositions P x).card) :
    lower i - (if i = 0 then 0 else upper (i-1)) ≤
        occurrenceCoefficients P x (occurrenceBoundary P x i) ∧
      occurrenceCoefficients P x (occurrenceBoundary P x i) ≤
        upper i - (if i = 0 then 0 else lower (i-1)) := by
  rw [occurrenceCoefficients_boundary P x i hP hi]
  by_cases hi0 : i = 0
  · simp only [hi0, if_true, sub_zero]
    exact hm 0 (by omega)
  · simp only [if_neg hi0]
    have hp := hm (i-1) (by omega)
    exact ⟨sub_le_sub (hm i hi).1 hp.2, sub_le_sub (hm i hi).2 hp.1⟩

end RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection

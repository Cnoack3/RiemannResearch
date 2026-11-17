import RiemannResearch.RH.ExactHeadOccurrenceCoefficientIntervals
import RiemannResearch.RH.ExactHeadAtomOptimizer
import RiemannResearch.RH.ExactHeadOccurrencePartition
import RiemannResearch.RH.ExactHeadOccurrenceBlocks
import RiemannResearch.RH.ExactHeadOccurrenceRational
import RiemannResearch.RH.ParetoRationalWeightIntervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
/-!
# Uniform oscillation-normalized radii for occurrence means

Source: the existing complete-weight rational coefficient intervals.
The lower base mass absorbs the block cardinality and period factors.
This controls certification error in units of target oscillation; it does
not prove bounded block oscillation or a cofinal mean--Green estimate.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
open RiemannResearch.Analysis.FiniteWeightedVariance
open ExactHeadAtomOptimizer
/-- The existing rational radius has no extra period or cardinality loss
after normalization by the actual block target range. -/
theorem rationalBlockMeanRadius_le_oscillation (P a b K : ℕ)
    (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ P) (hK : 0 < K) :
    rationalBlockMeanRadius P a b K ≤
      (rationalTarget P (b-1) - rationalTarget P a) / (K : ℚ)^2 := by
  have hP : 0 < P := by omega
  have hp : (0 : ℚ) < P := by exact_mod_cast hP
  have hk : (0 : ℚ) < K := by exact_mod_cast hK
  have hM : 0 < rationalBlockBaseMass P a b := by
    apply Finset.sum_pos
    · intro r hr
      exact elementaryProgressionInterval_lower_pos P r 0 hP (by
        have := Finset.mem_Ico.mp hr; omega)
    · exact ⟨a, Finset.mem_Ico.mpr ⟨le_rfl, hab⟩⟩
  have hm : ((Finset.Ico a b).card : ℚ) ≤ rationalBlockBaseMass P a b * (P : ℚ)^2 := by
    calc
      _ = ∑ r ∈ Finset.Ico a b, (1 : ℚ) := by simp
      _ ≤ ∑ r ∈ Finset.Ico a b,
          (elementaryProgressionInterval P r 0).lo * (P : ℚ)^2 := by
        apply Finset.sum_le_sum
        intro r hr
        have hr' := Finset.mem_Ico.mp hr
        have hrr : (0 : ℚ) < r := by exact_mod_cast (show 0 < r by omega)
        have hrP : (r : ℚ) ≤ P := by exact_mod_cast (show r ≤ P by omega)
        simp only [elementaryProgressionInterval, Finset.sum_range_zero, Nat.cast_zero,
          mul_zero, add_zero, zero_add]
        rw [div_mul_eq_mul_div, one_mul]
        apply (le_div_iff₀ (mul_pos hp hrr)).mpr
        nlinarith
      _ = _ := by rw [← Finset.sum_mul]; rfl
  have hR : (0 : ℚ) ≤ rationalTarget P (b-1) - rationalTarget P a := by
    apply (Rat.cast_nonneg (K := ℝ)).mp
    simp only [Rat.cast_sub, rationalTarget_cast]
    exact sub_nonneg.mpr (occurrence_target_mono P (by omega))
  unfold rationalBlockMeanRadius
  apply (div_le_div_iff₀ (mul_pos hM (sq_pos_of_pos (mul_pos hp hk)))
    (sq_pos_of_pos hk)).mpr
  have hh := mul_le_mul_of_nonneg_left hm
    (mul_nonneg hR (sq_nonneg (K : ℚ)))
  nlinarith

/-- Complete-weight means are approximated within target oscillation / K^2
uniformly over all positive blocks contained in the period. -/
theorem rationalBlockMean_error_le_oscillation (P a b K : ℕ)
    (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ P) (hK : 0 < K) :
    |mean (Finset.Ico a b) (progressionWeight P) (target P) -
      (rationalBlockMean P a b K : ℝ)| ≤
        (target P (b-1) - target P a) / (K : ℝ)^2 := by
  have h := rationalBlockMeanInterval_contains P a b K ha hab hb hK
  have hR := (Rat.cast_le (K := ℝ)).2
    (rationalBlockMeanRadius_le_oscillation P a b K ha hab hb hK)
  simp only [Rat.cast_div, Rat.cast_sub, Rat.cast_pow, Rat.cast_natCast,
    rationalTarget_cast] at hR
  change ((rationalBlockMean P a b K - rationalBlockMeanRadius P a b K : ℚ) : ℝ) ≤ _ ∧
    _ ≤ ((rationalBlockMean P a b K + rationalBlockMeanRadius P a b K : ℚ) : ℝ) at h
  simp only [Rat.cast_sub, Rat.cast_add] at h
  apply abs_le.mpr
  constructor <;> linarith [h.1, h.2]
end RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection

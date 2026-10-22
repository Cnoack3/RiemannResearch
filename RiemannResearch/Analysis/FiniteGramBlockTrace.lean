import RiemannResearch.Analysis.FiniteHilbertGram
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Full finite Gram gain versus aggregate scores and Gram trace

Source: user-provided CRT-carry memorandum, Section 5.1, and the
19 October 2026 continuation. The exact inverse-Gram energy is retained
before using Cauchy--Schwarz. This is a finite Hilbert-space bound; a
lower bound for the actual growing-family scores remains Open.

-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteHilbertGram

variable {ι H : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def blockGain {z : ι → H} (hz : LinearIndependent ℝ z) (r : H) : ℝ :=
  ∑ i, inverseCoeff hz r i * cross z r i

/-- Exact inverse-Gram gain, without replacing signed Gram entries. -/
theorem blockGain_eq_norm_sq {z : ι → H}
    (hz : LinearIndependent ℝ z) (r : H) :
    blockGain hz r =
      ‖Fintype.linearCombination ℝ z (inverseCoeff hz r)‖ ^ 2 := by
  rw [gram_quadratic]
  apply Finset.sum_congr rfl
  intro i hi
  change inverseCoeff hz r i * cross z r i =
    inverseCoeff hz r i *
      inner ℝ (z i) (Fintype.linearCombination ℝ z (inverseCoeff hz r))
  rw [inverseCoeff_normal]

theorem blockGain_nonneg {z : ι → H}
    (hz : LinearIndependent ℝ z) (r : H) : 0 ≤ blockGain hz r := by
  rw [blockGain_eq_norm_sq]
  exact sq_nonneg _

/-- Every actual score is controlled by the *same* optimized block vector. -/
theorem score_sq_le_blockGain {z : ι → H}
    (hz : LinearIndependent ℝ z) (r : H) (i : ι) :
    (cross z r i) ^ 2 ≤ ‖z i‖ ^ 2 * blockGain hz r := by
  rw [blockGain_eq_norm_sq, ← inverseCoeff_normal hz r i]
  have h := norm_inner_le_norm (𝕜 := ℝ) (z i)
    (Fintype.linearCombination ℝ z (inverseCoeff hz r))
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  simpa only [Real.norm_eq_abs, sq_abs, mul_pow] using hs

/-- Correlations need not have the same sign. The full-block trace bound
avoids replacing the inverse Gram matrix by its diagonal. -/
theorem aggregate_score_le_trace_gain {z : ι → H}
    (hz : LinearIndependent ℝ z) (r : H) :
    (∑ i, (cross z r i) ^ 2) ≤
      (∑ i, ‖z i‖ ^ 2) * blockGain hz r := by
  calc
    _ ≤ ∑ i, ‖z i‖ ^ 2 * blockGain hz r :=
      Finset.sum_le_sum (fun i hi => score_sq_le_blockGain hz r i)
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- Any certified upper bound for the complete trace yields a lower
bound for the exact full-block gain. -/
theorem blockGain_lower_of_trace_bound {z : ι → H}
    (hz : LinearIndependent ℝ z) (r : H) (T : ℝ)
    (hT : 0 < T) (htrace : (∑ i, ‖z i‖ ^ 2) ≤ T) :
    (∑ i, (cross z r i) ^ 2) / T ≤ blockGain hz r := by
  apply (div_le_iff₀ hT).mpr
  have h := aggregate_score_le_trace_gain hz r
  have hm := mul_le_mul_of_nonneg_right htrace (blockGain_nonneg hz r)
  nlinarith

end RiemannResearch.Analysis.FiniteHilbertGram

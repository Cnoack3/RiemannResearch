import RiemannResearch.RH.QCesaroEnergy
import RiemannResearch.RH.ConditionalMeanLowerGrowth
import RiemannResearch.RH.SquarefreeMobiusCesaroHeads
import RiemannResearch.Analysis.LowerLogGrowthComparability
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Measure-invariant normalized Cesàro RH reduction

Source: user's P/Q and squarefree continuation, 1 November 2026.
Both sides use the same arithmetic functions and heads; only the latent law
in their complete Cesàro energy changes. Establishing zero lower growth for
an actual cofinal legal family remains an open arithmetic obligation.
-/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QCesaroLowerGrowth
open Pareto QCesaroEnergy ZetaTwoProbability
open Analysis.Cesaro Analysis.SubpolynomialWindow Probability.ConditionalIID

theorem normalized_lowerLogGrowth_zero_iff
    (g : ℕ → ℕ → ℝ) (H c : ℕ → ℝ)
    (hH : Tendsto H atTop atTop)
    (hg : ∀ j, Summable (fun k : ℕ => conditionalWeight k * cesaro (g j) (k + 1) ^ 2)) :
    lowerLogGrowth (fun j => conditionalMeanSquare (g j) / |c j| ^ 2) H = 0 ↔
      lowerLogGrowth (fun j => qConditionalMeanSquare (g j) / |c j| ^ 2) H = 0 := by
  apply lowerLogGrowth_eq_zero_iff_of_comparable _ _ H zetaTwo (9 / (4 * zetaTwo)) hH
    (fun j => div_nonneg (conditionalMeanSquare_nonneg _) (sq_nonneg _))
    (fun j => div_nonneg (qConditionalMeanSquare_nonneg _) (sq_nonneg _))
  · apply Eventually.of_forall
    intro j
    have h := div_le_div_of_nonneg_right
      (conditionalMean_measure_comparison (g j) (hg j)).2 (sq_nonneg |c j|)
    simpa only [mul_div_assoc] using h
  · apply Eventually.of_forall
    intro j
    have he : qConditionalMeanSquare (g j) ≤
        (9 / (4 * zetaTwo)) * conditionalMeanSquare (g j) := by
      by_contra hlt
      have hmul := mul_lt_mul_of_pos_left (lt_of_not_ge hlt) zetaTwo_pos
      have heq : zetaTwo * ((9 / (4 * zetaTwo)) * conditionalMeanSquare (g j)) =
          (9 / 4 : ℝ) * conditionalMeanSquare (g j) := by
        field_simp [ne_of_gt zetaTwo_pos]
      rw [heq] at hmul
      have h := (conditionalMean_measure_comparison (g j) (hg j)).1
      nlinarith
    have h := div_le_div_of_nonneg_right he (sq_nonneg |c j|)
    simpa only [mul_div_assoc] using h

/-- Conditional research reduction with the actual Q-latent energy.
No uniform lower bound on the nonzero head amplitudes is assumed. -/
theorem riemannHypothesis_of_q_lower_growth_normalized
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (g : ℕ → ℕ → ℝ) (Y : ℕ → ℕ) (c : ℕ → ℝ)
    (hg : ∀ j, g j ∈ legalSeedSpan A) (hc : ∀ j, c j ≠ 0)
    (hhead : ∀ j n, 0 < n → n ≤ Y j → g j n = c j)
    (hY : Tendsto Y atTop atTop)
    (hsmall : lowerLogGrowth (fun j => qConditionalMeanSquare (g j) / |c j| ^ 2)
      (fun j => (Y j : ℝ)) = 0) : RiemannHypothesis := by
  apply riemannHypothesis_of_lowerLogGrowth_normalized_conditionalMean_zero
    A hA g Y c hg hc hhead hY
  exact (normalized_lowerLogGrowth_zero_iff g (fun j => (Y j : ℝ)) c
    (tendsto_natCast_atTop_atTop.comp hY)
    (fun j => legal_conditionalMeanSquare_summable A hA (hg j))).mpr hsmall

/-- The explicit Möbius exact heads from the preceding agenda may use Q.
Squarefree repair conductors are allowed by their established membership theorem;
the statement below is stronger and only needs a conductor beyond the head. -/
theorem riemannHypothesis_of_mobiusHead_q_lower_growth
    (Y D : ℕ → ℕ) (hD : ∀ j, Y j < D j)
    (hY : Tendsto Y atTop atTop)
    (hsmall : lowerLogGrowth
      (fun j => qConditionalMeanSquare (squarefreeMobiusHead (Y j) (D j)))
      (fun j => (Y j : ℝ)) = 0) : RiemannHypothesis := by
  apply riemannHypothesis_of_q_lower_growth_normalized
    ArithmeticCumulative.allPositiveSeeds (by intro a ha; exact ha)
    (fun j => squarefreeMobiusHead (Y j) (D j)) Y (fun _ => 1)
    (fun j => squarefreeMobiusHead_mem_legal (Y j) (D j) (hD j))
    (fun _ => one_ne_zero)
    (fun j n hn hnY => squarefreeMobiusHead_exact (Y j) (D j) n (hD j) hn hnY) hY
  simpa using hsmall

end RiemannResearch.RH.QCesaroLowerGrowth

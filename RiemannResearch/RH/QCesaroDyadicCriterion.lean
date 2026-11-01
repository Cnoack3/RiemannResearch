/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCesaroDyadic
import RiemannResearch.RH.QCesaroLowerGrowth
import RiemannResearch.RH.SquarefreeMobiusCesaroEnergy
import RiemannResearch.Analysis.LowerLogGrowthComparability
import Lean.Elab.Tactic.Omega

/-!
# Complete dyadic cumulative budget and RH

Source: user-provided RH Cesàro P/Q squarefree research agenda, 1 November 2026,
Priority 3. The complete dyadic budget has zero lower logarithmic growth
exactly when the complete normalized latent energy does. All RH endpoints
are conditional research reductions: the arithmetic budget premise is open.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QCesaroDyadicCriterion
open QCesaroDyadic QCesaroEnergy QCesaroLowerGrowth QUniformMixture
open Pareto ZetaTwoProbability ArithmeticCumulative
open Analysis.SubpolynomialWindow Analysis.Cesaro Probability.ConditionalIID

/-- The proposed dyadic condition is equivalent to the existing energy condition,
including arbitrary nonzero head amplitudes and cofinal lower growth. -/
theorem normalized_dyadic_lowerLogGrowth_zero_iff
    (g : ℕ → ℕ → ℝ) (Y : ℕ → ℕ) (c : ℕ → ℝ)
    (hY : Tendsto Y atTop atTop) (hc : ∀ j, c j ≠ 0)
    (hs : ∀ j, Summable (fun k => qMixtureWeight (k + 1) * cesaro (g j) (k + 1) ^ 2))
    (hhead : ∀ j n, 0 < n → n ≤ Y j → g j n = c j) :
    lowerLogGrowth (fun j => qConditionalMeanSquare (g j) / |c j| ^ 2)
        (fun j => (Y j : ℝ)) = 0 ↔
      lowerLogGrowth (fun j => dyadicCumulativeBudget (g j) (Y j + 1) / |c j| ^ 2)
        (fun j => (Y j : ℝ)) = 0 := by
  have hyR : Tendsto (fun j => (Y j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hY
  have hE (j : ℕ) : 0 ≤ qConditionalMeanSquare (g j) / |c j| ^ 2 :=
    div_nonneg (qConditionalMeanSquare_nonneg _) (sq_nonneg _)
  have hB (j : ℕ) : 0 ≤ dyadicCumulativeBudget (g j) (Y j + 1) / |c j| ^ 2 :=
    div_nonneg (dyadicCumulativeBudget_nonneg _ _) (sq_nonneg _)
  constructor
  · intro hzero
    exact lowerLogGrowth_eq_zero_of_eventually_le_mul _ _ _ (8 * zetaTwo)
      hyR hB hE (Eventually.of_forall (fun j =>
        (normalized_dyadic_energy_bounds (g j) (c j) (Y j) (hc j) (hs j) (hhead j)).1))
      hzero
  · intro hzero
    exact lowerLogGrowth_eq_zero_of_eventually_le_add_mul _ _ _ 1 (2 / zetaTwo)
      hyR hE hB (Eventually.of_forall (fun j =>
        (normalized_dyadic_energy_bounds (g j) (c j) (Y j) (hc j) (hs j) (hhead j)).2))
      hzero

/-- The same complete block budget characterizes zero lower growth for P. -/
theorem normalized_p_dyadic_lowerLogGrowth_zero_iff
    (g : ℕ → ℕ → ℝ) (Y : ℕ → ℕ) (c : ℕ → ℝ)
    (hY : Tendsto Y atTop atTop) (hc : ∀ j, c j ≠ 0)
    (hs : ∀ j, Summable (fun k => conditionalWeight k * cesaro (g j) (k + 1) ^ 2))
    (hhead : ∀ j n, 0 < n → n ≤ Y j → g j n = c j) :
    lowerLogGrowth (fun j => conditionalMeanSquare (g j) / |c j| ^ 2)
        (fun j => (Y j : ℝ)) = 0 ↔
      lowerLogGrowth (fun j => dyadicCumulativeBudget (g j) (Y j + 1) / |c j| ^ 2)
        (fun j => (Y j : ℝ)) = 0 :=
  (normalized_lowerLogGrowth_zero_iff g (fun j => (Y j : ℝ)) c
    (tendsto_natCast_atTop_atTop.comp hY) hs).trans
    (normalized_dyadic_lowerLogGrowth_zero_iff g Y c hY hc
      (fun j => (conditionalMean_summable_iff (g j)).mp (hs j)) hhead)

/-- Conditional research reduction. The only remaining analytic growth input
is the actual complete normalized cumulative-square block budget. -/
theorem riemannHypothesis_of_dyadic_cumulative_lower_growth
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (g : ℕ → ℕ → ℝ) (Y : ℕ → ℕ) (c : ℕ → ℝ)
    (hg : ∀ j, g j ∈ legalSeedSpan A) (hc : ∀ j, c j ≠ 0)
    (hhead : ∀ j n, 0 < n → n ≤ Y j → g j n = c j)
    (hY : Tendsto Y atTop atTop)
    (hsmall : lowerLogGrowth
      (fun j => dyadicCumulativeBudget (g j) (Y j + 1) / |c j| ^ 2)
      (fun j => (Y j : ℝ)) = 0) : RiemannHypothesis := by
  apply riemannHypothesis_of_q_lower_growth_normalized A hA g Y c hg hc hhead hY
  exact (normalized_dyadic_lowerLogGrowth_zero_iff g Y c hY hc
    (fun j => (conditionalMean_summable_iff (g j)).mp
      (legal_conditionalMeanSquare_summable A hA (hg j))) hhead).mpr hsmall

/-- Explicit Möbius exact heads: a squarefree repair conductor retains the
already established literal squarefree support. -/
theorem riemannHypothesis_of_mobiusHead_dyadic_lower_growth
    (Y D : ℕ → ℕ) (hD : ∀ j, Y j < D j)
    (hY : Tendsto Y atTop atTop)
    (hsmall : lowerLogGrowth
      (fun j => dyadicCumulativeBudget (squarefreeMobiusHead (Y j) (D j)) (Y j + 1))
      (fun j => (Y j : ℝ)) = 0) : RiemannHypothesis := by
  apply riemannHypothesis_of_dyadic_cumulative_lower_growth
    allPositiveSeeds (by intro a ha; exact ha)
    (fun j => squarefreeMobiusHead (Y j) (D j)) Y (fun _ => 1)
    (fun j => squarefreeMobiusHead_mem_legal (Y j) (D j) (hD j))
    (fun _ => one_ne_zero)
    (fun j n hn hnY => squarefreeMobiusHead_exact (Y j) (D j) n (hD j) hn hnY) hY
  simpa using hsmall


/-- Exact signed arithmetic expression for the complete block budget.
The square is taken only after all Möbius and both repair terms are combined. -/
theorem meanNeutral_dyadic_budget_exact (H D E N : ℕ)
    (hH : 0 < H) (hD : H < D) (hDE : D < E) (hN : 0 < N) :
    dyadicCumulativeBudget (meanNeutralMobiusHead H D E) N =
      ∑' k, ∑ i ∈ Finset.range (N * 2 ^ k),
        meanNeutralMobiusRemainder H D E (N * 2 ^ k + i) ^ 2 /
          ((N * 2 ^ k : ℕ) : ℝ) ^ 4 := by
  apply tsum_congr
  intro k
  apply Finset.sum_congr rfl
  intro i _
  rw [meanNeutralMobiusHead_cumulative H D E _ hH hD hDE
    (by have := Nat.mul_pos hN (pow_pos (by decide : 0 < (2 : ℕ)) k); omega)]

/-- Explicit signed two-repair, mean-neutral family. Choosing both repair
conductors squarefree gives the existing legal squarefree-conductor family.
The new premise still requires signed cumulative cancellation across scales. -/
theorem riemannHypothesis_of_meanNeutral_dyadic_lower_growth
    (Y D E : ℕ → ℕ) (hY0 : ∀ j, 0 < Y j)
    (hD : ∀ j, Y j < D j) (hDE : ∀ j, D j < E j)
    (hY : Tendsto Y atTop atTop)
    (hsmall : lowerLogGrowth
      (fun j => dyadicCumulativeBudget (meanNeutralMobiusHead (Y j) (D j) (E j))
        (Y j + 1)) (fun j => (Y j : ℝ)) = 0) : RiemannHypothesis := by
  have hg (j : ℕ) : meanNeutralMobiusHead (Y j) (D j) (E j) ∈
      legalSeedSpan allPositiveSeeds := by
    change mobiusRepairWeightLeft (Y j) (D j) (E j) • squarefreeMobiusHead (Y j) (D j) +
      mobiusRepairWeightRight (Y j) (D j) (E j) • squarefreeMobiusHead (Y j) (E j) ∈ _
    exact (legalSeedSpan allPositiveSeeds).add_mem
      ((legalSeedSpan allPositiveSeeds).smul_mem _
        (squarefreeMobiusHead_mem_legal (Y j) (D j) (hD j)))
      ((legalSeedSpan allPositiveSeeds).smul_mem _
        (squarefreeMobiusHead_mem_legal (Y j) (E j) ((hD j).trans (hDE j))))
  apply riemannHypothesis_of_dyadic_cumulative_lower_growth
    allPositiveSeeds (by intro a ha; exact ha)
    (fun j => meanNeutralMobiusHead (Y j) (D j) (E j)) Y (fun _ => 1)
    hg (fun _ => one_ne_zero)
    (fun j n hn hnY => meanNeutralMobiusHead_exact (Y j) (D j) (E j)
      (hY0 j) (hD j) (hDE j) n hn hnY) hY
  simpa using hsmall

end RiemannResearch.RH.QCesaroDyadicCriterion

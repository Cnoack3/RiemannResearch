/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QNormalRepairMellinObstruction
import RiemannResearch.Analysis.SubpolynomialWindowGrowth
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip

/-!
# Subpolynomial target normal repair cost implies RH

Source: constructive-approximants continuation agenda, 24 October 2026.
This criterion concerns the actual signed target normal cost. Feasible normal
equations prove its nonnegativity. Neither boundedness nor subpolynomial growth
of the arithmetic cost is asserted here; that provider remains an open input.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QNormalRepairMellinObstruction

open Analysis.FiniteHilbertGram Analysis.FiniteConstrainedProjection
open Analysis.FiniteFeasibleGramRepair Analysis.SubpolynomialWindow
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeHeadRepair

/-- Cofinal physical heads and subpolynomial growth of their exact target
normal repair costs suffice for the actual Riemann hypothesis. -/
theorem riemannHypothesis_of_subpolynomial_normal_cost
    (J M : ℕ → ℕ) (D : ∀ j, Fin (J j) → ℕ)
    (hD : ∀ j i, 0 < D j i)
    (hv : ∀ j, LinearIndependent ℝ (fun i => qResidue (D j i)))
    (d : ∀ j, Fin (M j) → ℝ)
    (hn : ∀ j i, inner ℝ (projectedRow (hv j) (headObservation (M j)) i)
      (Fintype.linearCombination ℝ (projectedRow (hv j) (headObservation (M j))) (d j)) =
        headMismatch (hv j) (headObservation (M j)) qOne i)
    (hM : Tendsto (fun j => ((M j + 1 : ℕ) : ℝ)) atTop atTop)
    (hsub : Tendsto (fun j =>
      Real.log (1 + normalCost (D j) (hv j) (M j) (d j)) /
        Real.log ((M j + 1 : ℕ) : ℝ)) atTop (𝓝 0)) :
    RiemannHypothesis := by
  let C : ℕ → ℝ := fun j => normalCost (D j) (hv j) (M j) (d j)
  have hC : ∀ j, 0 ≤ C j := by
    intro j
    have he := normal_energy (projectedRow (hv j) (headObservation (M j)))
      (headMismatch (hv j) (headObservation (M j)) qOne) (d j) (hn j)
    change ‖Fintype.linearCombination ℝ
      (projectedRow (hv j) (headObservation (M j))) (d j)‖ ^ 2 = C j at he
    rw [← he]
    exact sq_nonneg _
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hslt hz
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at hslt
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hc : 0 < ((2 * s.re - 1) / ‖s‖ ^ 2) / zetaTwo :=
    div_pos (div_pos (by linarith) (pow_pos (norm_pos_iff.mpr hs0) 2)) zetaTwo_pos
  have ha : 0 < 2 * s.re - 1 := by linarith
  have hfloor : ∀ᶠ j : ℕ in atTop,
      (((2 * s.re - 1) / ‖s‖ ^ 2) / zetaTwo) *
        ((M j + 1 : ℕ) : ℝ) ^ (2 * s.re - 1) ≤ C j + 1 := by
    apply Filter.Eventually.of_forall
    intro j
    have h := normal_repair_cost_power_lower (D j) (hD j) (hv j) (M j) (d j)
      (hn j) s hs hs1 hz
    change (((2 * s.re - 1) / ‖s‖ ^ 2) *
      ((M j + 1 : ℕ) : ℝ) ^ (2 * s.re - 1)) / zetaTwo - 1 ≤ C j at h
    calc
      _ = (((2 * s.re - 1) / ‖s‖ ^ 2) *
          ((M j + 1 : ℕ) : ℝ) ^ (2 * s.re - 1)) / zetaTwo := by ring
      _ ≤ C j + 1 := by linarith only [h]
  exact no_positive_power_floor (fun j => ((M j + 1 : ℕ) : ℝ)) C 1
    (((2 * s.re - 1) / ‖s‖ ^ 2) / zetaTwo) (2 * s.re - 1)
    hM hC (by norm_num) hc ha hsub hfloor

/-- The rank-free directional formulation needs no separately supplied normal
solutions. Subpolynomial nonnegative budgets themselves imply RH. -/
theorem riemannHypothesis_of_subpolynomial_directional_budgets
    (J M : ℕ → ℕ) (D : ∀ j, Fin (J j) → ℕ)
    (hD : ∀ j i, 0 < D j i)
    (hv : ∀ j, LinearIndependent ℝ (fun i => qResidue (D j i)))
    (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hdual : ∀ j (c : Fin (M j) → ℝ),
      (∑ i, c i * headMismatch (hv j) (headObservation (M j)) qOne i) ^ 2 ≤
        B j * ‖Fintype.linearCombination ℝ
          (projectedRow (hv j) (headObservation (M j))) c‖ ^ 2)
    (hM : Tendsto (fun j => ((M j + 1 : ℕ) : ℝ)) atTop atTop)
    (hsub : Tendsto (fun j => Real.log (1 + B j) /
      Real.log ((M j + 1 : ℕ) : ℝ)) atTop (𝓝 0)) : RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hslt hz
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at hslt
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hc : 0 < ((2 * s.re - 1) / ‖s‖ ^ 2) / zetaTwo :=
    div_pos (div_pos (by linarith) (pow_pos (norm_pos_iff.mpr hs0) 2)) zetaTwo_pos
  have ha : 0 < 2 * s.re - 1 := by linarith
  have hfloor : ∀ᶠ j : ℕ in atTop,
      (((2 * s.re - 1) / ‖s‖ ^ 2) / zetaTwo) *
        ((M j + 1 : ℕ) : ℝ) ^ (2 * s.re - 1) ≤ B j + 1 := by
    apply Filter.Eventually.of_forall
    intro j
    have h := directional_budget_power_lower (D j) (hD j) (hv j) (M j) (B j)
      (hB j) (hdual j) s hs hs1 hz
    calc
      _ = (((2 * s.re - 1) / ‖s‖ ^ 2) *
          ((M j + 1 : ℕ) : ℝ) ^ (2 * s.re - 1)) / zetaTwo := by ring
      _ ≤ B j + 1 := by linarith only [h]
  exact no_positive_power_floor (fun j => ((M j + 1 : ℕ) : ℝ)) B 1
    (((2 * s.re - 1) / ‖s‖ ^ 2) / zetaTwo) (2 * s.re - 1)
    hM hB (by norm_num) hc ha hsub hfloor

end RiemannResearch.RH.QNormalRepairMellinObstruction

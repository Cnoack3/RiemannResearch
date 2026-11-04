/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreePrimorialCofinality
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.Analysis.ResidualPrimeGain
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Relative gains of actual squarefree primorial projections

Source: Bagchi, Proc. Indian Acad. Sci. Math. Sci. 116 (2006), 137-146,
Remark 8, DOI 10.1007/BF02829783, supplies the squarefree closure criterion.
Finite accounting is the standard Hilbert projection theorem, already
formalized in QSquarefreePrimorialCofinality. Euler's prime reciprocal
divergence supplies the scalar comparison in ResidualPrimeGain.

The repository's period at index n is primorial(n+3), so the incoming
prime at a nontrivial transition is n+4. This is a cutoff index rather
than the ordinal prime index used in the accompanying research document.
The identities and equivalence are unconditional. Each RH consumer
is a conditional research reduction: actual gain divergence or its
reciprocal-prime lower bound remains Open.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QPrimorialRelativeGain
open ZetaTwoHilbert QSquarefreePrimorialCofinality
open RiemannResearch.Analysis.ResidualGain

/-- Complete squared gain when the cutoff changes from n+3 to n+4. -/
def gain (n : ℕ) : ℝ :=
  ‖primorialOptimizer (n + 1) - primorialOptimizer n‖ ^ 2

def relativeGain (n : ℕ) : ℝ := gain n / primorialError n

theorem error_step (n : ℕ) :
    primorialError n = primorialError (n + 1) + gain n :=
  primorial_error_step n

theorem relativeGain_nonneg (n : ℕ) : 0 ≤ relativeGain n :=
  div_nonneg (sq_nonneg _) (primorialError_pos n).le

theorem relativeGain_lt_one (n : ℕ) : relativeGain n < 1 := by
  unfold relativeGain
  apply (div_lt_iff₀ (primorialError_pos n)).mpr
  have hs := error_step n
  have hp := primorialError_pos (n + 1)
  linarith

theorem gain_eq_error_mul_relativeGain (n : ℕ) :
    gain n = primorialError n * relativeGain n := by
  unfold relativeGain
  field_simp [ne_of_gt (primorialError_pos n)]

theorem error_relativeGain_step (n : ℕ) :
    primorialError (n + 1) = primorialError n * (1 - relativeGain n) := by
  have hs := error_step n
  rw [gain_eq_error_mul_relativeGain] at hs
  nlinarith

/-- Exact finite identity with the full initial residual energy retained. -/
theorem error_eq_product (n : ℕ) :
    primorialError n = primorialError 0 *
      ∏ j ∈ Finset.range n, (1 - relativeGain j) :=
  recurrence_eq_mul_product error_relativeGain_step n

theorem error_eq_initial_sub_gain_sum (n : ℕ) :
    primorialError n = primorialError 0 - ∑ j ∈ Finset.range n, gain j := by
  have h := recurrence_eq_initial_sub_sum error_relativeGain_step n
  simpa only [← gain_eq_error_mul_relativeGain] using h

theorem error_le_exp_neg_gain_sum (n : ℕ) :
    primorialError n ≤ primorialError 0 *
      Real.exp (-(∑ j ∈ Finset.range n, relativeGain j)) := by
  rw [error_eq_product]
  exact mul_le_mul_of_nonneg_left
    (survivalProduct_le_exp_neg_sum (fun j => (relativeGain_lt_one j).le) n)
    (primorialError_pos 0).le

/-- An actual arithmetic closure criterion, not a provider of divergent gains. -/
theorem closure_iff_relativeGain_not_summable :
    qOne ∈ ZetaTwoProbability.qSquarefreeCRTSpan.topologicalClosure ↔
      ¬ Summable relativeGain :=
  primorialError_tendsto_zero_iff.symm.trans
    (residual_tendsto_zero_iff_not_summable (primorialError_pos 0)
      relativeGain_nonneg relativeGain_lt_one error_relativeGain_step)

theorem riemannHypothesis_of_relativeGain_not_summable
    (h : ¬ Summable relativeGain) : RiemannHypothesis := by
  apply ZetaTwoParetoTransfer.riemannHypothesis_of_qOne_mem_squarefree_closure
  rw [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
  exact closure_iff_relativeGain_not_summable.mpr h

/-- Conditional research reduction. The lower bound is the Open arithmetic input.
The index n+4 is the newly admitted prime, not the ordinal number of a prime. -/
theorem riemannHypothesis_of_prime_gain_lower {c : ℝ} (hc : 0 < c)
    (hlower : ∀ n, (n + 4).Prime →
      c / ((n + 4 : ℕ) : ℝ) ≤ relativeGain n) : RiemannHypothesis :=
  riemannHypothesis_of_relativeGain_not_summable
    (not_summable_of_shifted_prime_lower 4 hc relativeGain_nonneg hlower)

/-- A direct block-energy hypothesis avoids any ambiguity about relative gains. -/
theorem riemannHypothesis_of_prime_energy_gain {c : ℝ} (hc : 0 < c)
    (hlower : ∀ n, (n + 4).Prime →
      c / ((n + 4 : ℕ) : ℝ) * primorialError n ≤ gain n) : RiemannHypothesis := by
  apply riemannHypothesis_of_prime_gain_lower hc
  intro n hn
  exact (le_div_iff₀ (primorialError_pos n)).mpr (hlower n hn)

end RiemannResearch.RH.QPrimorialRelativeGain

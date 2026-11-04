/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.QSquarefreeMultiplierRigidity
import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# A prime-product legality criterion for the actual projection displacement

Source: the user-provided final paper's multiplier rigidity, November 4, 2026,
combined with the existing checked displacement-boundedness RH reduction.

**Conditional research reduction.** The assertion that each actual product
`d g_p` belongs to the closed squarefree span is an OPEN arithmetic premise.
It is not inferred from CRT algebra density, Hilbert-norm bounds, or cyclicity.
The equivalence below identifies it exactly with zero target residual; the
following corollary obtains Mathlib's RH when that premise is supplied.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreePrimeProductCriterion
open ZetaTwoHilbert ZetaTwoOptimizerStage ArithmeticCumulative
open QSquarefreeMultiplierRigidity QSquarefreeDisplacementRigidity

/-- OPEN arithmetic condition: every prime product of the actual displacement
has an actual legal Q-Hilbert realization. -/
def DisplacementPrimeProductsLegal : Prop :=
  ∀ p : ℕ, p.Prime → ∃ f : QHilbert,
    f ∈ closure ∧ ∀ n,
      qSequence f n = qSequence displacement n * residueFraction p n

theorem displacement_bounded_of_prime_products
    (hproducts : DisplacementPrimeProductsLegal) :
    ∀ n : ℕ, |qSequence displacement n| ≤ |qSequence displacement 1| := by
  have hc := constant_of_prime_products_mem (qSequence displacement) hproducts
  intro n
  cases n with
  | zero =>
      simpa only [qSequence_zero, abs_zero] using abs_nonneg (qSequence displacement 1)
  | succ n =>
      rw [hc (n+1) (by omega)]

/-- Exact conditional reduction; its prime-product side remains open. -/
theorem residual_zero_iff_displacement_prime_products :
    limitingResidual = 0 ↔ DisplacementPrimeProductsLegal := by
  constructor
  · intro hr p hp
    have hd := displacement_eq_zero_of_residual_eq_zero hr
    refine ⟨0, closure.zero_mem, ?_⟩
    intro n
    rw [hd]
    have hz : qSequence (0 : QHilbert) n = 0 :=
      congrFun (map_zero qSequenceLinear) n
    rw [hz, zero_mul]
  · intro hproducts
    exact residual_eq_zero_of_displacement_physically_bounded
      |qSequence displacement 1| (displacement_bounded_of_prime_products hproducts)

/-- Mathlib RH follows from the explicitly displayed OPEN prime-product premise. -/
theorem riemannHypothesis_of_displacement_prime_products
    (hproducts : DisplacementPrimeProductsLegal) : RiemannHypothesis := by
  exact riemannHypothesis_of_displacement_bounded |qSequence displacement 1|
    (displacement_bounded_of_prime_products hproducts)

end RiemannResearch.RH.QSquarefreePrimeProductCriterion

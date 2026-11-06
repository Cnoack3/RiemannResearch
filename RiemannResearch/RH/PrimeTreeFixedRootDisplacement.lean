/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.PrimeTreeMertensImplication
import RiemannResearch.RH.MertensBaezDuarteConverse
import RiemannResearch.RH.QSquarefreeDisplacementRigidity

/-!
# The exact fixed-root route to matched projection agreement

Source: the user's request to follow the internally proved fixed-root implication,
6 November 2026. The analytic RH implication is internal. The reverse passage
from RH to squarefree physical approximation still uses the explicitly named
Báez-Duarte approximation proposition, as recorded in MertensBaezDuarteConverse.
Its mathematical source is L. Báez-Duarte, A strengthening of the Nyman-Beurling
criterion for the Riemann hypothesis, Rend. Mat. Acc. Lincei 14 (2003), 5–11;
the constructive version is Proposition 3.1 of https://arxiv.org/abs/math/0205003.

This is a conditional research reduction. Neither the ordinary Möbius subtree
power bounds nor a checked provider for BaezDuarteMobiusApproximation is supplied
here. In particular, the power bounds concern ordinary Möbius weights, not the
Möbius transforms of displacement increments.
-/

namespace RiemannResearch.RH.PrimeTreeFixedRootDisplacement
open RiemannResearch.NumberTheory.PrimeNumberTheorem.FixedPrimeCylinder
open QSquarefreeDisplacementRigidity

/-- The precise route requested by the user, retaining both analytic premises. -/
theorem displacement_eq_zero_of_fixedRoot_power_forall
    (r : ℕ) (hr : Squarefree r)
    (h : ∀ ε : ℝ, 0 < ε → PowerBound (1 / 2 + ε) (orderedSubtree r))
    (hBD : Pareto.BaezDuarte.BaezDuarteMobiusApproximation) :
    displacement = 0 :=
  displacement_eq_zero_of_residual_eq_zero
    (QMertensFirstMoment.residual_zero_of_baezDuarte_and_riemannHypothesis
      hBD (riemannHypothesis_of_orderedSubtree_power_forall hr h))

end RiemannResearch.RH.PrimeTreeFixedRootDisplacement

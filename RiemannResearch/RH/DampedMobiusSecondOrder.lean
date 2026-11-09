/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.DampedMobiusCoefficients
import RiemannResearch.Analysis.ExponentialQuadraticRemainder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Second-order damped Mobius coefficients

Source: continuation of the user-provided reciprocal-density report,
8 November 2026. Prime-power directions retain their von Mangoldt
first derivative; the quadratic envelope is unconditional.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto

/-- Every prime-power direction has derivative log p and a uniform quadratic remainder. -/
theorem dampedDivisorCoefficient_prime_pow_second_order
    {ε : ℝ} (hε : 0 ≤ ε) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    |dampedDivisorCoefficient ε (p ^ (k + 1)) - ε * Real.log p| ≤
      ε ^ 2 * (Real.log p) ^ 2 / 2 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hx := Real.exp_neg_first_order_remainder (ε * Real.log p) (mul_nonneg hε hlog)
  rw [dampedDivisorCoefficient_prime_pow ε hp k, Real.rpow_def_of_pos hp0,
    show Real.log (p : ℝ) * -ε = -(ε * Real.log p) by ring]
  rw [abs_of_nonpos (by linarith [hx.1] :
    1 - Real.exp (-(ε * Real.log p)) - ε * Real.log p ≤ 0)]
  nlinarith [hx.2]


end RiemannResearch.RH.Pareto

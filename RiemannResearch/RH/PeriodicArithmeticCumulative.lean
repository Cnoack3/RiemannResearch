/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ArithmeticCumulativeBasic
import Lean.Elab.Tactic.Omega
/-!
# Periodic cumulative sums with zero period mean

Source: user's weighted-CRT manuscript, 1 November 2026,
"The exact arithmetic measure on a periodic primitive". This elementary
shift identity is consumed by SquarefreeWeightedPrimitives.
-/
namespace RiemannResearch.RH.ArithmeticCumulative
theorem cumulative_periodic_of_zero_period (g : ℕ → ℝ) (L : ℕ)
    (hp : ∀ n, g (n + L) = g n) (hz : cumulative g L = 0) :
    ∀ n, cumulative g (n + L) = cumulative g n := by
  intro n
  induction n with
  | zero => simpa using hz
  | succ n ih =>
    rw [show n + 1 + L = (n + L) + 1 by omega,
      cumulative_succ, ih, cumulative_succ]
    rw [show n + L + 1 = n + 1 + L by omega, hp (n + 1)]
end RiemannResearch.RH.ArithmeticCumulative

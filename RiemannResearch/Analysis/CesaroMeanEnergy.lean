/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.CesaroFiniteCalculus
import RiemannResearch.RH.ConditionalUniformMixture
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Weighted square energy of finite Cesàro means

The exact conditional weights and summability for bounded means are independent
of Mellin transforms and zeta applications. These declarations were moved
unchanged from `MellinCesaroSummability`.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Analysis.Cesaro
open RH.ArithmeticCumulative

/-- Positive latent-endpoint weights in zero-based sequence coordinates. -/
def conditionalWeight (k : ℕ) : ℝ := mixtureWeight (k + 1)

theorem conditionalWeight_pos (k : ℕ) : 0 < conditionalWeight k := by
  unfold conditionalWeight mixtureWeight
  positivity

/-- Each bounded arithmetic function has a summable conditional-mean square energy. -/
theorem bounded_mean_energy_summable (F : ℕ → ℂ) (B : ℝ)
    (hB : ∀ n, 0 < n → ‖F n‖ ≤ B) :
    Summable (fun k : ℕ => conditionalWeight k * ‖mean F (k + 1)‖ ^ 2) := by
  have hB0 : 0 ≤ B := (norm_nonneg (F 1)).trans (hB 1 (by omega))
  apply (hasSum_mixtureWeight.summable.mul_right (B ^ 2)).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (conditionalWeight_pos k).le (sq_nonneg _))]
  apply mul_le_mul_of_nonneg_left _ (conditionalWeight_pos k).le
  have h := mean_norm_le F B hB (k + 1) (Nat.succ_pos k)
  nlinarith [norm_nonneg (mean F (k + 1))]

end RiemannResearch.Analysis.Cesaro

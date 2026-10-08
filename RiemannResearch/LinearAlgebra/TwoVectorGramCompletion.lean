/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact two-vector Gram completion

Source: user-provided optimizer-cancellation argument, 8 October 2026.
The primary equality retains the signed Gram cross term and the full
orthogonal remainder. Its intended application is the inverse-square
Möbius dual block at conductors four and nine.
-/

namespace RiemannResearch.LinearAlgebra
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Exact square completion for the normalized Gram block
`[[30,5],[5,158]] / Z`. -/
theorem gram30_5_158_completion (x u v : H) (Z L₄ L₉ : ℝ)
    (hZ : 0 < Z)
    (hu : inner ℝ u u = 30 / Z)
    (huv : inner ℝ u v = 5 / Z)
    (hv : inner ℝ v v = 158 / Z)
    (hxu : inner ℝ x u = L₄ / Z)
    (hxv : inner ℝ x v = L₉ / Z) :
    ‖x‖ ^ 2 = (158 * L₄ ^ 2 - 10 * L₄ * L₉ + 30 * L₉ ^ 2) /
        (4715 * Z) +
      ‖x - (((158 * L₄ - 5 * L₉) / 4715) • u +
        ((30 * L₉ - 5 * L₄) / 4715) • v)‖ ^ 2 := by
  let α : ℝ := (158 * L₄ - 5 * L₉) / 4715
  let β : ℝ := (30 * L₉ - 5 * L₄) / 4715
  have hvu : inner ℝ v u = 5 / Z := by rw [real_inner_comm, huv]
  have hpair : inner ℝ x (α • u + β • v) =
      α * (L₄ / Z) + β * (L₉ / Z) := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hxu, hxv]
  have hnorm : ‖α • u + β • v‖ ^ 2 =
      α ^ 2 * (30 / Z) + 2 * α * β * (5 / Z) + β ^ 2 * (158 / Z) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hu, huv, hvu, hv]
    ring
  have halg : 2 * (α * (L₄ / Z) + β * (L₉ / Z)) -
      (α ^ 2 * (30 / Z) + 2 * α * β * (5 / Z) + β ^ 2 * (158 / Z)) =
      (158 * L₄ ^ 2 - 10 * L₄ * L₉ + 30 * L₉ ^ 2) / (4715 * Z) := by
    dsimp only [α, β]
    field_simp [ne_of_gt hZ]
    <;> ring
  have he := norm_sub_sq_real x (α • u + β • v)
  rw [hpair, hnorm] at he
  change ‖x‖ ^ 2 = _ + ‖x - (α • u + β • v)‖ ^ 2
  linarith

/-- The lower bound is a consequence of the exact remainder identity. -/
theorem gram30_5_158_lower_bound (x u v : H) (Z L₄ L₉ : ℝ)
    (hZ : 0 < Z)
    (hu : inner ℝ u u = 30 / Z)
    (huv : inner ℝ u v = 5 / Z)
    (hv : inner ℝ v v = 158 / Z)
    (hxu : inner ℝ x u = L₄ / Z)
    (hxv : inner ℝ x v = L₉ / Z) :
    (158 * L₄ ^ 2 - 10 * L₄ * L₉ + 30 * L₉ ^ 2) / (4715 * Z) ≤ ‖x‖ ^ 2 := by
  rw [gram30_5_158_completion x u v Z L₄ L₉ hZ hu huv hv hxu hxv]
  exact le_add_of_nonneg_right (sq_nonneg _)

end
end RiemannResearch.LinearAlgebra

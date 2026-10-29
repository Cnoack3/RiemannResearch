/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Elementary normal equations for affine Hilbert energy minimizers.
Source: expansion of the squared norm along each affine line. -/
noncomputable section
namespace RiemannResearch.Analysis.AffineEnergyMinimum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem inner_eq_zero_of_line_minimum (f u : E)
    (hmin : ∀ t : ℝ, ‖f‖ ^ 2 ≤ ‖f + t • u‖ ^ 2) :
    inner ℝ u f = 0 := by
  by_cases hu : u = 0
  · simp [hu]
  have hn : ‖u‖ ≠ 0 := fun h => hu (norm_eq_zero.mp h)
  have hb : ‖u‖ ^ 2 ≠ 0 := pow_ne_zero _ hn
  let t : ℝ := -inner ℝ u f / ‖u‖ ^ 2
  have ht : t * ‖u‖ ^ 2 = -inner ℝ u f := by
    dsimp only [t]
    exact div_mul_cancel₀ _ hb
  have hexpand : ‖f + t • u‖ ^ 2 =
      ‖f‖ ^ 2 + 2 * t * inner ℝ u f + t ^ 2 * ‖u‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, inner_smul_right, real_inner_comm]
    ring
  have hmin' := hmin t
  rw [hexpand] at hmin'
  have ht2 : t ^ 2 * ‖u‖ ^ 2 = -t * inner ℝ u f := by
    nlinarith [congrArg (fun a : ℝ => t * a) ht]
  have hta : 0 ≤ t * inner ℝ u f := by linarith
  have hnonneg := mul_nonneg hta (sq_nonneg ‖u‖)
  have heq : (t * inner ℝ u f) * ‖u‖ ^ 2 = -(inner ℝ u f) ^ 2 := by
    nlinarith [congrArg (fun a : ℝ => inner ℝ u f * a) ht]
  rw [heq] at hnonneg
  nlinarith [sq_nonneg (inner ℝ u f)]

theorem minimum_iff_normal (U : Submodule ℝ E) (f : E) :
    (∀ u ∈ U, ‖f‖ ^ 2 ≤ ‖f + u‖ ^ 2) ↔
      ∀ u ∈ U, inner ℝ u f = 0 := by
  constructor
  · intro h u hu
    exact inner_eq_zero_of_line_minimum f u (fun t => h _ (U.smul_mem t hu))
  · intro h u hu
    rw [norm_add_sq_real, real_inner_comm, h u hu]
    nlinarith [sq_nonneg ‖u‖]

end RiemannResearch.Analysis.AffineEnergyMinimum

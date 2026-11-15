import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite-dimensional obstructions to geometric residual gain bounds

Source: user-directed residual-projection investigation, 14 November 2026.
The old space is zero and its strict enlargement is the coordinate plane in
real Euclidean three-space. Its correction Gram matrix is the identity.
Unit residuals may still have zero source. Even requiring positive gain
does not give a uniform positive relative gain. These are countermodels
to geometry-only arguments, not to the actual arithmetic bound.
-/

noncomputable section
namespace RiemannResearch.Analysis.ResidualProjectionObstruction

abbrev Space := EuclideanSpace ℝ (Fin 3)
def axis (i : Fin 3) : Space := EuclideanSpace.single i 1

def plane : Submodule ℝ Space where
  carrier := {x | x 2 = 0}
  zero_mem' := rfl
  add_mem' := by
    intro x y hx hy
    change x 2 + y 2 = 0
    rw [hx, hy, add_zero]
  smul_mem' := by
    intro c x hx
    change c * x 2 = 0
    rw [hx, mul_zero]

theorem axis_norm (i : Fin 3) : ‖axis i‖ = 1 := by
  simp [axis]

theorem axis_inner (i j : Fin 3) :
    inner ℝ (axis i) (axis j) = if i = j then 1 else 0 := by
  simp [axis, EuclideanSpace.inner_single_left]

theorem axis_zero_mem : axis 0 ∈ plane := by
  change (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) 2 = 0
  simp [show (2 : Fin 3) ≠ 0 by decide]

theorem axis_one_mem : axis 1 ∈ plane := by
  change (EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) 2 = 0
  simp [show (2 : Fin 3) ≠ 1 by decide]

theorem plane_strict_enlargement : (⊥ : Submodule ℝ Space) < plane := by
  apply bot_lt_iff_ne_bot.mpr
  intro h
  have he := axis_zero_mem
  rw [h, Submodule.mem_bot] at he
  have hn := axis_norm 0
  rw [he, norm_zero] at hn
  norm_num at hn

theorem axis_two_projection_zero : plane.starProjection (axis 2) = 0 := by
  have ho : axis 2 ∈ planeᗮ := by
    rw [Submodule.mem_orthogonal']
    intro u hu
    change u 2 = 0 at hu
    simpa [axis, EuclideanSpace.inner_single_left] using hu
  rw [Submodule.starProjection_apply,
    Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr ho]
  rfl

/-- A two-column identity Gram, unit residual, and zero projection coexist. -/
theorem identity_gram_zero_gain :
    inner ℝ (axis 0) (axis 0) = 1 ∧
    inner ℝ (axis 1) (axis 1) = 1 ∧
    inner ℝ (axis 0) (axis 1) = 0 ∧
    inner ℝ (axis 2) (axis 0) = 0 ∧
    inner ℝ (axis 2) (axis 1) = 0 ∧
    ‖axis 2‖^2 = 1 ∧ ‖plane.starProjection (axis 2)‖^2 = 0 := by
  simp [axis_inner, axis_norm, axis_two_projection_zero]

/-- The same two source columns can miss all the gain in a larger correction space. -/
theorem identity_gram_blind_positive_gain :
    inner ℝ (axis 2) (axis 0) = 0 ∧ inner ℝ (axis 2) (axis 1) = 0 ∧
      ‖(⊤ : Submodule ℝ Space).starProjection (axis 2)‖^2 = 1 := by
  have hp : (⊤ : Submodule ℝ Space).starProjection (axis 2) = axis 2 :=
    Submodule.starProjection_eq_self_iff.mpr (Submodule.mem_top)
  simp [axis_inner, hp, axis_norm]

def target (ε : ℝ) : Space := ε • axis 0 + axis 2

theorem target_projection (ε : ℝ) : plane.starProjection (target ε) = ε • axis 0 := by
  simp only [target, map_add, map_smul, axis_two_projection_zero, add_zero,
    Submodule.starProjection_eq_self_iff.mpr axis_zero_mem]

theorem target_energy (ε : ℝ) : ‖target ε‖^2 = 1 + ε^2 := by
  rw [target, norm_add_sq_real, norm_smul, axis_norm, axis_norm,
    real_inner_smul_left, axis_inner]
  norm_num [Real.norm_eq_abs, sq_abs, show (0 : Fin 3) ≠ 2 by decide]
  ring

theorem target_gain (ε : ℝ) : ‖plane.starProjection (target ε)‖^2 = ε^2 := by
  rw [target_projection, norm_smul, axis_norm]
  simp [Real.norm_eq_abs, sq_abs]

/-- Even strictly positive gains have no uniform relative lower bound. -/
theorem arbitrarily_small_positive_relative_gain (c : ℝ) (hc : 0 < c) :
    ∃ r : Space, 0 < ‖plane.starProjection r‖^2 ∧
      ‖plane.starProjection r‖^2 < c * ‖r‖^2 := by
  refine ⟨target (Real.sqrt (c/2)), ?_, ?_⟩
  · rw [target_gain, Real.sq_sqrt (by positivity)]
    positivity
  · rw [target_gain, target_energy, Real.sq_sqrt (by positivity)]
    nlinarith [sq_nonneg c]

end RiemannResearch.Analysis.ResidualProjectionObstruction

/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import RiemannResearch.Analysis.FiniteGramRange
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Minimum energy from a possibly singular observation Gram equation

Source: user-provided minimum-energy optimizer agenda, 29 October 2026,
Section 6 (the constraint formulation and complete-energy requirement).
The proof uses the defining adjoint identity, documented in Mathlib's
`Analysis/InnerProductSpace/Adjoint.lean`, and the existing finite self-adjoint
range theorem in `Analysis/FiniteGramRange.lean` for multiplier existence.

If `A (A.adjoint y) = b`, then `A.adjoint y` is the unique minimum-norm
solution to `A x = b`, with exact energy `inner ℝ b y`.  Neither row
independence nor an inverse of `A A*` is assumed.  Different multipliers
give the same minimizing vector.  In a finite-dimensional application,
`y = (A A*)† b` is one possible multiplier when `b` is feasible. This file
does not construct that pseudoinverse; it proves multiplier existence for
feasible data whenever the observation space is finite-dimensional.

For the squarefree-head application, the domain carries the complete Q
inner product, so the adjoint and norm include the whole infinite tail.
-/

noncomputable section
namespace RiemannResearch.Analysis.AdjointConstraintMinimum

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The complete cost of any solved observation Gram equation. -/
theorem gram_solution_energy (A : E →L[ℝ] F) (b y : F)
    (hy : A (A.adjoint y) = b) :
    ‖A.adjoint y‖ ^ 2 = inner ℝ b y := by
  calc
    ‖A.adjoint y‖ ^ 2 = inner ℝ (A.adjoint y) (A.adjoint y) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = inner ℝ (A (A.adjoint y)) y := A.adjoint_inner_right _ _
    _ = inner ℝ b y := by rw [hy]

/-- Every adjoint-produced vector is normal to the zero-observation tangent. -/
theorem adjoint_normal (A : E →L[ℝ] F) (y : F) (u : E) (hu : A u = 0) :
    inner ℝ u (A.adjoint y) = 0 := by
  rw [A.adjoint_inner_right, hu, inner_zero_left]

/-- Exact energy completion, retaining the full squared error remainder. -/
theorem gram_solution_completion (A : E →L[ℝ] F) (b y : F)
    (hy : A (A.adjoint y) = b) (x : E) (hx : A x = b) :
    ‖x‖ ^ 2 = ‖A.adjoint y‖ ^ 2 + ‖x - A.adjoint y‖ ^ 2 := by
  have hpair : inner ℝ x (A.adjoint y) = ‖A.adjoint y‖ ^ 2 := by
    rw [A.adjoint_inner_right, hx, gram_solution_energy A b y hy]
  rw [norm_sub_sq_real, hpair]
  ring

theorem gram_solution_minimizes (A : E →L[ℝ] F) (b y : F)
    (hy : A (A.adjoint y) = b) (x : E) (hx : A x = b) :
    ‖A.adjoint y‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [gram_solution_completion A b y hy x hx]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Equality in the minimum-energy bound characterizes the vector itself. -/
theorem gram_solution_equal_iff (A : E →L[ℝ] F) (b y : F)
    (hy : A (A.adjoint y) = b) (x : E) (hx : A x = b) :
    ‖x‖ ^ 2 = ‖A.adjoint y‖ ^ 2 ↔ x = A.adjoint y := by
  constructor
  · intro he
    have hc := gram_solution_completion A b y hy x hx
    have hz : ‖x - A.adjoint y‖ ^ 2 = 0 := by linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
  · rintro rfl
    rfl

/-- Singular Gram systems may have several multipliers but only one minimizer. -/
theorem gram_solution_vector_independent (A : E →L[ℝ] F) (b y z : F)
    (hy : A (A.adjoint y) = b) (hz : A (A.adjoint z) = b) :
    A.adjoint y = A.adjoint z := by
  have h₁ := gram_solution_minimizes A b y hy (A.adjoint z) hz
  have h₂ := gram_solution_minimizes A b z hz (A.adjoint y) hy
  exact ((gram_solution_equal_iff A b y hy (A.adjoint z) hz).mp
    (le_antisymm h₂ h₁)).symm

/-- The multiplier pairing is the attained least complete energy. -/
theorem gram_solution_isLeast (A : E →L[ℝ] F) (b y : F)
    (hy : A (A.adjoint y) = b) :
    IsLeast {e : ℝ | ∃ x : E, A x = b ∧ ‖x‖ ^ 2 = e} (inner ℝ b y) := by
  constructor
  · exact ⟨A.adjoint y, hy, gram_solution_energy A b y hy⟩
  · rintro e ⟨x, hx, rfl⟩
    rw [← gram_solution_energy A b y hy]
    exact gram_solution_minimizes A b y hy x hx

/-- Feasible finite-dimensional observations always have a Gram multiplier,
even when their rows are dependent. -/
theorem exists_gram_solution_of_feasible [FiniteDimensional ℝ F]
    (A : E →L[ℝ] F) (b : F) (x : E) (hx : A x = b) :
    ∃ y : F, A (A.adjoint y) = b := by
  let T : F →ₗ[ℝ] F := A.toLinearMap.comp A.adjoint.toLinearMap
  have hsym : ∀ y z, inner ℝ (T y) z = inner ℝ y (T z) := by
    intro y z
    change inner ℝ (A (A.adjoint y)) z = inner ℝ y (A (A.adjoint z))
    calc
      _ = inner ℝ (A.adjoint y) (A.adjoint z) :=
        (A.adjoint_inner_right _ _).symm
      _ = _ := A.adjoint_inner_left _ _
  have hnull : ∀ z, T z = 0 → inner ℝ z b = 0 := by
    intro z hz
    have hz' : A (A.adjoint z) = 0 := hz
    have he := A.adjoint_inner_right (A.adjoint z) z
    rw [hz', inner_zero_left, real_inner_self_eq_norm_sq] at he
    have hs : A.adjoint z = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp he)
    calc
      inner ℝ z b = inner ℝ z (A x) := by rw [hx]
      _ = inner ℝ (A.adjoint z) x := (A.adjoint_inner_left _ _).symm
      _ = 0 := by rw [hs, inner_zero_left]
  exact FiniteHilbertGram.exists_preimage_of_kernel_orthogonal T hsym b hnull

end RiemannResearch.Analysis.AdjointConstraintMinimum

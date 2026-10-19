/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/

import RiemannResearch.RH.QTriangularInverseGram
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Exact scalar synthesis from the triangular inverse-Gram direction

Source: user-provided Balazard_Triangular_Dual_Refinement (1).md,
Sections 7--8, and Michel Balazard, arXiv:1812.04309, for the dual-system
context. The finite Hilbert projection argument here preserves the entire
squared-norm gap. It supplies no arithmetic limit for the Rayleigh quotient.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QTriangularCharge
open Pareto ZetaTwoHilbert ZetaTwoProbability QCovarianceInverse QCovarianceInvertibility
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def targetCorrelation (d : ι → ℕ) : ℝ :=
  dotProduct (direction d) ((residueGramMatrix d)⁻¹.mulVec (qMean d))
def rayleighFit (d : ι → ℕ) : QHilbert :=
  (targetCorrelation d / directionCapacity d) • directionFit d
theorem qOne_directionFit_inner (d : ι → ℕ) (hd : ∀ i, 1 < d i)
    (hinj : Function.Injective d) :
    inner ℝ qOne (directionFit d) = targetCorrelation d := by
  have ho := target_residual_orthogonal d hd hinj
    ((residueGramMatrix d)⁻¹.mulVec (direction d))
  change inner ℝ (qOne - targetFit d) (directionFit d) = 0 at ho
  rw [inner_sub_left] at ho
  rw [show inner ℝ (targetFit d) (directionFit d) =
    inner ℝ (directionFit d) (targetFit d) from real_inner_comm _ _,
    direction_target_inner d hd hinj] at ho
  exact sub_eq_zero.mp ho
theorem rayleighFit_error (d : ι → ℕ) (hd : ∀ i, 1 < d i)
    (hinj : Function.Injective d) (hA : directionCapacity d ≠ 0) :
    ‖qOne - rayleighFit d‖ ^ 2 =
      1 - targetCorrelation d ^ 2 / directionCapacity d := by
  rw [rayleighFit, norm_sub_sq_real, qOne_norm_sq, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, directionFit_norm_sq d hd hinj,
    real_inner_smul_right, qOne_directionFit_inner d hd hinj]
  field_simp [hA]
  ring
theorem rayleighFit_scalar_error (d : ι → ℕ) (hd : ∀ i, 1 < d i)
    (hinj : Function.Injective d) (hA : directionCapacity d ≠ 0) (a : ℝ) :
    ‖qOne - a • directionFit d‖ ^ 2 =
      ‖qOne - rayleighFit d‖ ^ 2 +
        directionCapacity d * (a - targetCorrelation d / directionCapacity d)^2 := by
  rw [rayleighFit_error d hd hinj hA, norm_sub_sq_real, qOne_norm_sq,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    directionFit_norm_sq d hd hinj, real_inner_smul_right,
    qOne_directionFit_inner d hd hinj]
  field_simp [hA]
  ring
theorem rayleighFit_gap (d : ι → ℕ) (hd : ∀ i, 1 < d i)
    (hinj : Function.Injective d) :
    ‖qOne - rayleighFit d‖ ^ 2 =
      ‖qOne - targetFit d‖ ^ 2 + ‖targetFit d - rayleighFit d‖ ^ 2 := by
  have ht := target_residual_orthogonal d hd hinj
    ((residueGramMatrix d)⁻¹.mulVec (qMean d))
  change inner ℝ (qOne - targetFit d) (targetFit d) = 0 at ht
  have hu := target_residual_orthogonal d hd hinj
    ((residueGramMatrix d)⁻¹.mulVec (direction d))
  change inner ℝ (qOne - targetFit d) (directionFit d) = 0 at hu
  have ho : inner ℝ (qOne - targetFit d) (targetFit d - rayleighFit d) = 0 := by
    rw [inner_sub_right, ht, rayleighFit, real_inner_smul_right, hu]
    ring
  have he := norm_add_sq_real (qOne - targetFit d) (targetFit d - rayleighFit d)
  rw [ho] at he
  simpa only [sub_add_sub_cancel, mul_zero, add_zero] using he
end RiemannResearch.RH.QTriangularCharge

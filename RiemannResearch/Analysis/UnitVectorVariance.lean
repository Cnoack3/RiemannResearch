/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact centered energy and equality for a normalized real Hilbert vector

Source: the user's L1/L2 equality-case discussion, 25 October 2026.
The squared centered norm is retained exactly before deducing the equality
case of Cauchy--Schwarz. Concrete Q and Pareto constant vectors specialize
the same Hilbert-space result; no arithmetic closure claim is assumed.
-/

noncomputable section
namespace RiemannResearch.Analysis.UnitVectorVariance

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The exact squared distance from the constant direction. -/
theorem centered_norm_sq (e f : H) (he : ‖e‖ ^ 2 = 1) :
    ‖f - (inner ℝ e f) • e‖ ^ 2 = ‖f‖ ^ 2 - (inner ℝ e f) ^ 2 := by
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    he, real_inner_smul_right, real_inner_comm f e]
  ring

/-- Cauchy--Schwarz against a normalized constant direction. -/
theorem abs_inner_le_norm (e f : H) (he : ‖e‖ ^ 2 = 1) :
    |inner ℝ e f| ≤ ‖f‖ := by
  have hen : ‖e‖ = 1 := by nlinarith [norm_nonneg e]
  simpa only [hen, one_mul] using abs_real_inner_le_norm e f

/-- Equality means the vector is its scalar mean times the unit vector. -/
theorem abs_inner_eq_norm_iff (e f : H) (he : ‖e‖ ^ 2 = 1) :
    |inner ℝ e f| = ‖f‖ ↔ f = (inner ℝ e f) • e := by
  constructor
  · intro h
    have hz : ‖f - (inner ℝ e f) • e‖ ^ 2 = 0 := by
      rw [centered_norm_sq e f he, ← h, sq_abs, sub_self]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
  · intro h
    have hz : f - (inner ℝ e f) • e = 0 := sub_eq_zero.mpr h
    have hv := centered_norm_sq e f he
    rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hv
    nlinarith [sq_abs (inner ℝ e f), abs_nonneg (inner ℝ e f), norm_nonneg f]

/-- Equivalent scalar-span formulation of the equality case. -/
theorem abs_inner_eq_norm_iff_exists_smul (e f : H) (he : ‖e‖ ^ 2 = 1) :
    |inner ℝ e f| = ‖f‖ ↔ ∃ c : ℝ, f = c • e := by
  rw [abs_inner_eq_norm_iff e f he]
  constructor
  · intro h
    exact ⟨inner ℝ e f, h⟩
  · rintro ⟨c, rfl⟩
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq, he, mul_one]

end RiemannResearch.Analysis.UnitVectorVariance

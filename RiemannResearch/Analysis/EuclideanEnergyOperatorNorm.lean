/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.MatrixMaximalRayleigh
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The normalized Euclidean operator norm from its exact matrix energy

Source: the reciprocal-head investigation, 7 November 2026, Section 4.
The matrix energy is a genuine equality, and the source is EuclideanSpace,
separately from the ordinary finite Pi supremum norm.
-/

noncomputable section
namespace ContinuousLinearMap
variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Exact normalized operator norm from the actual quadratic energy matrix. -/
theorem norm_sq_eq_maximalRayleigh_of_energy
    (T : EuclideanSpace ℝ ι →L[ℝ] H) (A : Matrix ι ι ℝ)
    (henergy : ∀ x, ‖T x‖ ^ 2 = inner ℝ (Matrix.toEuclideanLin A x) x) :
    ‖T‖ ^ 2 = Matrix.maximalRayleigh A := by
  obtain ⟨x, hx⟩ := exists_ne (0 : EuclideanSpace ℝ ι)
  letI : Nonempty {v : EuclideanSpace ℝ ι // v ≠ 0} := ⟨⟨x, hx⟩⟩
  have hRayleigh : 0 ≤ Matrix.maximalRayleigh A := by
    have h := Matrix.rayleigh_le_maximalRayleigh A x hx
    rw [← henergy] at h
    exact (div_nonneg (sq_nonneg _) (sq_nonneg _)).trans h
  have hupper : ‖T‖ ^ 2 ≤ Matrix.maximalRayleigh A := by
    have hnorm : ‖T‖ ≤ Real.sqrt (Matrix.maximalRayleigh A) := by
      apply ContinuousLinearMap.opNorm_le_of_unit_norm (Real.sqrt_nonneg _)
      intro y hy
      have hy0 : y ≠ 0 := by
        intro hz
        rw [hz, norm_zero] at hy
        norm_num at hy
      have hr := Matrix.rayleigh_le_maximalRayleigh A y hy0
      rw [← henergy, hy, one_pow, div_one] at hr
      have hs := Real.sq_sqrt hRayleigh
      nlinarith [norm_nonneg (T y), Real.sqrt_nonneg (Matrix.maximalRayleigh A)]
    have hs := (sq_le_sq₀ (norm_nonneg T) (Real.sqrt_nonneg (Matrix.maximalRayleigh A))).mpr hnorm
    rwa [Real.sq_sqrt hRayleigh] at hs
  have hlower : Matrix.maximalRayleigh A ≤ ‖T‖ ^ 2 := by
    unfold Matrix.maximalRayleigh
    apply ciSup_le
    rintro ⟨y, hy⟩
    rw [← henergy]
    apply (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hy))).mpr
    have hn := T.le_opNorm y
    have hs := (sq_le_sq₀ (norm_nonneg (T y))
      (mul_nonneg (norm_nonneg T) (norm_nonneg y))).mpr hn
    simpa only [mul_pow] using hs
  exact le_antisymm hupper hlower

end ContinuousLinearMap

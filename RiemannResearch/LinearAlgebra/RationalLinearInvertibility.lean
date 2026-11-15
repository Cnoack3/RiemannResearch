/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.LinearAlgebra.RationalLinearSolveCertificate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Linarith

/-!
# Nonsingularity certified by a rational Neumann defect

Source: user-provided reciprocal-head investigation, 7 November 2026,
Section 5. The same finite defect bound used for the coordinate enclosures
also proves nonsingularity of the actual matrix. Hence the certificate's
normal equations have actual inverse solutions, with no existence premise.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RatInterval

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

theorem linearDefect_isUnit
    (AI : ι → ι → RatInterval) (A : Matrix ι ι ℝ) (R : ι → ι → ℚ)
    (θ : ℚ) (hA : ∀ i j, (AI i j).Contains (A i j)) (hθ : θ < 1)
    (hrows : ∀ i, (∑ j, absBound (linearDefect AI R i j)) ≤ θ) : IsUnit A := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  let E : ι → ι → ℝ := fun i j =>
    (if i = j then 1 else 0) - ∑ k, (R i k : ℝ) * A k j
  have hrowsR : ∀ i, (∑ j, |E i j|) ≤ (θ : ℝ) := by
    intro i
    calc
      _ ≤ ∑ j, (absBound (linearDefect AI R i j) : ℝ) :=
        Finset.sum_le_sum (fun j _ => abs_le_absBound (linearDefect_contains AI A R hA i j))
      _ = ((∑ j, absBound (linearDefect AI R i j) : ℚ) : ℝ) := by norm_cast
      _ ≤ _ := by exact_mod_cast hrows i
  have hfix : ∀ i, x i - y i = (∑ j, E i j * (x j - y j)) + 0 := by
    intro i
    have h := RiemannResearch.Analysis.FiniteNeumannCertificate.preconditioned_error_identity
      A (fun i j => (R i j : ℝ)) (A.mulVec y) y x (fun i => congrFun hxy i) i
    simpa only [Matrix.mulVec, dotProduct, sub_self, mul_zero, Finset.sum_const_zero] using h
  have he := RiemannResearch.Analysis.FiniteNeumannCertificate.coordinate_error_bound
    E (fun _ => 0) (fun i => x i - y i) (θ : ℝ) 0
    (by exact_mod_cast hθ) hrowsR (fun _ => by simp) hfix
  funext i
  have hi : |x i - y i| ≤ 0 := by simpa using he i
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hi (abs_nonneg _)))

/-- Actual inverse multiplication solves each finite source exactly. -/
theorem certified_inverse_solution
    (AI : ι → ι → RatInterval) (A : Matrix ι ι ℝ) (R : ι → ι → ℚ)
    (θ : ℚ) (hA : ∀ i j, (AI i j).Contains (A i j)) (hθ : θ < 1)
    (hrows : ∀ i, (∑ j, absBound (linearDefect AI R i j)) ≤ θ)
    (b : ι → ℝ) (i : ι) : (∑ j, A i j * (A⁻¹.mulVec b) j) = b i := by
  have hunit := linearDefect_isUnit AI A R θ hA hθ hrows
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hunit
  have h := congrArg (fun M : Matrix ι ι ℝ => M.mulVec b)
    (Matrix.mul_nonsing_inv A hdet)
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec] at h
  exact congrFun h i

end RiemannResearch.RatInterval

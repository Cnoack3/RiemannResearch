/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.ArithmeticScrewCellBounds
import RiemannResearch.RH.ArithmeticDyadicPositivityTransfer

/-!
# Conditional positivity from exact finite arithmetic approximations

Source: user-provided continuation task, supports this sufficient-condition chain.
This module uses the published signed archimedean-tail quadratic lower bound.
The existing arithmeticScrewApprox retains the polar term, every von Mangoldt
prime-power hinge below N, the linear term, and the negative truncated
archimedean series. In particular, no pointwise kernel comparison is integrated
against the signed product of Haar-step values.

These are conditional research reductions. Nonnegativity of the finite
approximations is an explicit, unproved premise. Completed Weil agreement,
support exhaustion, and RH are not conclusions.
-/

open scoped BigOperators
open MeasureTheory Set
open RiemannResearch.Analysis
open RiemannResearch.RH.PrimeGapCurvature

namespace RiemannResearch.RH
noncomputable section

/-- The literal cell-integral Haar compression of the existing exact finite
arithmetic approximation, with the original unnormalized Haar coefficients. -/
def arithmeticScrewApproxHaarMatrix (R : ℝ) (m N J : ℕ) :
    Matrix (FiniteDyadicHaarIndex m) (FiniteDyadicHaarIndex m) ℝ :=
  finiteDyadicHaarCompression m
    (dyadicCellKernel R m (fun x y => arithmeticScrewApprox N J (x - y)))

/-- Exact reconstruction; all signs and prime-power terms are inherited from
arithmeticScrewApprox without alteration. -/
theorem arithmeticScrewApproxHaarMatrix_quadratic
    {R : ℝ} (hR : 0 ≤ R) (m N J : ℕ)
    (c : FiniteDyadicHaarIndex m → ℝ) :
    (∫ x, dyadicHaarStep R m c x *
      (∫ y, arithmeticScrewApprox N J (x - y) * dyadicHaarStep R m c y)) =
      dotProduct c ((arithmeticScrewApproxHaarMatrix R m N J).mulVec c) := by
  exact dyadicHaarStep_quadratic_reconstruction hR m
    (fun x y => arithmeticScrewApprox N J (x - y))
    ((continuous_arithmeticScrewApprox N J).comp
      (continuous_fst.sub continuous_snd)) c

/-- The finite quadratic lies below the actual arithmetic quadratic. This uses
the signed tail theorem on mean-zero Haar steps, not pointwise kernel order. -/
theorem arithmeticScrewApproxHaarMatrix_quadratic_le
    {R : ℝ} (hR : 0 ≤ R) (m N J : ℕ)
    (hN : Real.exp (2 * R) < N)
    (c : FiniteDyadicHaarIndex m → ℝ) :
    dotProduct c ((arithmeticScrewApproxHaarMatrix R m N J).mulVec c) ≤
      dotProduct c ((arithmeticScrewHaarMatrix R m).mulVec c) := by
  have h := (arithmeticScrewFunction_sub_approx_dyadic_integral_bounds
    hR m N J hN c).1
  rw [arithmeticScrewApproxHaarMatrix_quadratic hR m N J c,
    dyadicHaarStep_quadratic_reconstruction hR m
      (fun x y => arithmeticScrewFunction (x - y))
      (continuous_arithmeticScrewFunction.comp
        (continuous_fst.sub continuous_snd)) c] at h
  exact sub_nonneg.mp h

/-- At a fixed window and level, nonnegativity of one exact finite
approximation suffices for nonnegativity of the actual arithmetic Haar form.
The finite-approximation premise is not established here. -/
theorem arithmeticScrewHaarMatrix_nonneg_of_approx_nonneg
    {R : ℝ} (hR : 0 ≤ R) (m N J : ℕ)
    (hN : Real.exp (2 * R) < N)
    (hpos : ∀ c : FiniteDyadicHaarIndex m → ℝ,
      0 ≤ dotProduct c ((arithmeticScrewApproxHaarMatrix R m N J).mulVec c)) :
    ∀ c : FiniteDyadicHaarIndex m → ℝ,
      0 ≤ dotProduct c ((arithmeticScrewHaarMatrix R m).mulVec c) := by
  intro c
  exact (hpos c).trans
    (arithmeticScrewApproxHaarMatrix_quadratic_le hR m N J hN c)

/-- One uniformly nonnegative finite approximation at each Haar level
supplies the exact all-level matrix premise. Cutoffs may vary with the level. -/
theorem arithmeticScrewHaarMatrix_nonneg_of_finite_approximations
    {R : ℝ} (hR : 0 ≤ R)
    (hpos : ∀ m : ℕ, ∃ N J : ℕ, Real.exp (2 * R) < N ∧
      ∀ c : FiniteDyadicHaarIndex m → ℝ,
        0 ≤ dotProduct c ((arithmeticScrewApproxHaarMatrix R m N J).mulVec c)) :
    ∀ (m : ℕ) (c : FiniteDyadicHaarIndex m → ℝ),
      0 ≤ dotProduct c ((arithmeticScrewHaarMatrix R m).mulVec c) := by
  intro m c
  obtain ⟨N, J, hN, hm⟩ := hpos m
  exact arithmeticScrewHaarMatrix_nonneg_of_approx_nonneg hR m N J hN hm c

/-- Published dyadic density and continuity transfer the finite-approximation
premise to real mean-zero tests on this same fixed window. -/
theorem arithmeticScrew_quadratic_nonneg_of_finite_approximations
    {R : ℝ} (hR : 0 ≤ R)
    (hpos : ∀ m : ℕ, ∃ N J : ℕ, Real.exp (2 * R) < N ∧
      ∀ c : FiniteDyadicHaarIndex m → ℝ,
        0 ≤ dotProduct c ((arithmeticScrewApproxHaarMatrix R m N J).mulVec c))
    {u : ℝ → ℝ} (hu : Integrable u)
    (hu2 : Integrable (fun x => u x ^ 2))
    (hus : ∀ x ∉ Icc (-R) R, u x = 0)
    (hu0 : (∫ x, u x) = 0) :
    0 ≤ realKernelQuadratic (fun x y => arithmeticScrewFunction (x - y)) u := by
  exact arithmeticScrew_quadratic_nonneg_of_haarMatrix_nonneg hR
    (arithmeticScrewHaarMatrix_nonneg_of_finite_approximations hR hpos)
    hu hu2 hus hu0

/-- The same conditional premise gives a real, nonnegative conjugate-first
complex quadratic on the same fixed window; it makes no RH assertion. -/
theorem arithmeticScrew_complexQuadratic_nonneg_of_finite_approximations
    {R : ℝ} (hR : 0 ≤ R)
    (hpos : ∀ m : ℕ, ∃ N J : ℕ, Real.exp (2 * R) < N ∧
      ∀ c : FiniteDyadicHaarIndex m → ℝ,
        0 ≤ dotProduct c ((arithmeticScrewApproxHaarMatrix R m N J).mulVec c))
    {u : ℝ → ℂ} (hu : Integrable u)
    (hur2 : Integrable (fun x => (u x).re ^ 2))
    (hui2 : Integrable (fun x => (u x).im ^ 2))
    (hus : ∀ x ∉ Icc (-R) R, u x = 0)
    (hu0 : (∫ x, u x) = 0) :
    (complexKernelQuadratic
      (fun x y => arithmeticScrewFunction (x - y)) u).im = 0 ∧
      0 ≤ (complexKernelQuadratic
        (fun x y => arithmeticScrewFunction (x - y)) u).re := by
  exact arithmeticScrew_complexQuadratic_nonneg_of_haarMatrix_nonneg hR
    (arithmeticScrewHaarMatrix_nonneg_of_finite_approximations hR hpos)
    hu hur2 hui2 hus hu0

end
end RiemannResearch.RH

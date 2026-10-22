/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.ArithmeticScrewCellBounds
import RiemannResearch.RH.ArithmeticDyadicPositivityTransfer
import RiemannResearch.RH.StrictDiagonalDominance
import Mathlib.MeasureTheory.Integral.Prod

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

namespace RiemannResearch.Analysis
noncomputable section

theorem continuous_integral_integral_swap_of_le
    (k : ℝ → ℝ → ℝ) (hk : Continuous (Function.uncurry k))
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (∫ x in a..b, ∫ y in c..d, k x y) =
      ∫ y in c..d, ∫ x in a..b, k x y := by
  have hi : Integrable (Function.uncurry k)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
    rw [Measure.prod_restrict]
    exact (ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      hk.continuousOn).mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  simp_rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  exact integral_integral_swap hi

/-- Fubini on two oriented compact intervals, with continuity supplying
absolute integrability. -/
theorem continuous_integral_integral_swap
    (k : ℝ → ℝ → ℝ) (hk : Continuous (Function.uncurry k))
    (a b c d : ℝ) :
    (∫ x in a..b, ∫ y in c..d, k x y) =
      ∫ y in c..d, ∫ x in a..b, k x y := by
  by_cases hab : a ≤ b
  · by_cases hcd : c ≤ d
    · exact continuous_integral_integral_swap_of_le k hk hab hcd
    · simp_rw [intervalIntegral.integral_symm d c, intervalIntegral.integral_neg]
      exact congrArg Neg.neg
        (continuous_integral_integral_swap_of_le k hk hab (le_of_not_ge hcd))
  · by_cases hcd : c ≤ d
    · simp_rw [intervalIntegral.integral_symm b a, intervalIntegral.integral_neg]
      exact congrArg Neg.neg
        (continuous_integral_integral_swap_of_le k hk (le_of_not_ge hab) hcd)
    · simp_rw [intervalIntegral.integral_symm b a, intervalIntegral.integral_symm d c,
        intervalIntegral.integral_neg, neg_neg]
      exact continuous_integral_integral_swap_of_le k hk
        (le_of_not_ge hab) (le_of_not_ge hcd)

end
end RiemannResearch.Analysis

namespace RiemannResearch.RH.PrimeGapCurvature
noncomputable section

theorem dyadicCellKernel_symm (R : ℝ) (m : ℕ)
    (k : ℝ → ℝ → ℝ) (hk : Continuous (Function.uncurry k))
    (hs : ∀ x y, k x y = k y x) :
    (dyadicCellKernel R m k).IsSymm := by
  ext i j
  change (∫ x in dyadicCellLeft R m j..dyadicCellRight R m j,
    ∫ y in dyadicCellLeft R m i..dyadicCellRight R m i, k x y) = _
  rw [continuous_integral_integral_swap k hk]
  simp_rw [hs]
  rfl

end
end RiemannResearch.RH.PrimeGapCurvature

namespace RiemannResearch.RH
noncomputable section

theorem arithmeticScrewApprox_neg (N J : ℕ) (t : ℝ) :
    arithmeticScrewApprox N J (-t) = arithmeticScrewApprox N J t := by
  simp only [arithmeticScrewApprox, screwPolarPart_neg, primePowerHingeTerm,
    hingeKernel, archimedeanScrewTerm, abs_neg]

/-- The literal cell-integral Haar compression of the existing exact finite
arithmetic approximation, with the original unnormalized Haar coefficients. -/
def arithmeticScrewApproxHaarMatrix (R : ℝ) (m N J : ℕ) :
    Matrix (FiniteDyadicHaarIndex m) (FiniteDyadicHaarIndex m) ℝ :=
  finiteDyadicHaarCompression m
    (dyadicCellKernel R m (fun x y => arithmeticScrewApprox N J (x - y)))

theorem arithmeticScrewApproxHaarMatrix_symm (R : ℝ) (m N J : ℕ) :
    (arithmeticScrewApproxHaarMatrix R m N J).IsSymm := by
  unfold arithmeticScrewApproxHaarMatrix
  apply finiteDyadicHaarCompression_symm
  apply dyadicCellKernel_symm R m (fun x y => arithmeticScrewApprox N J (x - y))
    ((continuous_arithmeticScrewApprox N J).comp
      (continuous_fst.sub continuous_snd))
  intro x y
  rw [show x - y = -(y - x) by ring, arithmeticScrewApprox_neg]

theorem arithmeticScrewApproxHaarMatrix_isHermitian (R : ℝ) (m N J : ℕ) :
    (arithmeticScrewApproxHaarMatrix R m N J).IsHermitian :=
  Matrix.isHermitian_iff_isSymm.mpr
    (arithmeticScrewApproxHaarMatrix_symm R m N J)

theorem arithmeticScrewApproxHaarMatrix_posSemidef_iff (R : ℝ) (m N J : ℕ) :
    (arithmeticScrewApproxHaarMatrix R m N J).PosSemidef ↔
      ∀ c : FiniteDyadicHaarIndex m → ℝ,
        0 ≤ dotProduct c
          ((arithmeticScrewApproxHaarMatrix R m N J).mulVec c) := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  simp only [arithmeticScrewApproxHaarMatrix_isHermitian R m N J,
    true_and, star_trivial]

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

/-- Native finite-matrix PSD is a sufficient premise for positivity of the
actual arithmetic Haar matrix. It does not construct that certificate. -/
theorem arithmeticScrewHaarMatrix_nonneg_of_approx_posSemidef
    {R : ℝ} (hR : 0 ≤ R) (m N J : ℕ)
    (hN : Real.exp (2 * R) < N)
    (hpos : (arithmeticScrewApproxHaarMatrix R m N J).PosSemidef) :
    ∀ c : FiniteDyadicHaarIndex m → ℝ,
      0 ≤ dotProduct c ((arithmeticScrewHaarMatrix R m).mulVec c) :=
  arithmeticScrewHaarMatrix_nonneg_of_approx_nonneg hR m N J hN
    ((arithmeticScrewApproxHaarMatrix_posSemidef_iff R m N J).mp hpos)

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

/-- Cutoffs may depend on the level. Existence of the native PSD certificates
remains an explicit, unproved premise. -/
theorem arithmeticScrewHaarMatrix_nonneg_of_finite_psd_approximations
    {R : ℝ} (hR : 0 ≤ R)
    (hpos : ∀ m : ℕ, ∃ N J : ℕ, Real.exp (2 * R) < N ∧
      (arithmeticScrewApproxHaarMatrix R m N J).PosSemidef) :
    ∀ (m : ℕ) (c : FiniteDyadicHaarIndex m → ℝ),
      0 ≤ dotProduct c ((arithmeticScrewHaarMatrix R m).mulVec c) := by
  intro m
  obtain ⟨N, J, hN, hm⟩ := hpos m
  exact arithmeticScrewHaarMatrix_nonneg_of_approx_posSemidef hR m N J hN hm

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

/-- Fixed-window real transfer from native finite PSD certificates at every
dyadic level. -/
theorem arithmeticScrew_quadratic_nonneg_of_finite_psd_approximations
    {R : ℝ} (hR : 0 ≤ R)
    (hpos : ∀ m : ℕ, ∃ N J : ℕ, Real.exp (2 * R) < N ∧
      (arithmeticScrewApproxHaarMatrix R m N J).PosSemidef)
    {u : ℝ → ℝ} (hu : Integrable u)
    (hu2 : Integrable (fun x => u x ^ 2))
    (hus : ∀ x ∉ Icc (-R) R, u x = 0)
    (hu0 : (∫ x, u x) = 0) :
    0 ≤ realKernelQuadratic
      (fun x y => arithmeticScrewFunction (x - y)) u :=
  arithmeticScrew_quadratic_nonneg_of_haarMatrix_nonneg hR
    (arithmeticScrewHaarMatrix_nonneg_of_finite_psd_approximations hR hpos)
    hu hu2 hus hu0

/-- Conjugate-first complex transfer from native finite PSD certificates. -/
theorem arithmeticScrew_complexQuadratic_nonneg_of_finite_psd_approximations
    {R : ℝ} (hR : 0 ≤ R)
    (hpos : ∀ m : ℕ, ∃ N J : ℕ, Real.exp (2 * R) < N ∧
      (arithmeticScrewApproxHaarMatrix R m N J).PosSemidef)
    {u : ℝ → ℂ} (hu : Integrable u)
    (hur2 : Integrable (fun x => (u x).re ^ 2))
    (hui2 : Integrable (fun x => (u x).im ^ 2))
    (hus : ∀ x ∉ Icc (-R) R, u x = 0)
    (hu0 : (∫ x, u x) = 0) :
    (complexKernelQuadratic
      (fun x y => arithmeticScrewFunction (x - y)) u).im = 0 ∧
      0 ≤ (complexKernelQuadratic
        (fun x y => arithmeticScrewFunction (x - y)) u).re :=
  arithmeticScrew_complexQuadratic_nonneg_of_haarMatrix_nonneg hR
    (arithmeticScrewHaarMatrix_nonneg_of_finite_psd_approximations hR hpos)
    hu hur2 hui2 hus hu0

/-- Exact diagonal/off-diagonal enclosures and strict row margins imply a
native PSD certificate. No enclosure or margin is constructed here. -/
theorem arithmeticScrewApproxHaarMatrix_posSemidef_of_entrywise_interval_certificate
    (R : ℝ) (m N J : ℕ)
    (diagLower absUpper :
      Matrix (FiniteDyadicHaarIndex m) (FiniteDyadicHaarIndex m) ℝ)
    (hdiag : ∀ i,
      diagLower i i ≤ arithmeticScrewApproxHaarMatrix R m N J i i)
    (hoff : ∀ i j, i ≠ j →
      ‖arithmeticScrewApproxHaarMatrix R m N J i j‖ ≤ absUpper i j)
    (hcert : ∀ i,
      ∑ j ∈ Finset.univ.erase i, absUpper i j < diagLower i i) :
    (arithmeticScrewApproxHaarMatrix R m N J).PosSemidef :=
  (StrictDiagonalDominance.posDef_of_entrywise_interval_certificate
    (arithmeticScrewApproxHaarMatrix_isHermitian R m N J)
    diagLower absUpper hdiag hoff hcert).posSemidef

end
end RiemannResearch.RH

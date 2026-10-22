import RiemannResearch.Analysis.BilateralLaplaceEntire
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Compact smooth interpolation at one actual Laplace argument

A normalized positive bump is modulated by the inverse Laplace kernel.
The resulting smooth test has support in [-2,2] and actual centered
Laplace integral exactly one at the specified complex argument. This
supplies nonzero signatures constructively, including at artificial
single-conductor zeros, without a transform injectivity assumption.

Source: the compact bump argument in Section 10.3 of the user-provided
Nyman--Weil continuation note, made explicit by exponential modulation.
-/

noncomputable section

open MeasureTheory
open scoped Topology

namespace MeasureTheory.BilateralLaplace

private def interpolationBump : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- A compact smooth test with prescribed unit centered Laplace value. -/
def compactLaplaceSeed (s : ℂ) (x : ℝ) : ℂ :=
  (interpolationBump.normed volume x : ℂ) *
    Complex.exp ((s - 1 / 2) * (x : ℂ))

theorem compactLaplaceSeed_contDiff (s : ℂ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (compactLaplaceSeed s) := by
  have hb : ContDiff ℝ (↑(⊤ : ℕ∞)) (interpolationBump.normed volume) :=
    interpolationBump.contDiff.div_const _
  have hlin : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun x : ℝ => (s - 1 / 2) * (x : ℂ)) :=
    contDiff_const.mul Complex.ofRealCLM.contDiff
  exact (Complex.ofRealCLM.contDiff.comp hb).mul hlin.cexp

theorem compactLaplaceSeed_zero_below (s : ℂ) :
    ∀ x < (-2 : ℝ), compactLaplaceSeed s x = 0 := by
  intro x hx
  have hb : interpolationBump x = 0 := by
    apply interpolationBump.zero_of_le_dist
    simp only [interpolationBump, Real.dist_eq, sub_zero]
    nlinarith [neg_le_abs x]
  simp [compactLaplaceSeed, ContDiffBump.normed_def, hb]

theorem compactLaplaceSeed_zero_above (s : ℂ) :
    ∀ x > (2 : ℝ), compactLaplaceSeed s x = 0 := by
  intro x hx
  have hb : interpolationBump x = 0 := by
    apply interpolationBump.zero_of_le_dist
    simp only [interpolationBump, Real.dist_eq, sub_zero]
    nlinarith [le_abs_self x]
  simp [compactLaplaceSeed, ContDiffBump.normed_def, hb]

theorem compactLaplaceSeed_hasCompactSupport (s : ℂ) :
    HasCompactSupport (compactLaplaceSeed s) := by
  have hb : HasCompactSupport
      (fun x : ℝ => (interpolationBump.normed volume x : ℂ)) :=
    interpolationBump.hasCompactSupport_normed.comp_left
      (g := Complex.ofReal) (by simp)
  exact hb.mul_right

/-- Exact cancellation is inside the actual Bochner integral. -/
theorem centeredTransform_compactLaplaceSeed (s : ℂ) :
    centeredTransform (compactLaplaceSeed s) s = 1 := by
  have hcancel (x : ℝ) :
      Complex.exp ((s - 1 / 2) * (x : ℂ)) *
        Complex.exp (-(s - 1 / 2) * (x : ℂ)) = 1 := by
    rw [← Complex.exp_add,
      show (s - 1 / 2) * (x : ℂ) + -(s - 1 / 2) * (x : ℂ) = 0 by ring,
      Complex.exp_zero]
  change (∫ x : ℝ, ((interpolationBump.normed volume x : ℂ) *
      Complex.exp ((s - 1 / 2) * (x : ℂ))) *
        Complex.exp (-(s - 1 / 2) * (x : ℂ))) = 1
  simp_rw [mul_assoc, hcancel, mul_one]
  rw [integral_complex_ofReal, interpolationBump.integral_normed]
  norm_num

theorem centeredTransform_compactLaplaceSeed_ne_zero (s : ℂ) :
    centeredTransform (compactLaplaceSeed s) s ≠ 0 := by
  rw [centeredTransform_compactLaplaceSeed]
  exact one_ne_zero

/-- Every complex evaluation has a smooth test in the same fixed support
interval on which the actual centered Laplace integral is exactly one. -/
theorem exists_compact_centeredTransform_eq_one (s : ℂ) :
    ∃ v : ℝ → ℂ,
      ContDiff ℝ (↑(⊤ : ℕ∞)) v ∧
      (∀ x < (-2 : ℝ), v x = 0) ∧
      (∀ x > (2 : ℝ), v x = 0) ∧
      centeredTransform v s = 1 :=
  ⟨compactLaplaceSeed s, compactLaplaceSeed_contDiff s,
    compactLaplaceSeed_zero_below s, compactLaplaceSeed_zero_above s,
    centeredTransform_compactLaplaceSeed s⟩

end MeasureTheory.BilateralLaplace

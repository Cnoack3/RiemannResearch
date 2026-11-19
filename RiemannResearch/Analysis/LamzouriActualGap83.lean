/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.LamzouriSchwartzCutoff
import RiemannResearch.Analysis.LamzouriCertifiedUnmarked83
import RiemannResearch.Analysis.LamzouriGapKernelCosine
import RiemannResearch.Analysis.GapKernelFourierObjective

/-!
# An explicit degree-83 Fourier test for the actual zero gaps

The only external input to the final theorem is the compact deletion estimate
from Lamzouri's Lemma 3.1 and Proposition 3.2. All polynomial signs,
normalizations, integrals and the finite gap comparison are local proofs.
-/

noncomputable section
open MeasureTheory Real
namespace RiemannResearch.Analysis.LamzouriGapKernel
open ActualZeroOrdinate GapKernelPolynomial GapKernelFourierGaussian LamzouriSmallGapCriterion
open GapKernelObjective

private def σ₀ : ℝ := (cutoff:ℝ)*Real.sqrt Real.pi/(radius:ℝ)
private theorem radius_pos : (0:ℝ) < radius := by norm_num [radius]
private theorem cutoff_pos : (0:ℝ) < cutoff := by norm_num [cutoff]
private theorem σ₀_pos : 0 < σ₀ :=
  div_pos (mul_pos cutoff_pos (Real.sqrt_pos.mpr Real.pi_pos)) radius_pos

private theorem test_identity :
    normalizedTest inputPolynomial fourierPolynomial σ₀ = physicalTest := by
  change normalizedTest inputPolynomial fourierPolynomial σ₀ =
    GapKernelObjective.test (radius:ℝ) (cutoff:ℝ)
      ((ratValue fourierPolynomial 0 : ℚ):ℝ) (value inputPolynomial)
  rw [cast_ratValue, Rat.cast_zero]
  exact normalizedTest_eq_objectiveTest _ _ radius_pos cutoff_pos fourierPolynomial_zero_pos

private theorem contDiff_value (p : List ℤ) : ContDiff ℝ 2 (value p) := by
  induction p with
  | nil =>
    change ContDiff ℝ 2 (fun _ : ℝ => (0:ℝ))
    exact contDiff_const
  | cons a p ih =>
    change ContDiff ℝ 2 (fun x : ℝ => (a:ℝ) + x*value p x)
    fun_prop

private theorem physical_integrable : Integrable physicalTest := by
  rw [← test_identity]
  have hi : Integrable (model inputPolynomial) := by
    simpa only [pow_zero,one_mul] using weighted_integrable inputPolynomial 0
  apply ((hi.comp_div σ₀_pos.ne').const_mul ((σ₀*value fourierPolynomial 0)⁻¹)).congr
  filter_upwards [] with x
  simp only [normalizedTest,div_eq_inv_mul]

theorem physicalTest_cosineTransform (u : ℝ) :
    cosineTransform physicalTest u = scaledFourier u := by
  rw [← test_identity]
  exact normalized_cosineTransform σ₀_pos u

/-- At least a positive lower proportion of actual adjacent zero gaps is
at most 0.784981 times the common-height average spacing. -/
theorem smallGapProportion_certified83 [LamzouriCompactDeletion2026] :
    0 < smallGapProportion (784981/1000000) := by
  rw [show (784981 / 1000000 : ℝ) = (gap : ℝ) by norm_num [gap]]
  have hs : ContDiff ℝ 2 physicalTest := by
    rw [← test_identity]
    unfold normalizedTest model
    have hv := contDiff_value inputPolynomial
    fun_prop
  have he : Function.Even physicalTest := by
    intro x
    rw [← test_identity]
    have hsquare : (-(x/σ₀))^2 = (x/σ₀)^2 := by ring
    simp only [normalizedTest, model, neg_div, hsquare]
  apply smallGapProportion_pos_of_smooth_integrable_test (θ := (cutoff:ℝ))
    (by norm_num [gap]) (by norm_num [gap]) (by norm_num [cutoff]) (by norm_num [cutoff])
    physical_integrable hs he (fun x => (physicalTest_pos x).le)
  · rw [physicalTest_cosineTransform,scaledFourier_at_zero]
  · intro u hu
    rw [physicalTest_cosineTransform]
    exact (scaledFourier_neg_of_separated hu.le).le
  · exact certifiedObjective

end RiemannResearch.Analysis.LamzouriGapKernel

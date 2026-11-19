/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ActualSmallGapPairBound
import RiemannResearch.Analysis.GapKernelFourierModel
import RiemannResearch.Analysis.LamzouriGapKernelSigns
import RiemannResearch.Analysis.LamzouriGapObjectiveCertificate

/-!
# The certified degree-83 polynomial pair on the actual unmarked zero array

The finite weighted sum of the Fourier-side model has upper bound one.
The physical test has a strictly larger objective. Identification of the
two tests by Fourier transformation and the asymptotic sparse-pair lower
bound are the remaining analytic steps in the compact-witness argument.
-/

noncomputable section
namespace RiemannResearch.Analysis.LamzouriGapKernel
open ActualZeroOrdinate GapKernelPolynomial GapKernelObjective MeasureTheory Zeta23

def scaledFourier (u : ℝ) : ℝ :=
  fourierModel ((cutoff:ℝ)*Real.sqrt Real.pi/(radius:ℝ)) fourierPolynomial u

theorem scaledFourier_at_zero : scaledFourier 0 = 1 :=
  fourierModel_zero fourierPolynomial_zero_pos

theorem scaledFourier_neg_of_separated {u : ℝ} (hu : (gap:ℝ) ≤ |u|) :
    scaledFourier u < 0 :=
  fourierModel_neg_of_separation fourierPolynomial_zero_pos (by norm_num [gap])
    (fun _ h => fourierPolynomial_neg h) fourier_radius hu

theorem normalized_actual_unmarked_le_one {T : ℝ} (hT : 1 ≤ T) :
    unmarkedGapPairSum (gap:ℝ) T scaledFourier / (Ncount 0 T : ℝ) ≤ 1 :=
  normalized_unmarkedGapPairSum_le_one (Real.log_nonneg hT) scaledFourier_at_zero
    (fun _ hu => (scaledFourier_neg_of_separated hu.le).le)

theorem physicalTest_pos (x : ℝ) : 0 < physicalTest x := by
  have hq : (0:ℝ) < ((ratValue fourierPolynomial 0 : ℚ):ℝ) := by
    simpa only [cast_ratValue, Rat.cast_zero] using fourierPolynomial_zero_pos
  have hr : (0:ℝ) < (radius:ℝ) := by norm_num [radius]
  have ht : (0:ℝ) < (cutoff:ℝ) := by norm_num [cutoff]
  unfold physicalTest test
  exact mul_pos (mul_pos (div_pos hr (mul_pos (mul_pos ht (Real.sqrt_pos.mpr Real.pi_pos)) hq))
    (Real.exp_pos _)) (inputPolynomial_pos (sq_nonneg _))

end RiemannResearch.Analysis.LamzouriGapKernel

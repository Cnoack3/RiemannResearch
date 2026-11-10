/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.PrimeBandlimitedMatrix
import RiemannResearch.Analysis.PrimeBandlimitedDiagonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-! # The complete actual-zero matrix with its diagonal correction

The exact diagonal retains the pole term without a zero-mean assumption.
For an even real compact-C2 zero-mean window, the actual normalized zero
matrix is centered at F(0)+c_F/log T with the complete error

  72 M2(F) (D/T)^3/log T + 11 M1(F)/(48 T^2 log T).

Source: user-provided MontgomeryGammaAudit20261110.md, Sections 4--6.
The identities and the sharpened remainder are assembled from the checked
spatial matrix and regulated diagonal modules. No RH or prime-pair
asymptotic is assumed; this is the smooth-height actual-zero matrix.
-/
open MeasureTheory Set Complex
open scoped BigOperators ComplexConjugate
noncomputable section
namespace RiemannResearch.Analysis.PrimeBandlimitedWeil
open SechGammaBounds SechGammaDiagonal

/-- All pole, logarithmic, and regulated remainder terms are retained. -/
theorem normalizedDiagonal_exact {F : ℝ → ℝ}
    (hFd : ContDiff ℝ 2 F) (hF : Function.support F ⊆ Icc (-1 : ℝ) 1)
    (hFe : ∀ x, F (-x) = F x) {T : ℝ} (hT : 2 < T) :
    normalizedDiagonal F T =
      (((1 / Real.pi) * (∫ x : ℝ, F x)) / zeroNormalizer T +
        F 0 + logarithmicCorrection F / Real.log T -
        (2 / (T * Real.log T)) * (∫ x in Ioc 0 1, F x * remainder (x/T)) : ℝ) := by
  have hT0 : 0 < T := by linarith
  have hT1 : 1 < T := by linarith
  have hFc := real_window_contDiff hFd
  have hFs := real_window_support hF
  have hFce : ∀ x, (F (-x) : ℂ) = (F x : ℂ) := by intro x; rw [hFe]
  have hsum : actualZeroEntry F T 1 1 =
      poleContribution (fun x => (F x : ℂ)) + gammaContribution (fun x => (F x : ℂ)) T 0 := by
    simpa only [actualZeroEntry, logRatio, sub_self] using
      actual_zero_sum_homogeneous_complete hFc hFs (n := 1) (m := 1)
        (by norm_num) (by norm_num) rfl (by norm_num; exact hT) (by norm_num; exact hT)
  have hc : HasCompactSupport F :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hF
  have hi : Integrable F := hFd.continuous.integrable_of_hasCompactSupport hc
  have hcast := Complex.ofRealCLM.integral_comp_comm hi
  change (∫ x : ℝ, (F x : ℂ)) = ((∫ x : ℝ, F x : ℝ) : ℂ) at hcast
  have hp : poleContribution (fun x => (F x : ℂ)) =
      ((1 / Real.pi) * (∫ x : ℝ, F x) : ℝ) := by
    unfold poleContribution
    rw [hcast]
    push_cast
    <;> ring
  have him := gammaContribution_im_real hFd hF hT0 0
  have hgreal : gammaContribution (fun x => (F x : ℂ)) T 0 =
      ((gammaContribution (fun x => (F x : ℂ)) T 0).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using him
  have hg := gammaContribution_diagonal_normalized hFc hFs hFce hT1
  simp only [Complex.ofReal_re] at hg
  change (gammaContribution (fun x => (F x : ℂ)) T 0).re / zeroNormalizer T = _ at hg
  unfold normalizedDiagonal
  rw [hsum, hp, hgreal, ← Complex.ofReal_add, ← Complex.ofReal_div]
  congr 1
  rw [add_div, hg]
  ring

theorem normalizedDiagonal_error_bound {F : ℝ → ℝ}
    (hFd : ContDiff ℝ 2 F) (hF : Function.support F ⊆ Icc (-1 : ℝ) 1)
    (hFe : ∀ x, F (-x) = F x) (h0 : windowMoment F 0 = 0)
    {T : ℝ} (hT : 2 < T) :
    ‖normalizedDiagonal F T - ((F 0 + logarithmicCorrection F / Real.log T : ℝ) : ℂ)‖ ≤
      11 * absoluteFirstMoment F / (48 * T^2 * Real.log T) := by
  rw [normalizedDiagonal_eq_real_gamma hFd hF h0 hT,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have he : (gammaContribution (fun x => (F x : ℂ)) T 0).re / zeroNormalizer T -
      (F 0 + logarithmicCorrection F / Real.log T) =
      (gammaContribution (fun x => (F x : ℂ)) T 0).re / zeroNormalizer T -
      F 0 - logarithmicCorrection F / Real.log T := by ring
  rw [he]
  exact real_gamma_diagonal_error_bound hFd hF hFe h0 (by linarith)

/-- The complete actual-zero quadratic estimate includes the logarithmic
diagonal correction and the explicit smaller diagonal remainder. -/
theorem actual_zero_quadratic_corrected_bound {F : ℝ → ℝ}
    (hFd : ContDiff ℝ 2 F) (hF : Function.support F ⊆ Icc (-1 : ℝ) 1)
    (hFe : ∀ x, F (-x) = F x) (h0 : windowMoment F 0 = 0)
    (s : Finset ℕ) (c : ℕ → ℂ) {T : ℝ} {D : ℕ}
    (hT : 4 ≤ T) (hTD : 2 * (D : ℝ) ≤ T)
    (hs : ∀ n ∈ s, 0 < n ∧ n ≤ D)
    (hdeg : ∀ n ∈ s, ∀ m ∈ s,
      ArithmeticFunction.cardFactors n = ArithmeticFunction.cardFactors m) :
    ‖(∑ n ∈ s, ∑ m ∈ s, c n * conj (c m) *
        (actualZeroEntry F T n m / (zeroNormalizer T : ℂ))) -
      ((F 0 + logarithmicCorrection F / Real.log T : ℝ) : ℂ) *
        ((∑ n ∈ s, ‖c n‖^2 : ℝ) : ℂ)‖ ≤
      (72 * absoluteSecondMoment F * ((D : ℝ)/T)^3 / Real.log T +
        11 * absoluteFirstMoment F / (48 * T^2 * Real.log T)) *
        ∑ n ∈ s, ‖c n‖^2 := by
  exact actual_zero_quadratic_error_le_of_diagonal_bound hFd hF hFe h0 s c
    hT hTD hs hdeg (F 0 + logarithmicCorrection F / Real.log T)
    (11 * absoluteFirstMoment F / (48 * T^2 * Real.log T))
    (normalizedDiagonal_error_bound hFd hF hFe h0 (by linarith))
end RiemannResearch.Analysis.PrimeBandlimitedWeil

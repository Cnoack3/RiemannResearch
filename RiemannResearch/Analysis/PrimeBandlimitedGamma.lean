/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.PrimeHomogeneousResonance
import RiemannResearch.Analysis.SechGammaBounds
import Mathlib.MeasureTheory.Group.Integral
import RiemannResearch.RH.WeilGammaFourierAdapter
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp


/-! # Complete poles and spatial gamma for band-limited homogeneous tests

The exact Guinand--Weil formula comes from PrimeHomogeneousResonance.
Both pole evaluations are retained and their sech denominator cancels
exactly. Their constant matrix is rank one, and vanishes for a zero-mean
frequency window. This does not remove the separate gamma diagonal.

The gamma spatial adapter is specialized with C2 compact support, and the
sech-modified gamma kernel is split exactly. No gamma asymptotic or
operator-smallness hypothesis is assumed or concluded here.

Source: Garrett, "Guinand's explicit formula", Theorem 0.0.1,
https://www-users.cse.umn.edu/~garrett/m/mfms/notes_2015-16/04_Guinand_explicit_fml.pdf,
supports the pole/gamma convention; DLMF 5.9.16 supports the digamma
representation used by the existing spatial adapter.
The cancellations and kernel split below are elementary deductions.
See THEOREM_CATALOG_MONTGOMERY_GAMMA_20261110.md for the verified
spatial estimates and the remaining actual-zero and raw-ordinate transfers.
-/

open MeasureTheory Zeta23
open scoped BigOperators ComplexConjugate
noncomputable section
namespace RiemannResearch.Analysis.PrimeBandlimitedWeil

theorem pole_integrand_cancel (F : ℝ → ℂ) (T u v : ℝ) :
    frequencyTest F T u v * Complex.exp (Complex.I * (Complex.I / 2) * (v : ℂ)) +
    frequencyTest F T u v * Complex.exp (Complex.I * (-Complex.I / 2) * (v : ℂ)) =
      ((T / Real.pi : ℝ) : ℂ) * F (T * (v-u)) := by
  have hp : Complex.I * (Complex.I / 2) * (v : ℂ) = ((-v / 2 : ℝ) : ℂ) := by
    calc
      _ = Complex.I ^ 2 * (v : ℂ) / 2 := by ring
      _ = _ := by rw [Complex.I_sq]; push_cast; ring
  have hm : Complex.I * (-Complex.I / 2) * (v : ℂ) = ((v / 2 : ℝ) : ℂ) := by
    calc
      _ = -(Complex.I ^ 2) * (v : ℂ) / 2 := by ring
      _ = _ := by rw [Complex.I_sq]; push_cast; ring
  rw [hp, hm, ← Complex.ofReal_exp, ← Complex.ofReal_exp]
  have hc : (Real.exp (-v/2) : ℂ) + (Real.exp (v/2) : ℂ) =
      2 * (Real.cosh (v/2) : ℂ) := by
    rw [Real.cosh_eq]
    push_cast
    rw [neg_div]
    ring
  rw [← mul_add, hc]
  unfold frequencyTest
  have hcos : (Real.cosh (v/2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.cosh_pos (v/2)).ne'
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_inv]
  field_simp [hcos]


theorem pole_pair_frequencyTest {F : ℝ → ℂ} (hFd : ContDiff ℝ 2 F)
    (hF : Function.support F ⊆ Set.Icc (-1 : ℝ) 1) {T : ℝ} (hT : 0 < T) (u : ℝ) :
    paperFT (frequencyTest F T u) (Complex.I/2) +
      paperFT (frequencyTest F T u) (-Complex.I/2) =
        (1 / Real.pi : ℂ) * ∫ x : ℝ, F x := by
  have hi (z : ℂ) : Integrable (fun v : ℝ =>
      frequencyTest F T u v * Complex.exp (Complex.I * z * (v : ℂ))) :=
    ((frequencyTest_contDiff hFd T u).continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      (frequencyTest_compact hF hT u).mul_right
  unfold paperFT
  rw [← integral_add (hi _) (hi _)]
  simp_rw [pole_integrand_cancel]
  rw [integral_const_mul]
  have hshift : (∫ v : ℝ, F (T * (v-u))) = ∫ v : ℝ, F (T*v) :=
    integral_sub_right_eq_self (fun v : ℝ => F (T*v)) u
  rw [hshift, Measure.integral_comp_mul_left]
  rw [abs_of_pos (inv_pos.mpr hT), Complex.real_smul]
  push_cast
  have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  field_simp [hTc]

theorem pole_pair_frequencyTest_eq_zero {F : ℝ → ℂ} (hFd : ContDiff ℝ 2 F)
    (hF : Function.support F ⊆ Set.Icc (-1 : ℝ) 1) {T : ℝ} (hT : 0 < T)
    (hmean : (∫ x : ℝ, F x) = 0) (u : ℝ) :
    paperFT (frequencyTest F T u) (Complex.I/2) +
      paperFT (frequencyTest F T u) (-Complex.I/2) = 0 := by
  rw [pole_pair_frequencyTest hFd hF hT, hmean, mul_zero]

theorem constant_pole_quadratic {ι : Type*} (s : Finset ι) (c : ι → ℂ) (p : ℂ) :
    (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * p) =
      ((∑ i ∈ s, c i) * conj (∑ i ∈ s, c i)) * p := by
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]


def gammaContribution (F : ℝ → ℂ) (T u : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ r : ℝ, paperFT (frequencyTest F T u) r * (EF.gammaBracket r : ℂ)

def poleContribution (F : ℝ → ℂ) : ℂ :=
  (1 / Real.pi : ℂ) * ∫ x : ℝ, F x

theorem actual_zero_sum_homogeneous_complete {F : ℝ → ℂ}
    (hFd : ContDiff ℝ 2 F) (hF : Function.support F ⊆ Set.Icc (-1 : ℝ) 1)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hdeg : ArithmeticFunction.cardFactors n = ArithmeticFunction.cardFactors m) {T : ℝ}
    (hTn : (n : ℝ) + 1 < T) (hTm : (m : ℝ) + 1 < T) :
    (∑' ρ : (zetaZeros zetaSeam).carrier,
      ((zetaZeros zetaSeam).mult ρ : ℂ) *
        paperFT (frequencyTest F T (logRatio n m)) (gammaOf ρ)) =
      poleContribution F + gammaContribution F T (logRatio n m) := by
  have hT : 0 < T := (by positivity : 0 < (n : ℝ) + 1).trans hTn
  have h := (actual_zero_sum_homogeneous hFd hF hn hm hdeg hTn hTm).2
  rw [pole_pair_frequencyTest hFd hF hT] at h
  exact h

end RiemannResearch.Analysis.PrimeBandlimitedWeil



namespace RiemannResearch.Analysis.PrimeBandlimitedWeil
open RiemannResearch.RH.SignedWeilCorrelation

theorem gammaContribution_diagonal_spatial {F : ℝ → ℂ}
    (hFd : ContDiff ℝ 2 F) (hF : Function.support F ⊆ Set.Icc (-1 : ℝ) 1)
    (hFe : ∀ x, F (-x) = F x) {T : ℝ} (hT : 0 < T) :
    (gammaContribution F T 0).re =
      -(Real.eulerMascheroniConstant + Real.log (4 * Real.pi)) *
        (frequencyTest F T 0 0).re -
      2 * (∫ t, weilGammaKernel t *
        ((frequencyTest F T 0 t).re -
          weilRegulator t * (frequencyTest F T 0 0).re) ∂positiveMeasure) := by
  apply gamma_spatial_of_contDiff_two (frequencyTest_contDiff hFd T 0)
    (frequencyTest_compact hF hT 0)
  intro t
  simp [frequencyTest, hFe, mul_neg, neg_div, Real.cosh_neg]

/-- Sech smoothing changes the spatial gamma kernel by this exact factor. -/
def sechGammaKernel (t : ℝ) : ℝ := weilGammaKernel t / Real.cosh (t/2)

theorem sechGammaKernel_split {t : ℝ} (ht : 0 < t) :
    sechGammaKernel t = 1 / (2 * Real.sinh t) + 1 / (4 * Real.cosh (t/2)^2) := by
  have hs : Real.sinh t ≠ 0 := by
    rw [Real.sinh_eq]
    exact ne_of_gt (div_pos (sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))) (by norm_num))
  have hc : Real.cosh (t/2) ≠ 0 := (Real.cosh_pos _).ne'
  have he : Real.exp (t/2) = Real.cosh (t/2) + Real.sinh (t/2) := by
    rw [Real.cosh_eq, Real.sinh_eq]
    ring
  have hd : Real.exp t - Real.exp (-t) = 2 * Real.sinh t := by
    rw [Real.sinh_eq]
    ring
  have htwo : Real.sinh t = 2 * Real.sinh (t/2) * Real.cosh (t/2) := by
    simpa only [show 2*(t/2) = t by ring] using Real.sinh_two_mul (t/2)
  unfold sechGammaKernel weilGammaKernel
  rw [he, hd]
  field_simp [hs,hc]
  nlinarith [htwo]


/-- The proved spatial-kernel estimate uses the actual sech-modified Weil
gamma kernel. Turning this integral into an off-diagonal zero-matrix entry
still requires the frequency-to-space and change-of-variables identity. -/
theorem gamma_kernel_window_bound (F : ℝ → ℝ) (hF : Continuous F)
    (hFe : ∀ x, F (-x) = F x)
    (h0 : SechGammaBounds.windowMoment F 0 = 0)
    {T u : ℝ} (hT : 1 < T) (hu : 0 < u) (hscale : 1 / T ≤ u / 2) :
    |-(∫ x in Set.Icc (-1 : ℝ) 1, F x * sechGammaKernel (u + x / T)) /
        (T * Real.log T)| ≤
      24 * SechGammaBounds.absoluteSecondMoment F /
        (T ^ 3 * Real.log T * u ^ 3) := by
  have hT0 : 0 < T := by linarith
  have hshift (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) : 0 < u + x / T := by
    have h := div_le_div_of_nonneg_right hx.1 hT0.le
    have he : (-1 : ℝ) / T = -(1 / T) := by ring
    rw [he] at h
    linarith
  have he :
      (∫ x in Set.Icc (-1 : ℝ) 1, F x * sechGammaKernel (u + x / T)) =
        SechGammaBounds.windowSample F T u := by
    unfold SechGammaBounds.windowSample
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [sechGammaKernel_split (hshift x hx)]
    rfl
  rw [he]
  exact SechGammaBounds.normalized_window_bound_of_even F hF hFe h0 hT hu hscale

end RiemannResearch.Analysis.PrimeBandlimitedWeil

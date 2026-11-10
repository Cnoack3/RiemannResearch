import RiemannResearch.Analysis.SechGammaDiagonal
import RiemannResearch.Analysis.PrimeBandlimitedGamma

/-!
# The diagonal gamma correction for bandlimited windows

The exact diagonal gamma integral equals its leading density, the explicit
logarithmic correction from Sections 6.1–6.4 of
`MontgomeryGammaAudit20261110.md`, and a controlled remainder.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section

namespace RiemannResearch.Analysis.SechGammaDiagonal

def logarithmicCorrection (F : ℝ → ℝ) : ℝ :=
  -(Real.eulerMascheroniConstant+Real.log (2*Real.pi))*F 0 +
    ∫ x in Ioc 0 1, (F 0-F x)/x
end RiemannResearch.Analysis.SechGammaDiagonal

namespace RiemannResearch.Analysis.PrimeBandlimitedWeil
open RiemannResearch.RH.SignedWeilCorrelation
open SechGammaDiagonal

theorem exists_re_linear_bound {F : ℝ → ℂ} (hFd : ContDiff ℝ 2 F)
    (hF : Function.support F ⊆ Icc (-1 : ℝ) 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x, 0 < x → |(F x).re-(F 0).re| ≤ K*x := by
  have hc : HasCompactSupport F :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hF
  have hder : ContDiff ℝ 1 (deriv F) := (contDiff_succ_iff_deriv.mp hFd).2.2
  obtain ⟨x₀, hx₀⟩ := hder.continuous.norm.exists_forall_ge_of_hasCompactSupport hc.deriv.norm
  let K : NNReal := ‖deriv F x₀‖₊
  have hlip : LipschitzWith K F := by
    apply lipschitzWith_of_nnnorm_deriv_le (hFd.differentiable (by norm_num))
    intro x
    exact hx₀ x
  refine ⟨(K : ℝ), K.coe_nonneg, ?_⟩
  intro x hx
  calc
    |(F x).re-(F 0).re| ≤ ‖F x-F 0‖ := by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (F x-F 0)
    _ ≤ (K : ℝ)*x := by
      simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_pos hx] using hlip.dist_le_mul x 0

theorem gammaContribution_diagonal_expansion {F : ℝ → ℂ}
    (hFd : ContDiff ℝ 2 F) (hF : Function.support F ⊆ Icc (-1 : ℝ) 1)
    (hFe : ∀ x, F (-x) = F x) {T : ℝ} (hT : 1 < T) :
    (gammaContribution F T 0).re =
      (T*Real.log T/(2*Real.pi))*(F 0).re +
      (T/(2*Real.pi))*logarithmicCorrection (fun x => (F x).re) -
      (1/Real.pi)*(∫ x in Ioc 0 1, (F x).re*remainder (x/T)) := by
  have hT0 : 0 < T := by linarith
  obtain ⟨K, hK, hLip⟩ := exists_re_linear_bound hFd hF
  have hFr : Continuous (fun x => (F x).re) := Complex.continuous_re.comp hFd.continuous
  have hz (x : ℝ) (hx : 1 < x) : (F x).re = 0 := by
    have hFx : F x = 0 := by
      by_contra h
      exact (not_le.mpr hx) (hF h).2
    rw [hFx]; rfl
  have hreg (t : ℝ) (ht : 0 < t) :
      weilGammaKernel t*weilRegulator t = halfCsch t := by
    have he : Real.exp t-Real.exp (-t) ≠ 0 :=
      (sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))).ne'
    unfold weilGammaKernel weilRegulator halfCsch
    rw [Real.sinh_eq]
    have hprod : Real.exp (t/2)*Real.exp (-(t/2)) = 1 := by rw [←Real.exp_add]; simp
    field_simp
    simpa only [neg_div] using hprod
  have h0 : (frequencyTest F T 0 0).re = (T/(2*Real.pi))*(F 0).re := by
    simp only [frequencyTest, sub_self, mul_zero, zero_div, Real.cosh_zero, inv_one,
      Complex.ofReal_one, mul_one, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  have hi :
      (∫ t in Ioi 0, weilGammaKernel t*((frequencyTest F T 0 t).re -
        weilRegulator t*(frequencyTest F T 0 0).re)) =
      (T/(2*Real.pi))*(∫ t in Ioi 0, SechGammaBounds.kernel t*(F (T*t)).re -
        halfCsch t*(F 0).re) := by
    rw [←integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := ht
    dsimp only []
    rw [h0]
    have hkt : (frequencyTest F T 0 t).re =
        (T/(2*Real.pi))*(F (T*t)).re/Real.cosh (t/2) := by
      simp only [frequencyTest, sub_zero, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
      ring
    rw [hkt]
    have hs := sechGammaKernel_split ht0
    unfold sechGammaKernel at hs
    change weilGammaKernel t/Real.cosh (t/2) = SechGammaBounds.kernel t at hs
    calc
      _ = (T/(2*Real.pi))*((weilGammaKernel t/Real.cosh (t/2))*(F (T*t)).re -
          (weilGammaKernel t*weilRegulator t)*(F 0).re) := by ring
      _ = _ := by rw [hs, hreg t ht0]
  rw [gammaContribution_diagonal_spatial hFd hF hFe hT0, hi, h0,
    regulated_rescale hFr hK hLip hz hT]
  have hlog : Real.log (4*Real.pi) = Real.log 2+Real.log (2*Real.pi) := by
    rw [show (4 : ℝ)*Real.pi = 2*(2*Real.pi) by ring,
      Real.log_mul (by norm_num) (by positivity)]
  rw [hlog]
  unfold logarithmicCorrection
  field_simp <;> ring

theorem gammaContribution_diagonal_normalized {F : ℝ → ℂ}
    (hFd : ContDiff ℝ 2 F) (hF : Function.support F ⊆ Icc (-1 : ℝ) 1)
    (hFe : ∀ x, F (-x) = F x) {T : ℝ} (hT : 1 < T) :
    (gammaContribution F T 0).re/(T*Real.log T/(2*Real.pi)) =
      (F 0).re + logarithmicCorrection (fun x => (F x).re)/Real.log T -
      (2/(T*Real.log T))*(∫ x in Ioc 0 1, (F x).re*remainder (x/T)) := by
  have hT0 : 0 < T := by linarith
  have hl := Real.log_pos hT
  rw [gammaContribution_diagonal_expansion hFd hF hFe hT]
  field_simp

theorem gammaContribution_diagonal_error_bound {F : ℝ → ℂ}
    (hFd : ContDiff ℝ 2 F) (hF : Function.support F ⊆ Icc (-1 : ℝ) 1)
    (hFe : ∀ x, F (-x) = F x)
    (hmean : (∫ x in Ioc 0 1, (F x).re) = 0) {T : ℝ} (hT : 1 < T) :
    |(gammaContribution F T 0).re/(T*Real.log T/(2*Real.pi)) -
      (F 0).re-logarithmicCorrection (fun x => (F x).re)/Real.log T| ≤
      11*absoluteFirstMoment (fun x => (F x).re)/(48*T^2*Real.log T) := by
  rw [gammaContribution_diagonal_normalized hFd hF hFe hT]
  have he : (F 0).re+logarithmicCorrection (fun x => (F x).re)/Real.log T -
      (2/(T*Real.log T))*(∫ x in Ioc 0 1, (F x).re*remainder (x/T)) -
      (F 0).re-logarithmicCorrection (fun x => (F x).re)/Real.log T =
      -(2/(T*Real.log T))*(∫ x in Ioc 0 1, (F x).re*remainder (x/T)) := by ring
  rw [he]
  exact normalized_window_integral_bound _ (Complex.continuous_re.comp hFd.continuous) hmean hT

end RiemannResearch.Analysis.PrimeBandlimitedWeil

namespace RiemannResearch.Analysis.PrimeBandlimitedWeil
open SechGammaDiagonal

theorem real_gamma_diagonal_error_bound {F : ℝ → ℝ}
    (hFd : ContDiff ℝ 2 F) (hF : Function.support F ⊆ Icc (-1 : ℝ) 1)
    (hFe : ∀ x, F (-x) = F x)
    (hmean : SechGammaBounds.windowMoment F 0 = 0) {T : ℝ} (hT : 1 < T) :
    |(gammaContribution (fun x => (F x : ℂ)) T 0).re/(T*Real.log T/(2*Real.pi)) -
      F 0-logarithmicCorrection F/Real.log T| ≤
      11*absoluteFirstMoment F/(48*T^2*Real.log T) := by
  have hFc : ContDiff ℝ 2 (fun x => (F x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hFd
  have hFs : Function.support (fun x => (F x : ℂ)) ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    apply hF
    simpa only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero] using hx
  have hFce : ∀ x, (F (-x) : ℂ) = (F x : ℂ) := by intro x; rw [hFe]
  have hm : (∫ x in Ioc 0 1, ((F x : ℂ)).re) = 0 := by
    simpa using half_mean_eq_zero_of_window hFd.continuous hF hFe hmean
  simpa only [Complex.ofReal_re] using
    gammaContribution_diagonal_error_bound hFc hFs hFce hm hT

end RiemannResearch.Analysis.PrimeBandlimitedWeil

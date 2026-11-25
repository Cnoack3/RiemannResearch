import RiemannResearch.Analysis.MontgomeryHeatKernelMixture
import RiemannResearch.Analysis.MontgomeryResolventHeatFamily

/-! # Spatial and spectral marginals of the resolvent heat mixture

Each positive heat time gives an admissible actual Weil test. Integrating
in heat time gives the translated bilateral exponential in space and its
rational transform on the critical strip, including both pole evaluations.
-/

noncomputable section
open MeasureTheory Complex Set Filter
namespace RiemannResearch.Analysis.MontgomeryResolventHeatEvaluation
open MontgomeryResolventWeilTest MontgomeryResolventHeatFamily MontgomeryFiniteResolventSignal
open MontgomeryHeatKernelMixture GaussianPolynomialFourier GaussianLaplaceBridge

theorem heatGaussian_spatial_factor (u t v y : ℝ) : heatGaussian u t v y =
    Complex.exp ((-(t:ℂ)*I)*((y-u:ℝ):ℂ)) *
      (2*(Real.exp (-v) : ℂ)*density v (y-u)) := by
  rw [heatGaussian_eq_density,Complex.ofReal_exp]
  push_cast
  ring

theorem heatGaussian_spatial_integrable (u t y : ℝ) :
    IntegrableOn (fun v : ℝ => heatGaussian u t v y) (Ioi 0) := by
  simp_rw [heatGaussian_spatial_factor]
  exact (gaussian_mixture_integrable (y-u)).const_mul _

theorem integral_heatGaussian (u t y : ℝ) :
    (∫ v : ℝ in Ioi 0, heatGaussian u t v y) = cutoffTest u t y := by
  simp_rw [heatGaussian_spatial_factor]
  rw [integral_const_mul,gaussian_mixture,cutoffTest]
  push_cast; ring

theorem integral_norm_heatGaussian (u t y : ℝ) :
    (∫ v : ℝ in Ioi 0, ‖heatGaussian u t v y‖) = Real.exp (-|y-u|) := by
  have he (v : ℝ) (hv : 0 < v) : ‖heatGaussian u t v y‖ =
      (2*(Real.exp (-v) : ℂ)*density v (y-u)).re := by
    let d : ℝ := Real.exp (-(y-u)^2/(4*v))/Real.sqrt (4*Real.pi*v)
    let A : ℝ := 2*Real.exp (-v)*d
    have hA : 0 ≤ A := by dsimp only [A,d]; positivity
    have hreal : 2*(Real.exp (-v) : ℂ)*density v (y-u) = (A:ℂ) := by
      simp only [A,d,density_eq_real,Complex.ofReal_mul,Complex.ofReal_ofNat]
    have hp : ‖Complex.exp ((-(t:ℂ)*I)*((y-u:ℝ):ℂ))‖ = 1 := by
      rw [Complex.norm_exp]; simp
    rw [heatGaussian_spatial_factor,norm_mul,hreal,hp,one_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hA,Complex.ofReal_re]
  rw [setIntegral_congr_fun measurableSet_Ioi he]
  have hs := integral_re (gaussian_mixture_integrable (y-u))
  change _ = ((Real.exp (-|y-u|) : ℂ)).re
  exact hs.trans (congrArg Complex.re (gaussian_mixture (y-u)))

/-- Shifted spectral rate; Re(rate) is strictly positive on the closed strip. -/
def spectralRate (ρ : ℂ) (t : ℝ) : ℂ := 1-(ρ-1/2-(t:ℂ)*I)^2

theorem spectralRate_re (ρ : ℂ) (t : ℝ) :
    (spectralRate ρ t).re = 1-(ρ.re-1/2)^2+(ρ.im-t)^2 := by
  simp only [spectralRate,pow_two,Complex.sub_re,Complex.sub_im,Complex.one_re,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im]
  norm_num <;> ring

theorem spectralRate_re_pos (ρ : ℂ) (t : ℝ) (hρ : |ρ.re-1/2| ≤ 1/2) :
    0 < (spectralRate ρ t).re := by
  have h := (sq_abs _).symm.le.trans (pow_le_pow_left₀ (abs_nonneg _) hρ 2)
  rw [spectralRate_re]
  nlinarith only [h,sq_nonneg (ρ.im-t)]

private theorem transform_heat_factor (u t : ℝ) (ρ : ℂ) {v : ℝ} (hv : 0 < v) :
    Zeta23.paperFT (heatGaussian u t v) (Zeta23.gammaOf ρ) =
      (2*Complex.exp ((u:ℂ)*(ρ-1/2))) * exponentialKernel 1 (spectralRate ρ t) v := by
  rw [paperFT_heatGaussian _ _ hv]
  simp [exponentialKernel,spectralRate]

theorem heat_transform_time_integrable (u t : ℝ) (ρ : ℂ) (hρ : |ρ.re-1/2| ≤ 1/2) :
    IntegrableOn (fun v : ℝ => Zeta23.paperFT (heatGaussian u t v) (Zeta23.gammaOf ρ)) (Ioi 0) := by
  apply ((exponentialKernel_integrable 1 (spectralRate ρ t) (spectralRate_re_pos ρ t hρ)).const_mul
    (2*Complex.exp ((u:ℂ)*(ρ-1/2)))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact (transform_heat_factor u t ρ hv).symm

theorem integral_heat_transform (u t : ℝ) (ρ : ℂ) (hρ : |ρ.re-1/2| ≤ 1/2) :
    (∫ v : ℝ in Ioi 0, Zeta23.paperFT (heatGaussian u t v) (Zeta23.gammaOf ρ)) =
      Zeta23.paperFT (cutoffTest u t) (Zeta23.gammaOf ρ) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun v hv => transform_heat_factor u t ρ hv),
    integral_const_mul,exponentialKernel_integral _ _ (spectralRate_re_pos ρ t hρ)]
  have he : (ρ-1/2:ℂ).re=ρ.re-1/2 := by norm_num
  rw [paperFT_cutoffTest _ _ _ (by rw [he]; exact hρ.trans_lt (by norm_num))]
  simp only [Nat.cast_one,spectralRate,rationalTerm]; ring

theorem gammaOf_centralPoint (r : ℝ) :
    Zeta23.gammaOf (1/2+(r:ℂ)*I) = (r:ℂ) := by
  unfold Zeta23.gammaOf
  field_simp <;> ring

theorem heat_transform_real (u t r : ℝ) {v : ℝ} (hv : 0 < v) :
    Zeta23.paperFT (heatGaussian u t v) (r:ℂ) =
      (2*Complex.exp ((u:ℂ)*(r:ℂ)*I))*exponentialKernel 1 ((1+(r-t)^2:ℝ):ℂ) v := by
  let ρ : ℂ := 1/2+(r:ℂ)*I
  have hc : ρ-1/2=(r:ℂ)*I := by dsimp [ρ]; ring
  have hd : spectralRate ρ t = ((1+(r-t)^2 : ℝ) : ℂ) := by
    unfold spectralRate
    rw [hc,show (r:ℂ)*I-(t:ℂ)*I = ((r:ℂ)-(t:ℂ))*I by ring,mul_pow,Complex.I_sq]
    push_cast; ring
  calc
    _ = Zeta23.paperFT (heatGaussian u t v) (Zeta23.gammaOf ρ) := by rw [gammaOf_centralPoint]
    _ = _ := by rw [transform_heat_factor u t ρ hv,hc,hd,← mul_assoc (u:ℂ) (r:ℂ) I]

theorem cutoff_transform_real (u t r : ℝ) :
    Zeta23.paperFT (cutoffTest u t) (r:ℂ) =
      Complex.exp ((u:ℂ)*(r:ℂ)*I)*((2/(1+(r-t)^2) : ℝ) : ℂ) := by
  have h := integral_heat_transform u t (1/2+(r:ℂ)*I) (by norm_num)
  rw [gammaOf_centralPoint] at h
  rw [← h,setIntegral_congr_fun measurableSet_Ioi (fun v hv => heat_transform_real u t r hv),
    integral_const_mul,exponentialKernel_integral 1 ((1+(r-t)^2 : ℝ) : ℂ)
      (show 0 < 1+(r-t)^2 by positivity)]
  push_cast; ring

end RiemannResearch.Analysis.MontgomeryResolventHeatEvaluation

namespace RiemannResearch.Analysis.MontgomeryResolventHeatEvaluation

/--
info: 'RiemannResearch.Analysis.MontgomeryResolventHeatEvaluation.integral_heatGaussian' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms integral_heatGaussian

end RiemannResearch.Analysis.MontgomeryResolventHeatEvaluation

namespace RiemannResearch.Analysis.MontgomeryResolventHeatEvaluation

/--
info: 'RiemannResearch.Analysis.MontgomeryResolventHeatEvaluation.integral_norm_heatGaussian' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms integral_norm_heatGaussian

end RiemannResearch.Analysis.MontgomeryResolventHeatEvaluation

namespace RiemannResearch.Analysis.MontgomeryResolventHeatEvaluation

/--
info: 'RiemannResearch.Analysis.MontgomeryResolventHeatEvaluation.integral_heat_transform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms integral_heat_transform

end RiemannResearch.Analysis.MontgomeryResolventHeatEvaluation

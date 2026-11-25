import RiemannResearch.Analysis.MontgomeryResolventHeatEvaluation
import RiemannResearch.Analysis.MontgomeryResolventGammaKernel

/-! # Absolute heat-time exchange for the Archimedean term -/

noncomputable section
open MeasureTheory Complex Set Filter
namespace RiemannResearch.Analysis.MontgomeryResolventGammaMixture
open MontgomeryResolventWeilTest MontgomeryResolventHeatFamily MontgomeryResolventHeatEvaluation
open MontgomeryResolventGammaKernel GaussianLaplaceBridge

private theorem heat_gammaKernel (u t r : ℝ) {v : ℝ} (hv : 0 < v) :
    Zeta23.paperFT (heatGaussian u t v) (r:ℂ)*(Zeta23.EF.gammaBracket r:ℂ) = gammaKernel u t r v := by
  rw [heat_transform_real _ _ _ hv,gammaKernel]
  ring

theorem heat_gamma_integrable (u t : ℝ) :
    IntegrableOn (fun v : ℝ => ∫ r : ℝ,
      Zeta23.paperFT (heatGaussian u t v) (r:ℂ)*(Zeta23.EF.gammaBracket r:ℂ)) (Ioi 0) := by
  apply (gamma_kernel_integrable u t).integral_prod_right.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact integral_congr_ae (ae_of_all _ fun r => (heat_gammaKernel u t r hv).symm)

theorem integral_heat_gamma (u t : ℝ) :
    (∫ v : ℝ in Ioi 0, ∫ r : ℝ, Zeta23.paperFT (heatGaussian u t v) (r:ℂ)*(Zeta23.EF.gammaBracket r:ℂ)) =
      ∫ r : ℝ, Zeta23.paperFT (cutoffTest u t) (r:ℂ)*(Zeta23.EF.gammaBracket r:ℂ) := by
  calc
    _ = ∫ v : ℝ in Ioi 0, ∫ r : ℝ, gammaKernel u t r v := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv; exact integral_congr_ae (ae_of_all _ fun r => heat_gammaKernel u t r hv)
    _ = ∫ r : ℝ, ∫ v : ℝ in Ioi 0, gammaKernel u t r v := (integral_integral_swap (gamma_kernel_integrable u t)).symm
    _ = _ := by
      apply integral_congr_ae (ae_of_all _ ?_)
      intro r
      have h := integral_heat_transform u t (1/2+(r:ℂ)*I) (by norm_num)
      rw [gammaOf_centralPoint] at h
      rw [setIntegral_congr_fun measurableSet_Ioi (fun v hv => (heat_gammaKernel u t r hv).symm),
        integral_mul_const,h]

end RiemannResearch.Analysis.MontgomeryResolventGammaMixture

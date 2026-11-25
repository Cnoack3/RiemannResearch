import RiemannResearch.Analysis.MontgomeryResolventGammaMixture

/-! # Signed logarithmic part of the all-zero archimedean term -/

noncomputable section
open MeasureTheory Complex Set
namespace RiemannResearch.Analysis.MontgomeryResolventGammaCentering
open MontgomeryResolventWeilTest MontgomeryResolventHeatEvaluation MontgomeryResolventGammaMixture
open MontgomeryHeatKernelMixture MontgomeryResolventGamma MontgomeryResolventGammaKernel

theorem gamma_term_eq_centered {u : ℝ} (hu : 0 ≤ u) (t : ℝ) :
    (1/(2*(Real.pi:ℂ)))*(∫ r : ℝ, Zeta23.paperFT (cutoffTest u t) (r:ℂ)*(Zeta23.EF.gammaBracket r:ℂ)) =
      Complex.exp (I*(u:ℂ)*t)*((Real.exp (-u)*Real.log (|t|+2):ℝ):ℂ) +
      (1/(2*(Real.pi:ℂ)))*gammaVariation u t := by
  let L := Real.log (|t|+2)
  let k := fun h : ℝ => Complex.exp (I*(u:ℂ)*(t+h))*((2/(1+h^2):ℝ):ℂ)
  have hk : Integrable k := angular_integrable _ _
  have ha : Integrable (fun h : ℝ => k h*(Zeta23.EF.gammaBracket (t+h):ℂ)) := by
    have hi := (abs_gammaBracket_weight_integrable t).comp_add_right t
    apply hi.mono' (by
      have hg : Continuous (fun h : ℝ => Zeta23.EF.gammaBracket (t+h)) :=
        gammaBracket_continuous.comp (continuous_const.add continuous_id)
      exact hk.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp hg).aestronglyMeasurable)
    filter_upwards [] with h
    have hp : ‖Complex.exp (I*(u:ℂ)*(t+h))‖=1 := by rw [Complex.norm_exp]; simp
    dsimp [k]
    rw [norm_mul,norm_mul,hp,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity),
      Complex.norm_real,Real.norm_eq_abs,add_comm h t,add_sub_cancel_left]
    exact le_of_eq (by ring)
  have hs (h : ℝ) : Zeta23.paperFT (cutoffTest u t) ((h+t:ℝ):ℂ)*(Zeta23.EF.gammaBracket (h+t):ℂ) =
      k h*(Zeta23.EF.gammaBracket (t+h):ℂ) := by
    rw [cutoff_transform_real,add_sub_cancel_right,add_comm h t]
    dsimp [k]; push_cast
    rw [show (u:ℂ)*((t:ℂ)+h)*I=I*(u:ℂ)*((t:ℂ)+h) by ring]
  have hv : gammaVariation u t =
      (∫ h : ℝ, k h*(Zeta23.EF.gammaBracket (t+h):ℂ)) - (∫ h : ℝ, k h*(L:ℂ)) := by
    rw [← integral_sub ha (hk.mul_const _)]
    unfold gammaVariation
    apply integral_congr_ae (ae_of_all _ ?_)
    intro h; dsimp [k,L]; rw [gammaBracket_eq_mu]; push_cast; ring
  have hang : (∫ h : ℝ, k h) = Complex.exp (I*(u:ℂ)*t)*((2*Real.pi*Real.exp (-u):ℝ):ℂ) := by
    have he (h : ℝ) : k h = Complex.exp (I*(u:ℂ)*t)*(Complex.exp (I*(u:ℂ)*h)*((2/(1+h^2):ℝ):ℂ)) := by
      dsimp [k]
      rw [mul_add,Complex.exp_add]; ring
    simp_rw [he]
    rw [integral_const_mul,angular_transform hu]
  rw [← integral_add_right_eq_self (μ := volume) (fun r : ℝ =>
    Zeta23.paperFT (cutoffTest u t) (r:ℂ)*(Zeta23.EF.gammaBracket r:ℂ)) t]
  simp_rw [hs]
  rw [hv,integral_mul_const,hang]
  dsimp [L]
  push_cast
  field_simp [Real.pi_ne_zero]
  <;> ring

end RiemannResearch.Analysis.MontgomeryResolventGammaCentering

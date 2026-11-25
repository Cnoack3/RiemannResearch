import RiemannResearch.Analysis.MontgomeryHeatKernelMixture
import RiemannResearch.Analysis.MontgomeryResolventGamma

/-! # Absolute convergence and angular transform of the Archimedean heat kernel -/

noncomputable section
open MeasureTheory Complex Set Filter
namespace RiemannResearch.Analysis.MontgomeryResolventGammaKernel
open MontgomeryResolventGamma GaussianLaplaceBridge MontgomeryHeatKernelMixture

theorem gammaBracket_eq_mu (r : ℝ) : Zeta23.EF.gammaBracket r = 2*Real.pi*Zeta23.mu r := by
  unfold Zeta23.EF.gammaBracket Zeta23.mu
  field_simp [Real.pi_ne_zero]

theorem gammaBracket_continuous : Continuous Zeta23.EF.gammaBracket := by
  simp_rw [funext gammaBracket_eq_mu]
  exact Zeta23.mu_smooth.continuous.const_mul _

theorem abs_gammaBracket_weight_integrable (t : ℝ) :
    Integrable (fun r : ℝ => 2*|Zeta23.EF.gammaBracket r|/(1+(r-t)^2)) := by
  obtain ⟨C,hC,hB⟩ := gamma_centering_bound
  let M := 4*(1+t^2)*(C+5)
  have hm : Integrable (fun r : ℝ => M*(1+‖r‖^2)^(-(3/2:ℝ)/2)) :=
    (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
      (by rw [Module.finrank_self]; norm_num)).const_mul _
  have hc : Continuous (fun r : ℝ => 2*|Zeta23.EF.gammaBracket r|/(1+(r-t)^2)) :=
    (gammaBracket_continuous.abs.const_mul _).div (by fun_prop) (fun r => by positivity)
  apply hm.mono' hc.aestronglyMeasurable
  filter_upwards [] with r
  have hr : 0 < 1+r^2 := by positivity
  have hrt : 0 < 1+(r-t)^2 := by positivity
  have hB' : |Zeta23.EF.gammaBracket r| ≤ C+Real.log (|r|+2) := by
    have h := abs_add_le (2*Real.pi*Zeta23.mu r-Real.log (|r|+2)) (Real.log (|r|+2))
    rw [sub_add_cancel,abs_of_nonneg (Real.log_nonneg (by linarith [abs_nonneg r] : 1 ≤ |r|+2))] at h
    rw [gammaBracket_eq_mu]
    exact h.trans (add_le_add (hB r) le_rfl)
  have hlog := Zeta23.WeilEF.log_two_add_le (x := |r|) (abs_nonneg _)
  rw [sq_abs,add_comm 2] at hlog
  have hp : 1 ≤ (1+r^2:ℝ)^(1/4:ℝ) :=
    Real.one_le_rpow (by linarith [sq_nonneg r]) (by norm_num)
  have henv : |Zeta23.EF.gammaBracket r| ≤ (C+5)*(1+r^2)^(1/4:ℝ) := by
    linarith only [hB',hlog,le_mul_of_one_le_right hC hp]
  have hden : 1/(1+(r-t)^2) ≤ 2*(1+t^2)/(1+r^2) := by
    apply (div_le_div_iff₀ hrt hr).2
    nlinarith only [sq_nonneg (r-2*t),sq_nonneg ((r-t)*t)]
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ 2*|Zeta23.EF.gammaBracket r|/(1+(r-t)^2))]
  calc
    _ = 2*|Zeta23.EF.gammaBracket r| *(1/(1+(r-t)^2)) := by ring
    _ ≤ (2*((C+5)*(1+r^2)^(1/4:ℝ)))*(2*(1+t^2)/(1+r^2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left henv (by positivity)) hden (by positivity) (by positivity)
    _ = _ := by
      dsimp [M]
      simp only [Real.norm_eq_abs,sq_abs]
      rw [show -(3/2:ℝ)/2=1/4-1 by norm_num,Real.rpow_sub hr,Real.rpow_one]
      ring

def gammaKernel (u t r v : ℝ) : ℂ :=
  ((2*Complex.exp ((u:ℂ)*(r:ℂ)*I))*(Zeta23.EF.gammaBracket r : ℂ)) *
    exponentialKernel 1 ((1+(r-t)^2:ℝ):ℂ) v

theorem gamma_kernel_integrable (u t : ℝ) :
    Integrable (fun p : ℝ × ℝ => gammaKernel u t p.1 p.2)
      (volume.prod (volume.restrict (Ioi (0:ℝ)))) := by
  have hc : Continuous (fun p : ℝ × ℝ => gammaKernel u t p.1 p.2) := by
    have hg : Continuous (fun p : ℝ × ℝ => Zeta23.EF.gammaBracket p.1) := gammaBracket_continuous.comp continuous_fst
    unfold gammaKernel exponentialKernel
    fun_prop
  have hi (r : ℝ) : IntegrableOn (gammaKernel u t r) (Ioi (0:ℝ)) := by
    unfold gammaKernel
    exact (exponentialKernel_integrable 1 ((1+(r-t)^2:ℝ):ℂ)
      (show 0 < 1+(r-t)^2 by positivity)).const_mul
      ((2*Complex.exp ((u:ℂ)*(r:ℂ)*I))*(Zeta23.EF.gammaBracket r:ℂ))
  refine (integrable_prod_iff hc.aestronglyMeasurable).2 ⟨ae_of_all _ hi,?_⟩
  have he (r : ℝ) : (∫ v : ℝ in Ioi 0, ‖gammaKernel u t r v‖) =
      2*|Zeta23.EF.gammaBracket r|/(1+(r-t)^2) := by
    have hp : ‖Complex.exp ((u:ℂ)*(r:ℂ)*I)‖=1 := by rw [Complex.norm_exp]; simp
    simp only [gammaKernel,norm_mul,hp,Complex.norm_ofNat,mul_one,integral_const_mul,
      exponentialKernel_integral_norm 1 ((1+(r-t)^2:ℝ):ℂ) (show 0 < 1+(r-t)^2 by positivity),
      Complex.ofReal_re,Complex.norm_real,Real.norm_eq_abs,Nat.cast_one]
    ring
  simpa only [he] using abs_gammaBracket_weight_integrable t

theorem angular_transform {u : ℝ} (hu : 0 ≤ u) :
    (∫ h : ℝ, Complex.exp (I*(u:ℂ)*h)*((2/(1+h^2):ℝ):ℂ)) =
      ((2*Real.pi*Real.exp (-u):ℝ):ℂ) := by
  have he (h : ℝ) : Complex.exp (I*(u:ℂ)*h)*((2/(1+h^2):ℝ):ℂ) =
      (2*(Real.pi:ℂ))*(((ProbabilityTheory.cauchyPDFReal 0 1 h:ℝ):ℂ)*Complex.exp (-(h:ℂ)*I*(-u))) := by
    have hp : ProbabilityTheory.cauchyPDFReal 0 1 h = Real.pi⁻¹*(1+h^2)⁻¹ := by
      unfold ProbabilityTheory.cauchyPDFReal; simp <;> ring_nf
    rw [hp,show -(h:ℂ)*I*(-(u:ℂ)) = I*(u:ℂ)*h by ring]
    push_cast
    field_simp [Real.pi_ne_zero]
    <;> ring
  simp_rw [he]
  have hh := integrated_cauchy (-u)
  simp only [Complex.ofReal_neg,abs_neg,abs_of_nonneg hu] at hh
  rw [integral_const_mul,hh]
  push_cast; ring

theorem angular_integrable (u t : ℝ) :
    Integrable (fun h : ℝ => Complex.exp (I*(u:ℂ)*(t+h))*((2/(1+h^2):ℝ):ℂ)) := by
  apply (integrable_inv_one_add_sq.const_mul (2:ℝ)).mono' (by fun_prop)
  filter_upwards [] with h
  have he : ‖Complex.exp (I*(u:ℂ)*(t+h))‖ = 1 := by rw [Complex.norm_exp]; simp
  rw [norm_mul,he,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)]
  exact le_of_eq (by ring)

end RiemannResearch.Analysis.MontgomeryResolventGammaKernel

namespace RiemannResearch.Analysis.MontgomeryResolventGammaKernel

/--
info: 'RiemannResearch.Analysis.MontgomeryResolventGammaKernel.gamma_kernel_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gamma_kernel_integrable

end RiemannResearch.Analysis.MontgomeryResolventGammaKernel

namespace RiemannResearch.Analysis.MontgomeryResolventGammaKernel

/--
info: 'RiemannResearch.Analysis.MontgomeryResolventGammaKernel.angular_transform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms angular_transform

end RiemannResearch.Analysis.MontgomeryResolventGammaKernel

import RiemannResearch.Analysis.GaussianPolynomialFourier
import RiemannResearch.Analysis.GaussianLaplaceBridge
import RiemannResearch.RH.CauchyFourierTransform

/-! # Resolvent mixture of the normalized real heat kernel

The heat-time mixture of the normalized Gaussian equals the bilateral
exponential, pointwise on the entire real line. Absolute Fubini follows
from the integrable reciprocal-square angular density. -/

noncomputable section
open MeasureTheory Complex Set Filter
open scoped NNReal ENNReal
namespace RiemannResearch.Analysis.MontgomeryHeatKernelMixture
open GaussianPolynomialFourier GaussianLaplaceBridge

private def integrand (y r v : ℝ) : ℂ :=
  (Real.pi : ℂ)⁻¹ * Complex.exp (-I*(y:ℂ)*r) *
    exponentialKernel 1 ((1+r^2 : ℝ) : ℂ) v

private theorem integrand_int (y r : ℝ) :
    IntegrableOn (integrand y r) (Ioi (0:ℝ)) :=
  (exponentialKernel_integrable 1 ((1+r^2 : ℝ) : ℂ) (show 0 < 1+r^2 by positivity)).const_mul _

private theorem integral_norm (y r : ℝ) :
    (∫ v : ℝ in Ioi 0, ‖integrand y r v‖) = Real.pi⁻¹*(1+r^2)⁻¹ := by
  simp only [integrand,norm_mul,integral_const_mul,exponentialKernel_integral_norm 1 ((1+r^2:ℝ):ℂ)
    (show 0 < 1+r^2 by positivity),Complex.ofReal_re,
    GaussianPolynomialFourier.norm_phase,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos Real.pi_pos,Nat.cast_one,one_div,mul_one]

private theorem integrable_prod (y : ℝ) : Integrable
    (fun p : ℝ × ℝ => integrand y p.1 p.2) (volume.prod (volume.restrict (Ioi (0:ℝ)))) := by
  have hc : Continuous (fun p : ℝ × ℝ => integrand y p.1 p.2) := by
    unfold integrand exponentialKernel; fun_prop
  refine (integrable_prod_iff hc.aestronglyMeasurable).2 ⟨ae_of_all _ (integrand_int y),?_⟩
  simpa only [integral_norm] using integrable_inv_one_add_sq.const_mul Real.pi⁻¹

private theorem integral_time (y r : ℝ) :
    (∫ v : ℝ in Ioi 0, integrand y r v) =
      ((ProbabilityTheory.cauchyPDFReal 0 1 r : ℝ) : ℂ) * Complex.exp (-(r:ℂ)*I*y) := by
  simp_rw [integrand]
  rw [integral_const_mul,exponentialKernel_integral 1 _
    (show 0 < 1+r^2 by positivity)]
  have hp : ProbabilityTheory.cauchyPDFReal 0 1 r = Real.pi⁻¹*(1+r^2)⁻¹ := by
    unfold ProbabilityTheory.cauchyPDFReal
    simp
    <;> ring_nf
  rw [hp]
  push_cast
  rw [show -(r:ℂ)*I*y = -I*(y:ℂ)*r by ring]
  ring

private theorem integral_frequency (y : ℝ) {v : ℝ} (hv : 0 < v) :
    (∫ r : ℝ, integrand y r v) = 2*(Real.exp (-v) : ℂ)*density v y := by
  have he (r : ℝ) : integrand y r v =
      ((Real.pi:ℂ)⁻¹*(Real.exp (-v) : ℂ)) *
        (Complex.exp (-I*(y:ℂ)*r)*gaussian v r) := by
    unfold integrand exponentialKernel gaussian
    rw [Complex.ofReal_exp]
    push_cast
    rw [show -((1:ℂ)+(r:ℂ)^2)*(v:ℂ) = -(v:ℂ) + (-(v:ℂ)*(r:ℂ)^2) by ring,Complex.exp_add]
    norm_num
    <;> ring
  simp_rw [he]
  rw [integral_const_mul, ← moment_zero hv y]
  simp only [moment,momentFunction,pow_zero,one_mul,transform]
  have hh : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  <;> ring

theorem integrated_cauchy (y : ℝ) :
    (∫ r : ℝ, ((ProbabilityTheory.cauchyPDFReal 0 1 r : ℝ) : ℂ) *
      Complex.exp (-(r:ℂ)*I*y)) = (Real.exp (-|y|) : ℂ) := by
  have h := RiemannResearch.RH.Pareto.SpectralObstruction.cauchyMeasure_integral_exp_neg_mul
    0 (1:ℝ≥0) (by norm_num) y
  rw [ProbabilityTheory.cauchyMeasure_of_scale_ne_zero 0 (by norm_num : (1:ℝ≥0) ≠ 0),
    integral_withDensity_eq_integral_toReal_smul (ProbabilityTheory.measurable_cauchyPDF 0 1)
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))] at h
  have hp (r : ℝ) : (ProbabilityTheory.cauchyPDF 0 1 r).toReal =
      ProbabilityTheory.cauchyPDFReal 0 1 r :=
    ENNReal.toReal_ofReal (ProbabilityTheory.cauchyPDF_pos 0 (by norm_num : (1:ℝ≥0) ≠ 0) r).le
  simp only [hp, Complex.real_smul,NNReal.coe_one,Complex.ofReal_one,Complex.ofReal_zero,
    zero_mul,sub_zero,neg_one_mul,Complex.ofReal_exp,Complex.ofReal_neg] at h ⊢
  exact h

/-- The time integral is absolutely convergent for each spatial argument. -/
theorem gaussian_mixture_integrable (y : ℝ) :
    IntegrableOn (fun v : ℝ => 2*(Real.exp (-v) : ℂ)*density v y) (Ioi 0) := by
  apply (integrable_prod y).integral_prod_right.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact integral_frequency y hv

/-- Exact spatial value at every y, including y=0. -/
theorem gaussian_mixture (y : ℝ) :
    (∫ v : ℝ in Ioi 0, 2*(Real.exp (-v) : ℂ)*density v y) = (Real.exp (-|y|) : ℂ) := by
  calc
    _ = ∫ v : ℝ in Ioi 0, ∫ r : ℝ, integrand y r v :=
      setIntegral_congr_fun measurableSet_Ioi (fun v hv => (integral_frequency y hv).symm)
    _ = ∫ r : ℝ, ∫ v : ℝ in Ioi 0, integrand y r v := (integral_integral_swap (integrable_prod y)).symm
    _ = _ := by simp_rw [integral_time]; exact integrated_cauchy y

end RiemannResearch.Analysis.MontgomeryHeatKernelMixture

namespace RiemannResearch.Analysis.MontgomeryHeatKernelMixture

/--
info: 'RiemannResearch.Analysis.MontgomeryHeatKernelMixture.gaussian_mixture' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gaussian_mixture

end RiemannResearch.Analysis.MontgomeryHeatKernelMixture

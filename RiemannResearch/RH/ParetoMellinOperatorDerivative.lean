import RiemannResearch.RH.ParetoMellinKernelPairing
import Mathlib.Analysis.Calculus.Deriv.Basic

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto

def mellinLineOperator (t : ℝ) : ThresholdHilbert →L[ℝ] ℂ :=
  paretoMellinContinuous (mellinLinePoint t) (by rw [mellinLinePoint_re]; norm_num)

def mellinLineDerivativeKernel (t x : ℝ) : ℂ := -Complex.I * mellinLogKernel t 1 x

theorem mellinLineKernel_memLp (t : ℝ) :
    MemLp (mellinLineKernel t) 2 (volume.restrict (Ioi 1)) :=
  paretoMellinKernel_memLp (mellinLinePoint t) (by rw [mellinLinePoint_re]; norm_num)
    (by norm_num : (0 : ℝ) < 1)

theorem mellinLineDerivativeKernel_memLp (t : ℝ) :
    MemLp (mellinLineDerivativeKernel t) 2 (volume.restrict (Ioi 1)) :=
  (mellinLogKernel_memLp t 1).const_mul (-Complex.I)

def mellinLineDerivativeOperator (t : ℝ) : ThresholdHilbert →L[ℝ] ℂ :=
  mellinKernelPairing (mellinLineDerivativeKernel t) (mellinLineDerivativeKernel_memLp t)

def mellinLineRemainderKernel (t h x : ℝ) : ℂ :=
  mellinLineKernel (t + h) x - mellinLineKernel t x - (h : ℂ) * mellinLineDerivativeKernel t x

theorem mellinLineRemainderKernel_memLp (t h : ℝ) :
    MemLp (mellinLineRemainderKernel t h) 2 (volume.restrict (Ioi 1)) :=
  ((mellinLineKernel_memLp (t + h)).sub (mellinLineKernel_memLp t)).sub
    ((mellinLineDerivativeKernel_memLp t).const_mul (h : ℂ))

theorem mellinLineKernel_add (t h : ℝ) {x : ℝ} (hx : 0 < x) :
    mellinLineKernel (t + h) x = mellinLineKernel t x *
      Complex.exp (Complex.I * ((-h * Real.log x : ℝ) : ℂ)) := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  simp only [mellinLineKernel, paretoMellinKernel, mellinLinePoint,
    Complex.cpow_def_of_ne_zero hxC, ← Complex.ofReal_log hx.le]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem mellinLineRemainderKernel_norm_le (t h : ℝ) {x : ℝ} (hx : 1 < x) :
    ‖mellinLineRemainderKernel t h x‖ ≤ 3 * h ^ 2 * ‖mellinLogKernel t 2 x‖ := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have heq : mellinLineRemainderKernel t h x = mellinLineKernel t x *
      (Complex.exp (Complex.I * ((-h * Real.log x : ℝ) : ℂ)) - 1 -
        Complex.I * ((-h * Real.log x : ℝ) : ℂ)) := by
    unfold mellinLineRemainderKernel
    rw [mellinLineKernel_add t h hx0]
    simp only [mellinLineDerivativeKernel, mellinLogKernel, pow_one]
    push_cast
    ring
  rw [heq, norm_mul, mellinLineKernel_norm t hx0]
  calc
    _ ≤ x⁻¹ * (3 * (-h * Real.log x) ^ 2) :=
      mul_le_mul_of_nonneg_left (norm_exp_imaginary_quadratic_remainder _)
        (inv_nonneg.mpr hx0.le)
    _ = _ := by
      rw [mellinLogKernel, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        sq_abs, mellinLineKernel_norm t hx0]
      ring

theorem mellinLineRemainder_pairing (t h : ℝ) :
    mellinKernelPairing (mellinLineRemainderKernel t h) (mellinLineRemainderKernel_memLp t h) =
      mellinLineOperator (t + h) - mellinLineOperator t - h • mellinLineDerivativeOperator t := by
  ext f
  have h1 := mellinKernelPairing_integrable (mellinLineKernel (t + h))
    (mellinLineKernel_memLp (t + h)) f
  have h0 := mellinKernelPairing_integrable (mellinLineKernel t) (mellinLineKernel_memLp t) f
  have hd := mellinKernelPairing_integrable (mellinLineDerivativeKernel t)
    (mellinLineDerivativeKernel_memLp t) f
  have hsub : IntegrableOn (fun x => mellinWeightedStep f x * mellinLineKernel (t + h) x -
      mellinWeightedStep f x * mellinLineKernel t x) (Ioi 1) := by
    simpa only [Pi.sub_apply] using! h1.sub h0
  change (∫ x in Ioi (1 : ℝ), mellinWeightedStep f x * mellinLineRemainderKernel t h x) =
    (∫ x in Ioi (1 : ℝ), mellinWeightedStep f x * mellinLineKernel (t + h) x) -
      (∫ x in Ioi (1 : ℝ), mellinWeightedStep f x * mellinLineKernel t x) -
        (h : ℂ) * ∫ x in Ioi (1 : ℝ), mellinWeightedStep f x * mellinLineDerivativeKernel t x
  have heq : (fun x => mellinWeightedStep f x * mellinLineRemainderKernel t h x) =
      fun x => (mellinWeightedStep f x * mellinLineKernel (t + h) x -
        mellinWeightedStep f x * mellinLineKernel t x) -
          (h : ℂ) * (mellinWeightedStep f x * mellinLineDerivativeKernel t x) := by
    funext x
    unfold mellinLineRemainderKernel
    ring
  rw [heq, integral_sub hsub (hd.const_mul (h : ℂ)), integral_sub h1 h0, integral_const_mul]

theorem mellinLineOperator_quadratic_remainder (t h : ℝ) :
    ‖mellinLineOperator (t + h) - mellinLineOperator t - h • mellinLineDerivativeOperator t‖ ≤
      (3 * Real.sqrt (∫ x in Ioi (1 : ℝ), ‖mellinLogKernel t 2 x‖ ^ 2)) * h ^ 2 := by
  let E : ℝ := ∫ x in Ioi (1 : ℝ), ‖mellinLogKernel t 2 x‖ ^ 2
  have hE : 0 ≤ E := integral_nonneg (fun _ => sq_nonneg _)
  have hR := mellinLineRemainderKernel_memLp t h
  have hK := mellinLogKernel_memLp t 2
  have hiR : IntegrableOn (fun x => ‖mellinLineRemainderKernel t h x‖ ^ 2) (Ioi 1) :=
    (memLp_two_iff_integrable_sq_norm hR.aestronglyMeasurable).mp hR
  have hiK : IntegrableOn (fun x => ‖mellinLogKernel t 2 x‖ ^ 2) (Ioi 1) :=
    (memLp_two_iff_integrable_sq_norm hK.aestronglyMeasurable).mp hK
  have henergy : (∫ x in Ioi (1 : ℝ), ‖mellinLineRemainderKernel t h x‖ ^ 2) ≤
      (3 * h ^ 2) ^ 2 * E := by
    rw [← integral_const_mul]
    apply integral_mono_ae hiR (hiK.const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hb := mellinLineRemainderKernel_norm_le t h hx
    have hp := mul_nonneg (sub_nonneg.mpr hb)
      (add_nonneg (by positivity : 0 ≤ 3 * h ^ 2 * ‖mellinLogKernel t 2 x‖)
        (norm_nonneg (mellinLineRemainderKernel t h x)))
    nlinarith
  rw [← mellinLineRemainder_pairing t h]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  have hb := mellinKernelPairing_norm_sq_le (mellinLineRemainderKernel t h) hR f
  have hb' := mul_le_mul_of_nonneg_left henergy (sq_nonneg ‖f‖)
  have heq : ((3 * Real.sqrt E) * h ^ 2 * ‖f‖) ^ 2 =
      ‖f‖ ^ 2 * ((3 * h ^ 2) ^ 2 * E) := by
    simp only [mul_pow]
    rw [Real.sq_sqrt hE]
    ring
  have hpos : 0 ≤ (3 * Real.sqrt E) * h ^ 2 * ‖f‖ := by positivity
  change ‖mellinKernelPairingValue (mellinLineRemainderKernel t h) f‖ ≤
    (3 * Real.sqrt E) * h ^ 2 * ‖f‖
  nlinarith [norm_nonneg (mellinKernelPairingValue (mellinLineRemainderKernel t h) f)]

theorem mellinLineOperator_hasDerivAt (t : ℝ) :
    HasDerivAt mellinLineOperator (mellinLineDerivativeOperator t) t := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  let B : ℝ := 3 * Real.sqrt (∫ x in Ioi (1 : ℝ), ‖mellinLogKernel t 2 x‖ ^ 2)
  have hB : 0 ≤ B := by positivity
  have hden : 0 < B + 1 := by linarith
  have hδ : 0 < c / (B + 1) := div_pos hc hden
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
  have hsmall : |h| < c / (B + 1) := by simpa [Metric.mem_ball, Real.dist_eq] using hh
  have hmul : |h| * (B + 1) < c := (lt_div_iff₀ hden).mp hsmall
  have hBh : B * |h| ≤ c := by nlinarith [abs_nonneg h]
  have hfinal := mul_le_mul_of_nonneg_right hBh (abs_nonneg h)
  have hrem := mellinLineOperator_quadratic_remainder t h
  change ‖mellinLineOperator (t + h) - mellinLineOperator t - h • mellinLineDerivativeOperator t‖ ≤ _
  rw [Real.norm_eq_abs]
  dsimp only [B] at hfinal
  nlinarith [sq_abs h]

end RiemannResearch.RH.Pareto

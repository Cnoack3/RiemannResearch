import RiemannResearch.RH.ParetoMellinFunctional
import RiemannResearch.RH.ParetoExponentialRealization
import Mathlib.Analysis.SpecialFunctions.Complex.Log

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

def mellinLinePoint (t : ℝ) : ℂ := 1 + (t : ℂ) * Complex.I

@[simp] theorem mellinLinePoint_re (t : ℝ) : (mellinLinePoint t).re = 1 := by
  simp [mellinLinePoint]

def mellinLineKernel (t x : ℝ) : ℂ := paretoMellinKernel (mellinLinePoint t) x

theorem mellinLineKernel_norm (t : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖mellinLineKernel t x‖ = x⁻¹ := by
  rw [mellinLineKernel, paretoMellinKernel, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp [mellinLinePoint, Real.rpow_neg_one]

theorem mellinLogPower_integrable (n : ℕ) :
    IntegrableOn (fun x : ℝ => Real.log x ^ n / x ^ 2) (Ioi 1) := by
  have hbase : IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-t)) (Ioi 0) := by
    have h := RamanujanLaguerre.allMomentsIntegrable_of_bounded
      (F := fun _ => 1) (C := 1) (by simp) n
    have h' : IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-t)) (Ici 0) := by
      simpa [RamanujanLaguerre.exponentialLift] using h
    exact h'.mono_set Set.Ioi_subset_Ici_self
  have heq : (fun t : ℝ => Real.exp t •
      (Real.log (Real.exp t) ^ n / Real.exp t ^ 2)) =
      (fun t : ℝ => t ^ n * Real.exp (-t)) := by
    funext t
    rw [Real.log_exp, smul_eq_mul, Real.exp_neg]
    field_simp [Real.exp_ne_zero]
  have h := (integrableOn_comp_exp_Ioi (fun x : ℝ => Real.log x ^ n / x ^ 2) 0)
  rw [heq, Real.exp_zero] at h
  exact h.mp hbase

def mellinLogKernel (t : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  (Real.log x : ℂ) ^ n * mellinLineKernel t x

theorem mellinLogKernel_memLp (t : ℝ) (n : ℕ) :
    MemLp (mellinLogKernel t n) 2 (volume.restrict (Ioi 1)) := by
  have hm : Measurable (mellinLogKernel t n) := by
    unfold mellinLogKernel mellinLineKernel paretoMellinKernel
    fun_prop
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply (mellinLogPower_integrable (2 * n)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (le_of_lt hx)
  have hpow : (Real.log x ^ n) ^ 2 = Real.log x ^ (2 * n) := by
    rw [← pow_mul, Nat.mul_comm n 2]
  rw [mellinLogKernel, norm_mul, norm_pow,
    mellinLineKernel_norm t (lt_trans zero_lt_one hx), Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hlog, mul_pow, hpow]
  simp [div_eq_mul_inv, inv_pow]

def mellinKernelPairingValue (K : ℝ → ℂ) (f : ThresholdHilbert) : ℂ :=
  ∫ x in Ioi (1 : ℝ), mellinWeightedStep f x * K x

theorem mellinKernelPairing_integrable (K : ℝ → ℂ)
    (hK : MemLp K 2 (volume.restrict (Ioi 1))) (f : ThresholdHilbert) :
    IntegrableOn (fun x => mellinWeightedStep f x * K x) (Ioi 1) :=
  (mellinWeightedStep_memLp f).integrable_mul hK

theorem mellinKernelPairing_norm_sq_le (K : ℝ → ℂ)
    (hK : MemLp K 2 (volume.restrict (Ioi 1))) (f : ThresholdHilbert) :
    ‖mellinKernelPairingValue K f‖ ^ 2 ≤
      ‖f‖ ^ 2 * ∫ x in Ioi (1 : ℝ), ‖K x‖ ^ 2 := by
  have h := RemoteLaplaceTail.norm_integral_mul_sq_le (mellinWeightedStep_memLp f) hK
  rwa [mellinWeightedStep_energy] at h

theorem mellinKernelPairing_norm_le (K : ℝ → ℂ)
    (hK : MemLp K 2 (volume.restrict (Ioi 1))) (f : ThresholdHilbert) :
    ‖mellinKernelPairingValue K f‖ ≤
      Real.sqrt (∫ x in Ioi (1 : ℝ), ‖K x‖ ^ 2) * ‖f‖ := by
  have hb := mellinKernelPairing_norm_sq_le K hK f
  have he : 0 ≤ ∫ x in Ioi (1 : ℝ), ‖K x‖ ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  have hs := Real.sq_sqrt he
  have hp : 0 ≤ Real.sqrt (∫ x in Ioi (1 : ℝ), ‖K x‖ ^ 2) * ‖f‖ := by positivity
  nlinarith [norm_nonneg (mellinKernelPairingValue K f)]

def mellinKernelPairing (K : ℝ → ℂ) (hK : MemLp K 2 (volume.restrict (Ioi 1))) :
    ThresholdHilbert →L[ℝ] ℂ :=
  ({ toFun := mellinKernelPairingValue K
     map_add' := by
       intro f g
       have he : (fun x => mellinWeightedStep (f + g) x * K x) =
           fun x => mellinWeightedStep f x * K x + mellinWeightedStep g x * K x := by
         funext x
         unfold mellinWeightedStep
         change ((hilbertSequenceLinear (f + g) ⌊x⌋₊ : ℝ) : ℂ) / (x : ℂ) * K x = _
         rw [map_add]
         simp [hilbertSequenceLinear, Complex.ofReal_add, add_div, add_mul]
       unfold mellinKernelPairingValue
       rw [he]
       exact integral_add (mellinKernelPairing_integrable K hK f)
         (mellinKernelPairing_integrable K hK g)
     map_smul' := by
       intro c f
       have he : (fun x => mellinWeightedStep (c • f) x * K x) =
           fun x => (c : ℂ) * (mellinWeightedStep f x * K x) := by
         funext x
         unfold mellinWeightedStep
         change ((hilbertSequenceLinear (c • f) ⌊x⌋₊ : ℝ) : ℂ) / (x : ℂ) * K x = _
         rw [map_smul]
         simp [hilbertSequenceLinear, Complex.ofReal_mul, mul_div_assoc, mul_assoc]
       unfold mellinKernelPairingValue
       rw [he, integral_const_mul]
       rfl } : ThresholdHilbert →ₗ[ℝ] ℂ).mkContinuous
    (Real.sqrt (∫ x in Ioi (1 : ℝ), ‖K x‖ ^ 2)) (mellinKernelPairing_norm_le K hK)

@[simp] theorem mellinKernelPairing_apply (K : ℝ → ℂ)
    (hK : MemLp K 2 (volume.restrict (Ioi 1))) (f : ThresholdHilbert) :
    mellinKernelPairing K hK f = mellinKernelPairingValue K f := rfl

theorem norm_exp_imaginary_quadratic_remainder (a : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - 1 - Complex.I * (a : ℂ)‖ ≤ 3 * a ^ 2 := by
  have hz : ‖Complex.I * (a : ℂ)‖ = |a| := by simp
  by_cases ha : |a| ≤ 1
  · have h := Complex.norm_exp_sub_one_sub_id_le (x := Complex.I * (a : ℂ))
      (by simpa only [hz] using ha)
    rw [hz, sq_abs] at h
    nlinarith [sq_nonneg a]
  · have hb : 1 ≤ |a| := le_of_lt (lt_of_not_ge ha)
    have h := norm_sub_le (Complex.exp (Complex.I * (a : ℂ)) - 1)
      (Complex.I * (a : ℂ))
    have hh := norm_sub_le (Complex.exp (Complex.I * (a : ℂ))) (1 : ℂ)
    have hu : ‖Complex.exp (Complex.I * (a : ℂ))‖ = 1 := by simp [Complex.norm_exp]
    rw [hu, norm_one] at hh
    rw [hz] at h
    nlinarith [sq_abs a, sq_nonneg (|a| - 1)]

end RiemannResearch.RH.Pareto

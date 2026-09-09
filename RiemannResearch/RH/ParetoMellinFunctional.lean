import RiemannResearch.RH.ParetoStepIsometry
import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.Analysis.RemoteLaplaceTail
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# The actual continuous Mellin functional on the Pareto Hilbert space

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Section 9.2. The functional is an actual Bochner integral of the physical
step sequence. Its continuity, sharp Cauchy bound and target value are
analytic theorems, with no zeta or RH assumptions.
-/

namespace RiemannResearch.RH.Pareto
open MeasureTheory Set
noncomputable section

/-- The unitary density factor of the physical step sequence. -/
def mellinWeightedStep (f : ThresholdHilbert) (x : ℝ) : ℂ :=
  (hilbertSequence f ⌊x⌋₊ : ℂ) / (x : ℂ)

def paretoMellinKernel (s : ℂ) (x : ℝ) : ℂ := (x : ℂ) ^ (-s)

def paretoMellin (f : ThresholdHilbert) (s : ℂ) : ℂ :=
  ∫ x in Ioi (1 : ℝ), mellinWeightedStep f x * paretoMellinKernel s x

theorem mellinWeightedStep_norm_sq (f : ThresholdHilbert) (x : ℝ) :
    ‖mellinWeightedStep f x‖ ^ 2 = hilbertSequence f ⌊x⌋₊ ^ 2 / x ^ 2 := by
  simp only [mellinWeightedStep, norm_div, Complex.norm_real, Real.norm_eq_abs,
    div_pow, sq_abs]

theorem mellinWeightedStep_measurable (f : ThresholdHilbert) :
    Measurable (mellinWeightedStep f) := by
  have hf : Measurable (fun x : ℝ => hilbertSequence f ⌊x⌋₊) :=
    (measurable_of_countable (hilbertSequence f)).comp Nat.measurable_floor
  exact (Complex.continuous_ofReal.measurable.comp hf).div
    Complex.continuous_ofReal.measurable

theorem mellinWeightedStep_memLp (f : ThresholdHilbert) :
    MemLp (mellinWeightedStep f) 2 (volume.restrict (Ioi (1 : ℝ))) := by
  apply (memLp_two_iff_integrable_sq_norm
    (mellinWeightedStep_measurable f).aestronglyMeasurable).2
  simp_rw [mellinWeightedStep_norm_sq]
  exact paretoStepEnergy_integrable _ (hilbertSequence_square_summable f)

theorem mellinWeightedStep_energy (f : ThresholdHilbert) :
    (∫ x in Ioi (1 : ℝ), ‖mellinWeightedStep f x‖ ^ 2) = ‖f‖ ^ 2 := by
  simp_rw [mellinWeightedStep_norm_sq]
  rw [paretoStep_energy_identity _ (hilbertSequence_square_summable f),
    hilbert_norm_weighted_sq]

theorem paretoMellinKernel_norm_sq (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖paretoMellinKernel s x‖ ^ 2 = x ^ (-(2 * s.re)) := by
  rw [paretoMellinKernel, Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.neg_re, ← Real.rpow_mul_natCast hx.le]
  congr 1
  norm_num
  ring

theorem paretoMellinKernel_memLp (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    {b : ℝ} (hb : 0 < b) :
    MemLp (paretoMellinKernel s) 2 (volume.restrict (Ioi b)) := by
  have hm : Measurable (paretoMellinKernel s) :=
    Complex.continuous_ofReal.measurable.pow_const (-s)
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2
  apply (integrableOn_Ioi_rpow_of_lt (by linarith : -(2 * s.re) < -1) hb).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (paretoMellinKernel_norm_sq s (lt_trans hb hx)).symm

/-- Exact square norm of the continuous kernel on any positive tail. -/
theorem paretoMellinKernel_energy (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    {b : ℝ} (hb : 0 < b) :
    (∫ x in Ioi b, ‖paretoMellinKernel s x‖ ^ 2) =
      b ^ (1 - 2 * s.re) / (2 * s.re - 1) := by
  calc
    _ = ∫ x in Ioi b, x ^ (-(2 * s.re)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact paretoMellinKernel_norm_sq s (lt_trans hb hx)
    _ = _ := by
      rw [integral_Ioi_rpow_of_lt (by linarith : -(2 * s.re) < -1) hb]
      rw [show -(2 * s.re) + 1 = 1 - 2 * s.re by ring]
      have he : 1 - 2 * s.re = -(2 * s.re - 1) := by ring
      rw [he, div_neg]
      ring

theorem paretoMellin_integrable (f : ThresholdHilbert) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) :
    IntegrableOn (fun x => mellinWeightedStep f x * paretoMellinKernel s x) (Ioi 1) := by
  exact (mellinWeightedStep_memLp f).integrable_mul
    (paretoMellinKernel_memLp s hs (by norm_num : (0 : ℝ) < 1))

/-- Cauchy--Schwarz in the genuine infinite Pareto norm. -/
theorem paretoMellin_norm_sq_le (f : ThresholdHilbert) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) :
    ‖paretoMellin f s‖ ^ 2 ≤ ‖f‖ ^ 2 / (2 * s.re - 1) := by
  have h := RemoteLaplaceTail.norm_integral_mul_sq_le
    (mellinWeightedStep_memLp f)
    (paretoMellinKernel_memLp s hs (by norm_num : (0 : ℝ) < 1))
  rw [mellinWeightedStep_energy, paretoMellinKernel_energy s hs (by norm_num)] at h
  simpa only [paretoMellin, Real.one_rpow, mul_one_div] using h

theorem paretoMellin_add (f g : ThresholdHilbert) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) :
    paretoMellin (f + g) s = paretoMellin f s + paretoMellin g s := by
  have he : mellinWeightedStep (f + g) = fun x => mellinWeightedStep f x +
      mellinWeightedStep g x := by
    funext x
    change ((hilbertSequenceLinear (f + g) ⌊x⌋₊ : ℝ) : ℂ) / (x : ℂ) = _
    rw [map_add]
    simp [mellinWeightedStep, hilbertSequenceLinear, Complex.ofReal_add, add_div]
  unfold paretoMellin
  simp_rw [he, add_mul]
  exact integral_add (paretoMellin_integrable f s hs) (paretoMellin_integrable g s hs)

theorem paretoMellin_smul (c : ℝ) (f : ThresholdHilbert) (s : ℂ) :
    paretoMellin (c • f) s = c • paretoMellin f s := by
  have he : mellinWeightedStep (c • f) = fun x => (c : ℂ) * mellinWeightedStep f x := by
    funext x
    change ((hilbertSequenceLinear (c • f) ⌊x⌋₊ : ℝ) : ℂ) / (x : ℂ) = _
    rw [map_smul]
    simp [mellinWeightedStep, hilbertSequenceLinear, Complex.ofReal_mul, mul_div_assoc]
  unfold paretoMellin
  simp_rw [he, mul_assoc]
  rw [integral_const_mul]
  rfl

theorem paretoMellin_norm_le (f : ThresholdHilbert) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) :
    ‖paretoMellin f s‖ ≤ Real.sqrt (1 / (2 * s.re - 1)) * ‖f‖ := by
  have hd : 0 < 2 * s.re - 1 := by linarith
  have hb := paretoMellin_norm_sq_le f s hs
  have he : (Real.sqrt (1 / (2 * s.re - 1)) * ‖f‖) ^ 2 =
      ‖f‖ ^ 2 / (2 * s.re - 1) := by
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 1 / (2 * s.re - 1))]
    ring
  have hp : 0 ≤ Real.sqrt (1 / (2 * s.re - 1)) * ‖f‖ := by positivity
  nlinarith [norm_nonneg (paretoMellin f s)]

/-- A bundled real-linear, complex-valued continuous Mellin functional. -/
def paretoMellinContinuous (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    ThresholdHilbert →L[ℝ] ℂ :=
  ({ toFun := fun f => paretoMellin f s
     map_add' := fun f g => paretoMellin_add f g s hs
     map_smul' := fun c f => paretoMellin_smul c f s } : ThresholdHilbert →ₗ[ℝ] ℂ).mkContinuous
    (Real.sqrt (1 / (2 * s.re - 1))) (fun f => paretoMellin_norm_le f s hs)

theorem paretoMellin_eq_step_integral (f : ThresholdHilbert) (s : ℂ) :
    paretoMellin f s =
      ∫ x in Ioi (1 : ℝ), (hilbertSequence f ⌊x⌋₊ : ℂ) * (x : ℂ)^(-s-1) := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans zero_lt_one hx))
  rw [Complex.cpow_sub (-s) 1 hx0, Complex.cpow_one]
  unfold mellinWeightedStep paretoMellinKernel
  ring

/-- The constant target has a nonzero transform throughout the continuity half-plane. -/
theorem paretoMellin_one (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    paretoMellin hilbertOne s = 1 / s := by
  rw [paretoMellin_eq_step_integral]
  have he : (∫ x in Ioi (1 : ℝ), (hilbertSequence hilbertOne ⌊x⌋₊ : ℂ) *
      (x : ℂ)^(-s-1)) = ∫ x in Ioi (1 : ℝ), (x : ℂ)^(-s-1) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    have hx' : (1 : ℝ) < x := hx
    have hf : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith : (0 : ℝ) ≤ x)).2 (by simpa using hx'.le)
    rw [hilbertOne_sequence]
    simp [zeroAnchor, show ⌊x⌋₊ ≠ 0 by omega]
  have hexp : (-s-1).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  rw [he, integral_Ioi_cpow_of_lt hexp (by norm_num : (0 : ℝ) < 1)]
  simp

/-- Exact tail Cauchy--Schwarz, before any arithmetic vanishing is imposed. -/
theorem paretoMellin_tail_norm_sq_le (f : ThresholdHilbert) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) {b : ℝ} (hb : 1 ≤ b) :
    ‖∫ x in Ioi b, mellinWeightedStep f x * paretoMellinKernel s x‖ ^ 2 ≤
      (∫ x in Ioi b, ‖mellinWeightedStep f x‖ ^ 2) *
        (b ^ (1 - 2 * s.re) / (2 * s.re - 1)) := by
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hf : MemLp (mellinWeightedStep f) 2 (volume.restrict (Ioi b)) :=
    MemLp.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi hb) le_rfl)
      (mellinWeightedStep_memLp f)
  have h := RemoteLaplaceTail.norm_integral_mul_sq_le hf (paretoMellinKernel_memLp s hs hb0)
  rw [paretoMellinKernel_energy s hs hb0] at h
  exact h

end
end RiemannResearch.RH.Pareto

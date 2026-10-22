import RiemannResearch.Analysis.BilateralLaplaceDifferential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Zero-moment primitives preserve superexponential decay

Source: independently developed standard integration estimate, September 29,
2026. The intended RH consumer is spectral zero removal from completed Nyman
tests. This file proves an analytic provider, not Weil positivity or RH.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace RiemannResearch.Analysis

noncomputable section
set_option backward.isDefEq.respectTransparency false

def leftPrimitive (f : ℝ → ℂ) (x : ℝ) : ℂ := ∫ t in Iic x, f t

theorem leftPrimitive_eq_neg_right {f : ℝ → ℂ} (hf : Integrable f)
    (hzero : ∫ t, f t = 0) (x : ℝ) :
    leftPrimitive f x = -(∫ t in Ioi x, f t) := by
  apply eq_neg_iff_add_eq_zero.mpr
  change (∫ t in Iic x, f t) + (∫ t in Ioi x, f t) = 0
  exact (intervalIntegral.integral_Iic_add_Ioi
      (hf.integrableOn : IntegrableOn f (Iic x))
      (hf.integrableOn : IntegrableOn f (Ioi x))).trans hzero

/-- The zero total integral is exactly what gives decay at both ends. -/
theorem leftPrimitive_norm_le {f : ℝ → ℂ} {C a : ℝ}
    (hf : Integrable f) (hzero : ∫ t, f t = 0) (ha : 0 < a)
    (hbound : ∀ x, ‖f x‖ ≤ C * Real.exp (-a * |x|)) (x : ℝ) :
    ‖leftPrimitive f x‖ ≤ (C / a) * Real.exp (-a * |x|) := by
  by_cases hx : x ≤ 0
  · have hb : ∀ᵐ t ∂volume.restrict (Iic x),
        ‖f t‖ ≤ C * Real.exp (a * t) := by
      filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
      have ht0 : t ≤ 0 := le_trans ht hx
      simpa only [abs_of_nonpos ht0, mul_neg, neg_mul, neg_neg] using hbound t
    have hi := (integrableOn_exp_mul_Iic ha x).const_mul C
    calc
      ‖leftPrimitive f x‖ ≤ ∫ t in Iic x, C * Real.exp (a * t) :=
        norm_integral_le_of_norm_le hi hb
      _ = (C / a) * Real.exp (-a * |x|) := by
        rw [integral_const_mul, integral_exp_mul_Iic ha]
        rw [abs_of_nonpos hx]
        rw [show -a * -x = a * x by ring]
        ring
  · have hx0 : 0 ≤ x := le_of_not_ge hx
    have hb : ∀ᵐ t ∂volume.restrict (Ioi x),
        ‖f t‖ ≤ C * Real.exp ((-a) * t) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (hbound t).trans_eq (by rw [abs_of_nonneg (le_trans hx0 ht.le)])
    have hi := (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) x).const_mul C
    rw [leftPrimitive_eq_neg_right hf hzero, norm_neg]
    calc
      ‖∫ t in Ioi x, f t‖ ≤ ∫ t in Ioi x, C * Real.exp ((-a) * t) :=
        norm_integral_le_of_norm_le hi hb
      _ = (C / a) * Real.exp (-a * |x|) := by
        rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos ha)]
        rw [abs_of_nonneg hx0]
        simp only [neg_div_neg_eq]
        ring

theorem SuperexponentialDecay.leftPrimitive {f : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (hfc : Continuous f)
    (hzero : ∫ t, f t = 0) : SuperexponentialDecay (leftPrimitive f) := by
  have hi : Integrable f := by
    apply (hf.integrable_weighted_norm hfc (a := 0) le_rfl).mono'
      hfc.aestronglyMeasurable
    exact ae_of_all _ (fun x => by simp)
  intro a ha
  obtain ⟨C, hC, hbound⟩ := hf a ha
  exact ⟨C / a, div_pos hC ha, leftPrimitive_norm_le hi hzero ha hbound⟩

theorem hasDerivAt_leftPrimitive {f : ℝ → ℂ} (hf : Integrable f)
    (hfc : Continuous f) (x : ℝ) : HasDerivAt (leftPrimitive f) (f x) x := by
  have heq : leftPrimitive f = fun y =>
      (∫ t in (0 : ℝ)..y, f t) + ∫ t in Iic (0 : ℝ), f t := by
    funext y
    exact eq_add_of_sub_eq (intervalIntegral.integral_Iic_sub_Iic
      (hf.integrableOn : IntegrableOn f (Iic (0 : ℝ)))
      (hf.integrableOn : IntegrableOn f (Iic y)))
  rw [heq]
  exact (intervalIntegral.integral_hasDerivAt_right
    (hfc.intervalIntegrable _ _)
    hfc.aestronglyMeasurable.stronglyMeasurableAtFilter hfc.continuousAt).add_const _

/-- Exact division by `s - 1/2`, stated without dividing at the removable point. -/
theorem centeredTransform_leftPrimitive {f : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (hfc : Continuous f)
    (hzero : ∫ t, f t = 0) (s : ℂ) :
    BilateralLaplace.centeredTransform f s =
      (s - 1 / 2) * BilateralLaplace.centeredTransform (leftPrimitive f) s := by
  have hi : Integrable f := by
    apply (hf.integrable_weighted_norm hfc (a := 0) le_rfl).mono'
      hfc.aestronglyMeasurable
    exact ae_of_all _ (fun x => by simp)
  have hd := hasDerivAt_leftPrimitive hi hfc
  have hc : Continuous (leftPrimitive f) :=
    (show Differentiable ℝ (leftPrimitive f) from fun x => (hd x).differentiableAt).continuous
  exact BilateralLaplace.centeredTransform_of_hasDerivAt
    ((hf.leftPrimitive hfc hzero).hasExponentialMoments hc)
    (hf.hasExponentialMoments hfc) hd s

/-- Multiplying by one complex exponential preserves decay faster than every
real exponential. -/
theorem SuperexponentialDecay.exp_mul {f : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (c : ℂ) :
    SuperexponentialDecay (fun x => Complex.exp (c * (x : ℂ)) * f x) := by
  intro a ha
  obtain ⟨C, hC, hbound⟩ := hf (a + |c.re|) (by positivity)
  refine ⟨C, hC, fun x => ?_⟩
  have harg : c.re * x ≤ |c.re| * |x| := by
    simpa only [abs_mul] using (le_abs_self (c.re * x))
  have he : ‖Complex.exp (c * (x : ℂ))‖ ≤ Real.exp (|c.re| * |x|) := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (by simpa using harg)
  calc
    ‖Complex.exp (c * (x : ℂ)) * f x‖ =
        ‖Complex.exp (c * (x : ℂ))‖ * ‖f x‖ := norm_mul _ _
    _ ≤ Real.exp (|c.re| * |x|) * (C * Real.exp (-(a + |c.re|) * |x|)) :=
      mul_le_mul he (hbound x) (norm_nonneg _) (Real.exp_nonneg _)
    _ = C * Real.exp (-a * |x|) := by
      rw [show Real.exp (|c.re| * |x|) *
        (C * Real.exp (-(a + |c.re|) * |x|)) =
        C * (Real.exp (|c.re| * |x|) * Real.exp (-(a + |c.re|) * |x|)) by ring,
        ← Real.exp_add]
      congr 2
      ring

theorem centeredTransform_exp_mul (f : ℝ → ℂ) (c s : ℂ) :
    BilateralLaplace.centeredTransform
      (fun x => Complex.exp (c * (x : ℂ)) * f x) s =
      BilateralLaplace.centeredTransform f (s - c) := by
  unfold BilateralLaplace.centeredTransform BilateralLaplace.transform
    BilateralLaplace.kernel
  apply integral_congr_ae
  apply ae_of_all
  intro x
  calc
    Complex.exp (c * (x : ℂ)) * f x * Complex.exp (-(s - 1 / 2) * (x : ℂ)) =
        f x * (Complex.exp (c * (x : ℂ)) *
          Complex.exp (-(s - 1 / 2) * (x : ℂ))) := by ring
    _ = f x * Complex.exp (-((s - c) - 1 / 2) * (x : ℂ)) := by
      rw [← Complex.exp_add]
      congr 2
      ring

/-- The genuine physical inverse of `D - (z - 1/2)`. Its opposite-tail
representation is valid precisely when the transform vanishes at `z`. -/
def removeTransformZero (f : ℝ → ℂ) (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp ((z - 1 / 2) * (x : ℂ)) *
    leftPrimitive (fun y => Complex.exp (-(z - 1 / 2) * (y : ℂ)) * f y) x

theorem removeTransformZero_properties {f : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (hfc : Continuous f) {z : ℂ}
    (hz : BilateralLaplace.centeredTransform f z = 0) :
    SuperexponentialDecay (removeTransformZero f z) ∧
      Continuous (removeTransformZero f z) ∧
      ∀ s : ℂ, BilateralLaplace.centeredTransform f s =
        (s - z) * BilateralLaplace.centeredTransform (removeTransformZero f z) s := by
  let c : ℂ := z - 1 / 2
  let h : ℝ → ℂ := fun x => Complex.exp (-c * (x : ℂ)) * f x
  have hh : SuperexponentialDecay h := hf.exp_mul (-c)
  have hhc : Continuous h := by unfold h; fun_prop
  have hhzero : ∫ x, h x = 0 := by
    simpa only [BilateralLaplace.centeredTransform, BilateralLaplace.transform,
      BilateralLaplace.kernel, h, c, mul_comm] using hz
  have hi : Integrable h := by
    apply (hh.integrable_weighted_norm hhc (a := 0) le_rfl).mono'
      hhc.aestronglyMeasurable
    exact ae_of_all _ (fun x => by simp)
  have hPc : Continuous (leftPrimitive h) :=
    (show Differentiable ℝ (leftPrimitive h) from
      fun x => (hasDerivAt_leftPrimitive hi hhc x).differentiableAt).continuous
  refine ⟨(hh.leftPrimitive hhc hhzero).exp_mul c, ?_, ?_⟩
  · change Continuous (fun x : ℝ => Complex.exp (c * (x : ℂ)) * leftPrimitive h x)
    fun_prop
  · intro s
    have hp := centeredTransform_leftPrimitive hh hhc hhzero (s - c)
    have hs : (s - c) - -c = s := by ring
    have hc : (s - c) - 1 / 2 = s - z := by dsimp [c]; ring
    change BilateralLaplace.centeredTransform f s =
      (s - z) * BilateralLaplace.centeredTransform
        (fun x => Complex.exp (c * (x : ℂ)) * leftPrimitive h x) s
    rw [centeredTransform_exp_mul]
    simpa only [h, centeredTransform_exp_mul, hs, hc] using hp

/-- Removing one zero leaves every distinct transform zero intact. -/
theorem centeredTransform_removeTransformZero_zero_of_ne {f : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (hfc : Continuous f) {z w : ℂ}
    (hz : BilateralLaplace.centeredTransform f z = 0)
    (hw : BilateralLaplace.centeredTransform f w = 0) (hwz : w ≠ z) :
    BilateralLaplace.centeredTransform (removeTransformZero f z) w = 0 := by
  have h := (removeTransformZero_properties hf hfc hz).2.2 w
  rw [hw] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (sub_ne_zero.mpr hwz)

/-- At the removed zero, the new transform equals the old derivative.
In particular a simple zero becomes a non-null evaluation. -/
theorem centeredTransform_removeTransformZero_at_zero {f : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (hfc : Continuous f) {z : ℂ}
    (hz : BilateralLaplace.centeredTransform f z = 0) :
    deriv (BilateralLaplace.centeredTransform f) z =
      BilateralLaplace.centeredTransform (removeTransformZero f z) z := by
  obtain ⟨hg, hgc, heq⟩ := removeTransformZero_properties hf hfc hz
  have hgd := BilateralLaplace.differentiable_centeredTransform
    (hg.hasExponentialMoments hgc)
  have hp := (((hasDerivAt_id z).sub_const z).mul (hgd z).hasDerivAt).deriv
  have he : BilateralLaplace.centeredTransform f = fun s =>
      (s - z) * BilateralLaplace.centeredTransform (removeTransformZero f z) s :=
    funext heq
  rw [he]
  simpa only [id_eq, Pi.mul_def, sub_self, one_mul, zero_mul, add_zero] using hp

end
end RiemannResearch.Analysis

import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import RiemannResearch.Analysis.RemoteLaplaceTail

/-!
# Weighted energy and holomorphic Mellin integrals

For measurable f, finite integral of ||f(x)||^2 x^(-s-1) on (1,infinity)
implies convergence and holomorphy of its Mellin integral on Re(z)>s/2.
The point-evaluation bound has the exact coefficient 1/(2*Re(z)-s).
The derivative is the integral with the additional factor -log(x).

Source: user-requested companion
RH_Energy_Holomorphy_Hardy_Implications_2026-09-18.md, energy-to-holomorphy
argument. Cauchy--Schwarz and dominated differentiation are the proof strategy.
The concrete RH consumer is RH/ChebyshevEnergyHardy. No arithmetic energy
estimate is assumed as an axiom or established by this generic result.
-/

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace MeasureTheory.WeightedMellin

def transform (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ x in Ioi (1 : ℝ), f x * (x : ℂ) ^ (-z - 1)

def energy (f : ℝ → ℂ) (s : ℝ) : ℝ :=
  ∫ x in Ioi (1 : ℝ), ‖f x‖ ^ 2 * x ^ (-s - 1)

def FiniteEnergy (f : ℝ → ℂ) (s : ℝ) : Prop :=
  Measurable f ∧ IntegrableOn (fun x : ℝ => ‖f x‖ ^ 2 * x ^ (-s - 1)) (Ioi 1)

def density (f : ℝ → ℂ) (s : ℝ) (x : ℝ) : ℂ :=
  f x * (x : ℂ) ^ (((-(s + 1) / 2 : ℝ) : ℂ))

def kernel (s : ℝ) (z : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (-z + (((s - 1) / 2 : ℝ) : ℂ))

theorem density_norm_sq (f : ℝ → ℂ) (s : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖density f s x‖ ^ 2 = ‖f x‖ ^ 2 * x ^ (-s - 1) := by
  rw [density, norm_mul, mul_pow, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.ofReal_re]
  rw [← Real.rpow_mul_natCast hx.le]
  congr 2
  push_cast
  ring

theorem density_memLp {f : ℝ → ℂ} {s : ℝ} (hf : FiniteEnergy f s) :
    MemLp (density f s) 2 (volume.restrict (Ioi 1)) := by
  have hm : Measurable (density f s) :=
    hf.1.mul (Complex.continuous_ofReal.measurable.pow_const _)
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2
  apply hf.2.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (density_norm_sq f s (lt_trans zero_lt_one hx)).symm

theorem density_energy (f : ℝ → ℂ) (s : ℝ) :
    (∫ x in Ioi (1 : ℝ), ‖density f s x‖ ^ 2) = energy f s := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  exact density_norm_sq f s (lt_trans zero_lt_one hx)

theorem kernel_norm_sq (s : ℝ) (z : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖kernel s z x‖ ^ 2 = x ^ (s - 2 * z.re - 1) := by
  rw [kernel, Complex.norm_cpow_eq_rpow_re_of_pos hx, ← Real.rpow_mul_natCast hx.le]
  congr 1
  simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re]
  push_cast
  ring

theorem kernel_memLp (s : ℝ) (z : ℂ) (hz : s / 2 < z.re) :
    MemLp (kernel s z) 2 (volume.restrict (Ioi (1 : ℝ))) := by
  have hm : Measurable (kernel s z) := Complex.continuous_ofReal.measurable.pow_const _
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2
  apply (integrableOn_Ioi_rpow_of_lt (by linarith : s - 2 * z.re - 1 < -1)
    (by norm_num : (0 : ℝ) < 1)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (kernel_norm_sq s z (lt_trans zero_lt_one hx)).symm

theorem kernel_energy (s : ℝ) (z : ℂ) (hz : s / 2 < z.re) :
    (∫ x in Ioi (1 : ℝ), ‖kernel s z x‖ ^ 2) = 1 / (2 * z.re - s) := by
  calc
    _ = ∫ x in Ioi (1 : ℝ), x ^ (s - 2 * z.re - 1) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact kernel_norm_sq s z (lt_trans zero_lt_one hx)
    _ = _ := by
      rw [integral_Ioi_rpow_of_lt (by linarith : s - 2 * z.re - 1 < -1)
        (by norm_num : (0 : ℝ) < 1), Real.one_rpow]
      rw [show s - 2 * z.re - 1 + 1 = -(2 * z.re - s) by ring, div_neg]
      ring

theorem density_mul_kernel (f : ℝ → ℂ) (s : ℝ) (z : ℂ) {x : ℝ} (hx : 0 < x) :
    density f s x * kernel s z x = f x * (x : ℂ) ^ (-z - 1) := by
  rw [density, kernel, mul_assoc, ← Complex.cpow_add _ _
    (Complex.ofReal_ne_zero.mpr hx.ne')]
  congr 2
  push_cast
  ring

theorem transform_integrable {f : ℝ → ℂ} {s : ℝ} (hf : FiniteEnergy f s)
    {z : ℂ} (hz : s / 2 < z.re) :
    IntegrableOn (fun x : ℝ => f x * (x : ℂ) ^ (-z - 1)) (Ioi 1) := by
  apply ((density_memLp hf).integrable_mul (kernel_memLp s z hz)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact density_mul_kernel f s z (lt_trans zero_lt_one hx)

theorem transform_norm_sq_le {f : ℝ → ℂ} {s : ℝ} (hf : FiniteEnergy f s)
    {z : ℂ} (hz : s/2 < z.re) :
    ‖transform f z‖^2 ≤ energy f s / (2*z.re-s) := by
  have he : transform f z = ∫ x in Ioi (1:ℝ), density f s x * kernel s z x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact (density_mul_kernel f s z (lt_trans zero_lt_one hx)).symm
  rw [he]
  simpa only [density_energy, kernel_energy s z hz, div_eq_mul_inv, one_mul]
    using RemoteLaplaceTail.norm_integral_mul_sq_le (density_memLp hf) (kernel_memLp s z hz)

theorem transform_hasDerivAt {f : ℝ → ℂ} {s : ℝ} (hf : FiniteEnergy f s)
    {z : ℂ} (hz : s / 2 < z.re) :
    HasDerivAt (transform f)
      (∫ x in Ioi (1 : ℝ), -(f x * (x : ℂ)^(-z-1)) * (Real.log x : ℂ)) z := by
  let r : ℝ := (z.re - s / 2) / 4
  have hr : 0 < r := by dsimp [r]; linarith
  let a : ℝ := z.re - 2*r
  have ha : s / 2 < a := by dsimp [a,r]; linarith
  let F' : ℂ → ℝ → ℂ := fun w x => -(f x * (x : ℂ)^(-w-1)) * (Real.log x : ℂ)
  have hmeas (w : ℂ) : Measurable (fun x : ℝ => f x * (x : ℂ)^(-w-1)) :=
    hf.1.mul (Complex.continuous_ofReal.measurable.pow_const _)
  have hmeas' : Measurable (F' z) :=
    (hmeas z).neg.mul (Complex.continuous_ofReal.measurable.comp Real.measurable_log)
  have hbound : ∀ᵐ x ∂volume.restrict (Ioi (1 : ℝ)),
      ∀ w ∈ Metric.ball z r, ‖F' w x‖ ≤ (1/r) * ‖f x * (x : ℂ)^(-(a:ℂ)-1)‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    intro w hw
    have hwre : z.re - r < w.re := by
      have hb : ‖w-z‖ < r := by simpa [dist_eq_norm] using hw
      have hc := Complex.abs_re_le_norm (w-z)
      simp only [Complex.sub_re] at hc
      have := (abs_le.mp hc).1
      linarith
    dsimp [F']
    rw [norm_mul, norm_neg, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx.le)]
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    calc
      ‖f x‖ * x ^ (-w.re-1) * Real.log x
          ≤ ‖f x‖ * x ^ (-w.re-1) * (x^r/r) :=
        mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hx0.le hr)
          (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hx0.le _))
      _ = (1/r) * ‖f x‖ * x ^ (-w.re-1+r) := by
        rw [Real.rpow_add hx0]; ring
      _ ≤ (1/r) * ‖f x‖ * x ^ (-a-1) := by
        apply mul_le_mul_of_nonneg_left
        · apply Real.rpow_le_rpow_of_exponent_le hx.le
          dsimp [a]; linarith
        · positivity
      _ = _ := by
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.one_re]
        ring
  have hdiff : ∀ᵐ x ∂volume.restrict (Ioi (1 : ℝ)), ∀ w ∈ Metric.ball z r,
      HasDerivAt (fun w : ℂ => f x*(x:ℂ)^(-w-1)) (F' w x) w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro w _
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    have hd := (((hasDerivAt_id w).neg.sub_const 1).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hx0.ne'))).const_mul (f x)
    convert! hd using 1
    simp [F', Complex.ofReal_log hx0.le]
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z hr) (Filter.Eventually.of_forall fun w =>
      (hmeas w).aestronglyMeasurable)
    (transform_integrable hf hz) hmeas'.aestronglyMeasurable hbound
    ((transform_integrable hf (z := (a:ℂ)) ha).norm.const_mul (1/r)) hdiff).2

theorem transform_analyticAt {f : ℝ → ℂ} {s : ℝ} (hf : FiniteEnergy f s)
    {z : ℂ} (hz : s / 2 < z.re) : AnalyticAt ℂ (transform f) z := by
  have hd : DifferentiableOn ℂ (transform f) {w : ℂ | s/2 < w.re} :=
    fun w hw => (transform_hasDerivAt hf hw).differentiableAt.differentiableWithinAt
  exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
theorem finiteEnergy_mono {f : ℝ → ℂ} {s u : ℝ}
    (hf : FiniteEnergy f s) (hs : s ≤ u) : FiniteEnergy f u := by
  refine ⟨hf.1, hf.2.mono' ?_ ?_⟩
  · exact (hf.1.norm.pow_const 2 |>.mul (measurable_id.pow_const _)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_trans zero_le_one hx.le) _))]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)) (sq_nonneg _)

theorem energy_mono {f : ℝ → ℂ} {s u : ℝ}
    (hf : FiniteEnergy f s) (hs : s ≤ u) : energy f u ≤ energy f s := by
  apply integral_mono_ae (finiteEnergy_mono hf hs).2 hf.2
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)) (sq_nonneg _)

theorem energy_tendsto {f : ℝ → ℂ} {s : ℝ} (hf : FiniteEnergy f s)
    {u : ℕ → ℝ} (hu : ∀ n, s ≤ u n) (hlim : Tendsto u atTop (𝓝 s)) :
    Tendsto (fun n => energy f (u n)) atTop (𝓝 (energy f s)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun x : ℝ => ‖f x‖^2*x^(-s-1))
  · intro n
    exact (finiteEnergy_mono hf (hu n)).2.aestronglyMeasurable
  · exact hf.2
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_trans zero_le_one hx.le) _))]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith [hu n])) (sq_nonneg _)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    exact tendsto_const_nhds.mul
      ((Real.continuous_const_rpow hx0.ne').continuousAt.tendsto.comp
        (hlim.neg.sub_const 1))


end MeasureTheory.WeightedMellin

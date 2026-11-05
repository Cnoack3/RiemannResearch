import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Integrated Mellin and logarithmic moments of a series of carries

The assertion after (19) in C. Noack, *Prime trees, fractional parts, and
zeta zeros* (2026), follows from absolute integrability of a single
log-weighted majorant. Its finite extended-real mass supplies both ordinary
integrability of each summand and summability of their integrals. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace RiemannResearch.RH.PrimeTreeIntegratedCarries

/-- The signed logarithmic kernel of the j-th Mellin moment. -/
def momentKernel (s : ℂ) (j : ℕ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (-s - 1) * ((-Real.log x : ℝ) : ℂ) ^ j

@[simp] theorem momentKernel_zero (s : ℂ) (x : ℝ) :
    momentKernel s 0 x = (x : ℂ) ^ (-s - 1) := by simp [momentKernel]

/-- Written as a nonnegative integral so infinite masses cannot disappear
through the convention for an undefined Bochner integral. -/
def absoluteMass (C : ℝ → ℂ) (v : ℂ) (s : ℂ) (k : ℕ) : ℝ≥0∞ :=
  ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal
    (‖v‖ * ‖C x‖ * x ^ (-s.re - 1) * (1 + Real.log x) ^ k)

private theorem norm_kernel (s : ℂ) (j : ℕ) (x : ℝ) (hx : 1 < x) :
    ‖momentKernel s j x‖ = x ^ (-s.re - 1) * (Real.log x) ^ j := by
  simp [momentKernel, norm_mul, norm_pow,
    Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hx),
    Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx.le)]

/-- One absolute-integrability assumption gives the exact integral of the
complex series for every logarithmic moment through order k. -/
theorem integrated_moments (C : ℕ → ℝ → ℂ) (v : ℕ → ℂ) (s : ℂ) (k : ℕ)
    (hC : ∀ i, AEStronglyMeasurable (C i) (volume.restrict (Ioi (1 : ℝ))))
    (habs : (∑' i, absoluteMass (C i) (v i) s k) < ⊤) (j : ℕ) (hj : j ≤ k) :
    HasSum (fun i => ∫ x in Ioi (1 : ℝ), v i * C i x * momentKernel s j x)
      (∫ x in Ioi (1 : ℝ), (∑' i, v i * C i x) * momentKernel s j x) := by
  let μ := volume.restrict (Ioi (1 : ℝ))
  let F (i : ℕ) (x : ℝ) := v i * C i x * momentKernel s j x
  let mass (i : ℕ) := ∫⁻ x, ‖F i x‖ₑ ∂μ
  have hk : Measurable (momentKernel s j) := by unfold momentKernel; fun_prop
  have hF (i : ℕ) : AEStronglyMeasurable (F i) μ :=
    (aestronglyMeasurable_const.mul (hC i)).mul hk.aestronglyMeasurable
  have hmajor (i : ℕ) : mass i ≤ absoluteMass (C i) (v i) s k := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    have hx1 : 1 < x := hx
    have hxpos : 0 < x := zero_lt_one.trans hx1
    have hlog := Real.log_nonneg hx1.le
    have hpow : (Real.log x) ^ j ≤ (1 + Real.log x) ^ k :=
      (pow_le_pow_left₀ hlog (by linarith : Real.log x ≤ 1 + Real.log x) j).trans
        (pow_le_pow_right₀ (by linarith) hj)
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    change ‖v i * C i x * momentKernel s j x‖ ≤ _
    rw [norm_mul, norm_mul, norm_kernel _ _ _ hx1, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have htotal : (∑' i, mass i) < ⊤ := lt_of_le_of_lt (ENNReal.tsum_le_tsum hmajor) habs
  have hi (i : ℕ) : Integrable (F i) μ :=
    ⟨hF i, hasFiniteIntegral_iff_enorm.mpr
      (lt_top_iff_ne_top.mpr (ENNReal.ne_top_of_tsum_ne_top htotal.ne i))⟩
  have hsum : Summable (fun i => ∫ x, ‖F i x‖ ∂μ) :=
    (ENNReal.summable_toReal htotal.ne).congr
      (fun i => (integral_norm_eq_lintegral_enorm (hF i)).symm)
  simpa only [F, μ, tsum_mul_right] using hasSum_integral_of_summable_integral_norm hi hsum

/-- Vanishing of the individual Mellin moments passes to the series at the
same point, including all the orders allowed by the one absolute majorant. -/
theorem integrated_moments_zero (C : ℕ → ℝ → ℂ) (v : ℕ → ℂ) (s : ℂ) (k : ℕ)
    (hC : ∀ i, AEStronglyMeasurable (C i) (volume.restrict (Ioi (1 : ℝ))))
    (habs : (∑' i, absoluteMass (C i) (v i) s k) < ⊤)
    (hz : ∀ j ≤ k, ∀ i, (∫ x in Ioi (1 : ℝ), C i x * momentKernel s j x) = 0) :
    ∀ j ≤ k, (∫ x in Ioi (1 : ℝ), (∑' i, v i * C i x) * momentKernel s j x) = 0 := by
  intro j hj
  rw [← (integrated_moments C v s k hC habs j hj).tsum_eq]
  simp_rw [mul_assoc, integral_const_mul, hz j hj, mul_zero, tsum_zero]

end RiemannResearch.RH.PrimeTreeIntegratedCarries

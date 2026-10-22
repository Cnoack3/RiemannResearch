import RiemannResearch.RH.SignedWeilCorrelation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Exact archimedean diagonal correction

Source: Suzuki, *Weil's quadratic form via the screw function*, section 1.1,
https://arxiv.org/html/2606.09096v1, supports the arithmetic normalization.
The elementary primitive below evaluates the regulator correction exactly.
No explicit formula, prime estimate, zeta-zero property, or RH input is used.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace RiemannResearch.RH.SignedWeilCorrelation

noncomputable section

/-- Continuous cancellation of `2 k(t) (1 - exp(-t/2))` at the origin. -/
def archimedeanCorrection (t : ℝ) : ℝ :=
  2 * Real.exp (-t / 2) /
    ((1 + Real.exp (-t / 2)) * (1 + Real.exp (-t / 2) ^ 2))

/-- A primitive vanishing at positive infinity. -/
def archimedeanCorrectionPrimitive (t : ℝ) : ℝ :=
  2 * Real.log (1 + Real.exp (-t / 2)) +
    2 * Real.arctan (Real.exp (-t / 2)) -
      Real.log (1 + Real.exp (-t / 2) ^ 2)

theorem archimedeanCorrection_nonneg (t : ℝ) :
    0 ≤ archimedeanCorrection t := by
  unfold archimedeanCorrection
  positivity

theorem hasDerivAt_archimedeanCorrectionPrimitive (t : ℝ) :
    HasDerivAt archimedeanCorrectionPrimitive (-archimedeanCorrection t) t := by
  have he : HasDerivAt (fun u : ℝ => Real.exp (-u / 2))
      (-Real.exp (-t / 2) / 2) t := by
    convert (((hasDerivAt_id t).neg).div_const 2).exp using 1
    <;> simp only [Pi.neg_apply, id_eq]
    <;> ring
  have h1 : 1 + Real.exp (-t / 2) ≠ 0 := by positivity
  have h2 : 1 + Real.exp (-t / 2) ^ 2 ≠ 0 := by positivity
  have h := ((((hasDerivAt_const t 1).add he).log h1).const_mul 2).add
    (he.arctan.const_mul 2)
  have h := h.sub (((hasDerivAt_const t 1).add (he.pow 2)).log h2)
  apply h.congr_deriv
  dsimp only [archimedeanCorrection, Pi.add_apply, Pi.pow_apply]
  norm_num
  field_simp [h1, h2]
  <;> ring

theorem archimedeanCorrectionPrimitive_tendsto :
    Tendsto archimedeanCorrectionPrimitive atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => t / 2) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨2 * b, fun t ht => by linarith⟩
  have he : Tendsto (fun t : ℝ => Real.exp (-t / 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_div] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp ht
  have hphi : ContinuousAt (fun x : ℝ =>
      2 * Real.log (1 + x) + 2 * Real.arctan x - Real.log (1 + x ^ 2)) 0 := by
    have hlog1 := (continuousAt_const.add continuousAt_id).log
      (show (1 : ℝ) + 0 ≠ 0 by norm_num)
    have hlog2 := (continuousAt_const.add (continuousAt_id.pow 2)).log
      (show (1 : ℝ) + 0 ^ 2 ≠ 0 by norm_num)
    exact ((hlog1.const_mul 2).add
      (Real.continuous_arctan.continuousAt.const_mul 2)).sub hlog2
  change Tendsto (fun t : ℝ =>
    2 * Real.log (1 + Real.exp (-t / 2)) + 2 * Real.arctan (Real.exp (-t / 2)) -
      Real.log (1 + Real.exp (-t / 2) ^ 2)) atTop (𝓝 0)
  simpa [Function.comp_def] using hphi.tendsto.comp he

theorem archimedeanCorrectionPrimitive_zero :
    archimedeanCorrectionPrimitive 0 = Real.log 2 + Real.pi / 2 := by
  simp only [archimedeanCorrectionPrimitive, neg_zero, zero_div, Real.exp_zero,
    one_pow, Real.arctan_one]
  norm_num
  ring

/-- Integrability is proved from the primitive and its derivative sign. -/
theorem integrable_archimedeanCorrection :
    IntegrableOn archimedeanCorrection (Ioi 0) := by
  have hneg : IntegrableOn (fun t => -archimedeanCorrection t) (Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonpos'
      (fun t _ => hasDerivAt_archimedeanCorrectionPrimitive t)
      (fun t _ => neg_nonpos.mpr (archimedeanCorrection_nonneg t))
      archimedeanCorrectionPrimitive_tendsto
  have hn := hneg.neg
  change IntegrableOn (fun t => -(-archimedeanCorrection t)) (Ioi 0) at hn
  simpa only [neg_neg] using hn

theorem integral_archimedeanCorrection :
    (∫ t in Ioi 0, archimedeanCorrection t) = Real.log 2 + Real.pi / 2 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonpos'
    (fun t (_ : t ∈ Ici (0 : ℝ)) => hasDerivAt_archimedeanCorrectionPrimitive t)
    (fun t _ => neg_nonpos.mpr (archimedeanCorrection_nonneg t))
    archimedeanCorrectionPrimitive_tendsto
  rw [integral_neg, archimedeanCorrectionPrimitive_zero, zero_sub] at h
  exact neg_injective h

/-- The continuous correction agrees with the actual gamma kernel at every
positive argument. The singular origin is excluded from the measure. -/
theorem archimedeanCorrection_eq_kernel {t : ℝ} (ht : 0 < t) :
    archimedeanCorrection t =
      2 * weilGammaKernel t * (1 - weilRegulator t) := by
  let x : ℝ := Real.exp (t / 2)
  have hxpos : 0 < x := Real.exp_pos _
  have hx1 : 1 < x := Real.one_lt_exp_iff.mpr (by linarith)
  have hx : x ≠ 0 := ne_of_gt hxpos
  have hneg : Real.exp (-t / 2) = x⁻¹ := by
    dsimp [x]
    rw [show -t / 2 = -(t / 2) by ring, Real.exp_neg]
  have htwo : Real.exp t = x ^ 2 := by
    dsimp [x]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hnegtwo : Real.exp (-t) = (x⁻¹) ^ 2 := by
    rw [Real.exp_neg, htwo, inv_pow]
  have hden : x ^ 2 - (x⁻¹) ^ 2 ≠ 0 := by
    rw [← htwo, ← hnegtwo]
    apply ne_of_gt
    exact sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  have h1 : 1 + x⁻¹ ≠ 0 := by positivity
  have h2 : 1 + (x⁻¹) ^ 2 ≠ 0 := by positivity
  have hx2 : 1 < x ^ 2 := by nlinarith
  have hx4 : -1 + x ^ 4 ≠ 0 := by nlinarith [sq_nonneg (x ^ 2 - 1)]
  unfold archimedeanCorrection weilGammaKernel weilRegulator
  rw [hneg, htwo, hnegtwo]
  change 2 * x⁻¹ / ((1 + x⁻¹) * (1 + (x⁻¹) ^ 2)) =
    2 * (x / (x ^ 2 - (x⁻¹) ^ 2)) * (1 - x⁻¹)
  field_simp [hx, h1, h2, hden, hx4]
  <;> ring_nf
  <;> field_simp [hx4]
  <;> ring

/-- Exact regulator integral producing the additional `log 2 + pi/2`
diagonal constant in the energy normalization of the Weil form. -/
theorem integral_weilGammaKernel_regulator_correction :
    (∫ t in Ioi 0, 2 * weilGammaKernel t * (1 - weilRegulator t)) =
      Real.log 2 + Real.pi / 2 := by
  rw [← integral_archimedeanCorrection]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (archimedeanCorrection_eq_kernel ht).symm

end
end RiemannResearch.RH.SignedWeilCorrelation

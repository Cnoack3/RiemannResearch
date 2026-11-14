/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Vertical contour shifts with a Cauchy majorant

The proof combines Mathlib's Cauchy--Goursat theorem on finite rectangles
with absolute convergence on the two vertical sides. A uniform inverse-square
bound makes both horizontal integrals tend to zero.
Concrete consumer: the Conrey--Baluyot Mellin weight, following the positive-line
shift used in Baluyot (2017), Lemma 3.1.1, equation (3.1.4).
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section

namespace Complex
/-- Cauchy contour shift on a vertical strip with an inverse-quadratic majorant. -/
theorem integral_vertical_eq_of_cauchy_bound {f : ℂ → ℂ} {a b B : ℝ}
    (hd : ∀ z : ℂ, z.re ∈ uIcc a b → DifferentiableAt ℂ f z)
    (ha : Integrable (fun t : ℝ => f ((a : ℂ) + t * I)))
    (hb : Integrable (fun t : ℝ => f ((b : ℂ) + t * I)))
    (hbound : ∀ r ∈ uIcc a b, ∀ t : ℝ,
      ‖f ((r : ℂ) + t * I)‖ ≤ B * (1 + t ^ 2)⁻¹) :
    (∫ t : ℝ, f ((a : ℂ) + t * I)) = ∫ t : ℝ, f ((b : ℂ) + t * I) := by
  let H : ℝ → ℂ := fun T => ∫ r in a..b, f ((r : ℂ) + T * I)
  have hH (T : ℝ) : ‖H T‖ ≤ (B * (1 + T ^ 2)⁻¹) * |b - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun r hr => hbound r (uIoc_subset_uIcc hr) T)
  have hdecay : Tendsto (fun T : ℝ => (1 + T ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_mono (fun T : ℝ => by linarith : ∀ T : ℝ, T ^ 2 ≤ 1 + T ^ 2)
        (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)))
  have hlim : Tendsto (fun T : ℝ => (B * (1 + T ^ 2)⁻¹) * |b - a|) atTop (𝓝 0) := by
    simpa using (hdecay.const_mul B).mul_const |b - a|
  have hpos : Tendsto H atTop (𝓝 0) := squeeze_zero_norm hH hlim
  have hneg : Tendsto (fun T => H (-T)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun T => by simpa only [neg_sq] using hH (-T)) hlim
  have hva := intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hvb := intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  have hrect (T : ℝ) :
      H (-T) - H T +
        I * (∫ t in -T..T, f ((b : ℂ) + t * I)) -
        I * (∫ t in -T..T, f ((a : ℂ) + t * I)) = 0 := by
    have hh := integral_boundary_rect_eq_zero_of_differentiableOn f
      ((a : ℂ) + (-T : ℝ) * I) ((b : ℂ) + T * I) (by
        intro z hz
        apply (hd z ?_).differentiableWithinAt
        simpa using (mem_reProdIm.mp hz).1)
    simpa [H, smul_eq_mul] using hh
  have hlimrect := ((hneg.sub hpos).add (hvb.const_mul I)).sub (hva.const_mul I)
  have heq : I * (∫ t : ℝ, f ((b : ℂ) + t * I)) -
      I * (∫ t : ℝ, f ((a : ℂ) + t * I)) = 0 := by
    have hh := tendsto_nhds_unique hlimrect
      (tendsto_const_nhds.congr' (Eventually.of_forall fun T => (hrect T).symm))
    simpa only [sub_self, zero_add] using hh
  exact (mul_left_cancel₀ I_ne_zero (sub_eq_zero.mp heq)).symm
end Complex

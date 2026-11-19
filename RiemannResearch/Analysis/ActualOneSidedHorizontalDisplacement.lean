/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ActualMicroscopicHorizontalConcentration
import RiemannResearch.Analysis.ActualZeroCountNormalization

/-!
# The one-sided physical mean in the horizontal PCC condition

Reflection and the exact zero-count normalization identify the small-o
version of Conrey's one-sided first moment with microscopic concentration.
The height denominator is T and zero multiplicities are retained.
-/

noncomputable section
open Filter Set Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ZeroOrdinate

def oneSidedHeightMean (T : ℝ) : ℝ :=
  realSum T (fun z => max (z.re - 1/2) 0) / T

/-- The finite factor 4π arises from reflection and the Riemann–von Mangoldt
normalization. -/
theorem firstMark_mul_countRatio_eq {T : ℝ} (hT : 1 < T) (hN : (Ncount 0 T : ℝ) ≠ 0) :
    (displacementMoment T 1 * Real.log T) *
        ((Ncount 0 T : ℝ) / (T * Real.log T / (2 * Real.pi))) =
      (4 * Real.pi) * oneSidedHeightMean T := by
  let f (z : ℂ) := max (z.re - 1/2) 0
  have href (z : ℂ) : |z.re - 1/2| = f z + f (reflect z) := by
    dsimp only [f]
    rw [reflect_re, show 1 - z.re - 1/2 = -(z.re-1/2) by ring]
    rcases le_total 0 (z.re - 1/2) with h | h
    · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (neg_nonpos.mpr h), add_zero]
    · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_add]
  have hs : (∑ j : Copies T, copyDisplacement T j ^ 1) = realSum T f + realSum T f := by
    calc
      _ = ∑ j : Copies T, (f j.1.1 + f (reflect j.1.1)) :=
        Finset.sum_congr rfl fun j _ => by simpa only [pow_one, copyDisplacement] using href j.1.1
      _ = realSum T (fun z => f z + f (reflect z)) := (realSum_eq_copies T (fun z : ℂ => f z + f (reflect z))).symm
      _ = _ := by rw [realSum_add, realSum_reflect]
  unfold displacementMoment
  rw [hs]
  change ((_ + _) / _ * _) * _ = _ * (realSum T f / T)
  field_simp [hN, (Real.log_pos hT).ne', (zero_lt_one.trans hT).ne', Real.pi_ne_zero]
  <;> ring

/-- Every little-o saving in the one-sided height-normalized first moment
is exactly the microscopic horizontal PCC hypothesis, under any fixed
positive Selberg slope. -/
theorem oneSidedHeightMean_tendsto_zero_iff {a : ℝ} (ha : 0 < a)
    (hD : UniformSelbergDensity a) :
    Tendsto oneSidedHeightMean atTop (𝓝 0) ↔ MicroscopicHorizontalConcentration := by
  let R (T : ℝ) := (Ncount 0 T : ℝ) / (T * Real.log T / (2 * Real.pi))
  let X (T : ℝ) := displacementMoment T 1 * Real.log T
  have hr : Tendsto R atTop (𝓝 1) := tendsto_count_div_mainTerm
  have hR := hr.eventually (Ioi_mem_nhds (by norm_num : (0:ℝ) < 1))
  have hEq : ∀ᶠ T : ℝ in atTop, X T * R T = (4*Real.pi) * oneSidedHeightMean T := by
    filter_upwards [hR, eventually_gt_atTop (1:ℝ)] with T hR hT
    apply firstMark_mul_countRatio_eq hT
    intro hz
    change 0 < (Ncount 0 T : ℝ) / _ at hR
    simp [hz] at hR
  have hiff : Tendsto X atTop (𝓝 0) ↔ MicroscopicHorizontalConcentration := by
    simpa [X] using scaled_displacement_tendsto_zero_iff ha hD 0
  rw [← hiff]
  constructor
  · intro h
    have ht := (h.const_mul (4*Real.pi)).div hr (by norm_num : (1:ℝ) ≠ 0)
    change Tendsto (fun T => (4*Real.pi)*oneSidedHeightMean T / R T) atTop (𝓝 ((4*Real.pi)*(0:ℝ)/1)) at ht
    apply (show Tendsto (fun T => (4*Real.pi)*oneSidedHeightMean T / R T) atTop (𝓝 0) from by simpa using ht).congr'
    filter_upwards [hEq, hR] with T he hp
    rw [← he, mul_div_cancel_right₀ _ (ne_of_gt hp)]
  · intro h
    have ht := (h.mul hr).div_const (4*Real.pi)
    change Tendsto (fun T => X T * R T / (4*Real.pi)) atTop (𝓝 ((0:ℝ)*1/(4*Real.pi))) at ht
    apply (show Tendsto (fun T => X T * R T / (4*Real.pi)) atTop (𝓝 0) from by simpa using ht).congr'
    filter_upwards [hEq] with T he
    rw [he]
    field_simp [Real.pi_ne_zero]

/-- A small-o saving over the published positive first-height-moment
constant is equivalent to vanishing of the scaled quadratic horizontal
error in the ordinary-ordinate pair program. -/
theorem oneSidedHeightMean_tendsto_zero_iff_quadratic {a : ℝ} (ha : 0 < a)
    (hD : UniformSelbergDensity a) :
    Tendsto oneSidedHeightMean atTop (𝓝 0) ↔
      Tendsto (fun T : ℝ => displacementMoment T 2 * Real.log T ^ 2) atTop (𝓝 0) :=
  (oneSidedHeightMean_tendsto_zero_iff ha hD).trans (scaled_displacement_tendsto_zero_iff ha hD 1).symm

end RiemannResearch.Analysis.ActualZeroOrdinate

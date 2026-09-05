/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.Analysis.HingeKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Symmetric hinge primitives and exact rectangle integrals

Derivatives of positive-part powers, including their threshold, give the exact
four-corner formula for integrals of max (|x-y|-a) 0 when a is nonnegative.

Source: user-provided RH_Local_to_Global_Trace_Attack_Plan_2026-09-05,
Section on exact prime-power cell entries, supplies the proof strategy.
RH consumer: ScrewPrimePart.
-/

open Filter Set MeasureTheory
open scoped Topology
namespace RiemannResearch.Analysis
noncomputable section

theorem hasDerivAt_positivePart_pow (n : ℕ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => (max t 0)^(n+2))
      ((n+2 : ℕ) * (max x 0)^(n+1)) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have h := (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
      (show (fun t : ℝ => (max t 0)^(n+2)) =ᶠ[𝓝 x] (fun _ => 0) from by
        filter_upwards [eventually_lt_nhds hx] with t ht
        simp [max_eq_right ht.le])
    simpa [max_eq_right hx.le] using h
  · simp only [max_self, zero_pow (Nat.succ_ne_zero _), mul_zero]
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have he (t : ℝ) :
        t⁻¹ * (max t 0)^(n+2) = (max t 0)^(n+1) := by
      rcases le_or_gt t 0 with ht | ht
      · simp [max_eq_right ht]
      · rw [max_eq_left ht.le, show n+2 = (n+1)+1 by omega, pow_succ]
        field_simp
    simp only [zero_add, max_self, zero_pow (Nat.succ_ne_zero _),
      sub_zero, smul_eq_mul]
    simp_rw [he]
    have hc : Continuous (fun t : ℝ => (max t 0)^(n+1)) :=
      (continuous_id.max continuous_const).pow (n+1)
    have h := hc.continuousAt (x := 0)
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  · have h := (hasDerivAt_id x).pow (n+2)
    have h' : HasDerivAt (fun t : ℝ => t^(n+2)) ((n+2 : ℕ)*x^(n+1)) x := by
      convert! h using 1
      simp
    have h'' := h'.congr_of_eventuallyEq
      (show (fun t : ℝ => (max t 0)^(n+2)) =ᶠ[𝓝 x] (fun t => t^(n+2)) from by
        filter_upwards [eventually_gt_nhds hx] with t ht
        simp [max_eq_left ht.le])
    simpa [max_eq_left hx.le] using h''

def hingeKernelPrimitive (a z : ℝ) : ℝ :=
  ((max (z-a) 0)^2 - (max (-z-a) 0)^2)/2
def hingeKernelSecondPrimitive (a z : ℝ) : ℝ :=
  ((max (z-a) 0)^3 + (max (-z-a) 0)^3)/6

theorem hingeKernel_split {a : ℝ} (ha : 0 ≤ a) (z : ℝ) :
    hingeKernel a z = max (z-a) 0 + max (-z-a) 0 := by
  unfold hingeKernel
  rcases le_or_gt 0 z with hz | hz
  · rw [abs_of_nonneg hz, max_eq_right (by linarith : -z-a ≤ 0), add_zero]
  · rw [abs_of_nonpos hz.le, max_eq_right (by linarith : z-a ≤ 0), zero_add]

theorem hingeKernelSecondPrimitive_eq {a : ℝ} (ha : 0 ≤ a) (z : ℝ) :
    hingeKernelSecondPrimitive a z = (hingeKernel a z)^3/6 := by
  rw [hingeKernel_split ha]
  unfold hingeKernelSecondPrimitive
  rcases le_or_gt 0 z with hz | hz
  · rw [max_eq_right (by linarith : -z-a ≤ 0)]
    simp
  · rw [max_eq_right (by linarith : z-a ≤ 0)]
    simp

theorem hasDerivAt_hingeKernelPrimitive {a : ℝ} (ha : 0 ≤ a) (z : ℝ) :
    HasDerivAt (hingeKernelPrimitive a) (hingeKernel a z) z := by
  have hp := (hasDerivAt_positivePart_pow 0 (z-a)).comp z
    ((hasDerivAt_id z).sub_const a)
  have hn := (hasDerivAt_positivePart_pow 0 (-z-a)).comp z
    ((hasDerivAt_id z).neg.sub_const a)
  have h := (hp.sub hn).div_const 2
  convert! h using 1
  rw [hingeKernel_split ha]
  norm_num
  ring

theorem hasDerivAt_hingeKernelSecondPrimitive (a z : ℝ) :
    HasDerivAt (hingeKernelSecondPrimitive a) (hingeKernelPrimitive a z) z := by
  have hp := (hasDerivAt_positivePart_pow 1 (z-a)).comp z
    ((hasDerivAt_id z).sub_const a)
  have hn := (hasDerivAt_positivePart_pow 1 (-z-a)).comp z
    ((hasDerivAt_id z).neg.sub_const a)
  have h := (hp.add hn).div_const 6
  convert! h using 1
  simp only [hingeKernelPrimitive]
  norm_num
  ring

theorem continuous_hingeKernelPrimitive {a : ℝ} (ha : 0 ≤ a) :
    Continuous (hingeKernelPrimitive a) :=
  continuous_iff_continuousAt.mpr (fun z => (hasDerivAt_hingeKernelPrimitive ha z).continuousAt)

theorem integral_hingeKernel_sub {a : ℝ} (ha : 0 ≤ a) (x b d : ℝ) :
    (∫ y in b..d, hingeKernel a (x-y)) =
      hingeKernelPrimitive a (x-b) - hingeKernelPrimitive a (x-d) := by
  have hd (y : ℝ) :
      HasDerivAt (fun y => -hingeKernelPrimitive a (x-y))
        (hingeKernel a (x-y)) y := by
    convert! ((hasDerivAt_hingeKernelPrimitive ha (x-y)).comp y
      ((hasDerivAt_const y x).sub (hasDerivAt_id y))).neg using 1
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)
    (((continuous_hingeKernel a).comp (continuous_const.sub continuous_id)).intervalIntegrable b d)
  convert! h using 1
  ring

theorem integral_hingeKernelPrimitive_sub {a : ℝ} (ha : 0 ≤ a) (y b d : ℝ) :
    (∫ x in b..d, hingeKernelPrimitive a (x-y)) =
      hingeKernelSecondPrimitive a (d-y) - hingeKernelSecondPrimitive a (b-y) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    convert! (hasDerivAt_hingeKernelSecondPrimitive a (x-y)).comp x
      ((hasDerivAt_id x).sub_const y) using 1
    ring
  · exact ((continuous_hingeKernelPrimitive ha).comp
      (continuous_id.sub continuous_const)).intervalIntegrable b d

/-- Exact double cell integral, including threshold crossings and oriented endpoints. -/
theorem integral_integral_hingeKernel {a : ℝ} (ha : 0 ≤ a)
    (b₁ d₁ b₂ d₂ : ℝ) :
    (∫ x in b₁..d₁, ∫ y in b₂..d₂, hingeKernel a (x-y)) =
      hingeKernelSecondPrimitive a (d₁-b₂) - hingeKernelSecondPrimitive a (b₁-b₂)
      - hingeKernelSecondPrimitive a (d₁-d₂) + hingeKernelSecondPrimitive a (b₁-d₂) := by
  simp_rw [integral_hingeKernel_sub ha]
  have hc (y : ℝ) : IntervalIntegrable
      (fun x => hingeKernelPrimitive a (x-y)) volume b₁ d₁ :=
    ((continuous_hingeKernelPrimitive ha).comp
      (continuous_id.sub continuous_const)).intervalIntegrable b₁ d₁
  rw [intervalIntegral.integral_sub (hc b₂) (hc d₂),
    integral_hingeKernelPrimitive_sub ha, integral_hingeKernelPrimitive_sub ha]
  ring

end
end RiemannResearch.Analysis

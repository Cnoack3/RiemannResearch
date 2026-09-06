/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.Analysis.HingeKernelIntegral
import RiemannResearch.Analysis.FiniteCellKernel
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact cell integrals for translation kernels

This module proves a reusable four-corner theorem from two global primitives,
then specializes it to exponential, absolute-value, and exponential-absolute-
value kernels on arbitrary oriented intervals. The piecewise first primitive
for the exponential-absolute-value kernel is glued with matching value and
derivative at the origin.

Source: the exact-cell strategy in the user-provided
RH_Local_to_Global_Trace_Attack_Plan_2026-09-05.pdf supports the statements and
proof architecture. RH consumer: ArithmeticFiniteEntryFormulas.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace RiemannResearch.Analysis
noncomputable section

def secondPrimitiveCell (F : ℝ → ℝ) (b₁ d₁ b₂ d₂ : ℝ) : ℝ :=
  F (d₁-b₂) - F (b₁-b₂) - F (d₁-d₂) + F (b₁-d₂)

theorem integral_integral_eq_secondPrimitiveCell
    (f F G : ℝ → ℝ) (hf : Continuous f)
    (hF : ∀ t, HasDerivAt F (f t) t)
    (hG : ∀ t, HasDerivAt G (F t) t) (b₁ d₁ b₂ d₂ : ℝ) :
    (∫ x in b₁..d₁, ∫ y in b₂..d₂, f (x-y)) =
      secondPrimitiveCell G b₁ d₁ b₂ d₂ := by
  have hFc : Continuous F :=
    continuous_iff_continuousAt.mpr (fun t => (hF t).continuousAt)
  have hi (x : ℝ) : (∫ y in b₂..d₂, f (x-y)) = F (x-b₂) - F (x-d₂) := by
    have hd (y : ℝ) : HasDerivAt (fun y => -F (x-y)) (f (x-y)) y := by
      convert! ((hF (x-y)).comp y
        ((hasDerivAt_const y x).sub (hasDerivAt_id y))).neg using 1
      ring
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)
      ((hf.comp (continuous_const.sub continuous_id)).intervalIntegrable b₂ d₂)
    convert! h using 1
    ring
  have ho (y : ℝ) : (∫ x in b₁..d₁, F (x-y)) = G (d₁-y) - G (b₁-y) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      convert! (hG (x-y)).comp x ((hasDerivAt_id x).sub_const y) using 1
      ring
    · exact (hFc.comp (continuous_id.sub continuous_const)).intervalIntegrable b₁ d₁
  simp_rw [hi]
  have hc (y : ℝ) : IntervalIntegrable (fun x => F (x-y)) volume b₁ d₁ :=
    (hFc.comp (continuous_id.sub continuous_const)).intervalIntegrable b₁ d₁
  rw [intervalIntegral.integral_sub (hc b₂) (hc d₂), ho, ho]
  simp only [secondPrimitiveCell]
  ring

def exponentialCell (β : ℝ) (b₁ d₁ b₂ d₂ : ℝ) : ℝ :=
  secondPrimitiveCell (fun t => Real.exp (β*t)/β^2) b₁ d₁ b₂ d₂

theorem integral_integral_exp_mul_sub {β : ℝ} (hβ : β ≠ 0)
    (b₁ d₁ b₂ d₂ : ℝ) :
    (∫ x in b₁..d₁, ∫ y in b₂..d₂, Real.exp (β*(x-y))) =
      exponentialCell β b₁ d₁ b₂ d₂ := by
  apply integral_integral_eq_secondPrimitiveCell
    (fun t => Real.exp (β*t)) (fun t => Real.exp (β*t)/β)
    (fun t => Real.exp (β*t)/β^2)
    (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  · intro t
    convert! (((hasDerivAt_id t).const_mul β).exp.div_const β) using 1
    field_simp
    rfl
  · intro t
    convert! (((hasDerivAt_id t).const_mul β).exp.div_const (β^2)) using 1
    field_simp
    rfl

theorem integral_integral_add {k l : ℝ → ℝ → ℝ}
    (hk : Continuous (Function.uncurry k)) (hl : Continuous (Function.uncurry l))
    (a b c d : ℝ) :
    (∫ x in a..b, ∫ y in c..d, k x y + l x y) =
      (∫ x in a..b, ∫ y in c..d, k x y) +
      (∫ x in a..b, ∫ y in c..d, l x y) := by
  have hki (x : ℝ) : IntervalIntegrable (k x) volume c d :=
    (hk.comp (continuous_const.prodMk continuous_id)).intervalIntegrable c d
  have hli (x : ℝ) : IntervalIntegrable (l x) volume c d :=
    (hl.comp (continuous_const.prodMk continuous_id)).intervalIntegrable c d
  simp_rw [intervalIntegral.integral_add (hki _) (hli _)]
  exact intervalIntegral.integral_add
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hk c d).intervalIntegrable a b)
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hl c d).intervalIntegrable a b)

theorem integral_integral_finsetSum {ι : Type*} (s : Finset ι) (k : ι → ℝ → ℝ → ℝ)
    (hk : ∀ i ∈ s, Continuous (Function.uncurry (k i))) (a b c d : ℝ) :
    (∫ x in a..b, ∫ y in c..d, ∑ i ∈ s, k i x y) =
      ∑ i ∈ s, ∫ x in a..b, ∫ y in c..d, k i x y := by
  have hi (x : ℝ) (i : ι) (hi : i ∈ s) : IntervalIntegrable (k i x) volume c d :=
    ((hk i hi).comp (continuous_const.prodMk continuous_id)).intervalIntegrable c d
  simp_rw [intervalIntegral.integral_finsetSum (fun i hi' => hi _ i hi')]
  exact intervalIntegral.integral_finsetSum (fun i hi' =>
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (hk i hi') c d).intervalIntegrable a b)

def absCell (b₁ d₁ b₂ d₂ : ℝ) : ℝ :=
  secondPrimitiveCell (hingeKernelSecondPrimitive 0) b₁ d₁ b₂ d₂

theorem integral_integral_abs_sub (b₁ d₁ b₂ d₂ : ℝ) :
    (∫ x in b₁..d₁, ∫ y in b₂..d₂, |x-y|) = absCell b₁ d₁ b₂ d₂ := by
  have he (t : ℝ) : hingeKernel 0 t = |t| := by
    simp [hingeKernel]
  simpa only [he, absCell, secondPrimitiveCell] using
    integral_integral_hingeKernel (a := 0) (by norm_num) b₁ d₁ b₂ d₂

private theorem hasDerivAt_glue_zero (f g df dg : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (df x) x) (hg : ∀ x, HasDerivAt g (dg x) x)
    (h0 : f 0 = g 0) (hd0 : df 0 = dg 0) (x : ℝ) :
    HasDerivAt (fun t => if t ≤ 0 then f t else g t)
      (if x ≤ 0 then df x else dg x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · simpa only [if_pos hx.le] using (hf x).congr_of_eventuallyEq
      (show (fun t => if t ≤ 0 then f t else g t) =ᶠ[𝓝 x] f from by
        filter_upwards [eventually_lt_nhds hx] with t ht
        simp [ht.le])
  · simp only [le_refl, if_true]
    have hL : HasDerivWithinAt (fun t => if t ≤ 0 then f t else g t)
        (df 0) (Iic 0) 0 := (hf 0).hasDerivWithinAt.congr
      (by intro t ht; simp only [mem_Iic] at ht; simp [ht]) (by simp)
    have hR : HasDerivWithinAt (fun t => if t ≤ 0 then f t else g t)
        (df 0) (Ioi 0) 0 := by
      rw [hd0]
      apply (hg 0).hasDerivWithinAt.congr
      · intro t ht
        simp only [mem_Ioi] at ht
        simp [not_le.mpr ht]
      · simpa using h0
    simpa only [Iic_union_Ioi, hasDerivWithinAt_univ] using hL.union hR
  · simpa only [if_neg (not_le.mpr hx)] using (hg x).congr_of_eventuallyEq
      (show (fun t => if t ≤ 0 then f t else g t) =ᶠ[𝓝 x] g from by
        filter_upwards [eventually_gt_nhds hx] with t ht
        simp [not_le.mpr ht])

def exponentialAbsPrimitive (α t : ℝ) : ℝ :=
  if t ≤ 0 then (Real.exp (α*t)-1)/α else (1-Real.exp (-α*t))/α

def exponentialAbsSecondPrimitive (α t : ℝ) : ℝ :=
  (Real.exp (-α*|t|)+α*|t|)/α^2

def exponentialAbsCell (α b₁ d₁ b₂ d₂ : ℝ) : ℝ :=
  exponentialAbsSecondPrimitive α (d₁-b₂) - exponentialAbsSecondPrimitive α (b₁-b₂)
    - exponentialAbsSecondPrimitive α (d₁-d₂) + exponentialAbsSecondPrimitive α (b₁-d₂)

theorem hasDerivAt_exponentialAbsPrimitive {α : ℝ} (hα : α ≠ 0) (x : ℝ) :
    HasDerivAt (exponentialAbsPrimitive α) (Real.exp (-α*|x|)) x := by
  have hf (t : ℝ) : HasDerivAt (fun t : ℝ => (Real.exp (α*t)-1)/α)
      (Real.exp (α*t)) t := by
    convert! (((hasDerivAt_id t).const_mul α).exp.sub_const 1).div_const α using 1
    simp only [id_eq, mul_one]
    field_simp
  have hg (t : ℝ) : HasDerivAt (fun t : ℝ => (1-Real.exp (-α*t))/α)
      (Real.exp (-α*t)) t := by
    convert! ((hasDerivAt_const t (1 : ℝ)).sub
      ((hasDerivAt_id t).const_mul (-α)).exp).div_const α using 1
    simp only [id_eq, mul_one, zero_sub]
    field_simp
  have h := hasDerivAt_glue_zero _ _ _ _ hf hg (by simp) (by simp) x
  convert! h using 1
  split_ifs with hx
  · rw [abs_of_nonpos hx]
    congr 1
    ring
  · rw [abs_of_nonneg (le_of_lt (not_le.mp hx))]

theorem hasDerivAt_exponentialAbsSecondPrimitive {α : ℝ} (hα : α ≠ 0) (x : ℝ) :
    HasDerivAt (exponentialAbsSecondPrimitive α) (exponentialAbsPrimitive α x) x := by
  have hf (t : ℝ) : HasDerivAt (fun t : ℝ => (Real.exp (α*t)-α*t)/α^2)
      ((Real.exp (α*t)-1)/α) t := by
    convert! ((((hasDerivAt_id t).const_mul α).exp).sub
      ((hasDerivAt_id t).const_mul α)).div_const (α^2) using 1
    simp only [id_eq, mul_one]
    field_simp
  have hg (t : ℝ) : HasDerivAt (fun t : ℝ => (Real.exp (-α*t)+α*t)/α^2)
      ((1-Real.exp (-α*t))/α) t := by
    convert! ((((hasDerivAt_id t).const_mul (-α)).exp).add
      ((hasDerivAt_id t).const_mul α)).div_const (α^2) using 1
    simp only [id_eq, mul_one]
    field_simp
    ring
  have h := hasDerivAt_glue_zero _ _ _ _ hf hg (by simp) (by simp) x
  convert! h using 1
  funext t
  unfold exponentialAbsSecondPrimitive
  split_ifs with ht
  · rw [abs_of_nonpos ht]
    simp only [mul_neg, neg_mul, neg_neg, sub_eq_add_neg]
  · rw [abs_of_nonneg (le_of_lt (not_le.mp ht))]

theorem continuous_exponentialAbsPrimitive {α : ℝ} (hα : α ≠ 0) :
    Continuous (exponentialAbsPrimitive α) :=
  continuous_iff_continuousAt.mpr
    (fun x => (hasDerivAt_exponentialAbsPrimitive hα x).continuousAt)

theorem exponentialAbsSecondPrimitive_even (α : ℝ) :
    Function.Even (exponentialAbsSecondPrimitive α) := by
  intro t
  simp [exponentialAbsSecondPrimitive]

/-- The even second primitive is globally `C²`, including at the origin. -/
theorem contDiff_exponentialAbsSecondPrimitive {α : ℝ} (hα : α ≠ 0) :
    ContDiff ℝ 2 (exponentialAbsSecondPrimitive α) := by
  have hdF : deriv (exponentialAbsSecondPrimitive α) = exponentialAbsPrimitive α :=
    funext (fun x => (hasDerivAt_exponentialAbsSecondPrimitive hα x).deriv)
  have hdP : deriv (exponentialAbsPrimitive α) = (fun x => Real.exp (-α*|x|)) :=
    funext (fun x => (hasDerivAt_exponentialAbsPrimitive hα x).deriv)
  apply (contDiff_succ_iff_deriv (n := 1)).mpr
  refine ⟨fun x => (hasDerivAt_exponentialAbsSecondPrimitive hα x).differentiableAt,
    by simp, ?_⟩
  rw [hdF, contDiff_one_iff_deriv]
  refine ⟨fun x => (hasDerivAt_exponentialAbsPrimitive hα x).differentiableAt, ?_⟩
  rw [hdP]
  exact Real.continuous_exp.comp (continuous_const.mul continuous_abs)

/-- Exact exponential absolute-value cells, including the origin and all orientations. -/
theorem integral_integral_exp_neg_mul_abs {α : ℝ} (hα : α ≠ 0)
    (b₁ d₁ b₂ d₂ : ℝ) :
    (∫ x in b₁..d₁, ∫ y in b₂..d₂, Real.exp (-α*|x-y|)) =
      exponentialAbsCell α b₁ d₁ b₂ d₂ :=
  integral_integral_eq_secondPrimitiveCell
    (fun t => Real.exp (-α*|t|)) (exponentialAbsPrimitive α)
    (exponentialAbsSecondPrimitive α)
    (Real.continuous_exp.comp (continuous_const.mul continuous_abs))
    (hasDerivAt_exponentialAbsPrimitive hα)
    (hasDerivAt_exponentialAbsSecondPrimitive hα) b₁ d₁ b₂ d₂

end
end RiemannResearch.Analysis

/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite interval L2 assembly

Cauchy--Schwarz and Minkowski on a finite interval, stated directly in
terms of real square-root moments. The finite-sum bound squares only
after adding the individual L2 costs.

Source: standard Cauchy--Schwarz and Minkowski inequalities. The intended
consumer is the five-piece actual-zeta remainder in the Ingham continuation.
-/
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace intervalIntegral

private theorem continuous_memLp_two_interval {f : ℝ → ℝ}
    (hf : Continuous f) (H T : ℝ) :
    MemLp f (ENNReal.ofReal 2) (volume.restrict (Ioc H T)) := by
  apply (integrable_norm_rpow_iff hf.aestronglyMeasurable
    (by norm_num : ENNReal.ofReal (2 : ℝ) ≠ 0) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
  have hc := hf.norm.rpow_const (by intro x; exact Or.inr (by norm_num : (0 : ℝ) ≤ 2))
  exact hc.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem integral_norm_mul_le_sqrt {E : Type*} [NormedAddCommGroup E]
    {f g : ℝ → E} (hf : Continuous f) (hg : Continuous g)
    {H T : ℝ} (hHT : H ≤ T) :
    (∫ t in H..T, ‖f t‖ * ‖g t‖) ≤
      Real.sqrt (∫ t in H..T, ‖f t‖ ^ 2) *
      Real.sqrt (∫ t in H..T, ‖g t‖ ^ 2) := by
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (Ioc H T))
    (show (2 : ℝ).HolderConjugate 2 by rw [Real.holderConjugate_iff]; norm_num)
    (f := fun t => ‖f t‖) (g := fun t => ‖g t‖)
    (Filter.Eventually.of_forall (fun t => norm_nonneg _))
    (Filter.Eventually.of_forall (fun t => norm_nonneg _))
    (continuous_memLp_two_interval hf.norm H T)
    (continuous_memLp_two_interval hg.norm H T)
  simpa only [integral_of_le hHT, Real.rpow_two, Real.sqrt_eq_rpow] using hh

/-- Minkowski without converting the consumer to an Lp quotient space. -/
theorem sqrt_integral_norm_sq_add_le {E : Type*} [NormedAddCommGroup E]
    {f g : ℝ → E} (hf : Continuous f) (hg : Continuous g)
    {H T : ℝ} (hHT : H ≤ T) :
    Real.sqrt (∫ t in H..T, ‖f t + g t‖ ^ 2) ≤
      Real.sqrt (∫ t in H..T, ‖f t‖ ^ 2) +
      Real.sqrt (∫ t in H..T, ‖g t‖ ^ 2) := by
  have hiF : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume H T :=
    (hf.norm.pow 2).intervalIntegrable H T
  have hiG : IntervalIntegrable (fun t => ‖g t‖ ^ 2) volume H T :=
    (hg.norm.pow 2).intervalIntegrable H T
  have hiFG : IntervalIntegrable (fun t => ‖f t‖ * ‖g t‖) volume H T :=
    (hf.norm.mul hg.norm).intervalIntegrable H T
  have hF : 0 ≤ ∫ t in H..T, ‖f t‖ ^ 2 :=
    integral_nonneg hHT (fun _ _ => sq_nonneg _)
  have hG : 0 ≤ ∫ t in H..T, ‖g t‖ ^ 2 :=
    integral_nonneg hHT (fun _ _ => sq_nonneg _)
  have hm := integral_mono_on (μ := volume) hHT
    ((hf.add hg).norm.pow 2 |>.intervalIntegrable H T)
    (((hf.norm.pow 2).add (hg.norm.pow 2)).add ((hf.norm.mul hg.norm).const_mul 2)
      |>.intervalIntegrable H T)
    (fun t _ => show ‖f t + g t‖ ^ 2 ≤
      ‖f t‖ ^ 2 + ‖g t‖ ^ 2 + 2 * (‖f t‖ * ‖g t‖) from by
        have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (f t) (g t)) 2
        nlinarith)
  change (∫ t in H..T, ‖f t + g t‖ ^ 2) ≤
    ∫ t in H..T, ‖f t‖ ^ 2 + ‖g t‖ ^ 2 + 2 * (‖f t‖ * ‖g t‖) at hm
  rw [integral_add (hiF.add hiG) (hiFG.const_mul 2),
    integral_add hiF hiG, integral_const_mul] at hm
  have hcs := integral_norm_mul_le_sqrt hf hg hHT
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith [Real.sq_sqrt hF, Real.sq_sqrt hG]

/-- Finite pieces are combined in L2 before squaring. -/
theorem sqrt_integral_norm_sq_sum_le {ι E : Type*} [NormedAddCommGroup E]
    (s : Finset ι) (f : ι → ℝ → E) (hf : ∀ i ∈ s, Continuous (f i))
    {H T : ℝ} (hHT : H ≤ T) :
    Real.sqrt (∫ t in H..T, ‖∑ i ∈ s, f i t‖ ^ 2) ≤
      ∑ i ∈ s, Real.sqrt (∫ t in H..T, ‖f i t‖ ^ 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      have hfa : Continuous (f a) := hf a (Finset.mem_insert_self _ _)
      have hfs : ∀ i ∈ s, Continuous (f i) :=
        fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hc : Continuous (fun t => ∑ i ∈ s, f i t) :=
        continuous_finsetSum _ hfs
      exact (sqrt_integral_norm_sq_add_le hfa hc hHT).trans
        (add_le_add le_rfl (ih hfs))

/-- A common moment scale and any finite number of pieces, including zero costs. -/
theorem integral_norm_sq_sum_le_of_bounds {ι E : Type*} [NormedAddCommGroup E]
    (s : Finset ι) (f : ι → ℝ → E) (hf : ∀ i ∈ s, Continuous (f i))
    (B : ι → ℝ) (hB : ∀ i ∈ s, 0 ≤ B i) {W H T : ℝ} (hW : 0 ≤ W)
    (hHT : H ≤ T)
    (hb : ∀ i ∈ s, (∫ t in H..T, ‖f i t‖ ^ 2) ≤ B i ^ 2 * W) :
    (∫ t in H..T, ‖∑ i ∈ s, f i t‖ ^ 2) ≤ (∑ i ∈ s, B i) ^ 2 * W := by
  have hsum : Real.sqrt (∫ t in H..T, ‖∑ i ∈ s, f i t‖ ^ 2) ≤
      (∑ i ∈ s, B i) * Real.sqrt W := by
    apply (sqrt_integral_norm_sq_sum_le s f hf hHT).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg (hB i hi) (Real.sqrt_nonneg _), ?_⟩
    simpa only [mul_pow, Real.sq_sqrt hW] using hb i hi
  have hsum0 : 0 ≤ ∫ t in H..T, ‖∑ i ∈ s, f i t‖ ^ 2 :=
    integral_nonneg hHT (fun _ _ => sq_nonneg _)
  have hp := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsum 2
  simpa only [Real.sq_sqrt hsum0, mul_pow, Real.sq_sqrt hW] using hp

end intervalIntegral

/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroTailLayerCake
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# Transfer of actual scalar density estimates to weighted bad tails

The density hypothesis bounds the actual scalar `strictTail`, with analytic
multiplicity. It is the sole analytic input, and remains an explicit premise.
Exact layer cake converts it into the cosh-minus-one weighted sum; the closed
formula retains both `q - ell` and `q + ell` finite endpoint terms.

The intended Ingham input is motivated by Chourasiya--Simonič,
"An explicit form of Ingham's zero density estimate", Corollary 1:
https://arxiv.org/html/2507.15184v2 . The paper's deep zero-density theorem is
not formalized or replaced by a hypothesis-free assertion in this module.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace Real

theorem integral_neg_exp (δ M p : ℝ) (hp : p ≠ 0) :
    (∫ t in δ..M, Real.exp (-p * t)) =
      (Real.exp (-p * δ) - Real.exp (-p * M)) / p := by
  have hderiv : ∀ t, HasDerivAt (fun t => Real.exp (-p * t))
      ((-p) * Real.exp (-p * t)) t := by
    intro t
    simpa only [Function.comp_def, mul_one, mul_comm] using
      (Real.hasDerivAt_exp (-p * t)).comp t
        ((hasDerivAt_id t).const_mul (-p))
  have hint : IntervalIntegrable (fun t => (-p) * Real.exp (-p * t))
      volume δ M := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hderiv t) hint
  rw [intervalIntegral.integral_const_mul] at h
  apply (eq_div_iff hp).mpr
  calc
    _ = -((-p) * ∫ t in δ..M, Real.exp (-p * t)) := by ring
    _ = -(Real.exp (-p * M) - Real.exp (-p * δ)) := by rw [h]
    _ = _ := by ring

/-- Exact endpoint formula for the cosh−1 layer-cake integral. -/
theorem coshTail_integral_eq (δ M ell q : ℝ)
    (hell : 0 ≤ ell) (hql : ell < q) :
    (∫ t in δ..M, Real.exp (-q * t) * (ell * Real.sinh (ell * t))) =
      (ell / 2) *
        ((Real.exp (-(q - ell) * δ) - Real.exp (-(q - ell) * M)) / (q - ell) -
          (Real.exp (-(q + ell) * δ) - Real.exp (-(q + ell) * M)) / (q + ell)) := by
  have heq : (fun t => Real.exp (-q * t) * (ell * Real.sinh (ell * t))) =
      (fun t => (ell / 2) *
        (Real.exp (-(q - ell) * t) - Real.exp (-(q + ell) * t))) := by
    funext t
    rw [Real.sinh_eq]
    have hp : Real.exp (-q * t) * Real.exp (ell * t) =
        Real.exp (-(q - ell) * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hm : Real.exp (-q * t) * Real.exp (-(ell * t)) =
        Real.exp (-(q + ell) * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = (ell / 2) * (Real.exp (-q * t) * Real.exp (ell * t) -
          Real.exp (-q * t) * Real.exp (-(ell * t))) := by ring
      _ = _ := by rw [hp, hm]
  have hminus : IntervalIntegrable (fun t => Real.exp (-(q - ell) * t))
      volume δ M := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hplus : IntervalIntegrable (fun t => Real.exp (-(q + ell) * t))
      volume δ M := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [heq, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hminus hplus,
    integral_neg_exp δ M (q - ell) (ne_of_gt (sub_pos.mpr hql)),
    integral_neg_exp δ M (q + ell) (ne_of_gt (by linarith))]

end Real

namespace RiemannResearch.Analysis.ActualZeroOrdinate
open Zeta23

/-- An actual scalar tail bound transfers to any increasing differentiable
weight. No density provider is manufactured by this transfer theorem. -/
theorem badWeightedSum_le_of_expTail
    (T δ K q : ℝ) (φ f : ℝ → ℝ)
    (hδ : δ ≤ 1 / 2) (hf : Continuous f)
    (hderiv : ∀ t, HasDerivAt φ (f t) t)
    (hφ : 0 ≤ φ δ) (hf0 : ∀ t ∈ Icc δ (1 / 2), 0 ≤ f t)
    (htail : ∀ t ∈ Icc δ (1 / 2), strictTail T t ≤ K * Real.exp (-q * t)) :
    badWeightedSum T δ φ ≤ K *
      (φ δ * Real.exp (-q * δ) +
        ∫ t in δ..(1 / 2), Real.exp (-q * t) * f t) := by
  have hleft : IntervalIntegrable (fun t => strictTail T t * f t)
      volume δ (1 / 2) :=
    FiniteStrictTail.intervalIntegrable_tail_mul _ _ f hf δ (1 / 2)
  have hright : IntervalIntegrable
      (fun t => (K * Real.exp (-q * t)) * f t) volume δ (1 / 2) := by
    apply Continuous.intervalIntegrable
    exact (continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul hf
  have hint : (∫ t in δ..(1 / 2), strictTail T t * f t) ≤
      ∫ t in δ..(1 / 2), (K * Real.exp (-q * t)) * f t := by
    apply intervalIntegral.integral_mono_on hδ hleft hright
    intro t ht
    exact mul_le_mul_of_nonneg_right (htail t ht) (hf0 t ht)
  rw [badWeightedSum_layerCake T δ φ f hδ hf hderiv]
  calc
    _ ≤ φ δ * (K * Real.exp (-q * δ)) +
        ∫ t in δ..(1 / 2), (K * Real.exp (-q * t)) * f t :=
      add_le_add
        (mul_le_mul_of_nonneg_left (htail δ ⟨le_rfl, hδ⟩) hφ) hint
    _ = _ := by
      simp_rw [mul_assoc]
      rw [intervalIntegral.integral_const_mul]
      ring

theorem badCoshSum_le_of_expTail (T δ ell K q : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (hell : 0 ≤ ell)
    (htail : ∀ t ∈ Icc δ (1 / 2), strictTail T t ≤ K * Real.exp (-q * t)) :
    badWeightedSum T δ (fun t => Real.cosh (ell * t) - 1) ≤
      K * ((Real.cosh (ell * δ) - 1) * Real.exp (-q * δ) +
        ∫ t in δ..(1 / 2), Real.exp (-q * t) *
          (ell * Real.sinh (ell * t))) := by
  apply badWeightedSum_le_of_expTail T δ K q _ _ hδ
  · fun_prop
  · intro t
    simpa only [Function.comp_def, mul_one, mul_comm] using
      ((Real.hasDerivAt_cosh (ell * t)).comp t
        ((hasDerivAt_id t).const_mul ell)).sub_const 1
  · exact sub_nonneg.mpr (Real.one_le_cosh _)
  · intro t ht
    exact mul_nonneg hell (Real.sinh_nonneg_iff.mpr
      (mul_nonneg hell (hδ0.trans ht.1)))
  · exact htail

theorem badCoshSum_le_of_expTail_closed (T δ ell K q : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (hell : 0 ≤ ell) (hql : ell < q)
    (htail : ∀ t ∈ Icc δ (1 / 2), strictTail T t ≤ K * Real.exp (-q * t)) :
    badWeightedSum T δ (fun t => Real.cosh (ell * t) - 1) ≤
      K * ((Real.cosh (ell * δ) - 1) * Real.exp (-q * δ) +
        (ell / 2) *
          ((Real.exp (-(q - ell) * δ) - Real.exp (-(q - ell) / 2)) / (q - ell) -
            (Real.exp (-(q + ell) * δ) - Real.exp (-(q + ell) / 2)) / (q + ell))) := by
  have h := badCoshSum_le_of_expTail T δ ell K q hδ0 hδ hell htail
  rw [Real.coshTail_integral_eq δ (1 / 2) ell q hell hql] at h
  simpa only [mul_one_div] using h

end RiemannResearch.Analysis.ActualZeroOrdinate

/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroBadTailDensity
import RiemannResearch.Analysis.ActualZeroPhaseBootstrap
import RiemannResearch.Analysis.NonlinearZeroDensityRate
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Nonlinear actual zero-density consumers with complete additive remainders

Source for the proposed analytic input: Chourasiya--Simonic,
An explicit form of Ingham's zero density estimate, Theorem 1 and Table 1,
https://arxiv.org/html/2507.15184v2#S2.SS1 . This file proves the transfer
and finite operator consequences, not the source analytic density theorem.
The strict actual-zero tail, analytic multiplicities, original Ncount,
both exponential endpoints, negative companion term and full additive-error
endpoint are retained. A fixed low-height count can be included in E.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualZeroOrdinate
open Zeta23 ZeroDensityRate

/-- Additive density errors retain their full upper endpoint weight. -/
theorem badWeightedSum_le_of_expTail_add_constant
    (T δ K q E : ℝ) (φ f : ℝ → ℝ)
    (hδ : δ ≤ 1 / 2) (hf : Continuous f)
    (hderiv : ∀ t, HasDerivAt φ (f t) t)
    (hφ : 0 ≤ φ δ) (hf0 : ∀ t ∈ Icc δ (1 / 2), 0 ≤ f t)
    (htail : ∀ t ∈ Icc δ (1 / 2), strictTail T t ≤ K * Real.exp (-q * t) + E) :
    badWeightedSum T δ φ ≤ K *
      (φ δ * Real.exp (-q * δ) +
        ∫ t in δ..(1 / 2), Real.exp (-q * t) * f t) + E * φ (1 / 2) := by
  have hleft : IntervalIntegrable (fun t => strictTail T t * f t)
      volume δ (1 / 2) :=
    FiniteStrictTail.intervalIntegrable_tail_mul _ _ f hf δ (1 / 2)
  have hright : IntervalIntegrable
      (fun t => (K * Real.exp (-q * t) + E) * f t) volume δ (1 / 2) := by
    apply Continuous.intervalIntegrable
    exact ((continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).add
        continuous_const).mul hf
  have hK : IntervalIntegrable
      (fun t => K * (Real.exp (-q * t) * f t)) volume δ (1 / 2) := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hf)
  have hE : IntervalIntegrable (fun t => E * f t) volume δ (1 / 2) :=
    (continuous_const.mul hf).intervalIntegrable δ (1 / 2)
  have hFTC : (∫ t in δ..(1 / 2), f t) = φ (1 / 2) - φ δ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hf.intervalIntegrable δ (1 / 2))
  have hint : (∫ t in δ..(1 / 2), strictTail T t * f t) ≤
      ∫ t in δ..(1 / 2), (K * Real.exp (-q * t) + E) * f t := by
    apply intervalIntegral.integral_mono_on hδ hleft hright
    intro t ht
    exact mul_le_mul_of_nonneg_right (htail t ht) (hf0 t ht)
  rw [badWeightedSum_layerCake T δ φ f hδ hf hderiv]
  calc
    _ ≤ φ δ * (K * Real.exp (-q * δ) + E) +
        ∫ t in δ..(1 / 2), (K * Real.exp (-q * t) + E) * f t :=
      add_le_add
        (mul_le_mul_of_nonneg_left (htail δ ⟨le_rfl, hδ⟩) hφ) hint
    _ = _ := by
      have heq : (fun t => (K * Real.exp (-q * t) + E) * f t) =
          (fun t => K * (Real.exp (-q * t) * f t) + E * f t) := by
        funext t
        ring
      rw [heq, intervalIntegral.integral_add hK hE,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hFTC]
      ring

theorem badCoshSum_le_of_expTail_add_constant (T δ ell K q E : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (hell : 0 ≤ ell)
    (htail : ∀ t ∈ Icc δ (1 / 2), strictTail T t ≤ K * Real.exp (-q * t) + E) :
    badWeightedSum T δ (fun t => Real.cosh (ell * t) - 1) ≤
      K * ((Real.cosh (ell * δ) - 1) * Real.exp (-q * δ) +
        ∫ t in δ..(1 / 2), Real.exp (-q * t) *
          (ell * Real.sinh (ell * t))) + E * (Real.cosh (ell / 2) - 1) := by
  have h : badWeightedSum T δ (fun t => Real.cosh (ell * t) - 1) ≤
      K * ((Real.cosh (ell * δ) - 1) * Real.exp (-q * δ) +
        ∫ t in δ..(1 / 2), Real.exp (-q * t) *
          (ell * Real.sinh (ell * t))) + E * (Real.cosh (ell * (1 / 2)) - 1) := by
    apply badWeightedSum_le_of_expTail_add_constant T δ K q E _ _ hδ
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
  simpa only [mul_one_div] using h

theorem badCoshSum_le_of_expTail_add_constant_closed (T δ ell K q E : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (hell : 0 ≤ ell) (hql : ell < q)
    (htail : ∀ t ∈ Icc δ (1 / 2), strictTail T t ≤ K * Real.exp (-q * t) + E) :
    badWeightedSum T δ (fun t => Real.cosh (ell * t) - 1) ≤
      K * ((Real.cosh (ell * δ) - 1) * Real.exp (-q * δ) +
        (ell / 2) *
          ((Real.exp (-(q - ell) * δ) - Real.exp (-(q - ell) / 2)) / (q - ell) -
            (Real.exp (-(q + ell) * δ) - Real.exp (-(q + ell) / 2)) / (q + ell))) +
      E * (Real.cosh (ell / 2) - 1) := by
  have h := badCoshSum_le_of_expTail_add_constant T δ ell K q E hδ0 hδ hell htail
  rw [Real.coshTail_integral_eq δ (1 / 2) ell q hell hql] at h
  simpa only [mul_one_div] using h

/-- The actual scalar density estimate is still an explicit analytic premise.
The consumer keeps the nonlinear rate, both exponential endpoint terms,
and the complete additive error upper endpoint. -/
theorem badCoshSum_le_of_nonlinearTail_add_constant_closed
    (T δ ell K M E : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (hell : 0 ≤ ell)
    (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hql : ell < 12 * M / (3 - 2 * δ) ^ 2)
    (htail : ∀ t ∈ Icc δ (1 / 2),
      strictTail T t ≤ K * Real.exp (-M * inghamRate t) + E) :
    let q := 12 * M / (3 - 2 * δ) ^ 2
    let A := K * Real.exp (q * δ - M * inghamRate δ)
    badWeightedSum T δ (fun t => Real.cosh (ell * t) - 1) ≤
      A * ((Real.cosh (ell * δ) - 1) * Real.exp (-q * δ) +
        (ell / 2) *
          ((Real.exp (-(q - ell) * δ) - Real.exp (-(q - ell) / 2)) / (q - ell) -
            (Real.exp (-(q + ell) * δ) - Real.exp (-(q + ell) / 2)) / (q + ell))) +
      E * (Real.cosh (ell / 2) - 1) := by
  dsimp only
  apply badCoshSum_le_of_expTail_add_constant_closed T δ ell
    (K * Real.exp ((12 * M / (3 - 2 * δ) ^ 2) * δ - M * inghamRate δ))
    (12 * M / (3 - 2 * δ) ^ 2) E hδ0 hδ hell hql
  intro t ht
  have he := exp_inghamRate_tangent_le hM ht.1 ht.2
  calc
    strictTail T t ≤ K * Real.exp (-M * inghamRate t) + E := htail t ht
    _ ≤ K * (Real.exp ((12 * M / (3 - 2 * δ) ^ 2) * δ - M * inghamRate δ) *
        Real.exp (-(12 * M / (3 - 2 * δ) ^ 2) * t)) + E :=
      add_le_add (mul_le_mul_of_nonneg_left he hK) le_rfl
    _ = _ := by ring

end RiemannResearch.Analysis.ActualZeroOrdinate

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open Zeta23 ActualZeroOrdinate ZeroDensityRate Set

/-- Complete nonlinear weighted budget, including both finite endpoints. -/
def nonlinearCoshBudget (δ ell K M E : ℝ) : ℝ :=
  let q := 12 * M / (3 - 2 * δ) ^ 2
  let A := K * Real.exp (q * δ - M * inghamRate δ)
  A * ((Real.cosh (ell * δ) - 1) * Real.exp (-q * δ) +
    (ell / 2) *
      ((Real.exp (-(q - ell) * δ) - Real.exp (-(q - ell) / 2)) / (q - ell) -
       (Real.exp (-(q + ell) * δ) - Real.exp (-(q + ell) / 2)) / (q + ell))) +
    E * (Real.cosh (ell / 2) - 1)

theorem badCorrection_norm_le_of_nonlinearTail
    (T : ℝ) (d : ℕ) (hd : 1 ≤ d) (δ K M E : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hql : Real.log (d : ℝ) < 12 * M / (3 - 2 * δ) ^ 2)
    (htail : ∀ t ∈ Icc δ (1 / 2),
      strictTail T t ≤ K * Real.exp (-M * inghamRate t) + E) :
    ‖badCorrection T d δ‖ ≤
      (d : ℝ) / (2 * (Ncount 0 T : ℝ)) *
        nonlinearCoshBudget δ (Real.log (d : ℝ)) K M E := by
  have hL : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  apply (badCorrection_norm_le_badWeightedSum T d hd δ).trans
  exact mul_le_mul_of_nonneg_left
    (badCoshSum_le_of_nonlinearTail_add_constant_closed
      T δ (Real.log (d : ℝ)) K M E hδ0 hδ hL hK hM hql htail) (by positivity)

/-- Explicit scalar-density specialization of the actual finite frame test.
The actual density estimate and Landau-to-identity norm are explicit premises. -/
theorem phaseGram_isUnit_of_nonlinearTail
    (T : ℝ) (d : ℕ) (hd : 1 ≤ d) (δ K M E α : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hql : Real.log (d : ℝ) < 12 * M / (3 - 2 * δ) ^ 2)
    (htail : ∀ t ∈ Icc δ (1 / 2),
      strictTail T t ≤ K * Real.exp (-M * inghamRate t) + E)
    (hH : ‖landauGram T d - 1‖ ≤ α)
    (hsmall : α + (d : ℝ) / (2 * (Ncount 0 T : ℝ)) *
      nonlinearCoshBudget δ (Real.log (d : ℝ)) K M E +
      Real.cosh (δ * Real.log (d : ℝ)) < 2) :
    IsUnit (phaseGram T d) :=
  phaseGram_isUnit T d hd δ hδ0 α _ hH
    (badCorrection_norm_le_of_nonlinearTail T d hd δ K M E
      hδ0 hδ hK hM hql htail) hsmall

end RiemannResearch.Analysis.ActualZeroPhaseMoments

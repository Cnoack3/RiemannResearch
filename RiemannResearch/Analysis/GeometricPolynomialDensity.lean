/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ExponentialMomentDeterminacy
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Geometric polynomial moment uniqueness

Source: the user's generating-function density argument, 25 October 2026.
This uses the project's analytic moment-determinacy theorem with a geometric
atomic measure. Every exponential-integrability hypothesis is discharged.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology

namespace RiemannResearch.Analysis

/-- A bounded sequence annihilating all geometrically weighted monomials is zero.
The interval `0 < r ≤ 1/2` covers `r = p⁻¹` for every prime. -/
theorem eq_zero_of_geometric_polynomial_moments
    (r : ℝ) (hr0 : 0 < r) (hrhalf : r ≤ 1 / 2)
    (x : ℕ → ℝ) (C : ℝ) (hx : ∀ k, ‖x k‖ ≤ C)
    (hm : ∀ m : ℕ, (∑' k : ℕ, (k : ℝ)^m * r^k * x k) = 0) :
    ∀ k, x k = 0 := by
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hr0]
    linarith
  let μ : Measure ℝ :=
    Measure.sum (fun k : ℕ => ENNReal.ofReal (r^k) • Measure.dirac (k : ℝ))
  have hw (k : ℕ) : 0 ≤ r^k := pow_nonneg hr0.le k
  let : IsFiniteMeasure μ := ⟨by
    change (Measure.sum (fun k : ℕ =>
      ENNReal.ofReal (r^k) • Measure.dirac (k : ℝ))) univ < ∞
    simpa using (summable_geometric_of_norm_lt_one hr).tsum_ofReal_lt_top⟩
  let f : ℝ → ℝ := fun t => x (Nat.floor t)
  have hfm : Measurable f :=
    (measurable_of_countable x).comp Nat.measurable_floor
  have hf : MemLp f 2 μ :=
    MemLp.of_bound hfm.aestronglyMeasurable C (ae_of_all _ (fun t => hx _))
  have hp : ∀ m : ℕ, MemLp (fun t : ℝ => t^m) 2 μ := by
    intro m
    apply (memLp_two_iff_integrable_sq
      (continuous_id.pow m).measurable.aestronglyMeasurable).mpr
    change Integrable (fun t : ℝ => (t^m)^2)
      (Measure.sum (fun k : ℕ => ENNReal.ofReal (r^k) • Measure.dirac (k : ℝ)))
    apply integrable_sum_dirac (by simp)
    apply (summable_pow_mul_geometric_of_norm_lt_one (2*m) hr).congr
    intro k
    rw [ENNReal.toReal_ofReal (hw k), Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [← pow_mul, Nat.mul_comm m 2]
    exact mul_comm _ _
  have he : ∀ s ∈ Ioo (-1 / 4 : ℝ) (1 / 4),
      MemLp (fun t : ℝ => Real.exp (s*t)) 2 μ := by
    intro s hs
    have hexp : Real.exp (2*s) < 2 := by
      have hhalf := Real.exp_lt_two_add_div_two_sub
        (x := (1/2 : ℝ)) (by norm_num) (by norm_num)
      have hlt : Real.exp (2*s) < Real.exp (1/2) :=
        Real.exp_lt_exp.mpr (by linarith [hs.2])
      norm_num at hhalf
      linarith
    have hratio : ‖r * Real.exp (2*s)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (mul_pos hr0 (Real.exp_pos _))]
      nlinarith [Real.exp_pos (2*s)]
    apply (memLp_two_iff_integrable_sq
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.aestronglyMeasurable).mpr
    change Integrable (fun t : ℝ => Real.exp (s*t)^2)
      (Measure.sum (fun k : ℕ => ENNReal.ofReal (r^k) • Measure.dirac (k : ℝ)))
    apply integrable_sum_dirac (by simp)
    apply (summable_geometric_of_norm_lt_one hratio).congr
    intro k
    rw [ENNReal.toReal_ofReal (hw k), Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _), mul_pow]
    congr 1
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hmoment : ∀ m : ℕ, (∫ t, f t * t^m ∂μ) = 0 := by
    intro m
    change (∫ t, f t * t^m ∂Measure.sum
      (fun k : ℕ => ENNReal.ofReal (r^k) • Measure.dirac (k : ℝ))) = 0
    rw [integral_sum_dirac (by simp)]
    convert hm m using 1
    apply tsum_congr
    intro k
    simp only [ENNReal.toReal_ofReal (hw k), smul_eq_mul, f, Nat.floor_natCast]
    ring
  have hz : f =ᵐ[μ] 0 := ae_eq_zero_of_polynomial_moments hf hp he hmoment
  intro k
  have hz' : f =ᵐ[ENNReal.ofReal (r^k) • Measure.dirac (k : ℝ)] 0 :=
    (Measure.ae_sum_iff.mp hz) k
  have hwne : ENNReal.ofReal (r^k) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hr0 k))
  have hz'' : f =ᵐ[Measure.dirac (k : ℝ)] 0 :=
    (Measure.ae_ennreal_smul_measure_iff hwne).mp hz'
  simpa [Filter.EventuallyEq, f] using hz''

end RiemannResearch.Analysis

/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteClassDirichlet
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite weighted sampling: relative metrics and optimizer transfer

Source: user-directed zero-ordinate/CRT continuation, 21 October 2026.
The proofs are elementary finite weighted Cauchy--Schwarz and normal equations.
This is generic finite algebra. The relative sampling-frequency bound and
the two normal equations are explicit inputs. No zero equidistribution,
arithmetic gain lower bound, legal-density assertion, or RH is supplied.

The optimizer estimate retains the signed perturbation before applying
weighted Cauchy--Schwarz. Its squared displacement bound is quadratic in
the relative metric discrepancy, improving the direct minimization bound.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.FiniteWeightedSampling

variable {α : Type*}

def form (s : Finset α) (w f g : α → ℝ) : ℝ :=
  ∑ a ∈ s, w a * f a * g a

def energy (s : Finset α) (w f : α → ℝ) : ℝ :=
  ∑ a ∈ s, w a * f a ^ 2

theorem energy_nonneg (s : Finset α) (w f : α → ℝ)
    (hw : ∀ a ∈ s, 0 ≤ w a) : 0 ≤ energy s w f :=
  Finset.sum_nonneg (fun a ha => mul_nonneg (hw a ha) (sq_nonneg _))

theorem form_self (s : Finset α) (w f : α → ℝ) :
    form s w f f = energy s w f := by
  unfold form energy
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem form_sub_left (s : Finset α) (w f g h : α → ℝ) :
    form s w (fun a => f a - g a) h = form s w f h - form s w g h := by
  unfold form
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- Exact signed change of the bilinear form. -/
theorem sampled_form_sub_exact (s : Finset α) (w q f g : α → ℝ) :
    form s (fun a => w a * q a) f g - form s w f g =
      form s w (fun a => (q a - 1) * f a) g := by
  unfold form
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- Exact signed change of the quadratic form. -/
theorem sampled_energy_sub_exact (s : Finset α) (w q f : α → ℝ) :
    energy s (fun a => w a * q a) f - energy s w f =
      ∑ a ∈ s, w a * (q a - 1) * f a ^ 2 := by
  unfold energy
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- A relative frequency error gives a simultaneous comparison for every vector.
The result does not depend on the size of any individual weight. -/
theorem sampled_energy_comparison (s : Finset α) (w q f : α → ℝ) (δ : ℝ)
    (hw : ∀ a ∈ s, 0 ≤ w a)
    (hq : ∀ a ∈ s, |q a - 1| ≤ δ) :
    (1 - δ) * energy s w f ≤ energy s (fun a => w a * q a) f ∧
      energy s (fun a => w a * q a) f ≤ (1 + δ) * energy s w f := by
  constructor
  · unfold energy
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    have hqa : 1 - δ ≤ q a := by
      have h := (abs_le.mp (hq a ha)).1
      linarith
    have hmul := mul_le_mul_of_nonneg_right hqa
      (mul_nonneg (hw a ha) (sq_nonneg (f a)))
    nlinarith
  · unfold energy
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    have hqa : q a ≤ 1 + δ := by
      have h := (abs_le.mp (hq a ha)).2
      linarith
    have hmul := mul_le_mul_of_nonneg_right hqa
      (mul_nonneg (hw a ha) (sq_nonneg (f a)))
    nlinarith

/-- The multiplicative perturbation has energy at most delta squared times
the original energy. No boundedness assumption on the vector is required. -/
theorem relative_error_energy_le (s : Finset α) (w q f : α → ℝ) (δ : ℝ)
    (hw : ∀ a ∈ s, 0 ≤ w a)
    (hq : ∀ a ∈ s, |q a - 1| ≤ δ) :
    energy s w (fun a => (q a - 1) * f a) ≤ δ ^ 2 * energy s w f := by
  unfold energy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have hb := abs_le.mp (hq a ha)
  have hprod : 0 ≤ (δ - (q a - 1)) * (δ + (q a - 1)) :=
    mul_nonneg (by linarith) (by linarith)
  have hs : (q a - 1) ^ 2 ≤ δ ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hs
    (mul_nonneg (hw a ha) (sq_nonneg (f a)))
  nlinarith

/-- Signed cross-term control, uniform over both vectors. -/
theorem sampled_form_sub_sq_le (s : Finset α) (w q f g : α → ℝ) (δ : ℝ)
    (hw : ∀ a ∈ s, 0 ≤ w a)
    (hq : ∀ a ∈ s, |q a - 1| ≤ δ) :
    (form s (fun a => w a * q a) f g - form s w f g) ^ 2 ≤
      δ ^ 2 * energy s w f * energy s w g := by
  rw [sampled_form_sub_exact]
  calc
    (form s w (fun a => (q a - 1) * f a) g) ^ 2 ≤
        energy s w (fun a => (q a - 1) * f a) * energy s w g := by
      exact FiniteClassDirichlet.weighted_cauchy s w
        (fun a => (q a - 1) * f a) g hw
    _ ≤ δ ^ 2 * energy s w f * energy s w g :=
      mul_le_mul_of_nonneg_right (relative_error_energy_le s w q f δ hw hq)
        (energy_nonneg s w g hw)

theorem energy_sub_exact (s : Finset α) (w r z : α → ℝ) :
    energy s w (fun a => r a - z a) =
      energy s w r + energy s w z - 2 * form s w r z := by
  calc
    energy s w (fun a => r a - z a) =
        ∑ a ∈ s, (w a * r a ^ 2 + w a * z a ^ 2 -
          2 * (w a * r a * z a)) := by
      unfold energy
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = energy s w r + energy s w z - 2 * form s w r z := by
      simp only [energy, form, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Pythagorean identity from the true normal equation. Here r is the true
residual and z is the change from the true to the sampled optimizer. -/
theorem residual_energy_exact (s : Finset α) (w r z : α → ℝ)
    (htrue : form s w r z = 0) :
    energy s w (fun a => r a - z a) = energy s w r + energy s w z := by
  rw [energy_sub_exact, htrue]
  ring

/-- The whole optimizer displacement is an exact signed metric perturbation.
Both normal equations are retained explicitly. -/
theorem optimizer_perturbation_exact (s : Finset α) (w q r z : α → ℝ)
    (htrue : form s w r z = 0)
    (hsampled : form s (fun a => w a * q a) (fun a => r a - z a) z = 0) :
    form s (fun a => w a * q a) (fun a => r a - z a) z -
        form s w (fun a => r a - z a) z = energy s w z := by
  rw [hsampled, form_sub_left, htrue, form_self]
  ring

/-- Quadratic discrepancy bound for the true energy of optimizer movement.
The multiplied formulation remains valid at delta=1 and at zero displacement. -/
theorem optimizer_displacement_mul_bound (s : Finset α) (w q r z : α → ℝ)
    (δ : ℝ) (hw : ∀ a ∈ s, 0 ≤ w a)
    (hq : ∀ a ∈ s, |q a - 1| ≤ δ)
    (htrue : form s w r z = 0)
    (hsampled : form s (fun a => w a * q a) (fun a => r a - z a) z = 0) :
    (1 - δ ^ 2) * energy s w z ≤ δ ^ 2 * energy s w r := by
  have hcross := sampled_form_sub_sq_le s w q (fun a => r a - z a) z δ hw hq
  rw [optimizer_perturbation_exact s w q r z htrue hsampled,
    residual_energy_exact s w r z htrue] at hcross
  by_cases hz : energy s w z = 0
  · rw [hz, mul_zero]
    exact mul_nonneg (sq_nonneg δ) (energy_nonneg s w r hw)
  · have hzpos : 0 < energy s w z :=
      lt_of_le_of_ne (energy_nonneg s w z hw) (Ne.symm hz)
    have hcancel : energy s w z ≤ δ ^ 2 * (energy s w r + energy s w z) := by
      apply (mul_le_mul_iff_right₀ hzpos).mp
      nlinarith [hcross]
    nlinarith [hcancel]

theorem sampled_optimizer_residual_mul_bound (s : Finset α) (w q r z : α → ℝ)
    (δ : ℝ) (hw : ∀ a ∈ s, 0 ≤ w a)
    (hq : ∀ a ∈ s, |q a - 1| ≤ δ)
    (htrue : form s w r z = 0)
    (hsampled : form s (fun a => w a * q a) (fun a => r a - z a) z = 0) :
    (1 - δ ^ 2) * energy s w (fun a => r a - z a) ≤ energy s w r := by
  rw [residual_energy_exact s w r z htrue]
  have h := optimizer_displacement_mul_bound s w q r z δ hw hq htrue hsampled
  nlinarith

theorem optimizer_displacement_le (s : Finset α) (w q r z : α → ℝ)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hw : ∀ a ∈ s, 0 ≤ w a)
    (hq : ∀ a ∈ s, |q a - 1| ≤ δ)
    (htrue : form s w r z = 0)
    (hsampled : form s (fun a => w a * q a) (fun a => r a - z a) z = 0) :
    energy s w z ≤ (δ ^ 2 * energy s w r) / (1 - δ ^ 2) := by
  have hprod : 0 < (1 - δ) * (1 + δ) :=
    mul_pos (by linarith) (by linarith)
  have hden : 0 < 1 - δ ^ 2 := by nlinarith
  apply (le_div_iff₀ hden).mpr
  have h := optimizer_displacement_mul_bound s w q r z δ hw hq htrue hsampled
  nlinarith

theorem sampled_optimizer_true_error_le (s : Finset α) (w q r z : α → ℝ)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hw : ∀ a ∈ s, 0 ≤ w a)
    (hq : ∀ a ∈ s, |q a - 1| ≤ δ)
    (htrue : form s w r z = 0)
    (hsampled : form s (fun a => w a * q a) (fun a => r a - z a) z = 0) :
    energy s w (fun a => r a - z a) ≤ energy s w r / (1 - δ ^ 2) := by
  have hprod : 0 < (1 - δ) * (1 + δ) :=
    mul_pos (by linarith) (by linarith)
  have hden : 0 < 1 - δ ^ 2 := by nlinarith
  apply (le_div_iff₀ hden).mpr
  have h := sampled_optimizer_residual_mul_bound s w q r z δ hw hq htrue hsampled
  nlinarith

/-- Minimum-value comparison from actual two-way competitor inequalities.
The caller can use any common feasible affine family, not only a linear span. -/
theorem sampled_minimum_comparison (s : Finset α) (w q r rhat : α → ℝ)
    (δ : ℝ) (hδ : δ ≤ 1) (hw : ∀ a ∈ s, 0 ≤ w a)
    (hq : ∀ a ∈ s, |q a - 1| ≤ δ)
    (htrueMin : energy s w r ≤ energy s w rhat)
    (hsampledMin : energy s (fun a => w a * q a) rhat ≤
      energy s (fun a => w a * q a) r) :
    (1 - δ) * energy s w r ≤ energy s (fun a => w a * q a) rhat ∧
      energy s (fun a => w a * q a) rhat ≤ (1 + δ) * energy s w r := by
  constructor
  · exact (mul_le_mul_of_nonneg_left htrueMin (by linarith)).trans
      (sampled_energy_comparison s w q rhat δ hw hq).1
  · exact hsampledMin.trans (sampled_energy_comparison s w q r δ hw hq).2

end RiemannResearch.Analysis.FiniteWeightedSampling

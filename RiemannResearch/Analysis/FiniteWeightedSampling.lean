/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteClassDirichlet
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
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


/-- Weighted normality in the direction of the candidate itself controls its
true energy. The signed cross term is estimated only after the exact
energy identity; no target-closure assumption is used. -/
theorem sampled_projection_energy_mul_bound {α : Type*}
    (s : Finset α) (w q y f : α → ℝ) (δ : ℝ)
    (hw : ∀ a ∈ s, 0 ≤ w a)
    (hq : ∀ a ∈ s, |q a - 1| ≤ δ)
    (hnormal : form s (fun a => w a * q a) (fun a => y a - f a) f = 0) :
    (1 - δ ^ 2) * energy s w f ≤ energy s w y := by
  have hcross := sampled_form_sub_sq_le s w q (fun a => y a - f a) f δ hw hq
  rw [hnormal, zero_sub, neg_sq] at hcross
  have cross_lower (e d t : ℝ) (he : 0 ≤ e) (hd : 0 ≤ d)
      (ht : t ^ 2 ≤ e * d) : 0 ≤ e + d + 2 * t := by
    by_contra h
    have hn : e + d + 2 * t < 0 := lt_of_not_ge h
    have hp : 0 < e + d - 2 * t := by linarith
    have hprod := mul_neg_of_neg_of_pos hn hp
    nlinarith [sq_nonneg (e - d)]
  have hnonneg := cross_lower
    (energy s w (fun a => y a - f a))
    (δ ^ 2 * energy s w f)
    (form s w (fun a => y a - f a) f)
    (energy_nonneg s w _ hw)
    (mul_nonneg (sq_nonneg δ) (energy_nonneg s w f hw))
    (by nlinarith [hcross])
  have he := energy_sub_exact s w y f
  rw [form_sub_left, form_self] at hnonneg
  nlinarith [hnonneg, he]

/-- A sampled projection of a unit-energy target has true energy at most
`1 / (1 - δ^2)`. This bounds the unconstrained optimizer, not a candidate
subject to additional affine head constraints. -/
theorem sampled_projection_energy_le {α : Type*}
    (s : Finset α) (w q y f : α → ℝ) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hw : ∀ a ∈ s, 0 ≤ w a)
    (hq : ∀ a ∈ s, |q a - 1| ≤ δ)
    (hnormal : form s (fun a => w a * q a) (fun a => y a - f a) f = 0) :
    energy s w f ≤ energy s w y / (1 - δ ^ 2) := by
  have hden : 0 < 1 - δ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hδ1) (show 0 < 1 + δ by linarith)]
  apply (le_div_iff₀ hden).mpr
  simpa only [mul_comm] using
    sampled_projection_energy_mul_bound s w q y f δ hw hq hnormal

/-- Exact rational equality case at relative discrepancy one half.
The factor `1 / (1 - δ^2)` cannot be improved using only these hypotheses. -/
theorem sampled_projection_two_cell_sharpness :
    let w : Fin 2 → ℝ := fun a => if a.val = 0 then 1 / 4 else 3 / 4
    let q : Fin 2 → ℝ := fun a => if a.val = 0 then 1 / 2 else 3 / 2
    let f : Fin 2 → ℝ := fun a => if a.val = 0 then 2 else 2 / 3
    (∀ a, 0 ≤ w a) ∧ (∀ a, |q a - 1| ≤ 1 / 2) ∧
      form Finset.univ (fun a => w a * q a) (fun a => 1 - f a) f = 0 ∧
      energy Finset.univ w (fun _ => 1) = 1 ∧
      energy Finset.univ w f = 4 / 3 := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a; fin_cases a <;> norm_num
  · intro a; fin_cases a <;> norm_num
  · norm_num [form, Fin.sum_univ_two]
  · norm_num [energy, Fin.sum_univ_two]
  · norm_num [energy, Fin.sum_univ_two]

end RiemannResearch.Analysis.FiniteWeightedSampling

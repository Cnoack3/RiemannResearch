/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Exact square-partition localization of autocorrelations

Source: Sections 4 and 5 of the user-provided research note
`RH_Exact_Arithmetic_Channel_Effects_2026-09-07.md`.

These are identities for actual complex Lebesgue integrals, with all
integrability assumptions explicit. No sign is assigned to the nonlocal
defect and no estimate uniform in a growing support window is asserted.
-/

open scoped ComplexConjugate
open MeasureTheory

namespace RiemannResearch.Analysis.SquarePartitionLocalization

variable {ι : Type*} [Fintype ι]

/-- Real defect of a finite square partition. -/
def partitionDefect (χ : ι → ℝ → ℝ) (x y : ℝ) : ℝ :=
  1 - ∑ j, χ j x * χ j y

/-- Exact polarization identity for the nonlocal partition defect. -/
theorem partitionDefect_eq_half_sum_sq (χ : ι → ℝ → ℝ) (x y : ℝ)
    (hx : ∑ j, χ j x ^ 2 = 1) (hy : ∑ j, χ j y ^ 2 = 1) :
    partitionDefect χ x y = (1 / 2 : ℝ) * ∑ j, (χ j x - χ j y) ^ 2 := by
  have h : (∑ j, (χ j x - χ j y) ^ 2) =
      (∑ j, χ j x ^ 2) - 2 * (∑ j, χ j x * χ j y) + ∑ j, χ j y ^ 2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.mul_sum]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h, hx, hy]
  unfold partitionDefect
  ring

theorem partitionDefect_nonneg (χ : ι → ℝ → ℝ) (x y : ℝ)
    (hx : ∑ j, χ j x ^ 2 = 1) (hy : ∑ j, χ j y ^ 2 = 1) :
    0 ≤ partitionDefect χ x y := by
  rw [partitionDefect_eq_half_sum_sq χ x y hx hy]
  positivity

theorem partitionDefect_diag (χ : ι → ℝ → ℝ) (x : ℝ)
    (hx : ∑ j, χ j x ^ 2 = 1) : partitionDefect χ x x = 0 := by
  rw [partitionDefect_eq_half_sum_sq χ x x hx hx]
  simp

/-- Autocorrelation, with the convention used by the signed Weil note. -/
noncomputable def autocorrelation (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ x, f (x + t) * conj (f x)

/-- Multiplication by one real localization function. -/
def localized (χ : ℝ → ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ := (χ x : ℂ) * f x

/-- The complete nonlocal gluing autocorrelation, before applying Weil. -/
noncomputable def gluingCorrelation (χ : ι → ℝ → ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ x, (partitionDefect χ (x + t) x : ℂ) * f (x + t) * conj (f x)

private theorem localized_integrand_sum (χ : ι → ℝ → ℝ) (f : ℝ → ℂ)
    (x t : ℝ) :
    (∑ j, localized (χ j) f (x + t) * conj (localized (χ j) f x)) =
      f (x + t) * conj (f x) -
        (partitionDefect χ (x + t) x : ℂ) * f (x + t) * conj (f x) := by
  simp only [localized, map_mul, Complex.conj_ofReal, partitionDefect,
    Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_sum,
    Complex.ofReal_mul]
  rw [sub_mul, sub_mul, one_mul, sub_sub_cancel]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exact gluing identity, retaining the full mixed-window correlation. -/
theorem sum_autocorrelation_localized (χ : ι → ℝ → ℝ) (f : ℝ → ℂ) (t : ℝ)
    (hf : Integrable (fun x => f (x + t) * conj (f x)))
    (hχ : ∀ j, Integrable
      (fun x => localized (χ j) f (x + t) * conj (localized (χ j) f x))) :
    (∑ j, autocorrelation (localized (χ j) f) t) =
      autocorrelation f t - gluingCorrelation χ f t := by
  have hs : Integrable (fun x => ∑ j,
      localized (χ j) f (x + t) * conj (localized (χ j) f x)) :=
    integrable_finsetSum _ (fun j _ => hχ j)
  have hd : Integrable (fun x =>
      (partitionDefect χ (x + t) x : ℂ) * f (x + t) * conj (f x)) := by
    convert hf.sub hs using 1
    ext x
    simp only [Pi.sub_apply]
    rw [localized_integrand_sum]
    ring
  unfold autocorrelation gluingCorrelation
  rw [← integral_finsetSum _ (fun j _ => hχ j)]
  simp_rw [localized_integrand_sum]
  exact integral_sub hf hd

/-- A square partition makes the gluing defect vanish exactly on the diagonal. -/
theorem gluingCorrelation_zero (χ : ι → ℝ → ℝ) (f : ℝ → ℂ)
    (hχ : ∀ x, ∑ j, χ j x ^ 2 = 1) : gluingCorrelation χ f 0 = 0 := by
  unfold gluingCorrelation
  simp only [add_zero, partitionDefect_diag χ _ (hχ _), Complex.ofReal_zero,
    zero_mul, integral_zero]

/-- Autocorrelation expansion under channel addition; both mixed terms remain. -/
theorem autocorrelation_add (f g : ℝ → ℂ) (t : ℝ)
    (hff : Integrable (fun x => f (x+t) * conj (f x)))
    (hfg : Integrable (fun x => f (x+t) * conj (g x)))
    (hgf : Integrable (fun x => g (x+t) * conj (f x)))
    (hgg : Integrable (fun x => g (x+t) * conj (g x))) :
    autocorrelation (f + g) t = autocorrelation f t + autocorrelation g t +
      (∫ x, f (x+t) * conj (g x)) + (∫ x, g (x+t) * conj (f x)) := by
  let F : Fin 4 → ℝ → ℂ := ![
    (fun x => f (x+t) * conj (f x)),
    (fun x => g (x+t) * conj (g x)),
    (fun x => f (x+t) * conj (g x)),
    (fun x => g (x+t) * conj (f x))]
  have hi : ∀ j : Fin 4, Integrable (F j) := by
    intro j
    fin_cases j
    · exact hff
    · exact hgg
    · exact hfg
    · exact hgf
  have heq : (fun x => (f+g) (x+t) * conj ((f+g) x)) =
      (fun x => ∑ j : Fin 4, F j x) := by
    ext x
    simp [F, Fin.sum_univ_succ, map_add]
    ring
  unfold autocorrelation
  rw [heq, integral_finsetSum _ (fun j _ => hi j)]
  simp [F, Fin.sum_univ_succ]
  ring

end RiemannResearch.Analysis.SquarePartitionLocalization

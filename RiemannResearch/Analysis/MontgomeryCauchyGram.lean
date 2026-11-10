/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.MontgomeryPoisson
import RiemannResearch.Analysis.ZeroOrdinateEquidistribution
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # The positive Cauchy Gram for finite ordinate families

Source: Montgomery (1973), https://websites.umich.edu/~hlm/paircor1.pdf,
and the user's handoff, Section 4. The integral identity is proved for arbitrary
finite real ordinates, with repeated ordinates and arbitrary complex coefficients.
The bilateral transform provider is MontgomeryPoisson.integral_cauchy.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace RiemannResearch.Analysis.MontgomeryPoisson
open ZeroOrdinate
variable {ι : Type*} [Fintype ι]

def cauchyWeight (d : ℝ) : ℝ := 4/(4+d^2)

def signal (t : ι → ℝ) (c : ι → ℂ) (s : ℝ) : ℂ :=
  ∑ i, c i * phase s (t i)

def kernelQuadratic (t : ι → ℝ) (c : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, c i * conj (c j) * (cauchyWeight (t i-t j) : ℂ)

theorem phase_mul_conj (s t v : ℝ) :
    phase s t * conj (phase s v) = phase s (t-v) := by
  simp only [phase, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp
  <;> ring

theorem feature_phase (d s : ℝ) :
    feature 2 ((d : ℂ)*Complex.I) s =
      (Real.exp (-2*|s|) : ℂ) * phase s d := by
  rw [feature, phase, Complex.exp_add, Complex.ofReal_exp]
  congr 1
  · congr 2; ring
  · congr 1
    push_cast
    ring

theorem finite_gram_integrand (t : ι → ℝ) (c : ι → ℂ) (s : ℝ) :
    ((Real.exp (-2*|s|) * ‖signal t c s‖^2 : ℝ) : ℂ) =
      ∑ i, ∑ j, c i * conj (c j) *
        feature 2 (((t i-t j : ℝ) : ℂ)*Complex.I) s := by
  rw [Complex.ofReal_mul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  simp only [signal, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [feature_phase, ← phase_mul_conj]
  ring

theorem finite_gram_complex (t : ι → ℝ) (c : ι → ℂ) :
    (∫ s : ℝ, ((Real.exp (-2*|s|) * ‖signal t c s‖^2 : ℝ) : ℂ)) =
      kernelQuadratic t c := by
  have hint (i j : ι) : Integrable (fun s : ℝ =>
      c i * conj (c j) * feature 2 (((t i-t j : ℝ) : ℂ)*Complex.I) s) :=
    (integrable_feature 2 _ (by simp)).const_mul _
  simp_rw [finite_gram_integrand]
  rw [integral_finsetSum _ (fun i hi => integrable_finsetSum _ (fun j hj => hint i j))]
  unfold kernelQuadratic
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j hj => hint i j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul, integral_cauchy]
  rfl

theorem finite_gram_integrable (t : ι → ℝ) (c : ι → ℂ) :
    Integrable (fun s : ℝ =>
      ((Real.exp (-2*|s|) * ‖signal t c s‖^2 : ℝ) : ℂ)) := by
  simp_rw [finite_gram_integrand]
  apply integrable_finsetSum
  intro i hi
  apply integrable_finsetSum
  intro j hj
  exact (integrable_feature 2 _ (by simp)).const_mul _

theorem finite_gram (t : ι → ℝ) (c : ι → ℂ) :
    ∫ s : ℝ, Real.exp (-2*|s|) * ‖signal t c s‖^2 =
      (kernelQuadratic t c).re := by
  have h := integral_re (finite_gram_integrable t c)
  change (∫ s : ℝ, (((Real.exp (-2*|s|) * ‖signal t c s‖^2 : ℝ) : ℂ)).re) =
    (∫ s : ℝ, ((Real.exp (-2*|s|) * ‖signal t c s‖^2 : ℝ) : ℂ)).re at h
  simpa only [Complex.ofReal_re, finite_gram_complex] using h

theorem kernelQuadratic_nonneg (t : ι → ℝ) (c : ι → ℂ) :
    0 ≤ (kernelQuadratic t c).re := by
  rw [← finite_gram]
  exact integral_nonneg (fun s => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))

end RiemannResearch.Analysis.MontgomeryPoisson

/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ZeroSamplingQuadratic

/-!
# Sharp finite spectral Gram comparison

Source: direct finite Cauchy--Schwarz argument, developed in the zero-ordinate
harmonic analysis continuation. The diagonal is retained exactly; only the
off-diagonal remainder is bounded. This improves the earlier cardinality
factor from `card` to `card - 1`, including empty and singleton supports.
-/

noncomputable section
open scoped BigOperators
open RiemannResearch.Analysis.ZeroSamplingQuadratic

namespace RiemannResearch.Analysis.SharpSpectralGram

variable {ι : Type*}

theorem offdiag_mass [DecidableEq ι] (s : Finset ι) (a : ι → ℂ) :
    (∑ i ∈ s, ∑ j ∈ s, if i = j then (0 : ℝ) else ‖a i‖ * ‖a j‖) =
      (∑ i ∈ s, ‖a i‖) ^ 2 - coefficientEnergy s a := by
  classical
  have hi : ∀ i j, (if i = j then (0 : ℝ) else ‖a i‖ * ‖a j‖) =
      ‖a i‖ * ‖a j‖ - (if i = j then ‖a i‖ ^ 2 else 0) := by
    intro i j
    split_ifs with h
    · subst j
      ring
    · ring
  simp_rw [hi, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq]
  simp only [Finset.sum_ite_mem]
  rw [← Finset.sum_mul_sum, ← pow_two]
  simp [coefficientEnergy]

theorem form_offdiag_bound (s : Finset ι) (R : ι → ι → ℂ)
    (a : ι → ℂ) (e : ℝ) (he : 0 ≤ e)
    (hdiag : ∀ i ∈ s, R i i = 0)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ‖R i j‖ ≤ e) :
    ‖form s R a‖ ≤ ((s.card : ℝ) - 1) * e * coefficientEnergy s a := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖a i‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  calc
    ‖form s R a‖ ≤ ∑ i ∈ s, ∑ j ∈ s,
        e * (if i = j then (0 : ℝ) else ‖a i‖ * ‖a j‖) := by
      unfold form
      apply le_trans (norm_sum_le _ _)
      apply Finset.sum_le_sum
      intro i hi
      apply le_trans (norm_sum_le _ _)
      apply Finset.sum_le_sum
      intro j hj
      by_cases hij : i = j
      · subst j
        simp [hdiag i hi]
      · simp only [if_neg hij, norm_mul, norm_star]
        calc
          _ ≤ ‖a i‖ * ‖a j‖ * e := mul_le_mul_of_nonneg_left
            (hoff i hi j hj hij) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          _ = _ := by ring
    _ = e * ((∑ i ∈ s, ‖a i‖) ^ 2 - coefficientEnergy s a) := by
      simp_rw [← Finset.mul_sum]
      rw [offdiag_mass]
    _ ≤ e * (((s.card : ℝ) - 1) * coefficientEnergy s a) := by
      apply mul_le_mul_of_nonneg_left _ he
      unfold coefficientEnergy at *
      nlinarith
    _ = _ := by ring

theorem real_form_error_sharp (s : Finset ι) (G : ι → ι → ℂ)
    (a : ι → ℂ) (e : ℝ) (he : 0 ≤ e)
    (hdiag : ∀ i ∈ s, G i i = 1)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ‖G i j‖ ≤ e) :
    |(form s G a).re - coefficientEnergy s a| ≤
      ((s.card : ℝ) - 1) * e * coefficientEnergy s a := by
  classical
  let R : ι → ι → ℂ := fun i j => G i j - if i = j then 1 else 0
  have hRdiag : ∀ i ∈ s, R i i = 0 := by
    intro i hi
    simp [R, hdiag i hi]
  have hRoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ‖R i j‖ ≤ e := by
    intro i hi j hj hij
    simpa [R, hij] using hoff i hi j hj hij
  have h := form_offdiag_bound s R a e he hRdiag hRoff
  have hform : form s R a = form s G a - (coefficientEnergy s a : ℂ) := by
    dsimp [R]
    rw [form_sub, form_identity]
  rw [hform] at h
  have hreal : |(form s G a).re - coefficientEnergy s a| ≤
      ‖form s G a - (coefficientEnergy s a : ℂ)‖ := by
    simpa only [Complex.sub_re, Complex.ofReal_re] using
      Complex.abs_re_le_norm (form s G a - (coefficientEnergy s a : ℂ))
  exact hreal.trans h

theorem near_identity_bounds_sharp
    (s : Finset ι) (G : ι → ι → ℂ) (a : ι → ℂ)
    (e : ℝ) (he : 0 ≤ e) (hdiag : ∀ i ∈ s, G i i = 1)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ‖G i j‖ ≤ e) :
    (1 - ((s.card : ℝ) - 1) * e) * coefficientEnergy s a ≤ (form s G a).re ∧
      (form s G a).re ≤
        (1 + ((s.card : ℝ) - 1) * e) * coefficientEnergy s a := by
  have h := abs_le.mp (real_form_error_sharp s G a e he hdiag hoff)
  constructor <;> nlinarith [h.1, h.2]

theorem positive_form_of_sharp_error
    (s : Finset ι) (G : ι → ι → ℂ) (a : ι → ℂ)
    (e : ℝ) (he : 0 ≤ e) (hdiag : ∀ i ∈ s, G i i = 1)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ‖G i j‖ ≤ e)
    (hsmall : ((s.card : ℝ) - 1) * e < 1)
    (ha : 0 < coefficientEnergy s a) : 0 < (form s G a).re := by
  have h := (near_identity_bounds_sharp s G a e he hdiag hoff).1
  exact (mul_pos (sub_pos.mpr hsmall) ha).trans_le h

end RiemannResearch.Analysis.SharpSpectralGram

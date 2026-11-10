/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomeryResolventDifference
import RiemannResearch.Analysis.MontgomeryLocalMass
import RiemannResearch.Analysis.MontgomeryComplexGram
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FunProp
/-! # A coefficient-sensitive horizontal perturbation bound
The full signed mixed kernel is the Gram matrix of exponential differences.
Its Schur estimate is linear in the sum of squared horizontal displacements,
including repeated ordinates. Source: Montgomery's Poisson/Gram framework;
the mixed-resolvent estimate is proved in MontgomeryResolventDifference.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace RiemannResearch.Analysis.MontgomeryDifferenceGram
open MontgomeryPoisson MontgomeryComplexGram MontgomeryResolventDifference
open MontgomeryLocalMass MarkedFourierTail
variable {ι : Type*} [Fintype ι]
def shiftedExponent (a t : ℝ) : ℂ := (a : ℂ) + Complex.I*t
@[simp] theorem shiftedExponent_re (a t : ℝ) : (shiftedExponent a t).re = a := by
  simp [shiftedExponent]
@[simp] theorem shiftedExponent_im (a t : ℝ) : (shiftedExponent a t).im = t := by
  simp [shiftedExponent]
theorem shiftedExponent_pair (a b t v : ℝ) :
    shiftedExponent a t + conj (shiftedExponent b v) =
      (a+b : ℝ) + Complex.I*(t-v) := by
  simp [shiftedExponent]
  ring
def differenceSignal (a t : ι → ℝ) (c : ι → ℂ) (s : ℝ) : ℂ :=
  complexSignal (fun i => shiftedExponent (a i) (t i)) c s -
    complexSignal (fun i => shiftedExponent 0 (t i)) c s
def pairFeature (a b d s : ℝ) : ℂ :=
  feature 2 ((a+b : ℝ)+Complex.I*d) s -
    feature 2 ((a : ℂ)+Complex.I*d) s -
    feature 2 ((b : ℂ)+Complex.I*d) s +
    feature 2 (Complex.I*d) s
theorem pairFeature_integrable (a b d : ℝ) (ha : |a| ≤ 1 / 2) (hb : |b| ≤ 1 / 2) :
    Integrable (pairFeature a b d) := by
  have h1 : |(((a+b : ℝ) : ℂ)+Complex.I*d).re| < (2 : ℝ) := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    have hh := abs_add_le a b
    linarith
  have h2 : |((a : ℂ)+Complex.I*d).re| < (2 : ℝ) := by simpa using ha.trans_lt (by norm_num)
  have h3 : |((b : ℂ)+Complex.I*d).re| < (2 : ℝ) := by simpa using hb.trans_lt (by norm_num)
  have h4 : |(Complex.I*d).re| < (2 : ℝ) := by simp
  exact (((integrable_feature 2 _ h1).sub (integrable_feature 2 _ h2)).sub
    (integrable_feature 2 _ h3)).add (integrable_feature 2 _ h4)
theorem integral_pairFeature (a b d : ℝ) (ha : |a| ≤ 1 / 2) (hb : |b| ≤ 1 / 2) :
    (∫ s : ℝ, pairFeature a b d s) = differenceKernel a b d := by
  have hab : |a+b| ≤ 1 := (abs_add_le _ _).trans (by linarith)
  have hh (x : ℝ) (hx : |x| ≤ 1) :
      Integrable (feature 2 ((x : ℂ)+Complex.I*d)) := by
    apply integrable_feature
    simpa using hx.trans_lt (by norm_num : (1 : ℝ) < 2)
  have hi (x : ℝ) (hx : |x| ≤ 1) :
      (∫ s : ℝ, feature 2 ((x : ℂ)+Complex.I*d) s) =
        laplaceKernel ((x : ℂ)+Complex.I*d) := by
    rw [integral_feature 2 _ (by simpa using hx.trans_lt (by norm_num : (1 : ℝ) < 2)),
      laplaceKernel_eq _ (by simpa using hx)]
    norm_num
  have h0 := hh 0 (by norm_num)
  have h0i := hi 0 (by norm_num)
  simp only [Complex.ofReal_zero, zero_add] at h0 h0i
  unfold pairFeature differenceKernel
  have h12 := integral_sub (hh (a+b) hab) (hh a (by linarith))
  have h123 := integral_sub ((hh (a+b) hab).sub (hh a (by linarith)))
    (hh b (by linarith))
  have h1234 := integral_add (((hh (a+b) hab).sub (hh a (by linarith))).sub
    (hh b (by linarith))) h0
  simp only [Pi.sub_apply] at h123 h1234
  rw [h1234, h123, h12, hi (a+b) hab, hi a (by linarith),
    hi b (by linarith), h0i]

theorem pairFeature_product (a b t v s : ℝ) :
    pairFeature a b (t-v) s =
      (Real.exp (-2*|s|) : ℂ) *
      ((Complex.exp ((s : ℂ)*shiftedExponent a t) -
        Complex.exp ((s : ℂ)*shiftedExponent 0 t)) *
       conj (Complex.exp ((s : ℂ)*shiftedExponent b v) -
        Complex.exp ((s : ℂ)*shiftedExponent 0 v))) := by
  have h (x y : ℝ) := feature_complex_product (shiftedExponent x t) (shiftedExponent y v) s
  simp only [shiftedExponent_pair] at h
  have h10 := h a 0
  have h01 := h 0 b
  have h00 := h 0 0
  simp only [add_zero, zero_add, Complex.ofReal_zero] at h10 h01 h00
  unfold pairFeature
  simp only [Complex.ofReal_sub]
  rw [h a b, h10, h01, h00, map_sub]
  ring

theorem differenceSignal_sum (a t : ι → ℝ) (c : ι → ℂ) (s : ℝ) :
    differenceSignal a t c s =
      ∑ i, c i * (Complex.exp ((s : ℂ)*shiftedExponent (a i) (t i)) -
        Complex.exp ((s : ℂ)*shiftedExponent 0 (t i))) := by
  simp [differenceSignal, complexSignal, mul_sub, Finset.sum_sub_distrib]

theorem difference_gram_integrand (a t : ι → ℝ) (c : ι → ℂ) (s : ℝ) :
    ((Real.exp (-2*|s|) * ‖differenceSignal a t c s‖^2 : ℝ) : ℂ) =
      ∑ i, ∑ j, c i * conj (c j) * pairFeature (a i) (a j) (t i-t j) s := by
  rw [Complex.ofReal_mul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj,
    differenceSignal_sum]
  simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [pairFeature_product]
  ring

theorem difference_gram (a t : ι → ℝ) (c : ι → ℂ)
    (ha : ∀ i, |a i| ≤ 1 / 2) :
    (∫ s : ℝ, ((Real.exp (-2*|s|) * ‖differenceSignal a t c s‖^2 : ℝ) : ℂ)) =
      ∑ i, ∑ j, c i * conj (c j) * differenceKernel (a i) (a j) (t i-t j) := by
  have hint (i j : ι) : Integrable (fun s : ℝ =>
      c i * conj (c j) * pairFeature (a i) (a j) (t i-t j) s) :=
    (pairFeature_integrable _ _ _ (ha i) (ha j)).const_mul _
  simp_rw [difference_gram_integrand]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul, integral_pairFeature _ _ _ (ha i) (ha j)]

theorem weightedDifference_memLp (a t : ι → ℝ) (c : ι → ℂ)
    (ha : ∀ i, |a i| ≤ 1 / 2) :
    MemLp (fun s : ℝ => (Real.exp (-|s|) : ℂ)*differenceSignal a t c s) 2 := by
  have h1 := weightedSignal_memLp (fun i => shiftedExponent (a i) (t i)) c
    (fun i => by simpa using (ha i).trans_lt (by norm_num : (1 / 2 : ℝ) < 1))
  have h0 := weightedSignal_memLp (fun i => shiftedExponent 0 (t i)) c
    (fun i => by simp)
  convert h1.sub h0 using 1
  ext s
  simp only [Pi.sub_apply, weightedSignal, differenceSignal, mul_sub]

theorem difference_gram_integrable (a t : ι → ℝ) (c : ι → ℂ)
    (ha : ∀ i, |a i| ≤ 1 / 2) :
    Integrable (fun s : ℝ =>
      ((Real.exp (-2*|s|) * ‖differenceSignal a t c s‖^2 : ℝ) : ℂ)) := by
  simp_rw [difference_gram_integrand]
  apply integrable_finsetSum
  intro i hi
  apply integrable_finsetSum
  intro j hj
  exact (pairFeature_integrable _ _ _ (ha i) (ha j)).const_mul _

theorem difference_gram_re (a t : ι → ℝ) (c : ι → ℂ)
    (ha : ∀ i, |a i| ≤ 1 / 2) :
    (∫ s : ℝ, Real.exp (-2*|s|) * ‖differenceSignal a t c s‖^2) =
      (∑ i, ∑ j, c i * conj (c j) * differenceKernel (a i) (a j) (t i-t j)).re := by
  have h := integral_re (difference_gram_integrable a t c ha)
  change (∫ s : ℝ, (((Real.exp (-2*|s|) * ‖differenceSignal a t c s‖^2 : ℝ) : ℂ)).re) =
    (∫ s : ℝ, ((Real.exp (-2*|s|) * ‖differenceSignal a t c s‖^2 : ℝ) : ℂ)).re at h
  simpa only [Complex.ofReal_re, difference_gram a t c ha] using h

theorem difference_energy_le_of_rows (a t : ι → ℝ) (c : ι → ℂ) (D : ℝ)
    (ha : ∀ i, |a i| ≤ 1 / 2)
    (hrow : ∀ i, (∑ j, cauchyWeight (t i-t j)) ≤ D) :
    (∫ s : ℝ, Real.exp (-2*|s|) * ‖differenceSignal a t c s‖^2) ≤
      4 * D * ∑ i, ‖c i‖^2 * (a i)^2 := by
  have hterm (i j : ι) :
      ‖c i * conj (c j) * differenceKernel (a i) (a j) (t i-t j)‖ ≤
        4 * (cauchyWeight (t i-t j) * (‖c i‖*|a i|) * (‖c j‖*|a j|)) := by
    rw [norm_mul, norm_mul, Complex.norm_conj]
    calc
      _ ≤ (‖c i‖*‖c j‖)*(4*|a i| *|a j| *cauchyWeight (t i-t j)) :=
        mul_le_mul_of_nonneg_left (differenceKernel_bound _ _ _ (ha i) (ha j))
          (by positivity)
      _ = _ := by ring
  have hquad := symmetric_kernel_quadratic_le_row_bound
    Finset.univ (fun i => ‖c i‖*|a i|) (fun i j => cauchyWeight (t i-t j)) D
    (fun i _ j _ => cauchyWeight_nonneg _) (fun i _ j _ => by
      unfold cauchyWeight; congr 2; ring)
    (fun i _ => hrow i)
  rw [difference_gram_re a t c ha]
  calc
    _ ≤ ‖∑ i, ∑ j, c i * conj (c j) * differenceKernel (a i) (a j) (t i-t j)‖ :=
      Complex.re_le_norm _
    _ ≤ ∑ i, ∑ j, 4 * (cauchyWeight (t i-t j) * (‖c i‖*|a i|) * (‖c j‖*|a j|)) := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => hterm i j))))
    _ = 4 * ∑ i, ∑ j, cauchyWeight (t i-t j) * (‖c i‖*|a i|) * (‖c j‖*|a j|) := by
      simp only [Finset.mul_sum]
    _ ≤ 4 * (D * ∑ i, (‖c i‖*|a i|)^2) := mul_le_mul_of_nonneg_left hquad (by norm_num)
    _ = _ := by simp only [mul_pow, sq_abs, mul_assoc]


end RiemannResearch.Analysis.MontgomeryDifferenceGram

/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoMellinTwoKernel
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite continuous Mellin Gram certificates

Source: the user-directed zero-ordinate calculation of 21 October 2026.
The continuous Cauchy Gram kernel is classical; J.-F. Burnol,
"A note on Nyman's equivalent formulation of the Riemann Hypothesis",
https://arxiv.org/abs/math/9910055, Sections 1--2, supports the strategy.
The results evaluate actual integrals and retain the full squared remainder.
The inverse certificate explicitly requires nonsingularity; no Cauchy
determinant product, independence provider, or Burnol rate is assumed.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
variable {ι : Type*} [Fintype ι]

def finiteMellinKernel (s c : ι → ℂ) (x : ℝ) : ℂ :=
  ∑ i, starRingEnd ℂ (c i) * paretoMellinKernel (s i) x

def mellinCauchyGram (s : ι → ℂ) : Matrix ι ι ℂ :=
  fun i j => 1 / (s i + starRingEnd ℂ (s j) - 1)

def mellinGramQuadratic (s c : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * mellinCauchyGram s i j

omit [Fintype ι] in
theorem mellinCauchyGram_entry_re_im (s : ι → ℂ) (i j : ι) :
    mellinCauchyGram s i j =
      1 / (((((s i).re + (s j).re - 1 : ℝ) : ℂ)) +
        (((s i).im - (s j).im : ℝ) : ℂ) * Complex.I) := by
  unfold mellinCauchyGram
  apply congrArg (fun z : ℂ => 1 / z)
  apply Complex.ext <;> simp [sub_eq_add_neg]

theorem finiteMellinKernel_memLp (s c : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) :
    MemLp (finiteMellinKernel s c) 2 (volume.restrict (Ioi 1)) := by
  classical
  exact memLp_finsetSum _ (fun i _ =>
    (paretoMellinKernel_memLp (s i) (hs i) (by norm_num : (0 : ℝ) < 1)).const_mul _)

theorem finiteMellinKernel_pairing (f : ThresholdHilbert) (s c : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) :
    (∫ x in Ioi (1 : ℝ), mellinWeightedStep f x * finiteMellinKernel s c x) =
      ∑ i, starRingEnd ℂ (c i) * paretoMellin f (s i) := by
  classical
  have he : (fun x => mellinWeightedStep f x * finiteMellinKernel s c x) =
      fun x => ∑ i, starRingEnd ℂ (c i) *
        (mellinWeightedStep f x * paretoMellinKernel (s i) x) := by
    funext x
    simp only [finiteMellinKernel, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, integral_finsetSum _ (fun i _ =>
    (paretoMellin_integrable f (s i) (hs i)).const_mul _)]
  simp_rw [integral_const_mul]
  rfl

theorem finiteMellinKernel_cross_integrable (s c : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) :
    IntegrableOn (fun x => finiteMellinKernel s c x *
      starRingEnd ℂ (finiteMellinKernel s c x)) (Ioi 1) := by
  exact (finiteMellinKernel_memLp s c hs).integrable_mul
    (finiteMellinKernel_memLp s c hs).star

theorem finiteMellinKernel_gram_integral (s c : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) :
    (∫ x in Ioi (1 : ℝ), finiteMellinKernel s c x *
      starRingEnd ℂ (finiteMellinKernel s c x)) = mellinGramQuadratic s c := by
  classical
  have hi (i j : ι) : IntegrableOn (fun x =>
      (starRingEnd ℂ (c i) * c j) * (paretoMellinKernel (s i) x *
        starRingEnd ℂ (paretoMellinKernel (s j) x))) (Ioi 1) :=
    (paretoMellinKernel_cross_integrable (s i) (s j) (hs i) (hs j)).const_mul _
  have he : (fun x => finiteMellinKernel s c x *
      starRingEnd ℂ (finiteMellinKernel s c x)) =
      fun x => ∑ i, ∑ j, (starRingEnd ℂ (c i) * c j) *
        (paretoMellinKernel (s i) x *
          starRingEnd ℂ (paretoMellinKernel (s j) x)) := by
    funext x
    have hconj (z : ℂ) : starRingEnd ℂ (starRingEnd ℂ z) = z := by
      change star (star z) = z
      exact star_star z
    simp only [finiteMellinKernel, map_sum, map_mul, hconj,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  unfold mellinGramQuadratic
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, paretoMellinKernel_gram (s i) (s j) (hs i) (hs j)]
  rfl

theorem finiteMellinKernel_energy (s c : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) :
    (∫ x in Ioi (1 : ℝ), ‖finiteMellinKernel s c x‖ ^ 2) =
      (mellinGramQuadratic s c).re := by
  calc
    _ = ∫ x in Ioi (1 : ℝ),
        (finiteMellinKernel s c x * starRingEnd ℂ (finiteMellinKernel s c x)).re := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      dsimp only
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
    _ = (∫ x in Ioi (1 : ℝ),
        finiteMellinKernel s c x * starRingEnd ℂ (finiteMellinKernel s c x)).re :=
      integral_re (finiteMellinKernel_cross_integrable s c hs)
    _ = _ := congrArg Complex.re (finiteMellinKernel_gram_integral s c hs)

theorem finiteMellinKernel_remainder (f : ThresholdHilbert) (s c : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) :
    (∫ x in Ioi (1 : ℝ),
      ‖mellinWeightedStep f x - starRingEnd ℂ (finiteMellinKernel s c x)‖ ^ 2) =
      ‖f‖ ^ 2 + (mellinGramQuadratic s c).re -
        2 * (∑ i, starRingEnd ℂ (c i) * paretoMellin f (s i)).re := by
  have hif := (mellinWeightedStep_memLp f).norm.integrable_sq
  have hik := (finiteMellinKernel_memLp s c hs).norm.integrable_sq
  have hip : IntegrableOn (fun x =>
      mellinWeightedStep f x * finiteMellinKernel s c x) (Ioi 1) :=
    (mellinWeightedStep_memLp f).integrable_mul (finiteMellinKernel_memLp s c hs)
  have hiab : IntegrableOn (fun x =>
      ‖mellinWeightedStep f x‖ ^ 2 + ‖finiteMellinKernel s c x‖ ^ 2) (Ioi 1) :=
    hif.add hik
  have hir : IntegrableOn (fun x =>
      (mellinWeightedStep f x * finiteMellinKernel s c x).re) (Ioi 1) := hip.re
  have he : (fun x =>
      ‖mellinWeightedStep f x - starRingEnd ℂ (finiteMellinKernel s c x)‖ ^ 2) =
      fun x => ‖mellinWeightedStep f x‖ ^ 2 + ‖finiteMellinKernel s c x‖ ^ 2 -
        2 * (mellinWeightedStep f x * finiteMellinKernel s c x).re := by
    funext x
    simp only [Complex.sq_norm, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.conj_re, Complex.conj_im]
    ring
  have hival : (∫ x in Ioi (1 : ℝ),
      (mellinWeightedStep f x * finiteMellinKernel s c x).re) =
      (∑ i, starRingEnd ℂ (c i) * paretoMellin f (s i)).re := by
    calc
      _ = (∫ x in Ioi (1 : ℝ),
          mellinWeightedStep f x * finiteMellinKernel s c x).re := integral_re hip
      _ = _ := congrArg Complex.re (finiteMellinKernel_pairing f s c hs)
  rw [he, integral_sub hiab (hir.const_mul 2), integral_add hif hik,
    mellinWeightedStep_energy, finiteMellinKernel_energy s c hs,
    integral_const_mul, hival]

theorem mellinGramQuadratic_eq_of_normal (s c b : ι → ℂ)
    (hn : ∀ i, ∑ j, mellinCauchyGram s i j * c j = b i) :
    mellinGramQuadratic s c = ∑ i, starRingEnd ℂ (c i) * b i := by
  classical
  unfold mellinGramQuadratic
  apply Finset.sum_congr rfl
  intro i _
  rw [← hn i, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem finiteMellinKernel_normal_lower_bound (f : ThresholdHilbert) (s c : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hn : ∀ i, ∑ j, mellinCauchyGram s i j * c j = paretoMellin f (s i)) :
    (∑ i, starRingEnd ℂ (c i) * paretoMellin f (s i)).re ≤ ‖f‖ ^ 2 := by
  have he := finiteMellinKernel_remainder f s c hs
  rw [mellinGramQuadratic_eq_of_normal s c _ hn] at he
  have hnonneg : 0 ≤ ∫ x in Ioi (1 : ℝ),
      ‖mellinWeightedStep f x - starRingEnd ℂ (finiteMellinKernel s c x)‖ ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  linarith

private theorem conjugate_dot_re (c b : ι → ℂ) :
    (∑ i, starRingEnd ℂ (c i) * b i).re =
      (∑ i, starRingEnd ℂ (b i) * c i).re := by
  classical
  have he : (∑ i, starRingEnd ℂ (c i) * b i) =
      starRingEnd ℂ (∑ i, starRingEnd ℂ (b i) * c i) := by
    have hconj (z : ℂ) : starRingEnd ℂ (starRingEnd ℂ z) = z := by
      change star (star z) = z
      exact star_star z
    simp only [map_sum, map_mul, hconj]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, Complex.conj_re]

theorem finiteMellinKernel_inverse_lower_bound [DecidableEq ι]
    (f : ThresholdHilbert) (s : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hdet : (mellinCauchyGram s).det ≠ 0) :
    (dotProduct (fun i => starRingEnd ℂ (paretoMellin f (s i)))
      ((mellinCauchyGram s)⁻¹.mulVec (fun i => paretoMellin f (s i)))).re ≤
      ‖f‖ ^ 2 := by
  let b : ι → ℂ := fun i => paretoMellin f (s i)
  let c : ι → ℂ := (mellinCauchyGram s)⁻¹.mulVec b
  have hn : ∀ i, ∑ j, mellinCauchyGram s i j * c j = paretoMellin f (s i) := by
    have he : (mellinCauchyGram s).mulVec c = b := by
      dsimp only [c]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
        (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
    intro i
    exact congrFun he i
  have h := finiteMellinKernel_normal_lower_bound f s c hs hn
  rw [conjugate_dot_re] at h
  exact h

end RiemannResearch.RH.Pareto

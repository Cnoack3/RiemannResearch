/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/

import RiemannResearch.RH.ParetoMellinFunctional
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-!
# Exact Gram calculus for two Pareto Mellin kernels

The literal continuous kernels satisfy
`integral (K_s * conj K_t) = 1 / (s + conj t - 1)`.
The two-kernel energy retains the complete signed cross term. Completing
the square gives an exact integral remainder for every physical Pareto vector.

Source: classical Mellin/Hardy-space Gram geometry used in J.-F. Burnol,
"A note on Nyman's equivalent formulation of the Riemann Hypothesis",
arXiv:math/9910055, Sections 1--2. This reference supports the proof strategy.
The proofs below directly evaluate actual Bochner integrals; no Hardy-space
identification, zero hypothesis, or research provider is assumed.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

/-- Conjugation of a Mellin kernel on the positive real axis. -/
theorem paretoMellinKernel_conj (s : ℂ) {x : ℝ} (hx : 0 < x) :
    paretoMellinKernel (starRingEnd ℂ s) x =
      starRingEnd ℂ (paretoMellinKernel s x) := by
  have harg : (x : ℂ).arg ≠ Real.pi := by
    simpa [Complex.arg_ofReal_of_nonneg hx.le] using Real.pi_ne_zero.symm
  simpa [paretoMellinKernel] using
    Complex.conj_cpow (x : ℂ) (-(starRingEnd ℂ s)) harg

/-- Reality of the physical sequence makes its Mellin transform conjugate-symmetric. -/
theorem paretoMellin_conj (f : ThresholdHilbert) (s : ℂ) :
    paretoMellin f (starRingEnd ℂ s) = starRingEnd ℂ (paretoMellin f s) := by
  unfold paretoMellin
  rw [← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [paretoMellinKernel_conj s (lt_trans zero_lt_one hx), map_mul]
  simp [mellinWeightedStep]

/-- The complete signed cross-kernel product is integrable. -/
theorem paretoMellinKernel_cross_integrable (s t : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (ht : (1 / 2 : ℝ) < t.re) :
    IntegrableOn (fun x => paretoMellinKernel s x *
      starRingEnd ℂ (paretoMellinKernel t x)) (Ioi 1) := by
  have hc : (1 / 2 : ℝ) < (starRingEnd ℂ t).re := by simpa using ht
  apply ((paretoMellinKernel_memLp s hs (by norm_num : (0 : ℝ) < 1)).integrable_mul
    (paretoMellinKernel_memLp (starRingEnd ℂ t) hc (by norm_num : (0 : ℝ) < 1))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change paretoMellinKernel s x * paretoMellinKernel (starRingEnd ℂ t) x = _
  rw [paretoMellinKernel_conj t (lt_trans zero_lt_one hx)]

/-- Exact continuous Gram entry for two kernels in the continuity half-plane. -/
theorem paretoMellinKernel_gram (s t : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (ht : (1 / 2 : ℝ) < t.re) :
    (∫ x in Ioi (1 : ℝ), paretoMellinKernel s x *
      starRingEnd ℂ (paretoMellinKernel t x)) =
        1 / (s + starRingEnd ℂ t - 1) := by
  have he : (∫ x in Ioi (1 : ℝ), paretoMellinKernel s x *
      starRingEnd ℂ (paretoMellinKernel t x)) =
      ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-(s + starRingEnd ℂ t)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    rw [← paretoMellinKernel_conj t hx0]
    unfold paretoMellinKernel
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx0.ne')]
    congr 1
    ring
  rw [he, integral_Ioi_cpow_of_lt (by
    simp only [Complex.neg_re, Complex.add_re, Complex.conj_re]
    linarith) (by norm_num)]
  simp only [Complex.ofReal_one, Complex.one_cpow]
  rw [show -(s + starRingEnd ℂ t) + 1 = -(s + starRingEnd ℂ t - 1) by ring]
  rw [div_neg, neg_div, neg_neg]

/-- A two-kernel test with unrestricted complex coefficients. -/
def mellinTwoKernel (s t c d : ℂ) (x : ℝ) : ℂ :=
  c * paretoMellinKernel s x + d * paretoMellinKernel t x

/-- A finite complex combination of two Mellin kernels belongs to L². -/
theorem mellinTwoKernel_memLp (s t c d : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (ht : (1 / 2 : ℝ) < t.re) :
    MemLp (mellinTwoKernel s t c d) 2 (volume.restrict (Ioi 1)) :=
  ((paretoMellinKernel_memLp s hs (by norm_num : (0 : ℝ) < 1)).const_mul c).add
    ((paretoMellinKernel_memLp t ht (by norm_num : (0 : ℝ) < 1)).const_mul d)

/-- Exact signed Mellin signature of a two-kernel test. -/
theorem mellinTwoKernel_pairing (f : ThresholdHilbert) (s t c d : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (ht : (1 / 2 : ℝ) < t.re) :
    (∫ x in Ioi (1 : ℝ), mellinWeightedStep f x * mellinTwoKernel s t c d x) =
      c * paretoMellin f s + d * paretoMellin f t := by
  have he : (fun x => mellinWeightedStep f x * mellinTwoKernel s t c d x) =
      fun x => c * (mellinWeightedStep f x * paretoMellinKernel s x) +
        d * (mellinWeightedStep f x * paretoMellinKernel t x) := by
    funext x
    unfold mellinTwoKernel
    ring
  rw [he, integral_add ((paretoMellin_integrable f s hs).const_mul c)
    ((paretoMellin_integrable f t ht).const_mul d),
    integral_const_mul, integral_const_mul]
  rfl

/-- Exact energy, including the full signed cross term. -/
theorem mellinTwoKernel_energy (s t c d : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (ht : (1 / 2 : ℝ) < t.re) :
    (∫ x in Ioi (1 : ℝ), ‖mellinTwoKernel s t c d x‖ ^ 2) =
      ‖c‖ ^ 2 / (2 * s.re - 1) + ‖d‖ ^ 2 / (2 * t.re - 1) +
        2 * ((c * starRingEnd ℂ d) / (s + starRingEnd ℂ t - 1)).re := by
  have hi1 := ((paretoMellinKernel_memLp s hs
    (by norm_num : (0 : ℝ) < 1)).const_mul c).norm.integrable_sq
  have hi2 := ((paretoMellinKernel_memLp t ht
    (by norm_num : (0 : ℝ) < 1)).const_mul d).norm.integrable_sq
  have hic := (paretoMellinKernel_cross_integrable s t hs ht).const_mul (c * starRingEnd ℂ d)
  have he : (fun x => ‖mellinTwoKernel s t c d x‖ ^ 2) =
      fun x => ‖c * paretoMellinKernel s x‖ ^ 2 +
        ‖d * paretoMellinKernel t x‖ ^ 2 +
        2 * ((c * starRingEnd ℂ d) * (paretoMellinKernel s x *
          starRingEnd ℂ (paretoMellinKernel t x))).re := by
    funext x
    simp only [mellinTwoKernel, Complex.sq_norm, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im]
    ring
  have he1 : (∫ x in Ioi (1 : ℝ), ‖c * paretoMellinKernel s x‖ ^ 2) =
      ‖c‖ ^ 2 / (2 * s.re - 1) := by
    simp_rw [norm_mul, mul_pow]
    rw [integral_const_mul, paretoMellinKernel_energy s hs (by norm_num)]
    simp [Real.one_rpow, div_eq_mul_inv]
  have he2 : (∫ x in Ioi (1 : ℝ), ‖d * paretoMellinKernel t x‖ ^ 2) =
      ‖d‖ ^ 2 / (2 * t.re - 1) := by
    simp_rw [norm_mul, mul_pow]
    rw [integral_const_mul, paretoMellinKernel_energy t ht (by norm_num)]
    simp [Real.one_rpow, div_eq_mul_inv]
  have hiab : IntegrableOn (fun x => ‖c * paretoMellinKernel s x‖ ^ 2 +
      ‖d * paretoMellinKernel t x‖ ^ 2) (Ioi 1) := hi1.add hi2
  have hir : IntegrableOn (fun x =>
      ((c * starRingEnd ℂ d) * (paretoMellinKernel s x *
        starRingEnd ℂ (paretoMellinKernel t x))).re) (Ioi 1) := hic.re
  have hival : (∫ x in Ioi (1 : ℝ),
      ((c * starRingEnd ℂ d) * (paretoMellinKernel s x *
        starRingEnd ℂ (paretoMellinKernel t x))).re) =
      ((c * starRingEnd ℂ d) / (s + starRingEnd ℂ t - 1)).re := by
    rw [show (∫ x in Ioi (1 : ℝ),
      ((c * starRingEnd ℂ d) * (paretoMellinKernel s x *
        starRingEnd ℂ (paretoMellinKernel t x))).re) =
      (∫ x in Ioi (1 : ℝ), (c * starRingEnd ℂ d) *
        (paretoMellinKernel s x * starRingEnd ℂ (paretoMellinKernel t x))).re
      from integral_re hic]
    rw [integral_const_mul, paretoMellinKernel_gram s t hs ht]
    congr 1
    ring
  rw [he, integral_add hiab (hir.const_mul 2), integral_add hi1 hi2,
    he1, he2, integral_const_mul, hival]

/-- Completing the square retains the entire nonnegative integral remainder. -/
theorem mellinTwoKernel_remainder_energy (f : ThresholdHilbert) (s t c d : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (ht : (1 / 2 : ℝ) < t.re) :
    (∫ x in Ioi (1 : ℝ),
      ‖mellinWeightedStep f x - starRingEnd ℂ (mellinTwoKernel s t c d x)‖ ^ 2) =
      ‖f‖ ^ 2 + (∫ x in Ioi (1 : ℝ), ‖mellinTwoKernel s t c d x‖ ^ 2) -
        2 * (c * paretoMellin f s + d * paretoMellin f t).re := by
  have hif := (mellinWeightedStep_memLp f).norm.integrable_sq
  have hik := (mellinTwoKernel_memLp s t c d hs ht).norm.integrable_sq
  have hip := (mellinWeightedStep_memLp f).integrable_mul
    (mellinTwoKernel_memLp s t c d hs ht)
  have hiab : IntegrableOn (fun x => ‖mellinWeightedStep f x‖ ^ 2 +
      ‖mellinTwoKernel s t c d x‖ ^ 2) (Ioi 1) := hif.add hik
  have hir : IntegrableOn (fun x =>
      (mellinWeightedStep f x * mellinTwoKernel s t c d x).re) (Ioi 1) := hip.re
  have he : (fun x =>
      ‖mellinWeightedStep f x - starRingEnd ℂ (mellinTwoKernel s t c d x)‖ ^ 2) =
      fun x => ‖mellinWeightedStep f x‖ ^ 2 + ‖mellinTwoKernel s t c d x‖ ^ 2 -
        2 * (mellinWeightedStep f x * mellinTwoKernel s t c d x).re := by
    funext x
    simp only [Complex.sq_norm, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.conj_re, Complex.conj_im]
    ring
  have hival : (∫ x in Ioi (1 : ℝ),
      (mellinWeightedStep f x * mellinTwoKernel s t c d x).re) =
      (c * paretoMellin f s + d * paretoMellin f t).re := by
    calc
      _ = (∫ x in Ioi (1 : ℝ),
          mellinWeightedStep f x * mellinTwoKernel s t c d x).re := integral_re hip
      _ = _ := by rw [mellinTwoKernel_pairing f s t c d hs ht]
  rw [he, integral_sub hiab (hir.const_mul 2), integral_add hif hik,
    mellinWeightedStep_energy, integral_const_mul, hival]

end RiemannResearch.RH.Pareto

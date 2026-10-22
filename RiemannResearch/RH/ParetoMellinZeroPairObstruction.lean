/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/

import RiemannResearch.RH.ParetoMellinTwoKernel
import RiemannResearch.RH.ParetoBeurlingMellinObstruction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact two-zero and conjugate-pair obstructions for legal Pareto approximation

For an actual zero `s` with `Re s > 1/2` and `Im s ≠ 0`, the error of every
vector in the physical legal residue closure is exactly `2q - q²` plus a
nonnegative continuous integral remainder, where `q = (2 Re s - 1) / |s|²`.
Reality supplies the conjugate Mellin constraint directly; no unproved
zeta-conjugation or analytic-continuation provider is introduced.

The general two-zero identity allows arbitrary complex test coefficients and
retains the full signed Gram cross term.

Sources: J.-F. Burnol, arXiv:math/9910055, Theorem 1.2 and Section 2, supports
the finite-zero obstruction strategy and the product-form pair charge.
B. Bagchi, arXiv:math/0607733, Theorem 1 and Remark 4, supplies the discrete
Nyman--Beurling research context. These proofs directly specialize the
project's already proved actual Pareto Mellin signature.

Open: obtaining legal approximations whose errors tend to zero. This module
proves quantitative consequences of hypothetical actual zeros and zero-free
certificates from actual approximation witnesses; it does not discharge that
arithmetic convergence problem.
-/

noncomputable section
open MeasureTheory Set


namespace RiemannResearch.RH.Pareto

/-- The pair charge `2q - q²`, where `q = (2 Re s - 1) / |s|²`. -/
def mellinZeroPairCharge (s : ℂ) : ℝ :=
  2 * ((2 * s.re - 1) / Complex.normSq s) -
    ((2 * s.re - 1) / Complex.normSq s) ^ 2

/-- Explicit coefficient solving the continuous conjugate-pair Gram problem. -/
def mellinZeroPairCoefficient (s : ℂ) : ℂ :=
  ⟨(2 * s.re - 1) / (2 * Complex.normSq s),
    (2 * s.re - 1) * ((2 * s.re - 1) * (s.re - 1) + 2 * s.im ^ 2) /
      (2 * s.im * Complex.normSq s)⟩

/-- The explicit coefficient has exactly the conjugate-pair target charge. -/
theorem mellinZeroPairCoefficient_target (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hi : s.im ≠ 0) :
    mellinZeroPairCoefficient s / s +
      starRingEnd ℂ (mellinZeroPairCoefficient s) / starRingEnd ℂ s =
        (mellinZeroPairCharge s : ℂ) := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hR : s.re * s.re + s.im * s.im ≠ 0 := by
    simpa only [Complex.normSq_apply] using (Complex.normSq_pos.mpr hs0).ne'
  apply Complex.ext <;>
    simp only [Complex.ofReal_re, Complex.ofReal_im] <;>
    simp [mellinZeroPairCoefficient, mellinZeroPairCharge,
      Complex.div_re, Complex.div_im, Complex.normSq_apply] <;>
    field_simp [hi, hR] <;> ring

/-- The explicit two-kernel test has energy exactly equal to its target charge. -/
theorem mellinZeroPairCoefficient_energy (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hi : s.im ≠ 0) :
    (∫ x in Ioi (1 : ℝ),
      ‖mellinTwoKernel s (starRingEnd ℂ s)
        (mellinZeroPairCoefficient s) (starRingEnd ℂ (mellinZeroPairCoefficient s)) x‖ ^ 2) =
      mellinZeroPairCharge s := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hR : s.re * s.re + s.im * s.im ≠ 0 := by
    simpa only [Complex.normSq_apply] using (Complex.normSq_pos.mpr hs0).ne'
  have ha : 2 * s.re - 1 ≠ 0 := by linarith
  have hd : (2 * s.re - 1) * (2 * s.re - 1) + (2 * s.im) * (2 * s.im) ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero ha, sq_nonneg (2 * s.im)]
  rw [mellinTwoKernel_energy s (starRingEnd ℂ s) _ _ hs (by simpa using hs)]
  simp [mellinZeroPairCoefficient, mellinZeroPairCharge, Complex.sq_norm,
    Complex.normSq_apply, Complex.div_re]
  field_simp [hi, hR, ha, hd]
  ring

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto
open RiemannResearch.RH.ParetoBeurlingMellinObstruction

/-- The conjugate-pair charge strictly improves the single-zero charge. -/
theorem mellinZeroPairCharge_gt_single (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hi : s.im ≠ 0) :
    (2 * s.re - 1) / ‖s‖ ^ 2 < mellinZeroPairCharge s := by
  rw [Complex.sq_norm]
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hR : 0 < Complex.normSq s := Complex.normSq_pos.mpr hs0
  have ha : 0 < 2 * s.re - 1 := by linarith
  have hlt : 2 * s.re - 1 < Complex.normSq s := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg (s.re - 1), mul_self_pos.mpr hi]
  have hq0 : 0 < (2 * s.re - 1) / Complex.normSq s := div_pos ha hR
  have hq1 : (2 * s.re - 1) / Complex.normSq s < 1 := (div_lt_one hR).mpr hlt
  unfold mellinZeroPairCharge
  nlinarith [mul_pos hq0 (sub_pos.mpr hq1)]

/-- Every nonreal point strictly right of the critical line has positive pair charge. -/
theorem mellinZeroPairCharge_pos (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hi : s.im ≠ 0) :
    0 < mellinZeroPairCharge s := by
  have hp : 0 < (2 * s.re - 1) / ‖s‖ ^ 2 := by
    apply div_pos (by linarith)
    exact pow_pos (norm_pos_iff.mpr (by intro h; norm_num [h] at hs)) 2
  exact lt_trans hp (mellinZeroPairCharge_gt_single s hs hi)

/-- An actual nonreal zeta zero forces an exact physical error decomposition. -/
theorem normalizedResidue_error_zeroPair_identity
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hi : s.im ≠ 0)
    (hz : riemannZeta s = 0) (f : ThresholdHilbert)
    (hf : f ∈ normalizedResidueClosure) :
    ‖hilbertOne - f‖ ^ 2 = mellinZeroPairCharge s +
      ∫ x in Ioi (1 : ℝ),
        ‖mellinWeightedStep (hilbertOne - f) x -
          starRingEnd ℂ (mellinTwoKernel s (starRingEnd ℂ s)
            (mellinZeroPairCoefficient s)
            (starRingEnd ℂ (mellinZeroPairCoefficient s)) x)‖ ^ 2 := by
  have hs1 : s ≠ 1 := by intro h; apply hi; simp [h]
  have hm := paretoMellin_normalizedResidue_error_identity s hs hs1 hz f hf
  have hsignature :
      mellinZeroPairCoefficient s * paretoMellin (hilbertOne - f) s +
        starRingEnd ℂ (mellinZeroPairCoefficient s) *
          paretoMellin (hilbertOne - f) (starRingEnd ℂ s) =
        (mellinZeroPairCharge s : ℂ) := by
    rw [paretoMellin_conj, hm]
    simpa only [map_div₀, map_one, mul_one_div] using
      mellinZeroPairCoefficient_target s hs hi
  have he := mellinTwoKernel_remainder_energy (hilbertOne - f) s
    (starRingEnd ℂ s) (mellinZeroPairCoefficient s)
    (starRingEnd ℂ (mellinZeroPairCoefficient s)) hs (by simpa using hs)
  rw [mellinZeroPairCoefficient_energy s hs hi, hsignature, Complex.ofReal_re] at he
  linarith

/-- The full physical error dominates the optimized conjugate-pair charge. -/
theorem normalizedResidue_error_zeroPair_lower_bound
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hi : s.im ≠ 0)
    (hz : riemannZeta s = 0) (f : ThresholdHilbert)
    (hf : f ∈ normalizedResidueClosure) :
    mellinZeroPairCharge s ≤ ‖hilbertOne - f‖ ^ 2 := by
  rw [normalizedResidue_error_zeroPair_identity s hs hi hz f hf]
  exact le_add_of_nonneg_right (integral_nonneg (fun _ => sq_nonneg _))

/-- A legal approximation beating the pair charge certifies a zero-free point. -/
theorem zeta_ne_zero_of_error_lt_zeroPairCharge
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hi : s.im ≠ 0)
    (f : ThresholdHilbert) (hf : f ∈ normalizedResidueClosure)
    (herror : ‖hilbertOne - f‖ ^ 2 < mellinZeroPairCharge s) :
    riemannZeta s ≠ 0 := by
  intro hz
  exact (not_le_of_gt herror) (normalizedResidue_error_zeroPair_lower_bound s hs hi hz f hf)

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto
open RiemannResearch.RH.ParetoBeurlingMellinObstruction

/-- Two actual zeros give a variational identity with every signed term retained. -/
theorem normalizedResidue_error_twoZero_identity
    (s t c d : ℂ) (hs : (1 / 2 : ℝ) < s.re) (ht : (1 / 2 : ℝ) < t.re)
    (hs1 : s ≠ 1) (ht1 : t ≠ 1)
    (hzs : riemannZeta s = 0) (hzt : riemannZeta t = 0)
    (f : ThresholdHilbert) (hf : f ∈ normalizedResidueClosure) :
    ‖hilbertOne - f‖ ^ 2 =
      2 * (c / s + d / t).re -
        (‖c‖ ^ 2 / (2 * s.re - 1) + ‖d‖ ^ 2 / (2 * t.re - 1) +
          2 * ((c * starRingEnd ℂ d) / (s + starRingEnd ℂ t - 1)).re) +
      ∫ x in Ioi (1 : ℝ),
        ‖mellinWeightedStep (hilbertOne - f) x -
          starRingEnd ℂ (mellinTwoKernel s t c d x)‖ ^ 2 := by
  have hms := paretoMellin_normalizedResidue_error_identity s hs hs1 hzs f hf
  have hmt := paretoMellin_normalizedResidue_error_identity t ht ht1 hzt f hf
  have he := mellinTwoKernel_remainder_energy (hilbertOne - f) s t c d hs ht
  rw [mellinTwoKernel_energy s t c d hs ht, hms, hmt, mul_one_div, mul_one_div] at he
  linarith

/-- Dropping only the nonnegative remainder gives a two-zero variational bound. -/
theorem normalizedResidue_error_twoZero_lower_bound
    (s t c d : ℂ) (hs : (1 / 2 : ℝ) < s.re) (ht : (1 / 2 : ℝ) < t.re)
    (hs1 : s ≠ 1) (ht1 : t ≠ 1)
    (hzs : riemannZeta s = 0) (hzt : riemannZeta t = 0)
    (f : ThresholdHilbert) (hf : f ∈ normalizedResidueClosure) :
    2 * (c / s + d / t).re -
      (‖c‖ ^ 2 / (2 * s.re - 1) + ‖d‖ ^ 2 / (2 * t.re - 1) +
        2 * ((c * starRingEnd ℂ d) / (s + starRingEnd ℂ t - 1)).re) ≤
      ‖hilbertOne - f‖ ^ 2 := by
  rw [normalizedResidue_error_twoZero_identity s t c d hs ht hs1 ht1 hzs hzt f hf]
  exact le_add_of_nonneg_right (integral_nonneg (fun _ => sq_nonneg _))

end RiemannResearch.RH.Pareto

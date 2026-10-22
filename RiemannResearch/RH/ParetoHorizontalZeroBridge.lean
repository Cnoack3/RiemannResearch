/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroHorizontalEnergy
import RiemannResearch.RH.ParetoBeurlingMellinObstruction
import RiemannResearch.RH.ResidueProjectionSchur
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Actual Pareto residuals and horizontal zero energy

Source: the user's paper-first continuation, 11 October 2026. The Mellin
necessity argument is the classical Nyman--Beurling argument. This module
assembles existing actual Bochner-integral atom signatures and actual zeta
reflection and zero summability; the aggregate comparison is independently
developed algebra. No RH hypothesis or desired residual estimate is assumed.

The exact finite-candidate Mellin identity retains all signed coefficients.
The aggregate theorem applies to the physical normalized-residue closure.
The sibling module `ActualZeroReciprocalConstant.lean` evaluates the explicit
constant using the actual contour zero-sum theorem and regularized xi at one.
The theorem in this module uses the actual convergent ordinate reciprocal-square
sum.
-/

noncomputable section

open Complex Zeta23 Filter
open scoped BigOperators Topology ComplexConjugate

namespace RiemannResearch.RH.ParetoHorizontalZeroBridge

open RiemannResearch.RH.Pareto
open RiemannResearch.RH.ParetoAtomMellinSignature
open RiemannResearch.RH.ParetoBeurlingMellinObstruction
open RiemannResearch.Analysis.ActualZeroHorizontalEnergy

/-- Legal integer conductors, without a coefficient or approximation premise. -/
abbrev LegalConductor := {d : ℕ // 2 ≤ d}

/-- A literal finite signed candidate in the physical Pareto Hilbert space. -/
def finiteResidueCandidate (D : Finset LegalConductor) (c : LegalConductor → ℝ) :
    ThresholdHilbert :=
  ∑ d ∈ D, c d • normalizedResidueHilbert d.1 (by omega)

theorem finiteResidueCandidate_mem_span
    (D : Finset LegalConductor) (c : LegalConductor → ℝ) :
    finiteResidueCandidate D c ∈ normalizedResidueSpan := by
  unfold finiteResidueCandidate
  apply Submodule.sum_mem
  intro d hd
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨d, rfl⟩

theorem finiteResidueCandidate_mem_closure
    (D : Finset LegalConductor) (c : LegalConductor → ℝ) :
    finiteResidueCandidate D c ∈ normalizedResidueClosure :=
  subset_closure (finiteResidueCandidate_mem_span D c)

/-- The complete finite signed Mellin identity, before any norm estimate. -/
theorem paretoMellin_finiteResidue_error
    (D : Finset LegalConductor) (c : LegalConductor → ℝ)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) :
    paretoMellin (hilbertOne - finiteResidueCandidate D c) s =
      (1 - riemannZeta s * ∑ d ∈ D,
        (c d : ℂ) * ((1 / (d.1 : ℂ)) - (d.1 : ℂ) ^ (-s))) / s := by
  have hF : paretoMellin (finiteResidueCandidate D c) s =
      ∑ d ∈ D, (c d : ℂ) *
        (riemannZeta s / s * ((1 / (d.1 : ℂ)) - (d.1 : ℂ) ^ (-s))) := by
    change paretoMellinContinuous s hs
      (∑ d ∈ D, c d • normalizedResidueHilbert d.1 (by omega)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [map_smul]
    change (c d : ℂ) * paretoMellin
      (normalizedResidueHilbert d.1 (by omega)) s = _
    rw [paretoMellin_normalizedResidue_zeta d.1 (by omega) s (by linarith) hs1]
  have hsum : (∑ d ∈ D, (c d : ℂ) *
      (riemannZeta s / s * ((1 / (d.1 : ℂ)) - (d.1 : ℂ) ^ (-s)))) =
      riemannZeta s / s * (∑ d ∈ D,
        (c d : ℂ) * ((1 / (d.1 : ℂ)) - (d.1 : ℂ) ^ (-s))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  change paretoMellinContinuous s hs
    (hilbertOne - finiteResidueCandidate D c) = _
  rw [map_sub]
  change paretoMellin hilbertOne s - paretoMellin (finiteResidueCandidate D c) s = _
  rw [paretoMellin_one s hs, hF, hsum]
  ring

/-- Right-half zeros supply a physical residual bound without division by a
potentially small norm or any ordinate-height premise. -/
theorem rightZero_displacement_le_pareto_error
    (f : ThresholdHilbert) (hf : f ∈ normalizedResidueClosure)
    (s : ℂ) (hz : IsNontrivialZero s) (hs : (1 / 2 : ℝ) < s.re) :
    2 * (s.re - 1 / 2) ≤ ‖hilbertOne - f‖ ^ 2 * (1 + s.im ^ 2) := by
  have hs1 : s ≠ 1 := by
    intro h
    simpa [h] using hz.2.2
  have hs0 : s ≠ 0 := by
    intro h
    simpa [h] using hz.2.1
  have hnorm : 0 < ‖s‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hs0)
  have hb := normalizedResidue_error_sq_lower_bound_of_zeta_zero
    s hs hs1 hz.1 f hf
  have hb' := (div_le_iff₀ hnorm).mp hb
  have hnorm_le : ‖s‖ ^ 2 ≤ 1 + s.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith [hz.2.1, hz.2.2,
      mul_nonneg hz.2.1.le (sub_nonneg.mpr hz.2.2.le)]
  have hmul := mul_le_mul_of_nonneg_left hnorm_le
    (sq_nonneg ‖hilbertOne - f‖)
  linarith

/-- Reflection is used only to obtain the same evaluation bound for a left
zero. Every zero keeps its own actual multiplicity in the later sum. -/
theorem abs_displacement_le_pareto_error
    (f : ThresholdHilbert) (hf : f ∈ normalizedResidueClosure)
    (ρ : ActualZero) :
    2 * |(ρ : ℂ).re - 1 / 2| ≤
      ‖hilbertOne - f‖ ^ 2 * (1 + (ρ : ℂ).im ^ 2) := by
  rcases lt_trichotomy (1 / 2 : ℝ) (ρ : ℂ).re with hr | he | hl
  · rw [abs_of_pos (sub_pos.mpr hr)]
    exact rightZero_displacement_le_pareto_error f hf (ρ : ℂ) ρ.property hr
  · rw [← he]
    simp only [sub_self, abs_zero, mul_zero]
    positivity
  · have hz := zeta_reflect_zero (ρ : ℂ) ρ.property
    have hright : (1 / 2 : ℝ) < (reflect (ρ : ℂ)).re := by
      simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    have hb := rightZero_displacement_le_pareto_error f hf
      (reflect (ρ : ℂ)) hz hright
    simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re,
      Complex.sub_im, Complex.one_im, Complex.conj_im, zero_sub, neg_neg] at hb
    rw [abs_of_neg (sub_neg.mpr hl)]
    linarith

/-- The ordinate weight required by the paper bridge, with actual analytic
multiplicity and all nontrivial zeros. -/
def ordinateInverseSquareTerm (ρ : ActualZero) : ℝ :=
  (zeroMult (ρ : ℂ) : ℝ) / (1 + (ρ : ℂ).im ^ 2)

theorem ordinateInverseSquareTerm_nonneg (ρ : ActualZero) :
    0 ≤ ordinateInverseSquareTerm ρ := by
  unfold ordinateInverseSquareTerm
  positivity

/-- The existing unconditional gammaOf sum controls the ordinate-only sum. -/
theorem ordinateInverseSquareTerm_le_gammaOf (ρ : ActualZero) :
    ordinateInverseSquareTerm ρ ≤ (5 / 4 : ℝ) *
      ((zeroMult (ρ : ℂ) : ℝ) / (1 + normSq (gammaOf (ρ : ℂ)))) := by
  let d : ℝ := (ρ : ℂ).re - 1 / 2
  let B : ℝ := 1 + (ρ : ℂ).im ^ 2
  let M : ℝ := (zeroMult (ρ : ℂ) : ℝ)
  have hstrip : IsNontrivialZero (ρ : ℂ) := ρ.property
  have hd : d ^ 2 ≤ 1 / 4 := by
    dsimp only [d]
    nlinarith [hstrip.2.1, hstrip.2.2,
      mul_nonneg hstrip.2.1.le (sub_nonneg.mpr hstrip.2.2.le)]
  have hB : 1 ≤ B := by
    dsimp only [B]
    nlinarith [sq_nonneg (ρ : ℂ).im]
  have hBp : 0 < B := by linarith
  have hnorm : 1 + normSq (gammaOf (ρ : ℂ)) = B + d ^ 2 := by
    dsimp only [B, d]
    rw [normSq_apply, Zeta23.WeilEF.gammaOf_re, Zeta23.WeilEF.gammaOf_im]
    ring
  have hscale : B + d ^ 2 ≤ (5 / 4 : ℝ) * B := by linarith
  have hM : 0 ≤ M := Nat.cast_nonneg _
  change M / B ≤ (5 / 4 : ℝ) *
    (M / (1 + normSq (gammaOf (ρ : ℂ))))
  rw [hnorm, ← mul_div_assoc]
  apply (div_le_div_iff₀ hBp (by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hscale hM]

theorem ordinateInverseSquareTerm_summable : Summable ordinateInverseSquareTerm := by
  have hs := (Zeta23.WeilEF.zero_sum_inv_sq zetaSeam).mul_left (5 / 4 : ℝ)
  exact Summable.of_nonneg_of_le ordinateInverseSquareTerm_nonneg
    ordinateInverseSquareTerm_le_gammaOf hs

def ordinateInverseSquareSum : ℝ := ∑' ρ : ActualZero, ordinateInverseSquareTerm ρ

theorem ordinateInverseSquareSum_nonneg : 0 ≤ ordinateInverseSquareSum :=
  tsum_nonneg ordinateInverseSquareTerm_nonneg

theorem ordinateInverseSquareSum_le_gammaOf :
    ordinateInverseSquareSum ≤ (5 / 4 : ℝ) *
      ∑' ρ : ActualZero, (zeroMult (ρ : ℂ) : ℝ) /
        (1 + normSq (gammaOf (ρ : ℂ))) := by
  have hs := Zeta23.WeilEF.zero_sum_inv_sq zetaSeam
  have h := ordinateInverseSquareTerm_summable.tsum_le_tsum
    ordinateInverseSquareTerm_le_gammaOf (hs.mul_left (5 / 4 : ℝ))
  simpa only [ordinateInverseSquareSum, tsum_mul_left] using h

/-- Pointwise detecting comparison, retaining the actual physical residual. -/
theorem horizontalTerm_le_pareto_error
    (f : ThresholdHilbert) (hf : f ∈ normalizedResidueClosure) (ρ : ActualZero) :
    horizontalTerm ρ ≤ (‖hilbertOne - f‖ ^ 2 / 4) * ordinateInverseSquareTerm ρ := by
  let d : ℝ := (ρ : ℂ).re - 1 / 2
  let B : ℝ := 1 + (ρ : ℂ).im ^ 2
  let M : ℝ := (zeroMult (ρ : ℂ) : ℝ)
  let e : ℝ := ‖hilbertOne - f‖ ^ 2
  have hstrip : IsNontrivialZero (ρ : ℂ) := ρ.property
  have hd : |d| ≤ 1 / 2 := by
    rw [abs_le]
    dsimp only [d]
    constructor <;> linarith [hstrip.2.1, hstrip.2.2]
  have hBp : 0 < B := by dsimp only [B]; positivity
  have he : 0 ≤ e := sq_nonneg _
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hb : 2 * |d| ≤ e * B := abs_displacement_le_pareto_error f hf ρ
  have hmul1 := mul_le_mul_of_nonneg_right hb (abs_nonneg d)
  have hmul2 := mul_le_mul_of_nonneg_left hd (mul_nonneg he hBp.le)
  have hmain : d ^ 2 ≤ (e / 4) * B := by
    nlinarith [sq_abs d]
  change M * d ^ 2 / B ^ 2 ≤ (e / 4) * (M / B)
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity) hBp).mpr
  calc
    M * d ^ 2 * B = (M * B) * d ^ 2 := by ring
    _ ≤ (M * B) * ((e / 4) * B) :=
      mul_le_mul_of_nonneg_left hmain (mul_nonneg hM hBp.le)
    _ = ((e / 4) * M) * B ^ 2 := by ring

/-- The paper's all-zero energy bound, with no RH premise and no assumed
Mellin bridge: all providers are actual project theorems. -/
theorem horizontalFourthEnergy_le_pareto_error
    (f : ThresholdHilbert) (hf : f ∈ normalizedResidueClosure) :
    horizontalFourthEnergy ≤ (‖hilbertOne - f‖ ^ 2 / 4) * ordinateInverseSquareSum := by
  have h := horizontalTerm_summable.tsum_le_tsum
    (horizontalTerm_le_pareto_error f hf)
    (ordinateInverseSquareTerm_summable.mul_left (‖hilbertOne - f‖ ^ 2 / 4))
  simpa only [horizontalFourthEnergy, ordinateInverseSquareSum, tsum_mul_left] using h

/-- A bound stated entirely using the previously available unconditional
gammaOf reciprocal-square sum. -/
theorem horizontalFourthEnergy_le_pareto_error_gammaOf
    (f : ThresholdHilbert) (hf : f ∈ normalizedResidueClosure) :
    horizontalFourthEnergy ≤ (5 / 16 : ℝ) * ‖hilbertOne - f‖ ^ 2 *
      ∑' ρ : ActualZero, (zeroMult (ρ : ℂ) : ℝ) /
        (1 + normSq (gammaOf (ρ : ℂ))) := by
  have h := mul_le_mul_of_nonneg_left ordinateInverseSquareSum_le_gammaOf
    (by positivity : 0 ≤ ‖hilbertOne - f‖ ^ 2 / 4)
  have hb := horizontalFourthEnergy_le_pareto_error f hf
  nlinarith only [hb, h]

/-- The exact finite signed candidate is automatically in the domain of the
detecting horizontal-energy bound. -/
theorem horizontalFourthEnergy_le_finiteResidue_error
    (D : Finset LegalConductor) (c : LegalConductor → ℝ) :
    horizontalFourthEnergy ≤ (‖hilbertOne - finiteResidueCandidate D c‖ ^ 2 / 4) *
      ordinateInverseSquareSum :=
  horizontalFourthEnergy_le_pareto_error _ (finiteResidueCandidate_mem_closure D c)

/-- Any independent actual ordinate-sum bound specializes the bridge. The
sibling reciprocal-constant module supplies the explicit paper constant. -/
theorem horizontalFourthEnergy_le_of_ordinate_sum_le
    (f : ThresholdHilbert) (hf : f ∈ normalizedResidueClosure)
    (C : ℝ) (hC : ordinateInverseSquareSum ≤ C) :
    horizontalFourthEnergy ≤ (C / 4) * ‖hilbertOne - f‖ ^ 2 := by
  have h := mul_le_mul_of_nonneg_left hC
    (by positivity : 0 ≤ ‖hilbertOne - f‖ ^ 2 / 4)
  have hb := horizontalFourthEnergy_le_pareto_error f hf
  nlinarith only [hb, h]

/-- The actual inverse-Gram orthogonal optimizer is a finite legal synthesis.
This uses the repository's canonical coefficients, not a replacement vector. -/
theorem canonicalProjection_mem_normalizedResidueSpan (n : ℕ) :
    CoefficientStabilization.projection n ∈ normalizedResidueSpan := by
  rw [CoefficientStabilization.GramMobiusCorrection.projection_eq_inverseGram_synthesis]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  change normalizedResidueHilbert (i.val + 2) (by omega) ∈ normalizedResidueSpan
  exact Submodule.subset_span ⟨⟨i.val + 2, by omega⟩, rfl⟩

theorem canonicalProjection_mem_normalizedResidueClosure (n : ℕ) :
    CoefficientStabilization.projection n ∈ normalizedResidueClosure :=
  subset_closure (canonicalProjection_mem_normalizedResidueSpan n)

/-- Direct detecting bound for the actual full-Pareto orthogonal residual.
Stage n uses all integer conductors 2 through n+1. -/
theorem horizontalFourthEnergy_le_canonicalProjection_error (n : ℕ) :
    horizontalFourthEnergy ≤
      (‖hilbertOne - CoefficientStabilization.projection n‖ ^ 2 / 4) *
        ordinateInverseSquareSum :=
  horizontalFourthEnergy_le_pareto_error _
    (canonicalProjection_mem_normalizedResidueClosure n)

/-- The complete inverse-Gram captured energy appears with its exact deficit. -/
theorem horizontalFourthEnergy_le_canonicalCaptured_deficit (n : ℕ) :
    horizontalFourthEnergy ≤
      ((1 - CoefficientStabilization.ProjectionSchur.captured n) / 4) *
        ordinateInverseSquareSum := by
  have h := horizontalFourthEnergy_le_canonicalProjection_error n
  rw [CoefficientStabilization.ProjectionSchur.error_eq_one_sub_captured] at h
  exact h

end RiemannResearch.RH.ParetoHorizontalZeroBridge

/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteClassDirichlet
import RiemannResearch.Analysis.FiniteSignedVariance
import RiemannResearch.Analysis.FiniteWeightedTailCharge
import RiemannResearch.NumberTheory.DivisorIncidence
import RiemannResearch.RH.QRationalTailDirichlet
import RiemannResearch.RH.QRationalGcdTail
import RiemannResearch.RH.QRationalMinimumLimit
import RiemannResearch.RH.QRationalCoprimeLegality
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Explicit path bounds for actual rational residual tails

Source: direct finite Cauchy--Schwarz and the established gcd-class means;
user-directed investigation, 20 October 2026. The path resistance retains
every edge between the two sites. The resulting negative-mass bound is
unconditional but does not supply a fixed-factor absorption estimate.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QRationalCoprimeTail
open RiemannResearch.Analysis.FiniteClassDirichlet
open RiemannResearch.Analysis.FiniteWeightedTailCharge
open RiemannResearch.Analysis.FiniteIncidenceTailCharge
open RiemannResearch.NumberTheory.DivisorIncidence

def tailCut (k a : ℕ) : ℝ := if k ≤ a then 1 else 0

/-- This equals the sum of w(a) on min(i,j) <= a < max(i,j). -/
def pathResistance (L i j : ℕ) : ℝ :=
  ∑ a ∈ (sites L).erase L, weight L a * (tailCut i a - tailCut j a) ^ 2

def classPathConstant (L : ℕ) (C : Finset ℕ) : ℝ :=
  (∑ i ∈ C, ∑ j ∈ C, pathResistance L i j) / 2

theorem residualTail_sub_eq_edge_sum (L : ℕ) (hL : 0 < L)
    (f : ℕ → ℝ) (i j : ℕ) (hi : i ∈ sites L) (hj : j ∈ sites L) :
    residualTail L f i - residualTail L f j =
      ∑ a ∈ (sites L).erase L,
        weight L a * (1 - f a) * (tailCut i a - tailCut j a) := by
  have he : residualTail L f i - residualTail L f j =
      ∑ a ∈ sites L, weight L a * (1 - f a) * (tailCut i a - tailCut j a) := by
    unfold residualTail tail
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    unfold tailCut
    split_ifs <;> ring
  rw [he]
  have hh := Finset.sum_erase_add (s := sites L)
    (f := fun a => weight L a * (1 - f a) * (tailCut i a - tailCut j a))
    (Finset.mem_Icc.mpr ⟨hL, le_rfl⟩)
  simpa only [tailCut, if_pos (Finset.mem_Icc.mp hi).2,
    if_pos (Finset.mem_Icc.mp hj).2, sub_self, mul_zero, add_zero] using hh.symm

theorem residual_edge_energy (L : ℕ) (hL : 0 < L)
    (f : ℕ → ℝ) (hfL : f L = 0) :
    (∑ a ∈ (sites L).erase L, weight L a * (1 - f a) ^ 2) =
      rationalError L f - commonAverage L := by
  have he := Finset.sum_erase_add (s := sites L)
    (f := fun a => weight L a * (1 - f a) ^ 2)
    (Finset.mem_Icc.mpr ⟨hL, le_rfl⟩)
  rw [hfL, sub_zero, one_pow, mul_one, weight_endpoint L hL] at he
  change (∑ a ∈ (sites L).erase L, weight L a * (1 - f a) ^ 2) +
    commonAverage L = rationalError L f at he
  linarith

/-- Endpoint-removed Cauchy--Schwarz, for every pair of actual sites. -/
theorem residualTail_pairwise_sq_le (L : ℕ) (hL : 0 < L)
    (f : ℕ → ℝ) (hfL : f L = 0)
    (i j : ℕ) (hi : i ∈ sites L) (hj : j ∈ sites L) :
    (residualTail L f i - residualTail L f j) ^ 2 ≤
      pathResistance L i j * (rationalError L f - commonAverage L) := by
  rw [residualTail_sub_eq_edge_sum L hL f i j hi hj]
  have hc := weighted_cauchy ((sites L).erase L) (weight L)
    (fun a => 1 - f a) (fun a => tailCut i a - tailCut j a)
    (fun a _ => weight_nonneg L a)
  rw [residual_edge_energy L hL f hfL] at hc
  simpa only [pathResistance, mul_comm] using hc

/-- Exact class variance expressed by all pairwise tail differences. -/
theorem gcd_class_pairwise_identity (L : ℕ) (hL : 0 < L)
    (e : ℕ) (he : e ∈ L.divisors) :
    (∑ i ∈ gcdClass L e, ∑ j ∈ gcdClass L e,
      (residualTail L (divisorFit L (rationalCoefficients L)) i -
        residualTail L (divisorFit L (rationalCoefficients L)) j) ^ 2) =
      2 * ((gcdClass L e).card : ℝ) *
        ∑ i ∈ gcdClass L e,
          (residualTail L (divisorFit L (rationalCoefficients L)) i - commonAverage L) ^ 2 := by
  exact centered_pairwise_identity _ _ _
    (gcd_class_centered_zero L hL _
      (divisor_synthesis_endpoint L _ (rationalCoefficients L) (fun _ => rfl))
      (rationalCoefficients_normal L) e he)

/-- All gcd classes of the selected actual minimizer obey the path bound. -/
theorem rational_gcd_class_poincare (L : ℕ) (hL : 0 < L)
    (e : ℕ) (he : e ∈ L.divisors) :
    ((gcdClass L e).card : ℝ) *
        (∑ i ∈ gcdClass L e,
          (residualTail L (divisorFit L (rationalCoefficients L)) i - commonAverage L) ^ 2) ≤
      classPathConstant L (gcdClass L e) * (rationalMinimum L - commonAverage L) := by
  have hp := class_poincare (gcdClass L e)
    (residualTail L (divisorFit L (rationalCoefficients L))) (commonAverage L)
    (rationalMinimum L - commonAverage L) (pathResistance L)
    (gcd_class_centered_zero L hL _
      (divisor_synthesis_endpoint L _ (rationalCoefficients L) (fun _ => rfl))
      (rationalCoefficients_normal L) e he)
    (fun i hi j hj => residualTail_pairwise_sq_le L hL _
      (divisor_synthesis_endpoint L _ (rationalCoefficients L) (fun _ => rfl)) i j
      (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1)
  unfold classPathConstant
  linarith

/-- An unconditional negative-tail estimate with its explicit arithmetic constant. -/
theorem rational_negative_mass_path_budget (L : ℕ) (hL : 0 < L) :
    4 * coprimeNegativeMass L (divisorFit L (rationalCoefficients L)) *
        (coprimeNegativeMass L (divisorFit L (rationalCoefficients L)) +
          (Nat.totient L : ℝ) * commonAverage L) ≤
      classPathConstant L (coprimeSites L) * (rationalMinimum L - commonAverage L) := by
  have hp := rational_gcd_class_poincare L hL 1
    (Nat.mem_divisors.mpr ⟨one_dvd L, ne_of_gt hL⟩)
  have hc : (coprimeSites L).card = Nat.totient L := coprime_Icc_card L
  rw [gcd_class_one, hc] at hp
  exact (coprime_negative_mass_quadratic_budget L hL _
    (rationalCoefficients_normal L)).trans hp

end RiemannResearch.RH.QRationalCoprimeTail

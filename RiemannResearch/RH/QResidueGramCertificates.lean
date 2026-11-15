/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QResidueMoments
import RiemannResearch.RH.QPeriodicCertifiedWeights
import RiemannResearch.Analysis.RationalIntervalDecimal
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Complete-Q residue Gram entries with computable rational enclosures

Source: the reciprocal-head review's complete periodic Gram computation.
The existing actual trigamma moment theorem is rewritten into raw progression
weights, then enclosed by the proved rational prefix-and-tail certificates.
The common factor `zetaTwo` is explicit and no physical tail is omitted.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QResidueGramCertificates
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative
open RiemannResearch RatInterval

def rationalResidue (d a : ℕ) : ℚ := ((a % d : ℕ) : ℚ) / (d : ℚ)

theorem rationalResidue_cast (d a : ℕ) :
    (rationalResidue d a : ℝ) = residueFraction d a := by
  simp only [rationalResidue, residueFraction, Rat.cast_div, Rat.cast_natCast]

/-- The raw Q Gram matrix in the numerical review is the actual complete
Q Gram matrix times the normalization, exactly. -/
theorem rawGram_pairing_eq (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    zetaTwo * inner ℝ (qResidue d) (qResidue e) =
      ∑ r : Fin (Nat.lcm d e),
        rawResidueSquareWeight (Nat.lcm d e : ℝ) (((r.val + 1 : ℕ) : ℝ)) *
          (residueFraction d (r.val + 1) * residueFraction e (r.val + 1)) := by
  rw [qResidue_gram_eq_trigamma d e hd he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  have hL : (0 : ℝ) < (Nat.lcm d e : ℝ) := by
    exact_mod_cast Nat.lcm_pos hd he
  rw [rawResidueSquareWeight_eq_normalized,
    residueSquareWeight_eq_trigamma hL (by positivity)]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

theorem rawMean_pairing_eq (d : ℕ) (hd : 0 < d) :
    zetaTwo * inner ℝ qOne (qResidue d) =
      ∑ r : Fin d,
        rawResidueSquareWeight (d : ℝ) (((r.val + 1 : ℕ) : ℝ)) *
          residueFraction d (r.val + 1) := by
  rw [qResidue_mean_eq_trigamma d hd, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  have hdr : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rw [rawResidueSquareWeight_eq_normalized,
    residueSquareWeight_eq_trigamma hdr (by positivity)]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

def rawGramInterval (d e K digits : ℕ) : RatInterval :=
  sum Finset.univ (fun r : Fin (Nat.lcm d e) =>
    mul (decimalHull digits (rawResidueSquareInterval (Nat.lcm d e) (r.val + 1) K))
      (point (rationalResidue d (r.val + 1) * rationalResidue e (r.val + 1))))

theorem rawGramInterval_contains (d e K digits : ℕ)
    (hd : 0 < d) (he : 0 < e) (hK : 1 ≤ K) :
    (rawGramInterval d e K digits).Contains
      (zetaTwo * inner ℝ (qResidue d) (qResidue e)) := by
  rw [rawGram_pairing_eq d e hd he]
  apply contains_sum
  intro r _
  apply contains_mul
  · apply contains_decimalHull
    simpa only [Rat.cast_natCast, Nat.cast_add, Nat.cast_one, Rat.cast_add, Rat.cast_one] using
      rawResidueSquareInterval_contains (Nat.lcm d e : ℚ) ((r.val + 1 : ℕ) : ℚ) K
        (by exact_mod_cast Nat.lcm_pos hd he) (by positivity) hK
  · simpa only [Rat.cast_mul, rationalResidue_cast] using
      contains_point (rationalResidue d (r.val + 1) * rationalResidue e (r.val + 1))

def rawMeanInterval (d K digits : ℕ) : RatInterval :=
  sum Finset.univ (fun r : Fin d =>
    mul (decimalHull digits (rawResidueSquareInterval d (r.val + 1) K))
      (point (rationalResidue d (r.val + 1))))

theorem rawMeanInterval_contains (d K digits : ℕ) (hd : 0 < d) (hK : 1 ≤ K) :
    (rawMeanInterval d K digits).Contains (zetaTwo * inner ℝ qOne (qResidue d)) := by
  rw [rawMean_pairing_eq d hd]
  apply contains_sum
  intro r _
  apply contains_mul
  · apply contains_decimalHull
    simpa only [Rat.cast_natCast, Nat.cast_add, Nat.cast_one, Rat.cast_add, Rat.cast_one] using
      rawResidueSquareInterval_contains (d : ℚ) ((r.val + 1 : ℕ) : ℚ) K
        (by exact_mod_cast hd) (by positivity) hK
  · simpa only [rationalResidue_cast] using contains_point (rationalResidue d (r.val + 1))

end RiemannResearch.RH.QResidueGramCertificates

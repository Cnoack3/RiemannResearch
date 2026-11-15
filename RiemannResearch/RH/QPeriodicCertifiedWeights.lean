/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.InverseSquareTailCertificates
import RiemannResearch.Analysis.ArithmeticProgressionSquareSeries
import RiemannResearch.Analysis.RationalInterval
import RiemannResearch.RH.ZetaTwoPolygammaResidues
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rational intervals for actual complete periodic Q weights

Source: user-provided canonical and reciprocal-head review computations,
7 November 2026. Finite rational prefixes and exact telescoping remainder
identities supply every enclosure; no JSON entry or floating value is assumed.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ZetaTwoProbability
open RiemannResearch.Analysis.ArithmeticProgressionSquareTail
open RiemannResearch.Analysis.InverseSquareTailCertificates
open RiemannResearch RatInterval

def rawResidueSquareWeight (L a : ℝ) : ℝ :=
  ∑' k : ℕ, 1 / (a + (k : ℝ) * L) ^ 2

/-- The raw weight used by both numerical scripts is the actual normalized
physical Q residue mass multiplied by the complete zeta normalization. -/
theorem rawResidueSquareWeight_eq_normalized (L a : ℝ) :
    rawResidueSquareWeight L a = zetaTwo * residuePowerWeight 0 L a := by
  unfold rawResidueSquareWeight residuePowerWeight
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  simp only [Nat.zero_add]
  symm
  calc
    zetaTwo * (1 / (zetaTwo * (a + (k : ℝ) * L) ^ 2)) =
        (zetaTwo * zetaTwo⁻¹) * ((a + (k : ℝ) * L) ^ 2)⁻¹ := by
      simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
      ring
    _ = _ := by rw [mul_inv_cancel₀ (ne_of_gt zetaTwo_pos), one_mul, one_div]

theorem rawResidueSquareWeight_prefix_exact (L a : ℝ)
    (hL : 0 < L) (ha : 0 < a) (K : ℕ) :
    rawResidueSquareWeight L a =
      (∑ k ∈ Finset.range K, 1 / (a + (k : ℝ) * L) ^ 2) +
        rawResidueSquareWeight L (a + (K : ℝ) * L) := by
  have h := (full_progression_summable a L ha hL).sum_add_tsum_nat_add K
  simpa only [rawResidueSquareWeight, Nat.cast_add, add_mul,
    add_assoc, add_left_comm, add_comm] using h.symm

/-- A completely computable rational interval, including all omitted physical
integers. The same field-polymorphic tail functions are evaluated in Q and R. -/
def rawResidueSquareInterval (L a : ℚ) (K : ℕ) : RatInterval :=
  let P : ℚ := ∑ k ∈ Finset.range K, 1 / (a + (k : ℚ) * L) ^ 2
  ⟨P + lowerTen (a / L + (K : ℚ)) / L ^ 2,
   P + upperNine (a / L + (K : ℚ)) / L ^ 2⟩

theorem rawResidueSquareInterval_contains (L a : ℚ) (K : ℕ)
    (hL : 0 < L) (ha : 0 < a) (hK : 1 ≤ K) :
    (rawResidueSquareInterval L a K).Contains
      (rawResidueSquareWeight (L : ℝ) (a : ℝ)) := by
  have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have har : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hx : (1 : ℝ) ≤ (a : ℝ) / (L : ℝ) + (K : ℝ) := by
    have := div_pos har hLr
    linarith
  have hb := scaled_complete_tail_ten_bounds
    ((a : ℝ) / (L : ℝ) + (K : ℝ)) (L : ℝ) hx hLr
  have he : rawResidueSquareWeight (L : ℝ) ((a : ℝ) + (K : ℝ) * (L : ℝ)) =
      ∑' k : ℕ, 1 / ((L : ℝ) * ((a : ℝ) / (L : ℝ) + (K : ℝ)) +
        (k : ℝ) * (L : ℝ)) ^ 2 := by
    apply tsum_congr
    intro k
    congr 2
    field_simp [ne_of_gt hLr]
    <;> ring
  rw [← he] at hb
  have hprefix := rawResidueSquareWeight_prefix_exact (L : ℝ) (a : ℝ) hLr har K
  unfold RatInterval.Contains rawResidueSquareInterval
  dsimp only
  simp only [lowerTen, upperNine] at hb ⊢
  push_cast
  constructor <;> linarith [hb.1, hb.2]

theorem rawResidueSquareWeight_one_one : rawResidueSquareWeight 1 1 = zetaTwo := by
  unfold rawResidueSquareWeight zetaTwo
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => 1 / (n : ℝ) ^ 2)]
  apply tsum_congr
  intro k
  push_cast
  ring

/-- The normalization itself is enclosed by the same certified progression. -/
theorem zetaTwoInterval_contains (K : ℕ) (hK : 1 ≤ K) :
    (rawResidueSquareInterval 1 1 K).Contains zetaTwo := by
  simpa only [Rat.cast_one, rawResidueSquareWeight_one_one] using
    rawResidueSquareInterval_contains 1 1 K (by norm_num) (by norm_num) hK

def residueSquareInterval (L a : ℚ) (K : ℕ) : RatInterval :=
  RatInterval.div (rawResidueSquareInterval L a K) (rawResidueSquareInterval 1 1 K)

/-- The only extra premise is a finite rational endpoint positivity check. -/
theorem residueSquareInterval_contains (L a : ℚ) (K : ℕ)
    (hL : 0 < L) (ha : 0 < a) (hK : 1 ≤ K)
    (hz : 0 < (rawResidueSquareInterval 1 1 K).lo) :
    (residueSquareInterval L a K).Contains (residuePowerWeight 0 (L : ℝ) (a : ℝ)) := by
  have h := RatInterval.contains_div_pos
    (rawResidueSquareInterval_contains L a K hL ha hK)
    (zetaTwoInterval_contains K hK) hz
  rw [rawResidueSquareWeight_eq_normalized] at h
  have he : zetaTwo * residuePowerWeight 0 (L : ℝ) (a : ℝ) / zetaTwo =
      residuePowerWeight 0 (L : ℝ) (a : ℝ) := by
    field_simp [ne_of_gt zetaTwo_pos]
  simpa only [residueSquareInterval, he] using h

/-- Literal finite rational positivity check for the certificate normalizer. -/
theorem rawResidueSquareInterval_thirty_two_normalizer_pos :
    0 < (rawResidueSquareInterval 1 1 32).lo := by
  norm_num [rawResidueSquareInterval, lowerTen, upperNine, Finset.sum_range_succ]

/-- The exact normalization enclosure printed in the reciprocal-head review,
now attached to the actual complete infinite zeta series. -/
theorem zetaTwo_reciprocal_review_interval :
    (1.6449340668482264364724151666391172481846 : ℝ) ≤ zetaTwo ∧
      zetaTwo ≤ (1.6449340668482264364724151666527880792905 : ℝ) := by
  have h := zetaTwoInterval_contains 32 (by norm_num)
  norm_num [RatInterval.Contains, rawResidueSquareInterval,
    lowerTen, upperNine, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

end RiemannResearch.RH.ZetaTwoProbability

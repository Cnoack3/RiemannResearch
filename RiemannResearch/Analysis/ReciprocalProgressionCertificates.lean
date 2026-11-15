/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.RationalInterval
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import RiemannResearch.Analysis.ParetoProgressionCertificates
import RiemannResearch.RH.QPeriodicCertifiedWeights

/-!
# Exact signed reciprocal-square progression weights

The complete reciprocal Gram weight in the archived computation is Q(a,L) +
Q(a+1,L) - 2 P(a,L). The identity below connects that signed expression to
its actual complete positive series. Both inverse-square terms and the Pareto
cross term are retained.
-/

noncomputable section
namespace RiemannResearch.Analysis.ParetoProgressionCertificates
open ArithmeticProgressionSquareTail

/-- Complete progression weight for the square of the shifted reciprocal
multiplier, before the Q zeta normalization. -/
def reciprocalProgression (a L : ℝ) : ℝ :=
  ∑' n : ℕ, 1 / ((a + L * (n : ℝ))^2 * (a + L * (n : ℝ) + 1)^2)

private theorem reciprocal_kernel_signed (a L : ℝ) (ha : 0 < a) (hL : 0 < L)
    (n : ℕ) :
    1 / ((a + L * (n : ℝ))^2 * (a + L * (n : ℝ) + 1)^2) =
      1/(a+L*(n:ℝ))^2 + 1/((a+1)+L*(n:ℝ))^2 -
        2*(1/((a+L*(n:ℝ))*(a+L*(n:ℝ)+1))) := by
  have hx : 0 < a + L * (n : ℝ) := by positivity
  have hy : 0 < a + L * (n : ℝ) + 1 := by positivity
  have hz : 0 < a + 1 + L * (n : ℝ) := by positivity
  field_simp
  <;> ring

/-- The reciprocal progression converges as the exact signed combination of
three convergent complete progressions. -/
theorem reciprocalProgression_summable (a L : ℝ) (ha : 0 < a) (hL : 0 < L) :
    Summable (fun n : ℕ => 1 / ((a + L * (n : ℝ))^2 *
      (a + L * (n : ℝ) + 1)^2)) := by
  have hq : Summable (fun n : ℕ => 1/(a+L*(n:ℝ))^2) := by
    simpa only [mul_comm] using full_progression_summable a L ha hL
  have hq' : Summable (fun n : ℕ => 1/((a+1)+L*(n:ℝ))^2) := by
    simpa only [mul_comm] using full_progression_summable (a+1) L (by positivity) hL
  exact ((hq.add hq').sub ((paretoProgression_summable a L ha hL).mul_left 2)).congr
    (fun n => (reciprocal_kernel_signed a L ha hL n).symm)

/-- Exact complete signed weight identity underlying the reciprocal Gram
matrix. No finite prefix or omitted-term assumption occurs in this identity. -/
theorem reciprocalProgression_eq_signed (a L : ℝ) (ha : 0 < a) (hL : 0 < L) :
    reciprocalProgression a L =
      squareProgression a L 0 + squareProgression (a+1) L 0 -
        2*paretoProgression a L := by
  have hq : Summable (fun n : ℕ => 1/(a+L*(n:ℝ))^2) := by
    simpa only [mul_comm] using full_progression_summable a L ha hL
  have hq' : Summable (fun n : ℕ => 1/((a+1)+L*(n:ℝ))^2) := by
    simpa only [mul_comm] using full_progression_summable (a+1) L (by positivity) hL
  unfold reciprocalProgression squareProgression paretoProgression
  simp only [add_zero]
  calc
    _ = ∑' n : ℕ, (1/(a+L*(n:ℝ))^2 + 1/((a+1)+L*(n:ℝ))^2 -
        2*(1/((a+L*(n:ℝ))*(a+L*(n:ℝ)+1)))) :=
      tsum_congr (reciprocal_kernel_signed a L ha hL)
    _ = _ := by
      rw [(hq.add hq').tsum_sub ((paretoProgression_summable a L ha hL).mul_left 2),
        hq.tsum_add hq', tsum_mul_left]

theorem reciprocalProgression_nonneg (a L : ℝ) : 0 ≤ reciprocalProgression a L :=
  tsum_nonneg (fun _ => by positivity)

/-- The inverse-square term is the same complete raw Q residue weight used by
the rational certificate infrastructure. -/
theorem squareProgression_eq_rawResidueSquareWeight (a L : ℝ) :
    squareProgression a L 0 =
      RiemannResearch.RH.ZetaTwoProbability.rawResidueSquareWeight L a := by
  unfold squareProgression RiemannResearch.RH.ZetaTwoProbability.rawResidueSquareWeight
  simp only [add_zero, mul_comm]

/-- The archived signed J weight is an actual positive infinite series. -/
theorem reciprocalProgression_eq_raw_signed (a L : ℝ) (ha : 0 < a) (hL : 0 < L) :
    reciprocalProgression a L =
      RiemannResearch.RH.ZetaTwoProbability.rawResidueSquareWeight L a +
      RiemannResearch.RH.ZetaTwoProbability.rawResidueSquareWeight L (a+1) -
        2*paretoProgression a L := by
  rw [reciprocalProgression_eq_signed a L ha hL,
    squareProgression_eq_rawResidueSquareWeight,
    squareProgression_eq_rawResidueSquareWeight]


open RiemannResearch RatInterval RiemannResearch.RH.ZetaTwoProbability

/-- A rational enclosure for the actual reciprocal Gram progression weight.
Its subtraction retains the complete Pareto cross term. -/
def reciprocalProgressionInterval (a L : ℚ) (K : ℕ) : RatInterval :=
  RatInterval.sub
    (RatInterval.add (rawResidueSquareInterval L a K)
      (rawResidueSquareInterval L (a+1) K))
    (RatInterval.mul (RatInterval.point 2) (paretoProgressionInterval a L K))

theorem reciprocalProgressionInterval_contains (a L : ℚ) (K : ℕ)
    (ha : 0 < a) (hL : 0 < L) (hK : 1 ≤ K) :
    (reciprocalProgressionInterval a L K).Contains
      (reciprocalProgression (a : ℝ) (L : ℝ)) := by
  have hq := rawResidueSquareInterval_contains L a K hL ha hK
  have hq' := rawResidueSquareInterval_contains L (a+1) K hL (by positivity) hK
  have hp := paretoProgressionInterval_contains a L K ha hL hK
  have h := RatInterval.contains_sub (RatInterval.contains_add hq hq')
    (RatInterval.contains_mul (RatInterval.contains_point 2) hp)
  rw [reciprocalProgression_eq_raw_signed (a : ℝ) (L : ℝ)
    (by exact_mod_cast ha) (by exact_mod_cast hL)]
  simpa only [reciprocalProgressionInterval, Rat.cast_add, Rat.cast_one,
    Rat.cast_ofNat] using h

end RiemannResearch.Analysis.ParetoProgressionCertificates

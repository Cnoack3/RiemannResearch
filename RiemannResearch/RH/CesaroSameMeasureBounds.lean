/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.CesaroWeightedContraction
import RiemannResearch.RH.QCesaroEnergy
import RiemannResearch.RH.QUniformMixture
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Cesàro averaging in each marginal weighted space

Source: the user's 1 November 2026 P/Q change-of-measure question.
The conditional expectation contraction has different input and output laws.
This module gives bounds when the same marginal law is used on both sides,
and a pulse proving that neither such map is a contraction.
The exact pointwise remainders precede their nonnegative estimates.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.CesaroSameMeasureBounds
open Probability.ConditionalIID Analysis.Cesaro ArithmeticCumulative
open ZetaTwoProbability ZetaTwoHilbert QUniformMixture QCesaroEnergy

theorem p_weight_latent_remainder (n : ℕ) (hn : 0 < n) :
    (3 / 2 : ℝ) * mixtureWeight n - weight n =
      2 * ((n : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
  unfold mixtureWeight weight
  field_simp [hn0, hn1, hn2]
  ring

theorem p_weight_le_latent (n : ℕ) (hn : 0 < n) :
    weight n ≤ (3 / 2 : ℝ) * mixtureWeight n := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (ne_of_gt hn))
  apply sub_nonneg.mp
  rw [p_weight_latent_remainder n hn]
  exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hn1)) (by positivity)

theorem q_weight_latent_remainder (n : ℕ) (hn : 0 < n) :
    (4 / 3 : ℝ) * qMixtureWeight n - positiveQWeight n =
      (((n : ℝ) - 1) * (5 * (n : ℝ) + 3)) /
        (3 * zetaTwo * (n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  unfold qMixtureWeight positiveQWeight
  field_simp [hn0, hn1, ne_of_gt zetaTwo_pos]
  ring

theorem q_weight_le_latent (n : ℕ) (hn : 0 < n) :
    positiveQWeight n ≤ (4 / 3 : ℝ) * qMixtureWeight n := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (ne_of_gt hn))
  have hz := zetaTwo_pos
  apply sub_nonneg.mp
  rw [q_weight_latent_remainder n hn]
  apply div_nonneg
  · exact mul_nonneg (sub_nonneg.mpr hn1) (by positivity)
  · positivity

theorem cesaro_p_square_summable (F : ℕ → ℝ)
    (hF : Summable (fun k : ℕ => weight (k + 1) * F (k + 1) ^ 2)) :
    Summable (fun k : ℕ => weight (k + 1) * cesaro F (k + 1) ^ 2) := by
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (weight_nonneg _) (sq_nonneg _)) _
    ((cesaro_weighted_square_summable F hF).mul_left (3 / 2 : ℝ))
  intro k
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (p_weight_le_latent (k + 1) (Nat.succ_pos k)) (sq_nonneg (cesaro F (k + 1)))

/-- A squared norm bound in the P space itself, with no change of output law. -/
theorem cesaro_p_energy_le (F : ℕ → ℝ)
    (hF : Summable (fun k : ℕ => weight (k + 1) * F (k + 1) ^ 2)) :
    (∑' k : ℕ, weight (k + 1) * cesaro F (k + 1) ^ 2) ≤
      (3 / 2 : ℝ) * ∑' k : ℕ, weight (k + 1) * F (k + 1) ^ 2 := by
  calc
    _ ≤ ∑' k : ℕ, (3 / 2 : ℝ) *
        (mixtureWeight (k + 1) * cesaro F (k + 1) ^ 2) := by
      apply Summable.tsum_le_tsum _ (cesaro_p_square_summable F hF)
        ((cesaro_weighted_square_summable F hF).mul_left (3 / 2 : ℝ))
      intro k
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (p_weight_le_latent (k + 1) (Nat.succ_pos k)) (sq_nonneg (cesaro F (k + 1)))
    _ = (3 / 2 : ℝ) * ∑' k : ℕ,
        mixtureWeight (k + 1) * cesaro F (k + 1) ^ 2 := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (cesaro_weighted_energy_le F hF) (by norm_num)

theorem cesaro_q_square_summable (F : ℕ → ℝ)
    (hF : Summable (fun k : ℕ => positiveQWeight (k + 1) * F (k + 1) ^ 2)) :
    Summable (fun k : ℕ => positiveQWeight (k + 1) * cesaro F (k + 1) ^ 2) := by
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (positiveQWeight_nonneg _) (sq_nonneg _)) _
    ((q_cesaro_weighted_square_summable F hF).mul_left (4 / 3 : ℝ))
  intro k
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (q_weight_le_latent (k + 1) (Nat.succ_pos k)) (sq_nonneg (cesaro F (k + 1)))

/-- A squared norm bound in the Q space itself, with no change of output law. -/
theorem cesaro_q_energy_le (F : ℕ → ℝ)
    (hF : Summable (fun k : ℕ => positiveQWeight (k + 1) * F (k + 1) ^ 2)) :
    (∑' k : ℕ, positiveQWeight (k + 1) * cesaro F (k + 1) ^ 2) ≤
      (4 / 3 : ℝ) * ∑' k : ℕ, positiveQWeight (k + 1) * F (k + 1) ^ 2 := by
  calc
    _ ≤ ∑' k : ℕ, (4 / 3 : ℝ) *
        (qMixtureWeight (k + 1) * cesaro F (k + 1) ^ 2) := by
      apply Summable.tsum_le_tsum _ (cesaro_q_square_summable F hF)
        ((q_cesaro_weighted_square_summable F hF).mul_left (4 / 3 : ℝ))
      intro k
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (q_weight_le_latent (k + 1) (Nat.succ_pos k)) (sq_nonneg (cesaro F (k + 1)))
    _ = (4 / 3 : ℝ) * qConditionalMeanSquare F := by
      rw [tsum_mul_left]
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (q_cesaro_weighted_energy_le F hF) (by norm_num)

def firstPulse (n : ℕ) : ℝ := if n = 1 then 1 else 0

theorem cesaro_firstPulse_one : cesaro firstPulse 1 = 1 := by
  norm_num [cesaro, firstPulse]

theorem cesaro_firstPulse_two : cesaro firstPulse 2 = (1 / 2 : ℝ) := by
  norm_num [cesaro, firstPulse,
    show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide]

theorem firstPulse_energy_hasSum (w : ℕ → ℝ) :
    HasSum (fun k : ℕ => w (k + 1) * firstPulse (k + 1) ^ 2) (w 1) := by
  have he : (fun k : ℕ => w (k + 1) * firstPulse (k + 1) ^ 2) =
      (fun k : ℕ => if k = 0 then w 1 else 0) := by
    funext k
    by_cases hk : k = 0
    · simp [hk, firstPulse]
    · simp [hk, firstPulse]
  rw [he]
  exact hasSum_ite_eq 0 (w 1)

/-- The first two output coordinates already exceed the whole input energy. -/
theorem firstPulse_energy_lt_cesaro (w : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n) (hw2 : 0 < w 2)
    (hs : Summable (fun k : ℕ => w (k + 1) * cesaro firstPulse (k + 1) ^ 2)) :
    (∑' k : ℕ, w (k + 1) * firstPulse (k + 1) ^ 2) <
      ∑' k : ℕ, w (k + 1) * cesaro firstPulse (k + 1) ^ 2 := by
  rw [(firstPulse_energy_hasSum w).tsum_eq]
  have hprefix := Summable.sum_le_tsum ({0, 1} : Finset ℕ)
    (fun k _ => mul_nonneg (hw (k + 1)) (sq_nonneg (cesaro firstPulse (k + 1)))) hs
  norm_num [cesaro_firstPulse_one, cesaro_firstPulse_two] at hprefix
  nlinarith

theorem cesaro_not_p_contraction :
    (∑' k : ℕ, weight (k + 1) * firstPulse (k + 1) ^ 2) <
      ∑' k : ℕ, weight (k + 1) * cesaro firstPulse (k + 1) ^ 2 := by
  apply firstPulse_energy_lt_cesaro weight weight_nonneg (by norm_num [weight])
  exact cesaro_p_square_summable firstPulse (firstPulse_energy_hasSum weight).summable

theorem cesaro_not_q_contraction :
    (∑' k : ℕ, positiveQWeight (k + 1) * firstPulse (k + 1) ^ 2) <
      ∑' k : ℕ, positiveQWeight (k + 1) * cesaro firstPulse (k + 1) ^ 2 := by
  apply firstPulse_energy_lt_cesaro positiveQWeight positiveQWeight_nonneg
  · have hz := zetaTwo_pos
    unfold positiveQWeight
    positivity
  · exact cesaro_q_square_summable firstPulse (firstPulse_energy_hasSum positiveQWeight).summable

end RiemannResearch.RH.CesaroSameMeasureBounds

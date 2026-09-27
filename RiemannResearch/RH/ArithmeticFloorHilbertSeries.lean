/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.CommonDilationCoercivity
import RiemannResearch.RH.DampedMobiusSeed
import RiemannResearch.RH.ParetoCoordinateEvaluation
import Mathlib.Tactic.LinearCombination

/-!
# Absolutely summable arithmetic residue synthesis in the Pareto Hilbert space

For arbitrary real weights with sum |w(m)| / sqrt(m) finite, the complete
centered floor prefix is an actual Pareto Hilbert vector. The construction
retains every signed term and the entire infinite tail.

This is the elementary Hilbert-series mechanism behind the strict
epsilon > 1/2 part of J.-F. Burnol, Acta Cientifica Venezolana 54
(2003), 210-215, Lemma 4.1 in the author manuscript:
https://arxiv.org/abs/math/0202166.
The general real-weight statement does not use any arithmetic cancellation.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The arithmetic residue term with conductor m+1; conductor zero is absent. -/
def arithmeticResidueTerm (w : ℕ → ℝ) (m : ℕ) : ThresholdHilbert :=
  (w (m+1) / ((m+1 : ℕ) : ℝ)) • hilbertResidue (m+1) (by positivity)

/-- The full signed synthesis is the centered arithmetic floor prefix. -/
def arithmeticFloorHilbert (w : ℕ → ℝ) : ThresholdHilbert :=
  -(∑' m : ℕ, arithmeticResidueTerm w m)

def arithmeticFloorDensity (w : ℕ → ℝ) : ℝ :=
  ∑' m : ℕ, w (m+1) / ((m+1 : ℕ) : ℝ)

def arithmeticFloorHilbertPartial (w : ℕ → ℝ) (N : ℕ) : ThresholdHilbert :=
  -(∑ m ∈ Finset.range N, arithmeticResidueTerm w m)

private theorem sqrt_nat_succ_le (m : ℕ) :
    Real.sqrt ((m+1 : ℕ) : ℝ) ≤ ((m+1 : ℕ) : ℝ) := by
  have h1 : (1 : ℝ) ≤ ((m+1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ ((m+1 : ℕ) : ℝ) by positivity)
  have hp := mul_nonneg (show (0 : ℝ) ≤ ((m+1 : ℕ) : ℝ) by positivity)
    (show (0 : ℝ) ≤ ((m+1 : ℕ) : ℝ) - 1 by linarith)
  nlinarith [Real.sqrt_nonneg ((m+1 : ℕ) : ℝ)]

/-- Full norm bound, obtained from the exact infinite residue-tail estimate. -/
theorem arithmeticResidueTerm_norm_le (w : ℕ → ℝ) (m : ℕ) :
    ‖arithmeticResidueTerm w m‖ ≤
      Real.sqrt 2 * (|w (m+1)| / ((m+1 : ℕ) : ℝ) ^ (1/2 : ℝ)) := by
  have ha : (0 : ℝ) < ((m+1 : ℕ) : ℝ) := by positivity
  have hsqa := Real.sq_sqrt ha.le
  have hsqrt : 0 < Real.sqrt ((m+1 : ℕ) : ℝ) := Real.sqrt_pos.mpr ha
  have hsqtwo : (Real.sqrt (2 : ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  have hb := hilbertResidue_norm_sq_le_twice (m+1) (by positivity)
  have hnorm : ‖hilbertResidue (m+1) (by positivity)‖ ≤
      Real.sqrt 2 * Real.sqrt ((m+1 : ℕ) : ℝ) := by
    have hp : 0 ≤ Real.sqrt 2 * Real.sqrt ((m+1 : ℕ) : ℝ) := by positivity
    have he : (Real.sqrt 2 * Real.sqrt ((m+1 : ℕ) : ℝ))^2 = 2 * ((m+1 : ℕ) : ℝ) := by
      rw [mul_pow, hsqtwo, hsqa]
    nlinarith [norm_nonneg (hilbertResidue (m+1) (by positivity))]
  rw [arithmeticResidueTerm, norm_smul, Real.norm_eq_abs, abs_div,
    abs_of_pos ha, ← Real.sqrt_eq_rpow]
  calc
    _ ≤ (|w (m+1)| / ((m+1 : ℕ) : ℝ)) *
        (Real.sqrt 2 * Real.sqrt ((m+1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by
      have hm0 : ((m+1 : ℕ) : ℝ) ≠ 0 := ne_of_gt ha
      have hsq0 : Real.sqrt ((m+1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hsqrt
      field_simp [hm0, hsq0]
      linear_combination |w (m+1)| * hsqa

theorem arithmeticFloorDensity_summable (w : ℕ → ℝ)
    (hw : Summable (fun m : ℕ =>
      |w (m+1)| / ((m+1 : ℕ) : ℝ) ^ (1/2 : ℝ))) :
    Summable (fun m : ℕ => w (m+1) / ((m+1 : ℕ) : ℝ)) := by
  apply hw.of_norm_bounded
  intro m
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((m+1 : ℕ) : ℝ)),
    ← Real.sqrt_eq_rpow]
  exact div_le_div_of_nonneg_left (abs_nonneg _)
    (Real.sqrt_pos.mpr (by positivity)) (sqrt_nat_succ_le m)

theorem arithmeticResidueTerm_norm_summable (w : ℕ → ℝ)
    (hw : Summable (fun m : ℕ =>
      |w (m+1)| / ((m+1 : ℕ) : ℝ) ^ (1/2 : ℝ))) :
    Summable (fun m => ‖arithmeticResidueTerm w m‖) := by
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (arithmeticResidueTerm_norm_le w) (hw.mul_left (Real.sqrt 2))

theorem arithmeticResidueTerm_summable (w : ℕ → ℝ)
    (hw : Summable (fun m : ℕ =>
      |w (m+1)| / ((m+1 : ℕ) : ℝ) ^ (1/2 : ℝ))) :
    Summable (arithmeticResidueTerm w) :=
  (arithmeticResidueTerm_norm_summable w hw).of_norm

theorem arithmeticResidueTerm_sequence (w : ℕ → ℝ) (m n : ℕ) :
    hilbertSequence (arithmeticResidueTerm w m) n =
      (w (m+1) / ((m+1 : ℕ) : ℝ)) * residue (m+1) n := by
  rw [arithmeticResidueTerm, hilbertSequence_smul]
  simp only [Pi.smul_apply, smul_eq_mul, hilbertResidue_sequence]

private theorem shifted_floor_hasSum (w : ℕ → ℝ) (n : ℕ) :
    HasSum (fun m : ℕ => w (m+1) * (n / (m+1) : ℕ))
      (arithmeticFloorPrefix w n) := by
  have hz : ∀ m : ℕ, m ∉ Finset.range n →
      w (m+1) * (n / (m+1) : ℕ) = 0 := by
    intro m hm
    have hn : n < m+1 := by simp only [Finset.mem_range] at hm; omega
    simp [Nat.div_eq_of_lt hn]
  have hs : Summable (fun m : ℕ => w (m+1) * (n / (m+1) : ℕ)) :=
    summable_of_ne_finset_zero hz
  have he : (∑' m : ℕ, w (m+1) * (n / (m+1) : ℕ)) =
      arithmeticFloorPrefix w n := by
    rw [tsum_eq_sum hz]
    unfold arithmeticFloorPrefix
    rw [Finset.sum_range_succ']
    simp
  simpa only [he] using hs.hasSum

private theorem residueTerm_floor_identity (w : ℕ → ℝ) (m n : ℕ) :
    (w (m+1) / ((m+1 : ℕ) : ℝ)) * residue (m+1) n =
      (n : ℝ) * (w (m+1) / ((m+1 : ℕ) : ℝ)) - w (m+1) * (n / (m+1) : ℕ) := by
  have hd : (residue (m+1) n : ℝ) + ((m+1 : ℕ) : ℝ) * (n / (m+1) : ℕ) = n := by
    unfold residue
    exact_mod_cast Nat.mod_add_div n (m+1)
  have hm0 : ((m+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hm0]
  linear_combination w (m+1) * hd

/-- Exact physical coordinates of the genuine infinite Hilbert synthesis.
Neither positivity nor multiplicativity of the weights is required. -/
theorem arithmeticFloorHilbert_sequence (w : ℕ → ℝ)
    (hw : Summable (fun m : ℕ =>
      |w (m+1)| / ((m+1 : ℕ) : ℝ) ^ (1/2 : ℝ))) (n : ℕ) :
    hilbertSequence (arithmeticFloorHilbert w) n =
      arithmeticFloorPrefix w n - (n : ℝ) * arithmeticFloorDensity w := by
  have hH := arithmeticResidueTerm_summable w hw
  have hD := arithmeticFloorDensity_summable w hw
  have hP := shifted_floor_hasSum w n
  have hcoord : (∑' m : ℕ,
      (w (m+1) / ((m+1 : ℕ) : ℝ)) * residue (m+1) n) =
      (n : ℝ) * arithmeticFloorDensity w - arithmeticFloorPrefix w n := by
    simp_rw [residueTerm_floor_identity]
    simpa only [arithmeticFloorDensity, tsum_mul_left, hP.tsum_eq] using
      (hD.mul_left (n : ℝ)).tsum_sub hP.summable
  cases n with
  | zero => simp [arithmeticFloorPrefix]
  | succ k =>
    rw [← physicalEvaluationCLM_apply k]
    unfold arithmeticFloorHilbert
    rw [map_neg, (physicalEvaluationCLM k).map_tsum hH]
    simp_rw [physicalEvaluationCLM_apply, arithmeticResidueTerm_sequence]
    rw [hcoord]
    ring

theorem arithmeticFloorHilbert_norm_le (w : ℕ → ℝ)
    (hw : Summable (fun m : ℕ =>
      |w (m+1)| / ((m+1 : ℕ) : ℝ) ^ (1/2 : ℝ))) :
    ‖arithmeticFloorHilbert w‖ ≤ Real.sqrt 2 *
      ∑' m : ℕ, |w (m+1)| / ((m+1 : ℕ) : ℝ) ^ (1/2 : ℝ) := by
  have hs := arithmeticResidueTerm_norm_summable w hw
  rw [arithmeticFloorHilbert, norm_neg]
  calc
    _ ≤ ∑' m : ℕ, ‖arithmeticResidueTerm w m‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' m : ℕ, Real.sqrt 2 *
        (|w (m+1)| / ((m+1 : ℕ) : ℝ) ^ (1/2 : ℝ)) :=
      hs.tsum_le_tsum (arithmeticResidueTerm_norm_le w) (hw.mul_left _)
    _ = _ := by rw [tsum_mul_left]

/-- The approximation error is exactly the complete signed Hilbert tail. -/
theorem arithmeticFloorHilbert_partial_error_eq (w : ℕ → ℝ)
    (hw : Summable (fun m : ℕ =>
      |w (m+1)| / ((m+1 : ℕ) : ℝ) ^ (1/2 : ℝ))) (N : ℕ) :
    arithmeticFloorHilbert w - arithmeticFloorHilbertPartial w N =
      -(∑' j : ℕ, arithmeticResidueTerm w (j+N)) := by
  unfold arithmeticFloorHilbert arithmeticFloorHilbertPartial
  rw [← (arithmeticResidueTerm_summable w hw).sum_add_tsum_nat_add N]
  abel

set_option maxHeartbeats 800000 in
theorem arithmeticFloorHilbert_partial_error_le (w : ℕ → ℝ)
    (hw : Summable (fun m : ℕ =>
      |w (m+1)| / ((m+1 : ℕ) : ℝ) ^ (1/2 : ℝ))) (N : ℕ) :
    ‖arithmeticFloorHilbert w - arithmeticFloorHilbertPartial w N‖ ≤
      Real.sqrt 2 * ∑' j : ℕ,
        |w (j+N+1)| / ((j+N+1 : ℕ) : ℝ) ^ (1/2 : ℝ) := by
  have hs : Summable (fun j : ℕ => ‖arithmeticResidueTerm w (j+N)‖) :=
    (summable_nat_add_iff N).mpr (arithmeticResidueTerm_norm_summable w hw)
  have hm : Summable (fun j : ℕ => Real.sqrt 2 *
      (|w (j+N+1)| / ((j+N+1 : ℕ) : ℝ) ^ (1/2 : ℝ))) :=
    (summable_nat_add_iff N).mpr (hw.mul_left (Real.sqrt 2))
  rw [arithmeticFloorHilbert_partial_error_eq w hw N, norm_neg]
  calc
    _ ≤ ∑' j : ℕ, ‖arithmeticResidueTerm w (j+N)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' j : ℕ, Real.sqrt 2 *
        (|w (j+N+1)| / ((j+N+1 : ℕ) : ℝ) ^ (1/2 : ℝ)) :=
      hs.tsum_le_tsum (fun j => arithmeticResidueTerm_norm_le w (j+N)) hm
    _ = _ := by rw [tsum_mul_left]

/-- Finite energy determines the linear centering of any real sequence
uniquely. This elementary structural consequence uses no arithmetic input. -/
theorem square_summable_centering_unique (a : ℕ → ℝ) {C D : ℝ}
    (hC : Summable (fun n => positiveWeight n * (a n - (n : ℝ) * C) ^ 2))
    (hD : Summable (fun n => positiveWeight n * (a n - (n : ℝ) * D) ^ 2)) :
    C = D := by
  have hl : Summable (fun n : ℕ =>
      positiveWeight n * ((C - D) * (n : ℝ)) ^ 2) := by
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _)) _
      ((hC.add hD).mul_left 2)
    intro n
    have hb : ((C - D) * (n : ℝ)) ^ 2 ≤
        2 * ((a n - (n : ℝ) * C) ^ 2 + (a n - (n : ℝ) * D) ^ 2) := by
      nlinarith [sq_nonneg (2 * a n - (n : ℝ) * C - (n : ℝ) * D)]
    simpa only [mul_add, mul_assoc, mul_left_comm] using
      mul_le_mul_of_nonneg_left hb (positiveWeight_nonneg n)
  exact sub_eq_zero.mp ((linear_square_summable_iff (C - D)).mp hl)


end
end RiemannResearch.RH.Pareto

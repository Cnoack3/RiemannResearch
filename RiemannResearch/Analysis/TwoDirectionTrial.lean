/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Exact two-direction quadratic trials

Source: elementary two-by-two completion developed for the user's screened
full-squarefree agenda. Wolfram checked the scalar algebra independently.
The RH consumer is QCRTMixedFloorTrial. The exact determinant is retained;
regularization gives positivity without a uniform coercivity hypothesis.
-/
noncomputable section
namespace RiemannResearch.Analysis.TwoDirectionTrial
def first (A B C u v : ℝ) : ℝ := (C * u - B * v) / (A * C - B ^ 2)
def second (A B C u v : ℝ) : ℝ := (A * v - B * u) / (A * C - B ^ 2)
def gain (A B C u v : ℝ) : ℝ :=
  (C * u ^ 2 - 2 * B * u * v + A * v ^ 2) / (A * C - B ^ 2)

theorem quadratic_completion (A B C u v a : ℝ) :
    2 * first A B C u v * u + 2 * second A B C u v * v -
      (a * first A B C u v ^ 2 + 2 * B * first A B C u v * second A B C u v +
        C * second A B C u v ^ 2) =
      gain A B C u v + (A - a) * first A B C u v ^ 2 := by
  unfold first second gain
  field_simp
  ring

theorem gain_sub_first (A B C u v : ℝ) (hA : A ≠ 0) (hd : A * C - B ^ 2 ≠ 0) :
    gain A B C u v - u ^ 2 / A =
      (A * v - B * u) ^ 2 / (A * (A * C - B ^ 2)) := by
  unfold gain
  field_simp [hA, hd]
  field_simp [hd]
  ring

theorem gain_sub_second (A B C u v : ℝ) (hC : C ≠ 0) (hd : A * C - B ^ 2 ≠ 0) :
    gain A B C u v - v ^ 2 / C =
      (C * u - B * v) ^ 2 / (C * (A * C - B ^ 2)) := by
  have hd' : C * A - B ^ 2 ≠ 0 := by simpa only [mul_comm] using hd
  have he : gain A B C u v = gain C B A v u := by
    unfold gain
    congr 1 <;> ring
  rw [he]
  simpa only [mul_comm] using gain_sub_first C B A v u hC hd'

theorem gain_ge_first (A B C u v : ℝ) (hA : 0 < A) (hd : 0 < A * C - B ^ 2) :
    u ^ 2 / A ≤ gain A B C u v := by
  have h := gain_sub_first A B C u v (ne_of_gt hA) (ne_of_gt hd)
  have hp : 0 ≤ (A * v - B * u) ^ 2 / (A * (A * C - B ^ 2)) := by positivity
  linarith

theorem gain_ge_second (A B C u v : ℝ) (hC : 0 < C) (hd : 0 < A * C - B ^ 2) :
    v ^ 2 / C ≤ gain A B C u v := by
  have h := gain_sub_second A B C u v (ne_of_gt hC) (ne_of_gt hd)
  have hp : 0 ≤ (C * u - B * v) ^ 2 / (C * (A * C - B ^ 2)) := by positivity
  linarith

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem regularized_determinant_pos (h q : H) (A τ : ℝ)
    (hA : ‖h‖ ^ 2 ≤ A) (hq : q ≠ 0) (hτ : 0 < τ) :
    0 < (A + τ) * ‖q‖ ^ 2 - (inner ℝ h q) ^ 2 := by
  have hc := real_inner_mul_inner_self_le h q
  simp only [real_inner_self_eq_norm_sq] at hc
  have hq2 : 0 < ‖q‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hq)
  have hm := mul_le_mul_of_nonneg_right hA (le_of_lt hq2)
  have ht := mul_pos hτ hq2
  nlinarith

theorem norm_completion (f h q : H) (A : ℝ) :
    let B := inner ℝ h q
    let C := ‖q‖ ^ 2
    let u := inner ℝ f h
    let v := inner ℝ f q
    ‖f - (first A B C u v • h + second A B C u v • q)‖ ^ 2 =
      ‖f‖ ^ 2 - gain A B C u v -
        (A - ‖h‖ ^ 2) * first A B C u v ^ 2 := by
  dsimp only
  have hc := quadratic_completion A (inner ℝ h q) (‖q‖ ^ 2)
    (inner ℝ f h) (inner ℝ f q) (‖h‖ ^ 2)
  simp only [norm_sub_sq_real, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, inner_add_right, real_inner_smul_left, inner_smul_right]
  nlinarith
end RiemannResearch.Analysis.TwoDirectionTrial

/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QShiftedReciprocal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Variational estimates for the positive reciprocal quadratic form
Source: completion of a square in the reciprocal form, developed for the user's
actual squarefree correction agenda. These identities are general Q-Hilbert facts.
-/

noncomputable section
namespace RiemannResearch.RH.QShiftedReciprocal
open ZetaTwoHilbert
/-- The shifted reciprocal has quadratic-form norm at most one half. -/
theorem B_energy_le_half_norm_sq (f : QHilbert) :
    inner ℝ f (B f) ≤ ‖f‖ ^ 2 / 2 := by
  have hs := qCoordinate_square_summable f
  have hs2 : Summable (fun n : ℕ => (f n) ^ 2 / 2) := hs.div_const 2
  have hpoint (n : ℕ) : (f n) ^ 2 / ((n : ℝ) + 2) ≤ (f n) ^ 2 / 2 := by
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num)
      (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hsB : Summable (fun n : ℕ => (f n) ^ 2 / ((n : ℝ) + 2)) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hpoint hs2
  calc
    inner ℝ f (B f) = ∑' n : ℕ, (f n) ^ 2 / ((n : ℝ) + 2) := B_inner_tsum f
    _ ≤ ∑' n : ℕ, (f n) ^ 2 / 2 := Summable.tsum_le_tsum hpoint hsB hs2
    _ = (∑' n : ℕ, (f n) ^ 2) / 2 := by rw [tsum_div_const]
    _ = ‖f‖ ^ 2 / 2 := by rw [qNorm_sq]

/-- Exact completion of the positive B quadratic form. -/
theorem B_variational_identity (r v : QHilbert) :
    inner ℝ r (B r) -
      (2 * inner ℝ (B r) v - inner ℝ v (B v)) =
        inner ℝ (r - v) (B (r - v)) := by
  rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right]
  rw [← B_symmetric r v, real_inner_comm v (B r)]
  ring

/-- Cauchy--Schwarz for the strictly positive shifted-reciprocal form. -/
theorem B_cauchy_sq (r v : QHilbert) :
    (inner ℝ (B r) v) ^ 2 ≤ inner ℝ r (B r) * inner ℝ v (B v) := by
  by_cases hv : v = 0
  · simp [hv]
  have hdne : inner ℝ v (B v) ≠ 0 := fun hz => hv (B_faithful v hz)
  have hd : 0 < inner ℝ v (B v) :=
    lt_of_le_of_ne (B_positive v) (Ne.symm hdne)
  let c : ℝ := inner ℝ (B r) v
  let d : ℝ := inner ℝ v (B v)
  let e : ℝ := inner ℝ r (B r)
  have hquad (t : ℝ) : 0 ≤ e - 2 * t * c + t ^ 2 * d := by
    have hp := B_positive (r - t • v)
    have he : inner ℝ (r - t • v) (B (r - t • v)) =
        e - 2 * t * c + t ^ 2 * d := by
      rw [map_sub, map_smul, inner_sub_left, inner_sub_right,
        inner_sub_right, real_inner_smul_right, real_inner_smul_left,
        real_inner_smul_left, real_inner_smul_right]
      rw [← B_symmetric r v, real_inner_comm v (B r)]
      dsimp [e, c, d]
      simp only [real_inner_comm v (B r)]
      ring
    rwa [he] at hp
  have hp := mul_nonneg (hquad (c / d)) (le_of_lt hd)
  have he : (e - 2 * (c / d) * c + (c / d) ^ 2 * d) * d = e * d - c ^ 2 := by
    field_simp [show d ≠ 0 from hdne]
    ring
  rw [he] at hp
  change c ^ 2 ≤ e * d
  linarith

end RiemannResearch.RH.QShiftedReciprocal

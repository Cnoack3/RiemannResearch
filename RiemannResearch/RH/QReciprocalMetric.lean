/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Reciprocal multiplier and the reversed Pareto/Q metric identity

Source: user-provided argument, 6 November 2026. The physical multiplier D is
f(n) / n, with the anchored value at zero retained. The imported
QShiftedReciprocal.B is the multiplier f(n) / (n+1), called R in the discussion;
it is not the positive invertible metric operator A* A.

The identity (I - B) D = B proves that the two metric expansions are inverse
descriptions of the same change of measure. No closure invariance or residual
orthogonality is inferred from this identity.
-/

noncomputable section
namespace RiemannResearch.RH.QReciprocalMetric
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QShiftedReciprocal

def coordinates (f : QHilbert) : QHilbert :=
  ⟨fun n => f n / ((n : ℝ) + 1), by
    apply (memℓp_gen_iff (show 0 < (2 : ENNReal).toReal by norm_num)).mpr
    have hs : Summable (fun n : ℕ => (f n / ((n : ℝ) + 1)) ^ 2) := by
      apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _
        (qCoordinate_square_summable f)
      intro n
      rw [div_pow]
      have hd : 1 ≤ ((n : ℝ) + 1) ^ 2 := by
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      simpa only [div_one] using
        div_le_div_of_nonneg_left (sq_nonneg (f n)) zero_lt_one hd
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using hs⟩

@[simp] theorem coordinates_apply (f : QHilbert) (n : ℕ) :
    coordinates f n = f n / ((n : ℝ) + 1) := rfl

theorem coordinates_norm_le (f : QHilbert) : ‖coordinates f‖ ≤ ‖f‖ := by
  have hsq : ‖coordinates f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [qNorm_sq, qNorm_sq]
    apply Summable.tsum_le_tsum _ (qCoordinate_square_summable _)
      (qCoordinate_square_summable _)
    intro n
    rw [coordinates_apply, div_pow]
    have hd : 1 ≤ ((n : ℝ) + 1) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    simpa only [div_one] using
      div_le_div_of_nonneg_left (sq_nonneg (f n)) zero_lt_one hd
  nlinarith [norm_nonneg f, norm_nonneg (coordinates f)]

def linear : QHilbert →ₗ[ℝ] QHilbert where
  toFun := coordinates
  map_add' f g := by
    apply Subtype.ext
    funext n
    change (f n + g n) / ((n : ℝ) + 1) =
      f n / ((n : ℝ) + 1) + g n / ((n : ℝ) + 1)
    exact add_div _ _ _
  map_smul' c f := by
    apply Subtype.ext
    funext n
    change (c * f n) / ((n : ℝ) + 1) = c * (f n / ((n : ℝ) + 1))
    ring

def D : QHilbert →L[ℝ] QHilbert :=
  linear.mkContinuous 1 (fun f => by
    change ‖coordinates f‖ ≤ 1 * ‖f‖
    simpa using coordinates_norm_le f)

@[simp] theorem D_apply (f : QHilbert) (n : ℕ) :
    D f n = f n / ((n : ℝ) + 1) := rfl

theorem qSequence_D (f : QHilbert) (k : ℕ) :
    qSequence (D f) k = qSequence f k / (k : ℝ) := by
  cases k with
  | zero => simp
  | succ n =>
    simp only [qSequence_succ, D_apply, Nat.cast_add, Nat.cast_one]
    ring

/-- In the existing source B is the multiplier called R in the discussion. -/
theorem D_sub_B_D (f : QHilbert) : D f - B (D f) = B f := by
  apply Subtype.ext
  funext n
  change f n / ((n : ℝ) + 1) -
    (f n / ((n : ℝ) + 1)) / ((n : ℝ) + 2) =
    f n / ((n : ℝ) + 2)
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp [h1, h2]
  ring

/-- The mixed reciprocal pairing has the complete original Q weight. -/
theorem pareto_inner_D (f g : QHilbert) :
    inner ℝ (toPareto (D f)) (toPareto g) =
      zetaTwo * inner ℝ (B f) g := by
  calc
    _ = inner ℝ (toPareto g) (toPareto (D f)) := real_inner_comm _ _
    _ = zetaTwo * (inner ℝ g (D f) - inner ℝ g (B (D f))) :=
      pareto_inner_identity g (D f)
    _ = zetaTwo * inner ℝ g (B f) := by
      rw [← inner_sub_right, D_sub_B_D]
    _ = _ := by rw [real_inner_comm g (B f)]

/-- Exact swapped metric expansion, with D acting on the first argument. -/
theorem q_inner_identity (f g : QHilbert) :
    inner ℝ f g = (1 / zetaTwo) *
      (inner ℝ (toPareto f) (toPareto g) +
        inner ℝ (toPareto (D f)) (toPareto g)) := by
  rw [pareto_inner_identity, pareto_inner_D, B_symmetric]
  field_simp [ne_of_gt zetaTwo_pos]
  ring

end RiemannResearch.RH.QReciprocalMetric

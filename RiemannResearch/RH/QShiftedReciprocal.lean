/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.RH.QSievePrimeJump
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The inverse change-of-measure correction

The physical multiplier B is f(n)/(n+1), on positive physical sites n.
It is a strictly positive contraction, and Bf is bounded pointwise for
every f in the actual Q Hilbert space. The exact inverse metric formula
is <Tf,Tg>_P = zeta(2) * (<f,g>_Q - <f,Bg>_Q).
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QShiftedReciprocal
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer

def coordinates (f : QHilbert) : QHilbert :=
  ⟨fun n => f n / ((n : ℝ) + 2), by
    apply (memℓp_gen_iff (show 0 < (2 : ENNReal).toReal by norm_num)).mpr
    have hs : Summable (fun n : ℕ => (f n / ((n : ℝ) + 2)) ^ 2) := by
      apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _
        (qCoordinate_square_summable f)
      intro n
      rw [div_pow]
      have hd : 1 ≤ ((n : ℝ) + 2) ^ 2 := by
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      simpa only [div_one] using
        div_le_div_of_nonneg_left (sq_nonneg (f n)) zero_lt_one hd
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using hs⟩

@[simp] theorem coordinates_apply (f : QHilbert) (n : ℕ) :
    coordinates f n = f n / ((n : ℝ) + 2) := rfl

theorem coordinates_norm_le (f : QHilbert) : ‖coordinates f‖ ≤ ‖f‖ := by
  have hsq : ‖coordinates f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [qNorm_sq, qNorm_sq]
    apply Summable.tsum_le_tsum _ (qCoordinate_square_summable _)
      (qCoordinate_square_summable _)
    intro n
    rw [coordinates_apply, div_pow]
    have hd : 1 ≤ ((n : ℝ) + 2) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    simpa only [div_one] using
      div_le_div_of_nonneg_left (sq_nonneg (f n)) zero_lt_one hd
  nlinarith [norm_nonneg f, norm_nonneg (coordinates f)]

def linear : QHilbert →ₗ[ℝ] QHilbert where
  toFun := coordinates
  map_add' f g := by
    apply Subtype.ext
    funext n
    change (f n + g n) / ((n : ℝ) + 2) =
      f n / ((n : ℝ) + 2) + g n / ((n : ℝ) + 2)
    exact add_div _ _ _
  map_smul' c f := by
    apply Subtype.ext
    funext n
    change (c * f n) / ((n : ℝ) + 2) = c * (f n / ((n : ℝ) + 2))
    ring

def B : QHilbert →L[ℝ] QHilbert :=
  linear.mkContinuous 1 (fun f => by
    change ‖coordinates f‖ ≤ 1 * ‖f‖
    simpa using coordinates_norm_le f)

@[simp] theorem B_apply (f : QHilbert) (n : ℕ) :
    B f n = f n / ((n : ℝ) + 2) := rfl

theorem B_norm_le (f : QHilbert) : ‖B f‖ ≤ ‖f‖ := coordinates_norm_le f

theorem qSequence_B (f : QHilbert) (k : ℕ) :
    qSequence (B f) k = qSequence f k / ((k : ℝ) + 1) := by
  cases k with
  | zero => simp
  | succ n =>
    simp only [qSequence_succ, B_apply, Nat.cast_add, Nat.cast_one]
    ring

theorem B_symmetric (f g : QHilbert) :
    inner ℝ (B f) g = inner ℝ f (B g) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  change g n * (f n / ((n : ℝ) + 2)) = (g n / ((n : ℝ) + 2)) * f n
  ring

theorem B_inner_tsum (f : QHilbert) :
    inner ℝ f (B f) = ∑' n : ℕ, (f n) ^ 2 / ((n : ℝ) + 2) := by
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  change (f n / ((n : ℝ) + 2)) * f n = (f n) ^ 2 / ((n : ℝ) + 2)
  ring

theorem B_positive (f : QHilbert) : 0 ≤ inner ℝ f (B f) := by
  rw [B_inner_tsum]
  exact tsum_nonneg (fun n => by positivity)

theorem B_faithful (f : QHilbert) (hf : inner ℝ f (B f) = 0) : f = 0 := by
  have hs : Summable (fun n : ℕ => (f n) ^ 2 / ((n : ℝ) + 2)) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) _
      (qCoordinate_square_summable f)
    intro n
    exact div_le_self (sq_nonneg _) (by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith)
  have ht : (∑' n : ℕ, (f n) ^ 2 / ((n : ℝ) + 2)) = 0 := by
    rwa [B_inner_tsum] at hf
  apply Subtype.ext
  funext n
  change f n = 0
  have hl : (f n) ^ 2 / ((n : ℝ) + 2) ≤ 0 := by
    have hsingle := Summable.sum_le_tsum ({n} : Finset ℕ)
      (fun j _ => show 0 ≤ (f j) ^ 2 / ((j : ℝ) + 2) by positivity) hs
    simpa only [Finset.sum_singleton, ht] using hsingle
  have hz : (f n) ^ 2 / ((n : ℝ) + 2) = 0 :=
    le_antisymm hl (by positivity)
  have hden : (n : ℝ) + 2 ≠ 0 := by positivity
  have hsq : (f n) ^ 2 = 0 := (div_eq_zero_iff.mp hz).resolve_right hden
  nlinarith

theorem B_physical_bound (f : QHilbert) (k : ℕ) :
    |qSequence (B f) k| ≤ Real.sqrt zetaTwo * ‖f‖ := by
  rw [qSequence_B, abs_div, abs_of_pos (by positivity : 0 < (k : ℝ) + 1)]
  apply (div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)).mpr
  have h := QPrimePowerSieve.qSequence_abs_le f k
  have hnonneg : 0 ≤ Real.sqrt zetaTwo * ‖f‖ := by positivity
  nlinarith

theorem B_physical_bounded (f : QHilbert) :
    ∃ C : ℝ, ∀ k, |qSequence (B f) k| ≤ C :=
  ⟨Real.sqrt zetaTwo * ‖f‖, B_physical_bound f⟩

theorem inverse_weight_identity (k : ℕ) :
    positiveWeight k = zetaTwo *
      (positiveQWeight k - positiveQWeight k / ((k : ℝ) + 1)) := by
  by_cases hk : k = 0
  · simp [hk, positiveWeight, positiveQWeight]
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hnext : (k : ℝ) + 1 ≠ 0 := by positivity
  unfold positiveWeight positiveQWeight
  field_simp [hkR, hnext, ne_of_gt zetaTwo_pos]
  ring

theorem pareto_inner_identity (f g : QHilbert) :
    inner ℝ (toPareto f) (toPareto g) =
      zetaTwo * (inner ℝ f g - inner ℝ f (B g)) := by
  rw [hilbert_inner_weighted, toPareto_sequence, toPareto_sequence]
  unfold paretoInner
  rw [qInner_weighted, qInner_weighted,
    ← (qSequence_product_summable f g).tsum_sub
      (qSequence_product_summable f (B g)), ← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [qSequence_B, inverse_weight_identity]
  ring

end RiemannResearch.RH.QShiftedReciprocal

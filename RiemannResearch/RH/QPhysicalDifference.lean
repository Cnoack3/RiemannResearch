/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.SquarefreeRadicalDifference
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The bounded physical unilateral difference on the complete Q space

Source: user-provided Squarefree_Primitive_Energy_Regularization_2026-10-17,
Section 2. This realizes the literal boundary convention F(0)=0, proves the
unilateral shift is a contraction, and constructs the injective difference.
It is a physical operator, not translation on a Haar probability space.
-/

noncomputable section
open scoped Topology
namespace RiemannResearch.RH.QPhysicalDifference
open ZetaTwoHilbert ZetaTwoProbability SquarefreeRadicalDifference

private theorem shift_summand_le (f : QHilbert) (n : ℕ) :
    positiveQWeight (n+1) * (qSequence f n) ^ 2 ≤
      positiveQWeight n * (qSequence f n) ^ 2 := by
  cases n with
  | zero => simp
  | succ n =>
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hZ := zetaTwo_pos
    unfold positiveQWeight
    apply one_div_le_one_div_of_le
    · positivity
    · apply mul_le_mul_of_nonneg_left _ hZ.le
      simp only [Nat.cast_add, Nat.cast_one]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]

private theorem shift_summable' (f : QHilbert) :
    Summable (fun n => positiveQWeight (n+1) * (qSequence f n) ^ 2) := by
  apply (qSequence_square_summable f).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (positiveQWeight_nonneg _) (sq_nonneg _))]
  exact shift_summand_le f n

private theorem shift_summable (f : QHilbert) :
    Summable (fun n => positiveQWeight n * (qSequence f (n-1)) ^ 2) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [Nat.add_sub_cancel] using shift_summable' f

def physicalShift (f : QHilbert) : QHilbert :=
  encodeQ (fun n => qSequence f (n-1)) (shift_summable f)

@[simp] theorem qSequence_physicalShift (f : QHilbert) (n : ℕ) :
    qSequence (physicalShift f) n = qSequence f (n-1) := by
  rw [physicalShift, qSequence_encodeQ _ _ (by simp)]

theorem physicalShift_norm_sq (f : QHilbert) :
    ‖physicalShift f‖ ^ 2 = ∑' n, positiveQWeight (n+1) * (qSequence f n) ^ 2 := by
  rw [qNorm_weighted_sq]
  simp_rw [qSequence_physicalShift]
  rw [(shift_summable f).tsum_eq_zero_add]
  simp only [Nat.zero_sub, qSequence_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, zero_add, Nat.add_sub_cancel]

theorem physicalShift_norm_le (f : QHilbert) : ‖physicalShift f‖ ≤ ‖f‖ := by
  have h : ‖physicalShift f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [physicalShift_norm_sq, qNorm_weighted_sq]
    exact Summable.tsum_le_tsum (shift_summand_le f) (shift_summable' f)
      (qSequence_square_summable f)
  nlinarith [norm_nonneg (physicalShift f), norm_nonneg f]

def physicalShiftLinear : QHilbert →ₗ[ℝ] QHilbert where
  toFun := physicalShift
  map_add' f g := by
    apply qSequence_injective
    funext k
    rw [show qSequence (physicalShift f + physicalShift g) k =
      qSequence (physicalShift f) k + qSequence (physicalShift g) k from
      congrFun (qSequenceLinear.map_add _ _) k]
    simp only [qSequence_physicalShift]
    exact congrFun (qSequenceLinear.map_add f g) (k-1)
  map_smul' c f := by
    apply qSequence_injective
    funext k
    change qSequence (physicalShift (c • f)) k = qSequence (c • physicalShift f) k
    rw [show qSequence (c • physicalShift f) k =
      c * qSequence (physicalShift f) k from
      congrFun (qSequenceLinear.map_smul c _) k]
    simp only [qSequence_physicalShift]
    exact congrFun (qSequenceLinear.map_smul c f) (k-1)

def shiftCLM : QHilbert →L[ℝ] QHilbert :=
  physicalShiftLinear.mkContinuous 1 (by
    intro f
    change ‖physicalShift f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using physicalShift_norm_le f)

def differenceCLM : QHilbert →L[ℝ] QHilbert :=
  ContinuousLinearMap.id ℝ QHilbert - shiftCLM

@[simp] theorem qSequence_differenceCLM (f : QHilbert) (n : ℕ) :
    qSequence (differenceCLM f) n = qDifference f n := by
  change qSequenceLinear (f - physicalShift f) n = _
  rw [map_sub]
  change qSequence f n - qSequence (physicalShift f) n = _
  rw [qSequence_physicalShift]
  rfl

theorem differenceCLM_norm_le (f : QHilbert) : ‖differenceCLM f‖ ≤ 2 * ‖f‖ := by
  change ‖f - physicalShift f‖ ≤ _
  calc
    ‖f - physicalShift f‖ ≤ ‖f‖ + ‖physicalShift f‖ := norm_sub_le _ _
    _ ≤ 2 * ‖f‖ := by linarith [physicalShift_norm_le f]

theorem differenceCLM_injective : Function.Injective differenceCLM := by
  intro f g h
  apply qSequence_injective
  funext k
  induction k with
  | zero => simp
  | succ k ih =>
    have hd := congrArg (fun z : QHilbert => qSequence z (k+1)) h
    simp only [qSequence_differenceCLM, qDifference, Nat.add_sub_cancel] at hd
    linarith

end RiemannResearch.RH.QPhysicalDifference

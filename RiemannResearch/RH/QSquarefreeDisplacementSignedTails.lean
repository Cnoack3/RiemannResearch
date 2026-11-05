/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QSignedTailRigidity
import RiemannResearch.RH.QShiftedReciprocal
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import RiemannResearch.RH.QSquarefreeAnnihilatorSignedTails
import RiemannResearch.RH.QSignedPhysicalPrefix
import RiemannResearch.RH.QSquarefreeSignedPowerMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Signed tails under the shifted reciprocal multiplier

In physical coordinates the multiplier divides by n+1. Thus it sends every
complete-Q vector to one whose signed coefficients have finite first absolute
moment. The anchored tails respect subtraction. Applying the factorial sieve to the faithful
witness gives a signed-tail criterion and a one-sided harmonic criterion for RH.
-/

noncomputable section
namespace RiemannResearch.RH.QSignedTailRigidity
open ZetaTwoHilbert QShiftedReciprocal

theorem signedCoefficient_sub (u v : QHilbert) (n : ℕ) :
    signedCoefficient (u - v) n = signedCoefficient u n - signedCoefficient v n := by
  change positiveQWeight n * (qSequenceLinear (u - v)) n =
    positiveQWeight n * qSequence u n - positiveQWeight n * qSequence v n
  rw [map_sub]
  exact mul_sub _ _ _

theorem anchoredTail_sub (u v : QHilbert) :
    anchoredTail (u - v) = anchoredTail u - anchoredTail v := by
  funext k
  by_cases hk : k = 0
  · simp [anchoredTail, hk]
  change anchoredTail (u - v) k = anchoredTail u k - anchoredTail v k
  simp only [anchoredTail, if_neg hk, signedTail, signedCoefficient_sub]
  apply Summable.tsum_sub
  · exact (summable_nat_add_iff k).mpr (signedCoefficient_summable u)
  · exact (summable_nat_add_iff k).mpr (signedCoefficient_summable v)

theorem signedCoefficient_B_firstMoment (u : QHilbert) :
    Summable (fun n : ℕ => (n : ℝ) * signedCoefficient (B u) n) := by
  apply Summable.of_norm_bounded (signedCoefficient_summable u).norm
  intro n
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd : 0 < (n : ℝ) + 1 := by positivity
  have hid : (n : ℝ) * signedCoefficient (B u) n =
      ((n : ℝ) / ((n : ℝ) + 1)) * signedCoefficient u n := by
    simp only [signedCoefficient, qSequence_B]
    ring
  rw [hid, norm_mul, Real.norm_of_nonneg (div_nonneg hn hd.le)]
  exact mul_le_of_le_one_left (norm_nonneg _) ((div_le_one hd).2 (by linarith))

theorem anchoredTail_B_summable (u : QHilbert) : Summable (anchoredTail (B u)) :=
  anchoredTail_summable_of_firstMoment _ (signedCoefficient_B_firstMoment u)

end RiemannResearch.RH.QSignedTailRigidity

namespace RiemannResearch.RH.QSquarefreeDisplacementRigidity
open ZetaTwoHilbert ZetaTwoOptimizerStage QSignedTailRigidity QShiftedReciprocal

/-- The signed tails retain cancellation inside each complete-Q tail sum. -/
theorem residual_zero_iff_summable_displacement_signedTail :
    limitingResidual = 0 ↔ Summable (anchoredTail displacement) := by
  constructor
  · intro hr
    rw [displacement_eq_zero_of_residual_eq_zero hr]
    simpa only [map_zero] using anchoredTail_B_summable (0 : QHilbert)
  · intro hd
    have hw : Summable (anchoredTail witness) := by
      rw [witness, anchoredTail_sub]
      exact (anchoredTail_B_summable pResidual).sub hd
    exact residual_eq_zero_of_witness_mean_zero
      (mean_zero_of_summable_signedTail witness witness_mem_orthogonal hw)

/-- A complete signed-tail condition on the physical displacement implies RH. -/
theorem riemannHypothesis_of_summable_displacement_signedTail
    (hd : Summable (anchoredTail displacement)) : RiemannHypothesis := by
  have hr := residual_zero_iff_summable_displacement_signedTail.mpr hd
  have hm : qOne ∈ closure :=
    Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm
  exact QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr hm)

/-- The summation of the physical displacements precedes taking an absolute value. -/
theorem riemannHypothesis_of_summable_displacement_prefix
    (hd : Summable (Analysis.inverseSquarePrefix (fun n : ℕ => qSequence displacement (n + 1)))) :
    RiemannHypothesis :=
  riemannHypothesis_of_summable_displacement_signedTail
    (anchoredTail_summable_of_signedPhysicalPrefix displacement hd)

end RiemannResearch.RH.QSquarefreeDisplacementRigidity

open Filter
namespace RiemannResearch.RH.QSquarefreeDisplacementRigidity
open ZetaTwoHilbert QSignedTailRigidity QShiftedReciprocal

theorem displacement_absolute_power_moment_of_one_sided (a ε : ℝ)
    (ha : 0 < a) (ha₁ : a ≤ 1) (hε : |ε| = 1)
    (hd : Summable (fun n : ℕ => max (ε * signedCoefficient displacement n) 0 * (n : ℝ) ^ a)) :
    Summable (fun n : ℕ => |signedCoefficient displacement n| * (n : ℝ) ^ a) := by
  let s := signedCoefficient (B pResidual)
  let d := signedCoefficient displacement
  let w := signedCoefficient witness
  let H := fun n : ℕ => (n : ℝ) ^ a
  have hH (n : ℕ) : 0 ≤ H n := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hfirst := (signedCoefficient_B_firstMoment pResidual).abs
  have hs : Summable (fun n => |s n| * H n) := by
    apply Summable.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (hH n)) _ hfirst
    intro n
    change |s n| * (n : ℝ) ^ a ≤ |(n : ℝ) * s n|
    conv_rhs => rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)), mul_comm]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    cases n with
    | zero => simp [Real.zero_rpow ha.ne']
    | succ n =>
      have h1 : 1 ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_add_left 1 n)
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le h1 ha₁
  have hw (n : ℕ) : w n = s n - d n := signedCoefficient_sub _ _ _
  have hpos : Summable (fun n => max ((-ε) * w n) 0 * H n) := by
    apply Summable.of_nonneg_of_le (fun n => mul_nonneg (le_max_right _ _) (hH n)) _ (hs.add hd)
    intro n
    change _ ≤ |s n| * H n + max (ε * d n) 0 * H n
    rw [← add_mul]
    apply mul_le_mul_of_nonneg_right _ (hH n)
    apply max_le
    · have hbound := neg_le_abs (ε * s n)
      rw [abs_mul, hε, one_mul] at hbound
      rw [hw]
      linarith [le_max_left (ε * d n) 0]
    · exact add_nonneg (abs_nonneg _) (le_max_right _ _)
  have hwa := (squarefree_absolute_moment_of_one_sided witness witness_mem_orthogonal
    a (-ε) ha ha₁ (by simpa only [abs_neg] using hε) hpos).1
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (hH n)) _ (hs.add hwa)
  intro n
  change |d n| * H n ≤ |s n| * H n + |w n| * H n
  rw [← add_mul]
  apply mul_le_mul_of_nonneg_right _ (hH n)
  have he : d n = s n - w n := by rw [hw]; ring
  conv_lhs => rw [he]
  exact abs_sub _ _

/-- A finite harmonic moment on either side of the actual displacement suffices. -/
theorem riemannHypothesis_of_one_sided_displacement_harmonic_moment (ε : ℝ) (hε : |ε| = 1)
    (hd : Summable (fun n : ℕ => max (ε * signedCoefficient displacement n) 0 * (n : ℝ))) :
    RiemannHypothesis := by
  have hm := displacement_absolute_power_moment_of_one_sided 1 ε zero_lt_one le_rfl hε
    (by simpa only [Real.rpow_one] using hd)
  simp only [Real.rpow_one] at hm
  apply riemannHypothesis_of_summable_displacement_signedTail
  apply anchoredTail_summable_of_firstMoment
  apply Summable.of_norm_bounded hm
  intro n
  simp [Real.norm_eq_abs, mul_comm]

theorem riemannHypothesis_of_eventual_displacement_sign (ε : ℝ) (hε : |ε| = 1)
    (h : ∀ᶠ n : ℕ in atTop, ε * qSequence displacement n ≤ 0) : RiemannHypothesis := by
  apply riemannHypothesis_of_one_sided_displacement_harmonic_moment ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro n hn
  have hz := mul_nonpos_of_nonneg_of_nonpos (positiveQWeight_nonneg n)
    (hN n (by simpa using hn))
  have hsign : ε * signedCoefficient displacement n ≤ 0 := by
    simpa only [signedCoefficient, mul_left_comm ε (positiveQWeight n)] using hz
  simp [max_eq_right hsign]

end RiemannResearch.RH.QSquarefreeDisplacementRigidity

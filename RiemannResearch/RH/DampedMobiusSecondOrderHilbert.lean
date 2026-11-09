/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.DampedMobiusReciprocalHilbert
import RiemannResearch.RH.DampedMobiusSecondOrderPrefix
import Mathlib.Tactic.Module

/-!
# A second-order reciprocal Möbius approximation

The first-order direction is the actual smoothed Chebyshev discrepancy.
The complete Hilbert remainder is quadratic in damping, and Richardson
cancellation removes that direction without any unsmoothed-energy assumption.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.DampedMobiusSecondOrderHilbert
open Pareto ZetaTwoHilbert ZetaTwoProbability QShiftedReciprocal
open DampedMobiusReciprocalHilbert
open RiemannResearch.Analysis.PolylogTail

/-- The squared logarithmic remainder envelope belongs to the actual Q space. -/
theorem qLogSquareEnvelope_square_summable :
    Summable (fun n : ℕ => positiveQWeight n * (1 + (Real.log n)^2)^2) := by
  have hp : Summable (fun n : ℕ => (n : ℝ)^(-(3/2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  apply (hp.mul_left (4096 / Real.sqrt (Real.exp 2) / zetaTwo)).of_norm_bounded_eventually_nat
  have hlarge : ∀ᶠ n : ℕ in atTop, Real.exp 2 ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (Real.exp 2)
  filter_upwards [hlarge] with n hn
  have ha : 1 ≤ Real.exp 2 := by
    rw [Real.one_le_exp_iff]
    norm_num
  have hn1 : 1 ≤ (n : ℝ) := ha.trans hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hbase : 1 + (Real.log n)^2 ≤ (6 + Real.log n)^2 := by nlinarith
  have hsq : (1 + (Real.log n)^2)^2 ≤ (6 + Real.log n)^4 := by
    have hs := mul_self_le_mul_self (by positivity : 0 ≤ 1 + (Real.log n)^2) hbase
    nlinarith only [hs]
  have hraw := log_pow_div_sq_le 2 (a := Real.exp 2) (x := (n : ℝ)) ha hn
    (by norm_num [Real.log_exp])
  norm_num [Real.log_exp] at hraw
  rw [Real.norm_of_nonneg (mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _))]
  calc
    positiveQWeight n * (1 + (Real.log n)^2)^2 =
        ((1 + (Real.log n)^2)^2 / (n : ℝ)^2) / zetaTwo := by
      unfold positiveQWeight
      ring
    _ ≤ ((6 + Real.log n)^4 / (n : ℝ)^2) / zetaTwo :=
      div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hsq (sq_nonneg _)) zetaTwo_pos.le
    _ ≤ ((4096 / Real.sqrt (Real.exp 2)) * (n : ℝ)^(-(3/2 : ℝ))) / zetaTwo :=
      div_le_div_of_nonneg_right hraw zetaTwo_pos.le
    _ = _ := by ring

def qLogSquareEnvelopeSequence (n : ℕ) : ℝ :=
  if n = 0 then 0 else 1 + (Real.log n)^2

theorem qLogSquareEnvelopeSequence_square_summable :
    Summable (fun n : ℕ => positiveQWeight n * (qLogSquareEnvelopeSequence n)^2) := by
  apply qLogSquareEnvelope_square_summable.congr
  intro n
  by_cases hn : n = 0 <;> simp [qLogSquareEnvelopeSequence, hn, positiveQWeight]

def qLogSquareEnvelope : QHilbert :=
  encodeQ qLogSquareEnvelopeSequence qLogSquareEnvelopeSequence_square_summable

@[simp] theorem qSequence_qLogSquareEnvelope :
    qSequence qLogSquareEnvelope = qLogSquareEnvelopeSequence :=
  qSequence_encodeQ _ _ (by simp [qLogSquareEnvelopeSequence])

/-- The physical first derivative is the smoothed Chebyshev discrepancy. -/
def qChebyshevDirectionSequence (n : ℕ) : ℝ :=
  ((∑ k ∈ Finset.range (n + 1), ArithmeticFunction.vonMangoldt k) - n) /
    ((n : ℝ) + 1)

@[simp] theorem qChebyshevDirectionSequence_zero : qChebyshevDirectionSequence 0 = 0 := by
  simp [qChebyshevDirectionSequence]

theorem qChebyshevDirectionSequence_abs_le (n : ℕ) :
    |qChebyshevDirectionSequence n| ≤ qLogEnvelopeSequence n := by
  by_cases hn : n = 0
  · simp [hn, qLogEnvelopeSequence]
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hnonneg : 0 ≤ ∑ k ∈ Finset.range (n + 1), ArithmeticFunction.vonMangoldt k :=
    Finset.sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hsum : (∑ k ∈ Finset.range (n + 1), ArithmeticFunction.vonMangoldt k) ≤
      ((n : ℝ) + 1) * Real.log n := by
    calc
      _ ≤ ∑ _k ∈ Finset.range (n + 1), Real.log (n : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        by_cases hk0 : k = 0
        · simpa [hk0] using hlog
        · have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.pos_of_ne_zero hk0)
          have hkn : (k : ℝ) ≤ n := by
            exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
          exact ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hkpos hkn)
      _ = _ := by simp [Nat.cast_add, Nat.cast_one]
  have hden : 0 < (n : ℝ) + 1 := by positivity
  rw [qLogEnvelopeSequence, if_neg hn, qChebyshevDirectionSequence,
    abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).mpr
  have habs := abs_sub (∑ k ∈ Finset.range (n + 1), ArithmeticFunction.vonMangoldt k) (n : ℝ)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  simp only [abs_of_nonneg hnonneg, abs_of_nonneg hn0] at habs
  nlinarith

theorem qChebyshevDirectionSequence_square_summable :
    Summable (fun n : ℕ => positiveQWeight n * (qChebyshevDirectionSequence n)^2) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _))
    _ qLogEnvelopeSequence_square_summable
  intro n
  have hs := mul_self_le_mul_self (abs_nonneg _) (qChebyshevDirectionSequence_abs_le n)
  rw [← pow_two, sq_abs, ← pow_two] at hs
  exact mul_le_mul_of_nonneg_left hs (positiveQWeight_nonneg n)

def qChebyshevDirection : QHilbert :=
  encodeQ qChebyshevDirectionSequence qChebyshevDirectionSequence_square_summable

@[simp] theorem qSequence_qChebyshevDirection :
    qSequence qChebyshevDirection = qChebyshevDirectionSequence :=
  qSequence_encodeQ _ _ qChebyshevDirectionSequence_zero

/-- A physical envelope controls the complete Q Hilbert norm. -/
private theorem norm_le_of_coordinate_envelope {f g : QHilbert} {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ n, |qSequence f n| ≤ c * qSequence g n) :
    ‖f‖ ≤ c * ‖g‖ := by
  have hsq : ‖f‖^2 ≤ c^2 * ‖g‖^2 := by
    rw [qNorm_weighted_sq, qNorm_weighted_sq, ← tsum_mul_left]
    apply Summable.tsum_le_tsum _ (qSequence_square_summable _)
      ((qSequence_square_summable g).mul_left (c^2))
    intro n
    have hs := mul_self_le_mul_self (abs_nonneg _) (h n)
    rw [← pow_two, sq_abs, ← pow_two, mul_pow] at hs
    have hm := mul_le_mul_of_nonneg_left hs (positiveQWeight_nonneg n)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hm
  have hp : 0 ≤ c * ‖g‖ := mul_nonneg hc (norm_nonneg _)
  nlinarith [norm_nonneg f]

/-- Complete pointwise second-order remainder for the actual positive-damping family. -/
theorem dampedMobiusReciprocalQ_second_order_coordinate {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    |qSequence (dampedMobiusReciprocalQ ε hε - B qOne - ε • qChebyshevDirection) n| ≤
      ε^2 * qLogSquareEnvelopeSequence n := by
  have he : qSequence (dampedMobiusReciprocalQ ε hε - B qOne - ε • qChebyshevDirection) n =
      reciprocalDampedSequence ε ((1 / riemannZeta (1 + (ε : ℂ))).re) n -
        qOneSequence n / ((n : ℝ) + 1) - ε * qChebyshevDirectionSequence n := by
    change qSequenceLinear (dampedMobiusReciprocalQ ε hε - B qOne -
      ε • qChebyshevDirection) n = _
    rw [map_sub, map_sub, map_smul]
    change qSequence (dampedMobiusReciprocalQ ε hε) n - qSequence (B qOne) n -
      ε * qSequence qChebyshevDirection n = _
    rw [qSequence_dampedMobiusReciprocalQ, qSequence_B, qSequence_qOne,
      qSequence_qChebyshevDirection]
  rw [he]
  by_cases hn : n = 0
  · simp [hn, qOneSequence, qLogSquareEnvelopeSequence]
  · simpa only [reciprocalDampedSequence, qOneSequence, qLogSquareEnvelopeSequence,
      qChebyshevDirectionSequence, if_neg hn, mul_div_assoc] using
      dampedMobius_reciprocal_second_order hε (Nat.one_le_iff_ne_zero.mpr hn)

/-- The actual reciprocal Möbius family has a quadratic full-norm remainder. -/
theorem dampedMobiusReciprocalQ_second_order_norm_le {ε : ℝ} (hε : 0 < ε) :
    ‖dampedMobiusReciprocalQ ε hε - B qOne - ε • qChebyshevDirection‖ ≤
      ε^2 * ‖qLogSquareEnvelope‖ := by
  apply norm_le_of_coordinate_envelope (sq_nonneg ε)
  intro n
  simpa only [qSequence_qLogSquareEnvelope] using
    dampedMobiusReciprocalQ_second_order_coordinate hε n

/-- Richardson cancellation uses the actual vectors at two positive dampings. -/
def qRichardsonMobius (ε : ℝ) (hε : 0 < ε) : QHilbert :=
  (2 : ℝ) • dampedMobiusReciprocalQ (ε / 2) (by positivity) -
    dampedMobiusReciprocalQ ε hε

/-- The linear Chebyshev direction cancels; the complete error is quadratic. -/
theorem qRichardsonMobius_error_norm_le {ε : ℝ} (hε : 0 < ε) :
    ‖qRichardsonMobius ε hε - B qOne‖ ≤
      (3 / 2 : ℝ) * ‖qLogSquareEnvelope‖ * ε^2 := by
  have hh : 0 < ε / 2 := by positivity
  have hhalf := dampedMobiusReciprocalQ_second_order_norm_le hh
  have hfull := dampedMobiusReciprocalQ_second_order_norm_le hε
  have he : qRichardsonMobius ε hε - B qOne =
      (2 : ℝ) • (dampedMobiusReciprocalQ (ε / 2) hh - B qOne -
        (ε / 2) • qChebyshevDirection) -
      (dampedMobiusReciprocalQ ε hε - B qOne - ε • qChebyshevDirection) := by
    unfold qRichardsonMobius
    module
  rw [he]
  calc
    _ ≤ ‖(2 : ℝ) • (dampedMobiusReciprocalQ (ε / 2) hh - B qOne -
        (ε / 2) • qChebyshevDirection)‖ +
        ‖dampedMobiusReciprocalQ ε hε - B qOne - ε • qChebyshevDirection‖ :=
      norm_sub_le _ _
    _ = 2 * ‖dampedMobiusReciprocalQ (ε / 2) hh - B qOne -
        (ε / 2) • qChebyshevDirection‖ +
        ‖dampedMobiusReciprocalQ ε hε - B qOne - ε • qChebyshevDirection‖ := by
      rw [norm_smul]
      norm_num
    _ ≤ 2 * ((ε / 2)^2 * ‖qLogSquareEnvelope‖) + ε^2 * ‖qLogSquareEnvelope‖ :=
      add_le_add (mul_le_mul_of_nonneg_left hhalf (by norm_num)) hfull
    _ = _ := by ring

/-- The actual right difference quotient converges to the encoded Chebyshev
prime-power discrepancy, with a full-norm linear remainder. -/
theorem dampedMobiusReciprocalQ_differenceQuotient_norm_le {ε : ℝ} (hε : 0 < ε) :
    ‖ε⁻¹ • (dampedMobiusReciprocalQ ε hε - B qOne) - qChebyshevDirection‖ ≤
      ε * ‖qLogSquareEnvelope‖ := by
  have hcancel : ε⁻¹ • (ε • qChebyshevDirection) = qChebyshevDirection := by
    rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hε), one_smul]
  have he : ε⁻¹ • (dampedMobiusReciprocalQ ε hε - B qOne) - qChebyshevDirection =
      ε⁻¹ • (dampedMobiusReciprocalQ ε hε - B qOne - ε • qChebyshevDirection) := by
    calc
      _ = ε⁻¹ • (dampedMobiusReciprocalQ ε hε - B qOne) -
          ε⁻¹ • (ε • qChebyshevDirection) := by rw [hcancel]
      _ = _ := (smul_sub ε⁻¹ _ _).symm
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε)]
  calc
    _ ≤ ε⁻¹ * (ε^2 * ‖qLogSquareEnvelope‖) :=
      mul_le_mul_of_nonneg_left (dampedMobiusReciprocalQ_second_order_norm_le hε)
        (inv_nonneg.mpr hε.le)
    _ = _ := by field_simp [ne_of_gt hε] <;> ring

/-- Every positive damping schedule tending to zero has the same actual
Hilbert derivative; no unsmoothed Hilbert membership is assumed. -/
theorem dampedMobiusReciprocalQ_differenceQuotient_tendsto (ε : ℕ → ℝ)
    (hε : ∀ j, 0 < ε j) (hzero : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => (ε j)⁻¹ • (dampedMobiusReciprocalQ (ε j) (hε j) - B qOne))
      atTop (𝓝 qChebyshevDirection) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hu : Tendsto (fun j => ε j * ‖qLogSquareEnvelope‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using hzero.mul_const ‖qLogSquareEnvelope‖
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun j => dampedMobiusReciprocalQ_differenceQuotient_norm_le (hε j)) hu

end RiemannResearch.RH.DampedMobiusSecondOrderHilbert

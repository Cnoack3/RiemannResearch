/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.DampedMobiusReciprocalEnvelope
import RiemannResearch.RH.DampedMobiusDensityBounds
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.Analysis.PolylogTailProfile
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The actual reciprocal damped Mobius vector

Source: Reciprocal_Density_CRT_Nyman_Beurling_2026-11-08.pdf, Theorem 6.2,
and its logarithmic-envelope refinement. This module constructs genuine
QHilbert elements and bounds their complete norm errors. The scalar density
is kept explicit; the elementary zeta density sandwich specializes it.
No unsmoothed Hilbert limit or complete-energy growth bound is asserted.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.DampedMobiusReciprocalHilbert
open Pareto ZetaTwoHilbert ZetaTwoProbability QShiftedReciprocal
open RiemannResearch.Analysis.PolylogTail

/-- A logarithmic envelope is square integrable for the full inverse-square law. -/
theorem qLogEnvelope_square_summable :
    Summable (fun n : ℕ => positiveQWeight n * (1 + Real.log n)^2) := by
  have hp : Summable (fun n : ℕ => (n : ℝ)^(-(3/2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _))
    _ (hp.mul_left (36 / zetaTwo))
  intro n
  by_cases hn : n = 0
  · simp [hn, positiveQWeight]
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hsq : (1 + Real.log (n : ℝ))^2 ≤ (6 + Real.log (n : ℝ))^2 := by
    nlinarith
  have hraw := log_pow_div_sq_le 1 (a := 1) (x := (n : ℝ))
    (by norm_num) hn1 (by norm_num)
  norm_num at hraw
  calc
    positiveQWeight n * (1 + Real.log n)^2 =
        ((1 + Real.log n)^2 / (n : ℝ)^2) / zetaTwo := by
      unfold positiveQWeight
      ring
    _ ≤ ((6 + Real.log n)^2 / (n : ℝ)^2) / zetaTwo :=
      div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hsq (sq_nonneg _)) zetaTwo_pos.le
    _ ≤ (36 * (n : ℝ)^(-(3/2 : ℝ))) / zetaTwo :=
      div_le_div_of_nonneg_right hraw zetaTwo_pos.le
    _ = (36 / zetaTwo) * (n : ℝ)^(-(3/2 : ℝ)) := by ring

def qLogEnvelopeSequence (n : ℕ) : ℝ := if n = 0 then 0 else 1 + Real.log n

theorem qLogEnvelopeSequence_square_summable :
    Summable (fun n : ℕ => positiveQWeight n * (qLogEnvelopeSequence n)^2) := by
  apply qLogEnvelope_square_summable.congr
  intro n
  by_cases hn : n = 0 <;> simp [qLogEnvelopeSequence, hn, positiveQWeight]

def qLogEnvelope : QHilbert :=
  encodeQ qLogEnvelopeSequence qLogEnvelopeSequence_square_summable

@[simp] theorem qSequence_qLogEnvelope : qSequence qLogEnvelope = qLogEnvelopeSequence :=
  qSequence_encodeQ _ _ (by simp [qLogEnvelopeSequence])

/-- The exact reciprocal arithmetic expression, anchored at physical zero. -/
def reciprocalDampedSequence (ε c : ℝ) (n : ℕ) : ℝ :=
  (dampedMobiusPrefix ε n - (n : ℝ) * c) / ((n : ℝ) + 1)

@[simp] theorem reciprocalDampedSequence_zero (ε c : ℝ) :
    reciprocalDampedSequence ε c 0 = 0 := by
  simp [reciprocalDampedSequence, dampedMobiusPrefix, arithmeticFloorPrefix]

theorem dampedMobiusPrefix_bounds {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    0 ≤ dampedMobiusPrefix ε n ∧ dampedMobiusPrefix ε n ≤ n := by
  rw [← dampedDivisorCoefficient_sum_Icc]
  constructor
  · exact Finset.sum_nonneg (fun k _ => dampedDivisorCoefficient_nonneg hε k)
  · calc
      _ ≤ ∑ _k ∈ Finset.Icc 1 n, (1 : ℝ) :=
        Finset.sum_le_sum (fun k _ => dampedDivisorCoefficient_le_one hε k)
      _ = _ := by simp

/-- Existence of the smoothed Hilbert vector does not require unsmoothed energy. -/
theorem reciprocalDampedSequence_abs_le {ε : ℝ} (hε : 0 ≤ ε) (c : ℝ) (n : ℕ) :
    |reciprocalDampedSequence ε c n| ≤ 1 + |c| := by
  obtain ⟨hlo, hup⟩ := dampedMobiusPrefix_bounds hε n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hd : 0 < (n : ℝ) + 1 := by positivity
  rw [reciprocalDampedSequence, abs_div, abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  have habs := abs_sub (dampedMobiusPrefix ε n) ((n : ℝ) * c)
  rw [abs_of_nonneg hlo, abs_mul, abs_of_nonneg hn0] at habs
  nlinarith [abs_nonneg c]

def reciprocalDampedQ (ε c : ℝ) (hε : 0 ≤ ε) : QHilbert :=
  encodeQ (reciprocalDampedSequence ε c)
    (boundedQ_square_summable _ (1 + |c|) (by positivity)
      (reciprocalDampedSequence_abs_le hε c))

@[simp] theorem qSequence_reciprocalDampedQ (ε c : ℝ) (hε : 0 ≤ ε) :
    qSequence (reciprocalDampedQ ε c hε) = reciprocalDampedSequence ε c :=
  qSequence_encodeQ _ _ (reciprocalDampedSequence_zero ε c)

theorem reciprocalDampedQ_error_coordinate {ε c : ℝ}
    (hε : 0 ≤ ε) (hc : 0 ≤ c) (hcε : c ≤ ε) (n : ℕ) :
    |qSequence (reciprocalDampedQ ε c hε - B qOne) n| ≤
      ε * qLogEnvelopeSequence n := by
  have he : qSequence (reciprocalDampedQ ε c hε - B qOne) n =
      reciprocalDampedSequence ε c n - qOneSequence n / ((n : ℝ) + 1) := by
    change qSequenceLinear (reciprocalDampedQ ε c hε - B qOne) n = _
    rw [map_sub]
    change qSequence (reciprocalDampedQ ε c hε) n - qSequence (B qOne) n = _
    rw [qSequence_reciprocalDampedQ, qSequence_B, qSequence_qOne]
  rw [he]
  by_cases hn : n = 0
  · simp [hn, qOneSequence, qLogEnvelopeSequence]
  · simpa only [reciprocalDampedSequence, qOneSequence, qLogEnvelopeSequence,
      if_neg hn] using dampedMobius_reciprocal_error_le_log hε hc hcε
        (Nat.one_le_iff_ne_zero.mpr hn)

/-- Complete quadratic error, with an unconditional finite envelope constant. -/
theorem reciprocalDampedQ_error_norm_sq_le {ε c : ℝ}
    (hε : 0 ≤ ε) (hc : 0 ≤ c) (hcε : c ≤ ε) :
    ‖reciprocalDampedQ ε c hε - B qOne‖^2 ≤ ε^2 * ‖qLogEnvelope‖^2 := by
  rw [qNorm_weighted_sq, qNorm_weighted_sq, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _ (qSequence_square_summable _)
    ((qSequence_square_summable qLogEnvelope).mul_left (ε^2))
  intro n
  have h := reciprocalDampedQ_error_coordinate hε hc hcε n
  have hs := mul_self_le_mul_self (abs_nonneg _) h
  rw [← pow_two, sq_abs, ← pow_two, mul_pow] at hs
  have hm := mul_le_mul_of_nonneg_left hs (positiveQWeight_nonneg n)
  simpa only [qSequence_qLogEnvelope, mul_assoc, mul_left_comm, mul_comm] using hm

/-- The norm rate is linear in positive damping. -/
theorem reciprocalDampedQ_error_norm_le {ε c : ℝ}
    (hε : 0 ≤ ε) (hc : 0 ≤ c) (hcε : c ≤ ε) :
    ‖reciprocalDampedQ ε c hε - B qOne‖ ≤ ε * ‖qLogEnvelope‖ := by
  have hs := reciprocalDampedQ_error_norm_sq_le hε hc hcε
  have hp : 0 ≤ ε * ‖qLogEnvelope‖ := mul_nonneg hε (norm_nonneg _)
  nlinarith [norm_nonneg (reciprocalDampedQ ε c hε - B qOne)]

/-- Only positive damping and the scalar density bound are used in this strong limit. -/
theorem reciprocalDampedQ_tendsto (ε c : ℕ → ℝ)
    (hε : ∀ j, 0 ≤ ε j) (hc : ∀ j, 0 ≤ c j) (hcε : ∀ j, c j ≤ ε j)
    (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => reciprocalDampedQ (ε j) (c j) (hε j)) atTop (𝓝 (B qOne)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hu : Tendsto (fun j => ε j * ‖qLogEnvelope‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using hlim.mul_const ‖qLogEnvelope‖
  exact squeeze_zero (fun j => norm_nonneg _) (fun j =>
    reciprocalDampedQ_error_norm_le (hε j) (hc j) (hcε j)) hu

/-- The actual positive-damping reciprocal Möbius vector, with its zeta density. -/
def dampedMobiusReciprocalQ (ε : ℝ) (hε : 0 < ε) : QHilbert :=
  reciprocalDampedQ ε ((1 / riemannZeta (1 + (ε : ℂ))).re) hε.le

@[simp] theorem qSequence_dampedMobiusReciprocalQ (ε : ℝ) (hε : 0 < ε) :
    qSequence (dampedMobiusReciprocalQ ε hε) =
      reciprocalDampedSequence ε ((1 / riemannZeta (1 + (ε : ℂ))).re) :=
  qSequence_reciprocalDampedQ ε _ hε.le

/-- The PDF's reciprocal strong limit has an unconditional linear damping rate. -/
theorem dampedMobiusReciprocalQ_error_norm_le {ε : ℝ} (hε : 0 < ε) :
    ‖dampedMobiusReciprocalQ ε hε - B qOne‖ ≤ ε * ‖qLogEnvelope‖ := by
  obtain ⟨hc, hcε⟩ := dampedMobius_density_bounds hε
  exact reciprocalDampedQ_error_norm_le hε.le hc hcε

/-- The complete squared norm error tends to zero at least quadratically. -/
theorem dampedMobiusReciprocalQ_error_norm_sq_le {ε : ℝ} (hε : 0 < ε) :
    ‖dampedMobiusReciprocalQ ε hε - B qOne‖^2 ≤ ε^2 * ‖qLogEnvelope‖^2 := by
  obtain ⟨hc, hcε⟩ := dampedMobius_density_bounds hε
  exact reciprocalDampedQ_error_norm_sq_le hε.le hc hcε

/-- For every positive damping schedule tending to zero, the actual reciprocal
Möbius vectors converge strongly to the reciprocal constant target. -/
theorem dampedMobiusReciprocalQ_tendsto (ε : ℕ → ℝ)
    (hε : ∀ j, 0 < ε j) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => dampedMobiusReciprocalQ (ε j) (hε j)) atTop
      (𝓝 (B qOne)) := by
  exact reciprocalDampedQ_tendsto ε
    (fun j => (1 / riemannZeta (1 + (ε j : ℂ))).re)
    (fun j => (hε j).le)
    (fun j => (dampedMobius_density_bounds (hε j)).1)
    (fun j => (dampedMobius_density_bounds (hε j)).2) hlim

end RiemannResearch.RH.DampedMobiusReciprocalHilbert

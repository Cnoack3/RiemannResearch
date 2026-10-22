/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QRationalCoprimeLegality
import RiemannResearch.RH.QRationalCoprimeMinimum
import RiemannResearch.RH.QRationalMinimumLimit
import RiemannResearch.RH.QSquarefreePrimorialCofinality
import RiemannResearch.RH.SquarefreeStageExhaustion
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Primorial
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Signed tails of the actual rational minimizers

Source: user-provided RH/CRT research handoff, 20 October 2026, Section 8.
The exact coprime signed identity is specialized to the actual selected
divisor normal-equation solution. Its arithmetic endpoint tends to zero,
so the signed tail tends to minus zeta(2) times the squared closed-span Q
defect. If that defect is positive, the signed tail/error ratio tends to -1.
No asymptotic cancellation or optimizer coefficient bound is assumed.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QRationalCoprimeTail
open ZetaTwoHilbert ZetaTwoProbability
open QSquarefreePrimorialCofinality QSquarefreeInverseCapacity
open Pareto.SquarefreeStageExhaustion

/-- The existing signed-tail functional at the actual rational minimizer. -/
def rationalSignedTail (L : ℕ) : ℝ :=
  signedTail L (divisorFit L (rationalCoefficients L))

/-- The complete signed identity, including its arithmetic endpoint. -/
theorem rationalMinimum_signedTail_exact (L : ℕ) (hL : 0 < L) :
    rationalMinimum L + rationalSignedTail L =
      5 * (Nat.totient L : ℝ) / (3 * (L : ℝ)^2) :=
  signed_identity_of_divisor_synthesis L hL
    (divisorFit L (rationalCoefficients L)) (rationalCoefficients L)
    (fun _ => rfl) (rationalCoefficients_normal L)

theorem rationalCoprimeBoundary_bounds (L : ℕ) (hL : 0 < L) :
    0 ≤ 5 * (Nat.totient L : ℝ) / (3 * (L : ℝ)^2) ∧
      5 * (Nat.totient L : ℝ) / (3 * (L : ℝ)^2) ≤ 5 / (3 * (L : ℝ)) := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hφ : (Nat.totient L : ℝ) ≤ L := by exact_mod_cast Nat.totient_le L
  constructor
  · positivity
  · calc
      5 * (Nat.totient L : ℝ) / (3 * (L : ℝ)^2) ≤
          5 * (L : ℝ) / (3 * (L : ℝ)^2) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hφ (by norm_num)) (by positivity)
      _ = 5 / (3 * (L : ℝ)) := by
        field_simp [ne_of_gt hLR]
        <;> ring

theorem rationalCoprimeBoundary_tendsto_zero :
    Tendsto (fun n =>
      5 * (Nat.totient (primorialPeriod n) : ℝ) / (3 * (primorialPeriod n : ℝ)^2))
      atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun n =>
      ha.trans_le (rationalCoprimeBoundary_bounds _ (primorialPeriod_pos n)).1
  · intro b hb
    obtain ⟨N, hN⟩ := exists_nat_gt (5 / (3 * b))
    filter_upwards [eventually_ge_atTop N] with n hn
    have hNL : N ≤ primorialPeriod n :=
      hn.trans ((Nat.le_add_right n 3).trans le_primorial_self)
    have hNLR : (N : ℝ) ≤ primorialPeriod n := by exact_mod_cast hNL
    have hLR : (0 : ℝ) < primorialPeriod n := by
      exact_mod_cast primorialPeriod_pos n
    have hu : 5 / (3 * (primorialPeriod n : ℝ)) < b := by
      apply (div_lt_iff₀ (show 0 < 3 * (primorialPeriod n : ℝ) by positivity)).mpr
      have hmul := (div_lt_iff₀ (show 0 < 3 * b by positivity)).mp
        (hN.trans_le hNLR)
      nlinarith
    exact (rationalCoprimeBoundary_bounds _ (primorialPeriod_pos n)).2.trans_lt hu

/-- The actual signed tail has the opposite limit to the actual minimum. -/
theorem rationalSignedTail_tendsto :
    Tendsto (fun n => rationalSignedTail (primorialPeriod n)) atTop
      (𝓝 (-(zetaTwo * ‖qOne -
        qSquarefreeCRTSpan.topologicalClosure.starProjection qOne‖^2))) := by
  have hfun : (fun n => rationalSignedTail (primorialPeriod n)) =
      (fun n => 5 * (Nat.totient (primorialPeriod n) : ℝ) /
        (3 * (primorialPeriod n : ℝ)^2) - rationalMinimum (primorialPeriod n)) := by
    funext n
    have he := rationalMinimum_signedTail_exact _ (primorialPeriod_pos n)
    linarith
  rw [hfun]
  simpa only [zero_sub] using
    rationalCoprimeBoundary_tendsto_zero.sub rationalMinimum_tendsto

theorem rationalMinimum_primorial_pos (n : ℕ) :
    0 < rationalMinimum (primorialPeriod n) :=
  (mul_pos zetaTwo_pos (primorialError_pos n)).trans_le (rationalMinimum_lower n)

/-- Exact signed-tail/error ratio, retaining the endpoint correction. -/
theorem rationalSignedTail_ratio_exact (n : ℕ) :
    rationalSignedTail (primorialPeriod n) / rationalMinimum (primorialPeriod n) + 1 =
      (5 * (Nat.totient (primorialPeriod n) : ℝ) /
        (3 * (primorialPeriod n : ℝ)^2)) / rationalMinimum (primorialPeriod n) := by
  have hE := ne_of_gt (rationalMinimum_primorial_pos n)
  have he := rationalMinimum_signedTail_exact _ (primorialPeriod_pos n)
  apply (eq_div_iff hE).mpr
  calc
    (rationalSignedTail (primorialPeriod n) / rationalMinimum (primorialPeriod n) + 1) *
        rationalMinimum (primorialPeriod n) =
        rationalSignedTail (primorialPeriod n) + rationalMinimum (primorialPeriod n) := by
      field_simp [hE]
    _ = _ := by linarith

/-- A positive limiting Q defect forces full asymptotic signed cancellation. -/
theorem rationalSignedTail_div_minimum_tendsto
    (hdefect : 0 < ‖qOne -
      qSquarefreeCRTSpan.topologicalClosure.starProjection qOne‖^2) :
    Tendsto (fun n => rationalSignedTail (primorialPeriod n) /
      rationalMinimum (primorialPeriod n)) atTop (𝓝 (-1 : ℝ)) := by
  have hne : zetaTwo * ‖qOne -
      qSquarefreeCRTSpan.topologicalClosure.starProjection qOne‖^2 ≠ 0 :=
    ne_of_gt (mul_pos zetaTwo_pos hdefect)
  have ht := rationalSignedTail_tendsto.div rationalMinimum_tendsto hne
  change Tendsto (fun n => rationalSignedTail (primorialPeriod n) /
      rationalMinimum (primorialPeriod n)) atTop
    (𝓝 ((-(zetaTwo * ‖qOne -
      qSquarefreeCRTSpan.topologicalClosure.starProjection qOne‖^2)) /
      (zetaTwo * ‖qOne -
        qSquarefreeCRTSpan.topologicalClosure.starProjection qOne‖^2))) at ht
  simpa only [neg_div, div_self hne] using ht

/-- Vanishing of the signed tail is the same unresolved closure obligation
as vanishing of the rational minimum. -/
theorem rationalSignedTail_tendsto_zero_iff :
    Tendsto (fun n => rationalSignedTail (primorialPeriod n)) atTop (𝓝 0) ↔
      qOne ∈ qSquarefreeCRTSpan.topologicalClosure := by
  constructor
  · intro hz
    have he := tendsto_nhds_unique rationalSignedTail_tendsto hz
    have hzero : zetaTwo * ‖qOne -
        qSquarefreeCRTSpan.topologicalClosure.starProjection qOne‖^2 = 0 :=
      neg_eq_zero.mp he
    have hmin : Tendsto (fun n => rationalMinimum (primorialPeriod n)) atTop (𝓝 0) := by
      simpa only [hzero] using rationalMinimum_tendsto
    exact rationalMinimum_tendsto_zero_iff.mp hmin
  · intro hm
    have he : -(zetaTwo * ‖qOne -
        qSquarefreeCRTSpan.topologicalClosure.starProjection qOne‖^2) = 0 := by
      rw [Submodule.starProjection_eq_self_iff.mpr hm, sub_self, norm_zero]
      ring
    simpa only [he] using rationalSignedTail_tendsto

end RiemannResearch.RH.QRationalCoprimeTail

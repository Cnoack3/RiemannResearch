/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.NumberTheory.PrimorialPolynomialLower
import RiemannResearch.RH.QRationalCoprimeLower
import RiemannResearch.RH.QRationalMinimumLimit
import RiemannResearch.RH.QRationalSignedTailLimit
import RiemannResearch.RH.SquarefreeStageExhaustion
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Unconditional signed-tail cancellation for the actual rational minimizers

Source: `QRationalTailFluctuationResearch20261020.md`, Section 5, with an
all-cutoff three-interval Bertrand bound replacing prime-index bookkeeping.
This gives S/R -> -1 without assuming a positive limiting Q defect.
It does not determine whether R tends to zero and does not assert RH.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QRationalCoprimeTail
open Pareto.SquarefreeStageExhaustion
open RiemannResearch.NumberTheory.PrimorialPolynomialLower

/-- An explicit all-cutoff bound for the exact normalized boundary term. -/
theorem rationalSignedTail_ratio_primorial_bounds (n : ℕ) (hn : 21 ≤ n) :
    0 ≤ rationalSignedTail (primorialPeriod n) / rationalMinimum (primorialPeriod n) + 1 ∧
    rationalSignedTail (primorialPeriod n) / rationalMinimum (primorialPeriod n) + 1 ≤
      1280 / (3 * (((n + 3) / 8 : ℕ) : ℝ)) := by
  let x := n + 3
  let k := x / 8
  let L := primorialPeriod n
  have hx : 24 ≤ x := by dsimp [x]; omega
  have hk : 3 ≤ k := by dsimp [k]; omega
  have hxk : x ≤ 16 * k := by dsimp [k]; omega
  have hLpos : 0 < L := primorialPeriod_pos n
  have hcube : 8 * k ^ 3 ≤ L :=
    eight_mul_floor_cube_le_primorial x (by omega)
  obtain ⟨q, hq, hxq, hq2⟩ := Nat.exists_prime_lt_and_le_two_mul x (by omega)
  have hq32 : q ≤ 32 * k := by omega
  have hk2 : 9 ≤ k ^ 2 := by nlinarith
  have hk3 : 9 * k ≤ k ^ 3 := by
    have hh := Nat.mul_le_mul_left k hk2
    nlinarith
  have hqL : q < L := by nlinarith
  have hcop : Nat.Coprime q L := hq.coprime_iff_not_dvd.mpr (by
    intro hd
    have hh := hq.dvd_primorial_iff.mp hd
    omega)
  have hqsq : q ^ 2 ≤ 1024 * k ^ 2 := by
    have hh := Nat.mul_self_le_mul_self hq32
    nlinarith
  have hqk : q ^ 2 * k ≤ 128 * L := by
    have hh := Nat.mul_le_mul_right k hqsq
    nlinarith
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hqkR : (q : ℝ) ^ 2 * (k : ℝ) ≤ 128 * (L : ℝ) := by
    exact_mod_cast hqk
  have hR := rationalMinimum_primorial_pos n
  change 0 < rationalMinimum L at hR
  have hs := rationalSignedTail_near_negative_minimum L q (by omega) hqL hcop
  have hu : rationalSignedTail L / rationalMinimum L ≤
      -1 + 10 * (q : ℝ) ^ 2 / (3 * (L : ℝ)) := by
    apply (div_le_iff₀ hR).mpr
    nlinarith
  have hu' : 10 * (q : ℝ) ^ 2 / (3 * (L : ℝ)) ≤ 1280 / (3 * (k : ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  constructor
  · rw [rationalSignedTail_ratio_exact]
    exact div_nonneg (rationalCoprimeBoundary_bounds _ (primorialPeriod_pos n)).1 hR.le
  · change rationalSignedTail L / rationalMinimum L + 1 ≤ 1280 / (3 * (k : ℝ))
    linarith

/-- Full asymptotic cancellation holds even if the limiting minimum is zero. -/
theorem rationalSignedTail_div_minimum_tendsto_unconditional :
    Tendsto (fun n => rationalSignedTail (primorialPeriod n) /
      rationalMinimum (primorialPeriod n)) atTop (𝓝 (-1 : ℝ)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => by
      have he := rationalSignedTail_ratio_exact n
      have hb := div_nonneg
        (rationalCoprimeBoundary_bounds _ (primorialPeriod_pos n)).1
        (rationalMinimum_primorial_pos n).le
      linarith
  · intro b hb
    have hb' : 0 < b + 1 := by linarith
    obtain ⟨N, hN⟩ := exists_nat_gt (1280 / (3 * (b + 1)))
    filter_upwards [eventually_ge_atTop (max 21 (8 * N))] with n hn
    have hn21 : 21 ≤ n := (le_max_left _ _).trans hn
    have hNk : N ≤ (n + 3) / 8 := by
      have hh := (le_max_right 21 (8 * N)).trans hn
      omega
    have hkpos : (0 : ℝ) < (((n + 3) / 8 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < (n + 3) / 8 by omega)
    have hNkR : (N : ℝ) ≤ (((n + 3) / 8 : ℕ) : ℝ) := by exact_mod_cast hNk
    have hsmall : 1280 / (3 * (((n + 3) / 8 : ℕ) : ℝ)) < b + 1 := by
      apply (div_lt_iff₀ (by positivity)).mpr
      have hh := (div_lt_iff₀ (by positivity : 0 < 3 * (b + 1))).mp
        (hN.trans_le hNkR)
      nlinarith
    have hu := (rationalSignedTail_ratio_primorial_bounds n hn21).2
    linarith

end RiemannResearch.RH.QRationalCoprimeTail

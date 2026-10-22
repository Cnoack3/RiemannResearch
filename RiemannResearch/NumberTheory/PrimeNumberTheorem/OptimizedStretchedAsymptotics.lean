/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Eventual cutoff geometry and contraction for the optimized
stretched-exponential profile (s log s)^(1/11). -/

noncomputable section
open Filter Asymptotics
open scoped Topology

namespace RiemannResearch.NumberTheory.PrimeNumberTheorem

theorem optimized_stretched_geometry_atTop (K d : ℝ)
    (hK : 0 ≤ K) (hd : 0 < d) (hdsmall : d ≤ 1 / 100) :
    ∀ᶠ s : ℝ in atTop,
      let z := (s * Real.log s) ^ ((1 : ℝ) / 11)
      let L := z ^ 10
      12 ≤ s ∧ 1 ≤ z ∧ 2 * (Real.log s + 1) ≤ z ∧
        s / 2 ≤ s - L - Real.log 2 ∧
        ((3 * L + K) / (s - 6)) * Real.exp (2 * d * (Real.log s + 1)) ≤ 1 / 2 := by
  let a : ℝ := (1 : ℝ) / 11 - 2 * d
  have ha : 0 < a := by dsimp [a]; linarith
  have ha' : 0 < 1 - 2 * d := by linarith
  have hlogsmall := (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 11)).bound (by norm_num : (0 : ℝ) < 1 / 4)
  have hlogpower := (isLittleO_log_rpow_rpow_atTop ((10 : ℝ) / 11) ha).bound
    (by positivity : (0 : ℝ) < 1 / (24 * Real.exp (2 * d)))
  have hKpower := (tendsto_rpow_atTop ha').eventually
    (eventually_ge_atTop (8 * (K + 1) * Real.exp (2 * d)))
  filter_upwards [eventually_ge_atTop (12 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    hlogsmall, hlogpower, hKpower] with s hs hslog hsmall hpower hKpow
  let z : ℝ := (s * Real.log s) ^ ((1 : ℝ) / 11)
  let L : ℝ := z ^ 10
  change 12 ≤ s ∧ 1 ≤ z ∧ 2 * (Real.log s + 1) ≤ z ∧
    s / 2 ≤ s - L - Real.log 2 ∧
    ((3 * L + K) / (s - 6)) * Real.exp (2 * d * (Real.log s + 1)) ≤ 1 / 2
  have hs0 : 0 < s := by linarith
  have hlog0 : 0 ≤ Real.log s := by linarith
  have hprod0 : 0 ≤ s * Real.log s := mul_nonneg hs0.le hlog0
  have hz0 : 0 ≤ z := Real.rpow_nonneg hprod0 _
  have hL0 : 0 ≤ L := pow_nonneg hz0 _
  have hsmall' : Real.log s ≤ (1 / 4 : ℝ) * s ^ ((1 : ℝ) / 11) := by
    simpa only [Real.rpow_one, Real.norm_eq_abs,
      abs_of_nonneg hlog0,
      abs_of_nonneg (Real.rpow_nonneg hs0.le ((1 : ℝ) / 11))] using hsmall
  have hpower' : (Real.log s) ^ ((10 : ℝ) / 11) ≤
      (1 / (24 * Real.exp (2 * d))) * s ^ a := by
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hlog0 ((10 : ℝ) / 11)),
      abs_of_nonneg (Real.rpow_nonneg hs0.le a)] using hpower
  have hprod : s ≤ s * Real.log s := by nlinarith
  have hsz : s ^ ((1 : ℝ) / 11) ≤ z :=
    Real.rpow_le_rpow hs0.le hprod (by norm_num)
  have hhead : 2 * (Real.log s + 1) ≤ z := by linarith
  have hz1 : 1 ≤ z := by linarith
  have hexp : Real.exp (2 * d * (Real.log s + 1)) =
      Real.exp (2 * d) * s ^ (2 * d) := by
    rw [Real.rpow_def_of_pos hs0, ← Real.exp_add]
    congr 1
    ring
  have hL : L = s ^ ((10 : ℝ) / 11) * (Real.log s) ^ ((10 : ℝ) / 11) := by
    dsimp [L, z]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hprod0]
    convert (Real.mul_rpow (z := (10 : ℝ) / 11) hs0.le hlog0) using 1 <;> norm_num
  have hpowercancel :
      s ^ ((10 : ℝ) / 11 + 2 * d) * s ^ a = s := by
    rw [← Real.rpow_add hs0,
      show (10 : ℝ) / 11 + 2 * d + a = 1 by dsimp [a]; ring,
      Real.rpow_one]
  have hconstcancel : Real.exp (2 * d) * (1 / (24 * Real.exp (2 * d))) = (1 : ℝ) / 24 := by
    field_simp
  have hLscaled : L * Real.exp (2 * d * (Real.log s + 1)) ≤ s / 24 := by
    calc
      _ = Real.exp (2 * d) * s ^ ((10 : ℝ) / 11 + 2 * d) *
          (Real.log s) ^ ((10 : ℝ) / 11) := by
        rw [hL, hexp, Real.rpow_add hs0]
        ring
      _ ≤ Real.exp (2 * d) * s ^ ((10 : ℝ) / 11 + 2 * d) *
          ((1 / (24 * Real.exp (2 * d))) * s ^ a) :=
        mul_le_mul_of_nonneg_left hpower' (by positivity)
      _ = (Real.exp (2 * d) * (1 / (24 * Real.exp (2 * d)))) *
          (s ^ ((10 : ℝ) / 11 + 2 * d) * s ^ a) := by ring
      _ = s / 24 := by rw [hconstcancel, hpowercancel]; ring
  have hKweighted : 8 * (K + 1) * (Real.exp (2 * d) * s ^ (2 * d)) ≤ s := by
    calc
      _ = (8 * (K + 1) * Real.exp (2 * d)) * s ^ (2 * d) := by ring
      _ ≤ s ^ (1 - 2 * d) * s ^ (2 * d) :=
        mul_le_mul_of_nonneg_right hKpow (Real.rpow_nonneg hs0.le _)
      _ = s := by
        rw [← Real.rpow_add hs0, show 1 - 2 * d + 2 * d = 1 by ring, Real.rpow_one]
  have hKscaled : K * Real.exp (2 * d * (Real.log s + 1)) ≤ s / 8 := by
    rw [hexp]
    have hE0 : 0 ≤ Real.exp (2 * d) * s ^ (2 * d) := by positivity
    nlinarith
  have hE1 : 1 ≤ Real.exp (2 * d * (Real.log s + 1)) :=
    Real.one_le_exp_iff.mpr (by nlinarith)
  have hLsmall : L ≤ s / 24 :=
    (le_mul_of_one_le_right hL0 hE1).trans hLscaled
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hshift : s / 2 ≤ s - L - Real.log 2 := by linarith
  refine ⟨hs, hz1, hhead, hshift, ?_⟩
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (show 0 < s - 6 by linarith)).2
  nlinarith [hLscaled, hKscaled]

theorem optimized_stretched_cutoff_atTop (K d : ℝ)
    (hK : 0 ≤ K) (hd : 0 < d) (hdsmall : d ≤ 1 / 100) :
    ∀ᶠ T : ℝ in atTop,
      let s := T + 6
      let z := (s * Real.log s) ^ ((1 : ℝ) / 11)
      let L := z ^ 10
      6 ≤ T ∧ 1 ≤ z ∧ 2 * (Real.log s + 1) ≤ z ∧
        s / 2 ≤ s - L - Real.log 2 ∧
        ((3 * L + K) / T) * Real.exp (2 * d * (Real.log s + 1)) ≤ 1 / 2 := by
  obtain ⟨S, hS⟩ := eventually_atTop.mp
    (optimized_stretched_geometry_atTop K d hK hd hdsmall)
  filter_upwards [eventually_ge_atTop S] with T hT
  have hh := hS (T + 6) (by linarith : S ≤ T + 6)
  dsimp only at hh ⊢
  refine ⟨by linarith [hh.1], hh.2.1, hh.2.2.1, hh.2.2.2.1, ?_⟩
  simpa only [add_sub_cancel_right] using hh.2.2.2.2

end RiemannResearch.NumberTheory.PrimeNumberTheorem

/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.Consequences
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! # Actual von Mangoldt second moments from the prime number theorem

Source: the user-provided Montgomery_SC_Proof_Plan_2026-11-16.md, Section 5,
for the classical second-moment target. The proof is a direct squeeze:
the upper bound uses every von Mangoldt term, and the lower bound uses
primes in (δN,N]. The repository's proved PNT and Chebyshev asymptotic
supply both limits; δ is then allowed to approach zero.

Proper prime powers remain in squareMass throughout. No prime-pair,
short-interval, RH, or Montgomery cancellation hypothesis is used.
The centered version supplies the unshifted diagonal input for short
prime windows.
-/

open Filter Finset
open scoped Topology ArithmeticFunction BigOperators
namespace RiemannResearch.Analysis.MangoldtSquareAsymptotic
open RiemannResearch.NumberTheory.PrimeNumberTheorem

noncomputable def squareMass (N : ℕ) : ℝ := ∑ n ∈ Iic N, (Λ n) ^ 2

theorem squareMass_nonneg (N : ℕ) : 0 ≤ squareMass N :=
  sum_nonneg fun _ _ => sq_nonneg _

theorem squareMass_upper (N : ℕ) :
    squareMass N ≤ Real.log N * (∑ n ∈ Iic N, Λ n) := by
  rw [mul_sum]
  apply sum_le_sum
  intro n hn
  by_cases hn0 : n = 0
  · simp [hn0]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
  have hle : (n : ℝ) ≤ N := by exact_mod_cast (mem_Iic.mp hn)
  have hl := Real.log_le_log hnpos hle
  have hv := ArithmeticFunction.vonMangoldt_le_log (n := n)
  have hnΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  nlinarith

theorem squareMass_lower (N : ℕ) (A : ℝ) (hA : 0 < A) (hAN : A ≤ N) :
    Real.log A * (Chebyshev.theta N - Chebyshev.theta A) ≤ squareMass N := by
  have hs : (Nat.floor A).primesLE ⊆ N.primesLE := by
    intro p hp
    simp only [Nat.mem_primesLE] at hp ⊢
    have hfloor : Nat.floor A ≤ N := by
      exact_mod_cast (Nat.floor_le hA.le).trans hAN
    exact ⟨hp.1.trans hfloor, hp.2⟩
  rw [Chebyshev.theta_eq_theta_coe_floor A,
    Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
  rw [← sum_sdiff_eq_sub hs, mul_sum]
  calc
    _ ≤ ∑ p ∈ N.primesLE \ (Nat.floor A).primesLE, (Λ p)^2 := by
      apply sum_le_sum
      intro p hp
      have hpn := Nat.mem_primesLE.mp (mem_sdiff.mp hp).1
      have hpa : A < (p : ℝ) := by
        by_contra h
        have hpf : p ≤ Nat.floor A := Nat.le_floor (le_of_not_gt h)
        exact (mem_sdiff.mp hp).2 (Nat.mem_primesLE.mpr ⟨hpf, hpn.2⟩)
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpn.2.pos
      have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpn.2.one_lt.le)
      have hlog := Real.log_le_log hA hpa.le
      rw [ArithmeticFunction.vonMangoldt_apply_prime hpn.2]
      nlinarith
    _ ≤ squareMass N := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact mem_Iic.mpr (Nat.mem_primesLE.mp (mem_sdiff.mp hp).1).1
      · intro p hp _
        exact sq_nonneg _

theorem theta_ratio_tendsto :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) := by
  exact (Asymptotics.isEquivalent_iff_tendsto_one (by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact hx.ne')).mp chebyshev_asymptotic

theorem theta_scaled_ratio_tendsto (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => Chebyshev.theta (δ * N) / N) atTop (𝓝 δ) := by
  have ht : Tendsto (fun N : ℕ => δ * (N : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hδ
  have hh := (theta_ratio_tendsto.comp ht).const_mul δ
  simp only [mul_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  dsimp only [Function.comp_apply]
  field_simp [hδ.ne']

theorem log_scaled_ratio_tendsto (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => Real.log (δ * N) / Real.log N) atTop (𝓝 1) := by
  have hl : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have he : Tendsto (fun N : ℕ => Real.log δ / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hl
  have hh := he.add_const 1
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hlog0 : Real.log N ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < N by omega)))
  rw [Real.log_mul hδ.ne' hN0]
  field_simp

theorem lower_ratio_tendsto (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun N : ℕ =>
      (Real.log (δ * N) / Real.log N) *
      (Chebyshev.theta N / N - Chebyshev.theta (δ * N) / N))
      atTop (𝓝 (1 - δ)) := by
  simpa only [one_mul, Function.comp_apply] using (log_scaled_ratio_tendsto δ hδ).mul
    ((theta_ratio_tendsto.comp (tendsto_natCast_atTop_atTop (R := ℝ))).sub
      (theta_scaled_ratio_tendsto δ hδ))

/-- Actual von Mangoldt squares, including every proper prime power. -/
theorem squareMass_ratio_tendsto :
    Tendsto (fun N : ℕ => squareMass N / ((N : ℝ) * Real.log N))
      atTop (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨δ, hδ, hδmax⟩ := exists_between
      (lt_min (by norm_num : (0 : ℝ) < 1) (sub_pos.mpr ha))
    have hδ1 : δ < 1 := (lt_min_iff.mp hδmax).1
    have hδa : a < 1 - δ := by linarith [(lt_min_iff.mp hδmax).2]
    have hlo := (lower_ratio_tendsto δ hδ).eventually (eventually_gt_nhds hδa)
    filter_upwards [hlo, eventually_ge_atTop 2] with N hlo hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hlow := div_le_div_of_nonneg_right
      (squareMass_lower N (δ * N) (mul_pos hδ hN0) (by nlinarith))
      (show 0 ≤ (N : ℝ) * Real.log N by positivity)
    have hid : (Real.log (δ * N) / Real.log N) *
        (Chebyshev.theta N / N - Chebyshev.theta (δ * N) / N) =
        (Real.log (δ * N) * (Chebyshev.theta N - Chebyshev.theta (δ * N))) /
          ((N : ℝ) * Real.log N) := by ring
    exact hlo.trans_le (hid.symm ▸ hlow)
  · intro a ha
    have hhi := WeakPNT'.eventually (eventually_lt_nhds ha)
    filter_upwards [hhi, eventually_ge_atTop 2] with N hhi hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    calc
      _ ≤ (Real.log N * (∑ n ∈ Iic N, Λ n)) / ((N : ℝ) * Real.log N) :=
        div_le_div_of_nonneg_right (squareMass_upper N) (by positivity)
      _ = (∑ n ∈ Iic N, Λ n) / (N : ℝ) := by field_simp
      _ < a := hhi

/-- Centered second moment through the inclusive integer cutoff. -/
noncomputable def centeredSquareMass (N : ℕ) : ℝ :=
  ∑ n ∈ Iic N, (Λ n - 1)^2

theorem centeredSquareMass_exact (N : ℕ) :
    centeredSquareMass N = squareMass N - 2 * (∑ n ∈ Iic N, Λ n) + (N + 1) := by
  unfold centeredSquareMass squareMass
  simp_rw [show ∀ x : ℝ, (x - 1)^2 = x^2 - 2*x + 1 by intro x; ring]
  simp [sum_add_distrib, sum_sub_distrib, ← mul_sum]

theorem centeredSquareMass_ratio_tendsto :
    Tendsto (fun N : ℕ => centeredSquareMass N / ((N : ℝ) * Real.log N))
      atTop (𝓝 1) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hm : Tendsto (fun N : ℕ => ((∑ n ∈ Iic N, Λ n) / (N : ℝ)) / Real.log N)
      atTop (𝓝 0) := WeakPNT'.div_atTop hlog
  have h1 : Tendsto (fun N : ℕ => (1 : ℝ) / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have h2 : Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hh := (squareMass_ratio_tendsto.sub (hm.const_mul 2)).add
    (h1.add (h2.mul h1))
  simp only [mul_zero, sub_zero, add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hl : Real.log N ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < N by omega)))
  rw [centeredSquareMass_exact]
  field_simp
  <;> ring


end RiemannResearch.Analysis.MangoldtSquareAsymptotic

/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.PrimePowerEulerDecay
import RiemannResearch.RH.QPrimePowerSievePrimeStep
import RiemannResearch.RH.PrimeSieveSecantLimits
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Uniform prime-power sieve secant decay

Source: user-provided TwoStageSieveObstructionResearch20261020.md.
Elementary Euler decay controls every adjacent integer step; unchanged
stages are handled exactly. No Bertrand, PNT, or RH assumption is needed.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QPrimePowerSieve
open RiemannResearch.Analysis PrimeSieveSecant

theorem primePowerEulerFactor_scaled_tendsto_zero (p : ℕ) (hp : p.Prime)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1) :
    Tendsto (fun H : ℕ => (H : ℝ) ^ (1 - σ) * primePowerEulerFactor p H σ)
      atTop (𝓝 0) := by
  simpa only [primePowerEulerFactor, Nat.primesLE] using
    primePowerEulerProduct_erase_scaled_tendsto_zero σ hσ hσ1 p hp

theorem sieve_adjacent_intercept_eq (p H : ℕ) (hp : p.Prime) (hpH : p ≤ H)
    (hprime : (H + 1).Prime) (σ : ℝ) :
    intercept (sieveSlope (primorial H) p) (sieveSlope (primorial (H + 1)) p)
      (primePowerEulerFactor p H σ) (primePowerEulerFactor p (H + 1) σ) =
      primePowerEulerFactor p H σ * (1 - ((H + 1 : ℕ) : ℝ) ^ (1 - σ)) := by
  rw [sieveSlope_primorial_succ_prime p H hp hpH hprime,
    primePowerEulerFactor_succ_prime p H hpH hprime]
  have ha := ne_of_gt (sieveSlope_primorial_positive p H hp hpH)
  have hq : (0 : ℝ) < ((H + 1 : ℕ) : ℝ) := by positivity
  have hpow : ((H + 1 : ℕ) : ℝ) * ((H + 1 : ℕ) : ℝ) ^ (-σ) =
      ((H + 1 : ℕ) : ℝ) ^ (1 - σ) := by
    rw [sub_eq_add_neg, Real.rpow_add hq, Real.rpow_one]
  rw [← hpow]
  unfold intercept
  have hd (a q : ℝ) : a - a * (1 - 1/q) = a/q := by ring
  rw [hd]
  field_simp [ha, ne_of_gt hq]
  ring

theorem sieve_adjacent_intercept_bound (p H : ℕ) (hp : p.Prime) (hpH : p ≤ H)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1) :
    |intercept (sieveSlope (primorial H) p) (sieveSlope (primorial (H + 1)) p)
      (primePowerEulerFactor p H σ) (primePowerEulerFactor p (H + 1) σ)| ≤
      (2 : ℝ) ^ (1 - σ) * ((H : ℝ) ^ (1 - σ) * primePowerEulerFactor p H σ) := by
  have hH : 1 ≤ H := (Nat.succ_le_of_lt hp.pos).trans hpH
  have hHR : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hα : 0 ≤ 1 - σ := by linarith
  have ht := (primePowerEulerFactor_pos p H hp.pos σ hσ).le
  by_cases hprime : (H + 1).Prime
  · rw [sieve_adjacent_intercept_eq p H hp hpH hprime σ, abs_mul, abs_of_nonneg ht]
    have hq1 : (1 : ℝ) ≤ ((H + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ H + 1 by omega)
    have hqp : 1 ≤ ((H + 1 : ℕ) : ℝ) ^ (1 - σ) := Real.one_le_rpow hq1 hα
    rw [abs_of_nonpos (by linarith : 1 - ((H + 1 : ℕ) : ℝ) ^ (1 - σ) ≤ 0)]
    have hqH : ((H + 1 : ℕ) : ℝ) ≤ 2 * (H : ℝ) := by
      push_cast
      have : (1 : ℝ) ≤ H := by exact_mod_cast hH
      linarith
    have hpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ ((H + 1 : ℕ) : ℝ)) hqH hα
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hHR.le] at hpow
    calc
      _ ≤ primePowerEulerFactor p H σ * (((H + 1 : ℕ) : ℝ) ^ (1 - σ)) :=
        mul_le_mul_of_nonneg_left (by linarith) ht
      _ ≤ primePowerEulerFactor p H σ * ((2 : ℝ) ^ (1 - σ) * (H : ℝ) ^ (1 - σ)) :=
        mul_le_mul_of_nonneg_left hpow ht
      _ = _ := by ring
  · rw [primorial_succ_not_prime H hprime, primePowerEulerFactor_succ_not_prime p H hprime]
    simp only [intercept, sub_self, div_zero, abs_zero]
    positivity

theorem sieve_adjacent_intercept_tendsto_zero (p : ℕ) (hp : p.Prime)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1) :
    Tendsto (fun H : ℕ => intercept (sieveSlope (primorial H) p)
      (sieveSlope (primorial (H + 1)) p)
      (primePowerEulerFactor p H σ) (primePowerEulerFactor p (H + 1) σ))
      atTop (𝓝 0) := by
  have hb := (primePowerEulerFactor_scaled_tendsto_zero p hp σ hσ hσ1).const_mul
    ((2 : ℝ) ^ (1 - σ))
  simp only [mul_zero] at hb
  apply squeeze_zero_norm' _ hb
  filter_upwards [eventually_ge_atTop p] with H hH
  simpa only [Real.norm_eq_abs] using sieve_adjacent_intercept_bound p H hp hH σ hσ hσ1

theorem sieve_intercept_uniform (p : ℕ) (hp : p.Prime)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∀ ε > 0, ∃ N : ℕ, p ≤ N ∧ ∀ H ≥ N, ∀ K ≥ H,
      |intercept (sieveSlope (primorial H) p) (sieveSlope (primorial K) p)
        (primePowerEulerFactor p H σ) (primePowerEulerFactor p K σ)| < ε := by
  let a : ℕ → ℝ := fun n => sieveSlope (primorial (p + n)) p
  let u : ℕ → ℝ := fun n => primePowerEulerFactor p (p + n) σ
  have hpos : ∀ n, 0 < a n := fun n => sieveSlope_primorial_positive p (p + n) hp (by omega)
  have hanti : Antitone a := by
    apply antitone_nat_of_succ_le
    intro n
    exact sieveSlope_primorial_succ_le p (p + n) hp (by omega)
  have hstall : ∀ n, a (n + 1) = a n → u (n + 1) = u n := by
    intro n hn
    have hnp : ¬ (p + n + 1).Prime := by
      intro hprime
      have hlt := sieveSlope_primorial_succ_lt p (p + n) hp (by omega) hprime
      change a (n + 1) < a n at hlt
      rw [hn] at hlt
      exact lt_irrefl _ hlt
    exact primePowerEulerFactor_succ_not_prime p (p + n) hnp σ
  have hlim : Tendsto (fun k => intercept (a k) (a (k + 1)) (u k) (u (k + 1)))
      atTop (𝓝 0) := by
    have hshift : Tendsto (fun n : ℕ => p + n) atTop atTop := by
      apply tendsto_atTop.mpr
      intro b
      filter_upwards [eventually_ge_atTop b] with n hn
      omega
    simpa only [a, u, Function.comp_def, Nat.add_assoc] using
      (sieve_adjacent_intercept_tendsto_zero p hp σ hσ hσ1).comp
        hshift
  intro ε hε
  obtain ⟨N, hN⟩ := uniform_intercept_of_tendsto_adjacent_antitone a u hpos hanti hstall hlim ε hε
  refine ⟨p + N, by omega, ?_⟩
  intro H hH K hK
  have hh := hN (H - p) (by omega) (K - p) (by omega)
  simpa only [a, u, Nat.add_sub_of_le (show p ≤ H by omega),
    Nat.add_sub_of_le (show p ≤ K by omega)] using hh

end RiemannResearch.RH.QPrimePowerSieve

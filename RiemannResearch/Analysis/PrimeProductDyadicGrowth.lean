/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FinitePrimeProductBounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Dyadic growth of the actual finite prime-product head

Source: the user-directed RH/CRT continuation of 20 October 2026. This
quantitatively specializes the existing elementary prime-product estimate to
the complete-Q head of the gcd-two sieve.

The cutoff is written `64 ^ m`, equal to `2 ^ (6 * m)`, so its base-two
logarithm is `6 * m`. No prime number theorem or global floor-log Q norm is used.
-/

noncomputable section
open scoped Topology
open Filter

namespace RiemannResearch.Analysis

/-- An explicit dyadic rate, strong enough to absorb the finite-head log term. -/
theorem finitePrimeProduct_dyadic_energy_lower (m : ℕ) :
    (4 / 225 : ℝ) * 4 ^ m ≤
      finitePrimeProduct (64 ^ m) ^ 2 * ((64 ^ m : ℕ) : ℝ) := by
  let a : ℝ := finitePrimeProduct (64 ^ m)
  let t : ℝ := 4 ^ m
  have ha : 0 ≤ a := finitePrimeProduct_nonneg _
  have ht : 1 ≤ t := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4)
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have ht3 : 1 ≤ t ^ 3 := one_le_pow₀ ht
  have hY : ((64 ^ m : ℕ) : ℝ) = t ^ 3 := by
    dsimp [t]
    push_cast
    rw [← pow_mul, Nat.mul_comm m 3, pow_mul]
    norm_num
  have hcube := finitePrimeProduct_cube_lower (64 ^ m)
  change (4 / 15 : ℝ) ^ 3 ≤ a ^ 3 * (2 * ((64 ^ m : ℕ) : ℝ) + 1) at hcube
  rw [hY] at hcube
  have hdiff : 0 ≤ a ^ 3 * (6 * t ^ 3 - 1) :=
    mul_nonneg (pow_nonneg ha _) (by linarith)
  have hc : (4 / 15 : ℝ) ^ 3 ≤ (2 * a * t) ^ 3 := by
    nlinarith [hcube, hdiff]
  have hat : (4 / 15 : ℝ) ≤ 2 * a * t := by
    by_contra h
    have hlt : 2 * a * t < (4 / 15 : ℝ) := lt_of_not_ge h
    have hpow := pow_lt_pow_left₀ hlt
      (by positivity : (0 : ℝ) ≤ 2 * a * t)
      (by decide : (3 : ℕ) ≠ 0)
    linarith
  have hs : (2 / 15 : ℝ) ^ 2 ≤ (a * t) ^ 2 :=
    (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 2 / 15)
      (mul_nonneg ha ht0)).2 (by linarith)
  have hmul := mul_le_mul_of_nonneg_right hs ht0
  change (4 / 225 : ℝ) * t ≤ a ^ 2 * ((64 ^ m : ℕ) : ℝ)
  rw [hY]
  nlinarith [hmul]

/-- A fixed exponential term absorbs any fixed quadratic term. -/
theorem four_pow_sub_quadratic_tendsto_atTop (C D : ℝ) (hC : 0 < C) :
    Tendsto (fun m : ℕ => C * 4 ^ m - D * (m : ℝ) ^ 2) atTop atTop := by
  have hratio : Tendsto (fun m : ℕ => D * ((m : ℝ) ^ 2 / (4 : ℝ) ^ m))
      atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_div_const_pow_of_one_lt 2
      (by norm_num : (1 : ℝ) < 4)).const_mul D
  have hhalf : (0 : ℝ) < C / 2 := by positivity
  have hexp : Tendsto (fun m : ℕ => (C / 2) * (4 : ℝ) ^ m) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4)).const_mul_atTop hhalf
  apply tendsto_atTop.2
  intro b
  filter_upwards [hexp.eventually (eventually_ge_atTop b),
    hratio.eventually (isOpen_Iio.mem_nhds hhalf)] with m hm hq
  have hp : (0 : ℝ) < 4 ^ m := by positivity
  have hq' : D * (m : ℝ) ^ 2 / (4 : ℝ) ^ m < C / 2 := by
    simpa only [mul_div_assoc] using hq
  have hmul := (div_lt_iff₀ hp).1 hq'
  linarith

/-- The exact prime-product head lower bound diverges after subtracting the
coarse squared floor-log error. This needs only positivity of the fixed Q
normalization `Z`; the intended application is `Z = ζ(2)`. -/
theorem finitePrimeProduct_dyadic_head_tendsto_atTop (Z : ℝ) (hZ : 0 < Z) :
    Tendsto (fun m : ℕ =>
      finitePrimeProduct (64 ^ m) ^ 2 * ((64 ^ m : ℕ) : ℝ) / (2 * Z) -
        (6 * (m : ℝ)) ^ 2) atTop atTop := by
  have hbase := four_pow_sub_quadratic_tendsto_atTop
    (2 / (225 * Z)) 36 (by positivity : (0 : ℝ) < 2 / (225 * Z))
  apply tendsto_atTop.2
  intro b
  filter_upwards [hbase.eventually (eventually_ge_atTop b)] with m hm
  have hrate := finitePrimeProduct_dyadic_energy_lower m
  have hdiv := div_le_div_of_nonneg_right hrate
    (by positivity : (0 : ℝ) ≤ 2 * Z)
  have heq : (4 / 225 : ℝ) * 4 ^ m / (2 * Z) =
      (2 / (225 * Z)) * 4 ^ m := by
    field_simp [ne_of_gt hZ]
    <;> ring
  rw [heq] at hdiv
  nlinarith

end RiemannResearch.Analysis

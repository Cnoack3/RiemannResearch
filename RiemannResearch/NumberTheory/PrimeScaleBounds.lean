/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Bertrand
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A prime at a residual-dependent scale

Source: the matched projection calculations in the 5 November 2026 audit of
*Projection Displacement, Prime Atoms, and Carries*. The arithmetic selection
uses Mathlib's Bertrand postulate. The consumer is `QPrimeProjectionControl`.
-/

noncomputable section

namespace RiemannResearch.NumberTheory.PrimeScaleBounds

/-- An elementary conversion of a scaled pairing bound into a cubic bound. -/
theorem cube_le_of_prime_scale (e a Z p : ℝ)
    (he : 0 < e) (ha : 0 ≤ a) (hZ : 0 < Z) (hp : 0 < p)
    (hlo : 4 ≤ e * p) (hhi : e * p ≤ 8)
    (h : e ≤ Real.sqrt (2 * Z * p) * a + Real.sqrt (e / p)) :
    e ^ 3 ≤ 64 * Z * a ^ 2 := by
  have hr : e / p ≤ (e / 2) ^ 2 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith [mul_nonneg he.le (sub_nonneg.mpr hlo)]
  have hs : Real.sqrt (e / p) ≤ e / 2 := by
    nlinarith [Real.sq_sqrt (div_nonneg he.le hp.le),
      Real.sqrt_nonneg (e / p)]
  have hl : e / 2 ≤ Real.sqrt (2 * Z * p) * a := by
    linarith
  have hsq : (e / 2) ^ 2 ≤ (Real.sqrt (2 * Z * p) * a) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hl
  rw [mul_pow, Real.sq_sqrt (by positivity)] at hsq
  have hsquare : e ^ 2 ≤ 8 * Z * p * a ^ 2 := by
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hsquare he.le
  have hu := mul_le_mul_of_nonneg_right hhi
    (show 0 ≤ 8 * Z * a ^ 2 by positivity)
  nlinarith

/-- Bertrand's postulate chooses an included prime at the residual scale.
The floor gives the constant eight without a rounding loss. -/
theorem exists_prime_at_residual_scale (e : ℝ) (H : ℕ)
    (he : 0 < e) (heone : e ≤ 1) (hH : 8 ≤ e * (H : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ p ≤ H ∧ 4 ≤ e * (p : ℝ) ∧ e * (p : ℝ) ≤ 8 := by
  let n : ℕ := ⌊4 / e⌋₊
  have hone : 1 ≤ 4 / e := by
    apply (le_div_iff₀ he).mpr
    nlinarith
  have hn : n ≠ 0 := Nat.ne_of_gt (Nat.floor_pos.mpr hone)
  obtain ⟨p, hp, hnp, hpn⟩ := Nat.exists_prime_lt_and_le_two_mul n hn
  have hfloor : (n : ℝ) ≤ 4 / e := Nat.floor_le (by positivity)
  have hbelow : 4 / e < (p : ℝ) := Nat.lt_of_floor_lt hnp
  have habove : (p : ℝ) ≤ 8 / e := by
    calc
      (p : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hpn
      _ ≤ 2 * (4 / e) := mul_le_mul_of_nonneg_left hfloor (by norm_num)
      _ = 8 / e := by ring
  have hlo : 4 ≤ e * (p : ℝ) := by
    have hh := (div_lt_iff₀ he).mp hbelow
    nlinarith
  have hhi : e * (p : ℝ) ≤ 8 := by
    have hh := (le_div_iff₀ he).mp habove
    nlinarith
  have hpH : p ≤ H := by
    have hh : (p : ℝ) ≤ H := le_of_mul_le_mul_left (hhi.trans hH) he
    exact_mod_cast hh
  exact ⟨p, hp, hpH, hlo, hhi⟩

end RiemannResearch.NumberTheory.PrimeScaleBounds

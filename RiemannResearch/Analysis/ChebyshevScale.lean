/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Lean.Elab.Tactic.Omega
import RiemannResearch.Analysis.ChebyshevEnergy
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
/-!
# Exact accelerated denominator and averaging scale
Source: the user-directed Chebyshev continuation, 5 November 2026.
These are algebraic consequences of the verified Chebyshev energy recurrence.
-/
noncomputable section

namespace RiemannResearch.Analysis.ChebyshevEnergy
theorem denominator_closed_form_of_roots (r s : ℝ)
    (hr : r ^ 2 = 6 * r - 1) (hs : s ^ 2 = 6 * s - 1) (hrs : r + s = 6) (n : ℕ) :
    denominator n = (r ^ n + s ^ n) / 2 := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [denominator]
  | one => norm_num [denominator]; linarith
  | more n ih0 ih1 =>
    rw [denominator, ih1, ih0]
    simp only [pow_add, pow_one, hr, hs]
    ring

theorem denominator_closed_form (n : ℕ) :
    denominator n =
      ((3 + 2 * Real.sqrt 2) ^ n + (3 - 2 * Real.sqrt 2) ^ n) / 2 := by
  apply denominator_closed_form_of_roots
  · nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  · nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  · ring

theorem denominator_ge_accelerated_power (n : ℕ) :
    (3 + 2 * Real.sqrt 2) ^ n / 2 ≤ denominator n := by
  rw [denominator_closed_form]
  have hpos : 0 ≤ 3 - 2 * Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  nlinarith [pow_nonneg hpos n]

theorem accelerated_head_lower_bound (n : ℕ) :
    (17 + 12 * Real.sqrt 2) ^ n / 4 ≤ (denominator n) ^ 2 := by
  have hb := denominator_ge_accelerated_power n
  have hpos : 0 ≤ (3 + 2 * Real.sqrt 2) ^ n := by positivity
  have hr : (3 + 2 * Real.sqrt 2) ^ 2 = 17 + 12 * Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have he : ((3 + 2 * Real.sqrt 2) ^ n) ^ 2 = (17 + 12 * Real.sqrt 2) ^ n := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hr]
  nlinarith [denominator_pos n]

theorem approximant_exact_energy
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : E →L[ℝ] E)
    (hs : ∀ x y, inner ℝ (C x) y = inner ℝ x (C y)) (b d : E)
    (heq : C d = (3 : ℝ) • d - (4 : ℝ) • b) (n : ℕ) :
    (denominator n) ^ 2 * ‖d - approximant C b n‖ ^ 2 +
      ‖secondKind C d n‖ ^ 2 - ‖C (secondKind C d n)‖ ^ 2 = ‖d‖ ^ 2 := by
  rw [approximant_error C b d heq, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (denominator_pos n))]
  have hne := ne_of_gt (denominator_pos n)
  have he := exact_energy C hs d n
  field_simp
  nlinarith

end RiemannResearch.Analysis.ChebyshevEnergy

namespace RiemannResearch.Analysis.ChebyshevEnergy
theorem denominator_is_nat (n : ℕ) : ∃ k : ℕ, denominator n = (k : ℝ) := by
  induction n using Nat.twoStepInduction with
  | zero => exact ⟨1, by norm_num [denominator]⟩
  | one => exact ⟨3, by norm_num [denominator]⟩
  | more n ih0 ih1 =>
    obtain ⟨k0, h0⟩ := ih0
    obtain ⟨k1, h1⟩ := ih1
    have hg := (denominator_growth n).2
    rw [h0, h1] at hg
    have hleR : (k0 : ℝ) ≤ 6 * (k1 : ℝ) := by
      nlinarith [(Nat.cast_nonneg k0 : (0 : ℝ) ≤ k0)]
    have hle : k0 ≤ 6 * k1 := by exact_mod_cast hleR
    refine ⟨6 * k1 - k0, ?_⟩
    rw [denominator, h0, h1, Nat.cast_sub hle, Nat.cast_mul]
    norm_num

def acceleratedHead (n : ℕ) : ℕ := Nat.floor ((denominator n) ^ 2)

theorem acceleratedHead_cast (n : ℕ) :
    (acceleratedHead n : ℝ) = (denominator n) ^ 2 := by
  obtain ⟨k, hk⟩ := denominator_is_nat n
  simp only [acceleratedHead, hk, ← Nat.cast_pow, Nat.floor_natCast]

theorem acceleratedHead_cover (N : ℕ) (hN : 1 ≤ N) :
    ∃ j, N ≤ acceleratedHead j ∧ (acceleratedHead j : ℝ) ≤ 36 * (N : ℝ) := by
  have hex : ∃ j, N ≤ acceleratedHead j := by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt N (by norm_num : 1 < (3 : ℕ))
    have hjR : (N : ℝ) < (3 : ℝ) ^ j := by exact_mod_cast hj
    have ha := denominator_ge_pow j
    have hnR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    refine ⟨j, ?_⟩
    apply Nat.le_floor
    nlinarith [denominator_pos j]
  let j := Nat.find hex
  refine ⟨j, Nat.find_spec hex, ?_⟩
  cases hj : j with
  | zero =>
    rw [acceleratedHead_cast]
    norm_num [denominator]
    exact_mod_cast (show 1 ≤ 36 * N by omega)
  | succ k =>
    have hk : acceleratedHead k < N :=
      Nat.lt_of_not_ge (Nat.find_min hex (by omega : k < Nat.find hex))
    have hkR : (denominator k) ^ 2 < (N : ℝ) := by
      exact Nat.lt_of_floor_lt hk
    rw [acceleratedHead_cast]
    have hr := denominator_ratio_le k
    have hs := mul_self_le_mul_self (denominator_pos (k + 1)).le hr
    nlinarith

end RiemannResearch.Analysis.ChebyshevEnergy

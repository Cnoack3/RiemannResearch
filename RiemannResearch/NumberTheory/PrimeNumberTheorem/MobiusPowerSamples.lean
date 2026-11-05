/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MobiusFloorTailReindex
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Mertens power estimates from sparse arithmetic samples

The bounded unit steps of the ordinary Mertens function fill intervals between
consecutive perfect powers. The sample spacing determines the exponent loss.
The integer-cutoff argument also applies to an arbitrary sampling set with
sufficient coverage.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- The error in sampling Mertens sums at two integer sites is bounded by the
number of omitted Möbius terms. -/
theorem abs_M_nat_difference_le_gap {m n : ℕ} (hmn : m ≤ n) :
    |M (n : ℝ) - M (m : ℝ)| ≤ ((n-m : ℕ) : ℝ) := by
  rw [M_nat_difference m n hmn]
  calc
    _ ≤ ∑ k ∈ Finset.Ioc m n, |(ArithmeticFunction.moebius k : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.Ioc m n, (1 : ℝ) := Finset.sum_le_sum fun k _ => by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k)
    _ = _ := by simp [Nat.card_Ioc]

/-- A lower sample within `D n^s` of each integer supplies the same Mertens
exponent, with an additive change of the constant. -/
theorem mertens_power_of_samples (S : Set ℕ) (s C D : ℝ) (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hsample : ∀ k ∈ S, 0 < k → |M (k : ℝ)| ≤ C * (k : ℝ)^s)
    (hcover : ∀ n : ℕ, 0 < n → ∃ k ∈ S, 0 < k ∧ k ≤ n ∧
      ((n-k : ℕ) : ℝ) ≤ D * (n : ℝ)^s) (n : ℕ) (hn : 0 < n) :
    |M (n : ℝ)| ≤ (C + D) * (n : ℝ)^s := by
  obtain ⟨k, hkS, hk, hkn, hg⟩ := hcover n hn
  have hknR : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
  have hm := (hsample k hkS hk).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg k) hknR hs) hC)
  calc
    |M (n : ℝ)| = |(M (n : ℝ)-M (k : ℝ)) + M (k : ℝ)| := by rw [sub_add_cancel]
    _ ≤ |M (n : ℝ)-M (k : ℝ)| + |M (k : ℝ)| := abs_add_le _ _
    _ ≤ D * (n : ℝ)^s + C * (n : ℝ)^s := add_le_add ((abs_M_nat_difference_le_gap hkn).trans hg) hm
    _ = _ := by ring

private theorem pow_gap_le (j : ℕ) {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) :
    x^(j+1) - y^(j+1) ≤ ((j+1 : ℕ) : ℝ) * (x-y) * x^j := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc
      x^(j+1+1) - y^(j+1+1) = (x^(j+1)-y^(j+1)) * x + (x-y) * y^(j+1) := by
        rw [pow_succ x (j+1), pow_succ y (j+1)]
        ring
      _ ≤ (((j+1 : ℕ) : ℝ) * (x-y) * x^j) * x + (x-y) * x^(j+1) :=
        add_le_add (mul_le_mul_of_nonneg_right ih (hy.trans hyx))
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy hyx _) (sub_nonneg.mpr hyx))
      _ = _ := by push_cast; rw [pow_succ x j]; ring

/-- All integer power estimates follow from sampling just the `r`th powers
provided `s ≥ 1−1/r`. In particular `s ≥ 7/8` permits eighth-power inputs. -/
theorem mertens_power_of_perfect_power_samples (r : ℕ) (hr : 0 < r) (s C : ℝ)
    (hs : 0 ≤ s) (hgap : 1 - (r : ℝ)⁻¹ ≤ s) (hC : 0 ≤ C)
    (hM : ∀ k : ℕ, 0 < k → |M (((k^r : ℕ) : ℝ))| ≤ C * (((k^r : ℕ) : ℝ))^s)
    (n : ℕ) (hn : 0 < n) : |M (n : ℝ)| ≤ (C + r) * (n : ℝ)^s := by
  cases r with
  | zero => omega
  | succ j =>
    apply mertens_power_of_samples (Set.range (fun t : ℕ => t^(j+1))) s C (j.succ : ℝ) hs hC _ _ n hn
    · rintro m ⟨t, rfl⟩ ht
      apply hM
      by_contra! hz
      have ht0 : t = 0 := by omega
      simp [ht0] at ht
    · intro u hu
      let x : ℝ := (u : ℝ)^(((j+1 : ℕ) : ℝ)⁻¹)
      let k : ℕ := ⌊x⌋₊
      have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
      have hx1 : 1 ≤ x := Real.one_le_rpow hu1 (by positivity)
      have hx0 : 0 ≤ x := zero_le_one.trans hx1
      have hy0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      have hle : (k : ℝ) ≤ x := Nat.floor_le hx0
      have hlt : x < (k : ℝ) + 1 := Nat.lt_floor_add_one x
      have hk : 0 < k := by
        have h : (1 : ℕ) ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).2 (by simpa using hx1)
        exact h
      have hx : x^(j+1) = (u : ℝ) := Real.rpow_inv_natCast_pow (Nat.cast_nonneg u) (by omega : j+1 ≠ 0)
      have hy : k^(j+1) ≤ u := by
        exact_mod_cast (pow_le_pow_left₀ hy0 hle (j+1)).trans_eq hx
      have hscale : x^j = (u : ℝ)^(1 - ((j+1 : ℕ) : ℝ)⁻¹) := by
        dsimp only [x]
        rw [← Real.rpow_mul_natCast (Nat.cast_nonneg u)]
        congr 1
        push_cast
        field_simp [show (j : ℝ) + 1 ≠ 0 by positivity] <;> ring
      refine ⟨k^(j+1), ⟨k,rfl⟩, pow_pos hk _, hy, ?_⟩
      rw [Nat.cast_sub hy, Nat.cast_pow, ← hx]
      calc
        _ ≤ ((j+1 : ℕ) : ℝ) * (x-(k:ℝ)) * x^j := pow_gap_le j hy0 hle
        _ ≤ ((j+1 : ℕ) : ℝ) * 1 * x^j :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)) (pow_nonneg hx0 _)
        _ ≤ _ := by
          rw [mul_one, hscale, hx]
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hu1 hgap) (Nat.cast_nonneg _)

end RiemannResearch.NumberTheory.PrimeNumberTheorem

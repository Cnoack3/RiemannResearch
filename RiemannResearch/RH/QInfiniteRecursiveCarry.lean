/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.CRTCarryArithmetic
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Infinite pointwise cancellation along a normalized Bézout chain

Source: the user's recursive decomposition of squarefree atoms. The integer
floor at each step is the repository's actual CRT carry. The bounds use the
fixed physical site and hold without comparing successive prime sizes. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.CRTCarryArithmetic
open ArithmeticCumulative

/-- A growing conductor chain with normalized signed Bézout multipliers.
For a prime path the normalization is w(k+1) = w(k)/a(k). -/
structure NormalizedCarryChain where
  D : ℕ → ℕ
  p : ℕ → ℕ
  a : ℕ → ℤ
  b : ℕ → ℤ
  w : ℕ → ℝ
  start_pos : 0 < D 0
  radix_ge : ∀ k, 2 ≤ p k
  next : ∀ k, D (k + 1) = D k * p k
  bezout : ∀ k, (a k : ℝ) * (p k : ℝ) + (b k : ℝ) * (D k : ℝ) = 1
  normalize : ∀ k, w (k + 1) * (a k : ℝ) = w k
  weight_bound : ∀ k, |w k| ≤ 1

namespace NormalizedCarryChain

variable (s : NormalizedCarryChain)

theorem modulus_growth (k : ℕ) : 2 ^ k ≤ s.D k := by
  induction k with
  | zero => have h := s.start_pos; simp only [pow_zero]; omega
  | succ k ih =>
    rw [pow_succ, s.next]
    exact Nat.mul_le_mul ih (s.radix_ge k)

private theorem modulus_pos (k : ℕ) : 0 < s.D k :=
  (pow_pos (by decide : 0 < (2 : ℕ)) k).trans_le (s.modulus_growth k)

def parentTerm (n k : ℕ) : ℝ :=
  s.w k * residueFraction (s.D k) n

def primeTerm (n k : ℕ) : ℝ :=
  s.w (k + 1) * (s.b k : ℝ) * residueFraction (s.p k) n

def carryTerm (n k : ℕ) : ℝ :=
  s.w (k + 1) * (carry (s.D k) (s.p k) (s.a k) (s.b k) n : ℝ)

theorem carry_step (n k : ℕ) :
    s.carryTerm n k = s.parentTerm n k + s.primeTerm n k - s.parentTerm n (k + 1) := by
  have he := real_decomposition (s.D k) (s.p k) (s.a k) (s.b k) 0 n (s.modulus_pos k)
    (lt_of_lt_of_le (by decide : 0 < 2) (s.radix_ge k)) (by simpa using s.bezout k)
  simp only [carryTerm, parentTerm, primeTerm, s.next, he]
  linear_combination residueFraction (s.D k) n * s.normalize k

/-- All intermediate composite atoms cancel for every finite prefix. -/
theorem sum_carries (n K : ℕ) :
    ∑ k ∈ Finset.range K, s.carryTerm n k = s.parentTerm n 0 +
      (∑ k ∈ Finset.range K, s.primeTerm n k) - s.parentTerm n K := by
  induction K with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, s.carry_step]
    ring

private theorem inv_modulus_bound (k : ℕ) :
    |s.w k / (s.D k : ℝ)| ≤ (1 / 2 : ℝ) ^ k := by
  have hnat := s.modulus_growth k
  have hr : (2 : ℝ) ^ k ≤ s.D k := by exact_mod_cast hnat
  rw [abs_div, abs_of_nonneg (Nat.cast_nonneg (s.D k) : (0 : ℝ) ≤ s.D k),
    div_pow, one_pow]
  exact (div_le_div_of_nonneg_right (s.weight_bound k) (Nat.cast_nonneg _)).trans
    (one_div_le_one_div_of_le (by positivity) hr)

theorem parent_bound (n k : ℕ) :
    |s.parentTerm n k| ≤ (n : ℝ) * (1 / 2 : ℝ) ^ k := by
  have he : s.parentTerm n k = ((n % s.D k : ℕ) : ℝ) * (s.w k / (s.D k : ℝ)) := by
    unfold parentTerm residueFraction
    ring
  rw [he, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  exact mul_le_mul (by exact_mod_cast Nat.mod_le n (s.D k)) (s.inv_modulus_bound k)
    (abs_nonneg _) (Nat.cast_nonneg _)

/-- The reciprocal Bézout relation identifies the coefficient at the incoming
prime with the difference between two consecutive reciprocal parent weights. -/
theorem primeTerm_eq (n k : ℕ) :
    s.primeTerm n k = ((n % s.p k : ℕ) : ℝ) *
      (s.w (k + 1) / (s.D (k + 1) : ℝ) - s.w k / (s.D k : ℝ)) := by
  have hD : (s.D k : ℝ) ≠ 0 := by exact_mod_cast (s.modulus_pos k).ne'
  have hp : (s.p k : ℝ) ≠ 0 := by
    exact_mod_cast (show s.p k ≠ 0 by have := s.radix_ge k; omega)
  have hrel : s.w (k + 1) * (s.b k : ℝ) / (s.p k : ℝ) =
      s.w (k + 1) / ((s.D k : ℝ) * s.p k) - s.w k / (s.D k : ℝ) := by
    field_simp [hD, hp]
    linear_combination s.w (k + 1) * s.bezout k - (s.p k : ℝ) * s.normalize k
  rw [s.next, Nat.cast_mul, ← hrel]
  unfold primeTerm residueFraction
  ring

theorem prime_bound (n k : ℕ) :
    |s.primeTerm n k| ≤ (2 * (n : ℝ)) * (1 / 2 : ℝ) ^ k := by
  rw [s.primeTerm_eq, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  have hh := (abs_sub _ _).trans (add_le_add (s.inv_modulus_bound (k + 1))
    (s.inv_modulus_bound k))
  have hp := mul_le_mul (show ((n % s.p k : ℕ) : ℝ) ≤ n by exact_mod_cast Nat.mod_le n (s.p k))
    hh (abs_nonneg _) (Nat.cast_nonneg n (α := ℝ))
  rw [pow_succ] at hp
  nlinarith [show 0 ≤ (n : ℝ) * (1 / 2 : ℝ) ^ k by positivity]

/-- Absolute convergence of both series and the full pointwise identity. -/
theorem infinite_carry_expansion (n : ℕ) :
    Summable (s.primeTerm n) ∧ Summable (s.carryTerm n) ∧
    (∑' k, s.carryTerm n k) = s.parentTerm n 0 + ∑' k, s.primeTerm n k := by
  have hg : Summable (fun k : ℕ => (1 / 2 : ℝ)^k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hparent : Summable (s.parentTerm n) := by
    apply Summable.of_norm_bounded (hg.mul_left (n : ℝ))
    simpa only [Real.norm_eq_abs] using s.parent_bound n
  have hprime : Summable (s.primeTerm n) := by
    apply Summable.of_norm_bounded (hg.mul_left (2 * (n : ℝ)))
    simpa only [Real.norm_eq_abs] using s.prime_bound n
  have hshift : Summable (fun k : ℕ => s.parentTerm n (k + 1)) :=
    (summable_nat_add_iff 1).mpr hparent
  have hcarry : Summable (s.carryTerm n) :=
    ((hparent.add hprime).sub hshift).congr (fun k => (s.carry_step n k).symm)
  refine ⟨hprime, hcarry, ?_⟩
  have h := ((tendsto_const_nhds (x := s.parentTerm n 0)).add
    hprime.hasSum.tendsto_sum_nat).sub hparent.tendsto_atTop_zero
  rw [sub_zero] at h
  exact tendsto_nhds_unique hcarry.hasSum.tendsto_sum_nat
    (h.congr' (Eventually.of_forall (fun K => (s.sum_carries n K).symm)))

end NormalizedCarryChain
end RiemannResearch.RH.CRTCarryArithmetic

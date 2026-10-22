/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.FiniteTwoMomentEnergy
import Mathlib.Data.Finset.Range
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact double-root coefficient model

Source: J.-F. Burnol, A lower bound in an approximation problem involving
 the zeros of the Riemann zeta function, arXiv:math/0103058v2 (2001),
Theorems 1.4 and 2.1 and Section 2. The source motivates the polynomial model
and finite Gram strategy. We refine the double-root model with an exact
finite energy identity and an attained cubic-target minimum.

These are real coefficient-space theorems. The ordinary proof connecting
this model to polynomial divisibility and circle Parseval is recorded in
BurnolRatesResearch20261018.md, not formalized in this module.
No arithmetic upper bound or RH conclusion is asserted.
-/
open scoped BigOperators
namespace RiemannResearch.RH.BurnolDoubleRootModel
open RiemannResearch.Analysis.FiniteTwoMomentEnergy

/-- The first coefficient moment on the index set `0,...,L`. -/
theorem sum_index (L : ℕ) :
    (∑ j ∈ Finset.range (L + 1), (j : ℝ)) = (L : ℝ) * ((L : ℝ) + 1) / 2 := by
  induction L with
  | zero => norm_num
  | succ L ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- The second coefficient moment on the index set `0,...,L`. -/
theorem sum_index_sq (L : ℕ) :
    (∑ j ∈ Finset.range (L + 1), (j : ℝ) ^ 2) =
      (L : ℝ) * ((L : ℝ) + 1) * (2 * (L : ℝ) + 1) / 6 := by
  induction L with
  | zero => norm_num
  | succ L ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Centering the coefficient indices at `L/2` makes their mean zero. -/
theorem sum_centered_index (L : ℕ) :
    (∑ j ∈ Finset.range (L + 1), ((j : ℝ) - (L : ℝ) / 2)) = 0 := by
  simp only [Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, sum_index]
  push_cast
  ring

/-- Exact centered second moment of the coefficient indices. -/
theorem sum_centered_index_sq (L : ℕ) :
    (∑ j ∈ Finset.range (L + 1), ((j : ℝ) - (L : ℝ) / 2) ^ 2) =
      (L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2) / 12 := by
  have hp (j : ℕ) : ((j : ℝ) - (L : ℝ) / 2) ^ 2 =
      (j : ℝ) ^ 2 - (L : ℝ) * (j : ℝ) + (L : ℝ) ^ 2 / 4 := by ring
  simp_rw [hp]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    sum_index, sum_index_sq]
  push_cast
  ring

/-- Recenter the prescribed zeroth and first moments. -/
theorem centered_residual_moment (L : ℕ) (r : ℕ → ℝ) (a b : ℝ)
    (ha : ∑ j ∈ Finset.range (L + 1), r j = a)
    (hb : ∑ j ∈ Finset.range (L + 1), (j : ℝ) * r j = b) :
    (∑ j ∈ Finset.range (L + 1), ((j : ℝ) - (L : ℝ) / 2) * r j) =
      b - (L : ℝ) * a / 2 := by
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ha, hb]
  ring

/-- Exact energy decomposition for two coefficient moment constraints. -/
theorem double_root_decomposition (L : ℕ) (hL : 1 ≤ L)
    (r : ℕ → ℝ) (a b : ℝ)
    (ha : ∑ j ∈ Finset.range (L + 1), r j = a)
    (hb : ∑ j ∈ Finset.range (L + 1), (j : ℝ) * r j = b) :
    (∑ j ∈ Finset.range (L + 1), (r j) ^ 2) =
      a ^ 2 / ((L : ℝ) + 1) +
      12 * (b - (L : ℝ) * a / 2) ^ 2 /
        ((L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2)) +
      ∑ j ∈ Finset.range (L + 1),
        (r j - a / ((L : ℝ) + 1) -
          12 * (b - (L : ℝ) * a / 2) * ((j : ℝ) - (L : ℝ) / 2) /
            ((L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2))) ^ 2 := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL)
  have hm : (L : ℝ) + 1 ≠ 0 := by positivity
  have hv : (L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2) / 12 ≠ 0 := by positivity
  have hd := two_moment_decomposition (Finset.range (L + 1))
    (fun j => (j : ℝ) - (L : ℝ) / 2) r
    ((L : ℝ) + 1) ((L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2) / 12)
    a (b - (L : ℝ) * a / 2) hm hv
    (by simp) (sum_centered_index L) (sum_centered_index_sq L)
    ha (centered_residual_moment L r a b ha hb)
  have hquot (t : ℝ) :
      t / ((L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2) / 12) =
      12 * t / ((L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2)) := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  rw [hquot] at hd
  simp_rw [hquot] at hd
  convert hd using 1
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  ring

/-- Sharp two moment bound in the repeated boundary root coefficient model. -/
theorem double_root_lower_bound (L : ℕ) (hL : 1 ≤ L)
    (r : ℕ → ℝ) (a b : ℝ)
    (ha : ∑ j ∈ Finset.range (L + 1), r j = a)
    (hb : ∑ j ∈ Finset.range (L + 1), (j : ℝ) * r j = b) :
    a ^ 2 / ((L : ℝ) + 1) +
      12 * (b - (L : ℝ) * a / 2) ^ 2 /
        ((L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2)) ≤
      ∑ j ∈ Finset.range (L + 1), (r j) ^ 2 := by
  rw [double_root_decomposition L hL r a b ha hb]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)



/-- For arbitrary prescribed two moments, the affine residual attains the
exact lower bound in the double boundary root model. -/
theorem double_root_attainment (L : ℕ) (hL : 1 ≤ L) (a b : ℝ) :
    ∃ r : ℕ → ℝ,
      (∀ j, r j = a / ((L : ℝ) + 1) +
        12 * (b - (L : ℝ) * a / 2) * ((j : ℝ) - (L : ℝ) / 2) /
          ((L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2))) ∧
      (∑ j ∈ Finset.range (L + 1), r j) = a ∧
      (∑ j ∈ Finset.range (L + 1), (j : ℝ) * r j) = b ∧
      (∑ j ∈ Finset.range (L + 1), (r j) ^ 2) =
        a ^ 2 / ((L : ℝ) + 1) +
        12 * (b - (L : ℝ) * a / 2) ^ 2 /
          ((L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2)) := by
  have hLpos : (0 : ℝ) < L := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL)
  have hm : (L : ℝ) + 1 ≠ 0 := by positivity
  have hv : (L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2) / 12 ≠ 0 := by
    positivity
  let r : ℕ → ℝ := fun j =>
    a / ((L : ℝ) + 1) +
      ((b - (L : ℝ) * a / 2) /
        ((L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2) / 12)) *
          ((j : ℝ) - (L : ℝ) / 2)
  have h := two_moment_attainment (Finset.range (L + 1))
    (fun j => (j : ℝ) - (L : ℝ) / 2)
    ((L : ℝ) + 1) ((L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2) / 12)
    a (b - (L : ℝ) * a / 2) hm hv
    (by simp) (sum_centered_index L) (sum_centered_index_sq L)
  change
    (∑ j ∈ Finset.range (L + 1), r j) = a ∧
    (∑ j ∈ Finset.range (L + 1), ((j : ℝ) - (L : ℝ) / 2) * r j) =
      b - (L : ℝ) * a / 2 ∧
    (∑ j ∈ Finset.range (L + 1), (r j) ^ 2) =
      a ^ 2 / ((L : ℝ) + 1) +
        (b - (L : ℝ) * a / 2) ^ 2 /
          ((L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2) / 12) at h
  rcases h with ⟨ha, hb, he⟩
  refine ⟨r, ?_, ha, ?_, ?_⟩
  · intro j
    dsimp [r]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  · have hcenter :
        (∑ j ∈ Finset.range (L + 1), ((j : ℝ) - (L : ℝ) / 2) * r j) =
        (∑ j ∈ Finset.range (L + 1), (j : ℝ) * r j) - (L : ℝ) * a / 2 := by
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ha]
      ring
    rw [hcenter] at hb
    linarith
  · calc
      (∑ j ∈ Finset.range (L + 1), (r j) ^ 2) =
        a ^ 2 / ((L : ℝ) + 1) +
          (b - (L : ℝ) * a / 2) ^ 2 /
            ((L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2) / 12) := he
      _ = a ^ 2 / ((L : ℝ) + 1) +
        12 * (b - (L : ℝ) * a / 2) ^ 2 /
          ((L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2)) := by
        simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
        ring

/-- The cubic energy lower bound for the target `P(z) = 1-z` and
`Q(z) = (1-z) ^ 2`: the residual has total coefficient sum zero and
first coefficient moment minus one. -/
theorem cubic_target_lower_bound (L : ℕ) (hL : 1 ≤ L)
    (r : ℕ → ℝ)
    (ha : ∑ j ∈ Finset.range (L + 1), r j = 0)
    (hb : ∑ j ∈ Finset.range (L + 1), (j : ℝ) * r j = -1) :
    12 / ((L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2)) ≤
      ∑ j ∈ Finset.range (L + 1), (r j) ^ 2 := by
  have h := double_root_lower_bound L hL r 0 (-1) ha hb
  norm_num at h ⊢
  exact h

/-- An explicit affine residual attains the cubic target bound. -/
theorem cubic_target_attainment (L : ℕ) (hL : 1 ≤ L) :
    ∃ r : ℕ → ℝ,
      (∀ j, r j = -12 * ((j : ℝ) - (L : ℝ) / 2) /
        ((L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2))) ∧
      (∑ j ∈ Finset.range (L + 1), r j) = 0 ∧
      (∑ j ∈ Finset.range (L + 1), (j : ℝ) * r j) = -1 ∧
      (∑ j ∈ Finset.range (L + 1), (r j) ^ 2) =
        12 / ((L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2)) := by
  have hLpos : (0 : ℝ) < L := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL)
  have hm : (L : ℝ) + 1 ≠ 0 := by positivity
  have hv : (L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2) / 12 ≠ 0 := by
    positivity
  let r : ℕ → ℝ := fun j =>
    0 / ((L : ℝ) + 1) +
      (-1 / ((L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2) / 12)) *
        ((j : ℝ) - (L : ℝ) / 2)
  have h := two_moment_attainment (Finset.range (L + 1))
    (fun j => (j : ℝ) - (L : ℝ) / 2)
    ((L : ℝ) + 1) ((L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2) / 12)
    0 (-1) hm hv (by simp) (sum_centered_index L) (sum_centered_index_sq L)
  change
    (∑ j ∈ Finset.range (L + 1), r j) = 0 ∧
    (∑ j ∈ Finset.range (L + 1), ((j : ℝ) - (L : ℝ) / 2) * r j) = -1 ∧
    (∑ j ∈ Finset.range (L + 1), (r j) ^ 2) =
      0 ^ 2 / ((L : ℝ) + 1) +
        (-1) ^ 2 / ((L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2) / 12) at h
  rcases h with ⟨ha, hb, he⟩
  refine ⟨r, ?_, ha, ?_, ?_⟩
  · intro j
    dsimp [r]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  · have hcenter :
        (∑ j ∈ Finset.range (L + 1), ((j : ℝ) - (L : ℝ) / 2) * r j) =
        ∑ j ∈ Finset.range (L + 1), (j : ℝ) * r j := by
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ha]
      ring
    rw [hcenter] at hb
    exact hb
  · calc
      (∑ j ∈ Finset.range (L + 1), (r j) ^ 2) =
        0 ^ 2 / ((L : ℝ) + 1) +
          (-1) ^ 2 / ((L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2) / 12) := he
      _ = 12 / ((L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2)) := by
        simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
        ring

/-- The preceding lower bound is an attained exact minimum. -/
theorem cubic_target_exact_minimum (L : ℕ) (hL : 1 ≤ L) :
    ∃ r : ℕ → ℝ,
      (∑ j ∈ Finset.range (L + 1), r j) = 0 ∧
      (∑ j ∈ Finset.range (L + 1), (j : ℝ) * r j) = -1 ∧
      (∑ j ∈ Finset.range (L + 1), (r j) ^ 2) =
        12 / ((L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2)) ∧
      ∀ s : ℕ → ℝ,
        (∑ j ∈ Finset.range (L + 1), s j) = 0 →
        (∑ j ∈ Finset.range (L + 1), (j : ℝ) * s j) = -1 →
        (∑ j ∈ Finset.range (L + 1), (r j) ^ 2) ≤
          ∑ j ∈ Finset.range (L + 1), (s j) ^ 2 := by
  obtain ⟨r, _, ha, hb, he⟩ := cubic_target_attainment L hL
  refine ⟨r, ha, hb, he, ?_⟩
  intro s hsa hsb
  rw [he]
  exact cubic_target_lower_bound L hL s hsa hsb

/-- The leading `1/L` scale loses all information for this target; the
exact error has the strictly smaller cubic scale. -/
theorem cubic_target_scaled_energy_identity (L : ℕ) (hL : 1 ≤ L) :
    ((L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2)) *
      (12 / ((L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2))) = 12 := by
  have hLpos : (0 : ℝ) < L := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL)
  have hD : (L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2) ≠ 0 := by positivity
  field_simp [hD]
  <;> ring

end RiemannResearch.RH.BurnolDoubleRootModel

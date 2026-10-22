/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.TriangularOverlapKernel
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Integer quotient fibers as real ramps

Source: finite quotient regrouping developed for the triangular-dual
refinement of Michel Balazard, arXiv:1812.04309, Propositions 6--7.
These general identities connect natural-number quotient sums with
the exact overlap partition used in RH/MobiusTriangularEnergy.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis

def quotientFiberCount (N k j : ℕ) : ℕ :=
  ((Finset.range N).filter fun a => a / k = j).card

theorem quotientFiberCount_eq_sub (N k j : ℕ) (hk : 0 < k) :
    quotientFiberCount N k j = min N ((j + 1) * k) - min N (j * k) := by
  have he : (Finset.range N).filter (fun a => a / k = j) =
      Finset.Ico (min N (j * k)) (min N ((j + 1) * k)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    have hdiv : a / k = j ↔ j * k ≤ a ∧ a < (j + 1) * k := by
      constructor
      · intro h
        constructor
        · exact (Nat.le_div_iff_mul_le hk).mp (by omega)
        · exact (Nat.div_lt_iff_lt_mul hk).mp (by omega)
      · rintro ⟨hlo, hhi⟩
        have h₁ := (Nat.le_div_iff_mul_le hk).mpr hlo
        have h₂ := (Nat.div_lt_iff_lt_mul hk).mpr hhi
        omega
    rw [hdiv]
    omega
  unfold quotientFiberCount
  rw [he, Nat.card_Ico]

theorem sum_range_quotient_fibers (N k : ℕ) (f : ℕ → ℝ) :
    (∑ a ∈ Finset.range N, f (a / k)) =
      ∑ j ∈ Finset.range N, (quotientFiberCount N k j : ℝ) * f j := by
  classical
  have hmap : ∀ a ∈ Finset.range N, a / k ∈ Finset.range N := by
    intro a ha
    exact Finset.mem_range.mpr ((Nat.div_le_self a k).trans_lt (Finset.mem_range.mp ha))
  calc
    _ = ∑ j ∈ Finset.range N,
        ∑ a ∈ (Finset.range N).filter (fun a => a / k = j), f (a / k) :=
      (Finset.sum_fiberwise_of_maps_to hmap (fun a => f (a / k))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      calc
        _ = ∑ a ∈ (Finset.range N).filter (fun a => a / k = j), f j := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [(Finset.mem_filter.mp ha).2]
        _ = _ := by simp [quotientFiberCount]

theorem quotientFiberCount_real (N k j : ℕ) (hk : 0 < k) :
    (quotientFiberCount N k j : ℝ) = (k : ℝ) * unitRamp j ((N : ℝ) / k) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hle : min N (j * k) ≤ min N ((j + 1) * k) := by
    apply min_le_min_left
    nlinarith
  rw [quotientFiberCount_eq_sub N k j hk, Nat.cast_sub hle]
  push_cast
  unfold unitRamp
  have hscale (a : ℝ) :
      (k : ℝ) * max ((N : ℝ) / k - a) 0 = max ((N : ℝ) - k * a) 0 := by
    rw [mul_max_of_nonneg _ _ (le_of_lt hkR), mul_zero]
    congr 1
    field_simp
  rw [mul_sub, hscale, hscale]
  have hmin (a : ℝ) : min (N : ℝ) a = (N : ℝ) - max ((N : ℝ) - a) 0 := by
    by_cases h : (N : ℝ) ≤ a
    · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h)]
      ring
    · have h' : a ≤ (N : ℝ) := le_of_lt (lt_of_not_ge h)
      rw [min_eq_right h', max_eq_left (sub_nonneg.mpr h')]
      ring
  rw [hmin, hmin]
  push_cast
  ring

theorem sum_range_quotient_ramps (N k : ℕ) (hk : 0 < k) (f : ℕ → ℝ) :
    (∑ a ∈ Finset.range N, f (a / k)) =
      (k : ℝ) * ∑ j ∈ Finset.range N, unitRamp j ((N : ℝ) / k) * f j := by
  rw [sum_range_quotient_fibers, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [quotientFiberCount_real N k j hk]
  ring

end RiemannResearch.Analysis

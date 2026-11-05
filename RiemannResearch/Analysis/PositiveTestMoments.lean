/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# One-sided weighted moments from positive tests

A family of nonnegative tests that dominates a weight on finite heads transfers
summability of a positive part to absolute summability. The factor two comes
from the exact identity for the signed mass against each test.
-/

open scoped BigOperators

namespace RiemannResearch.Analysis

/-- Positive tests with zero signed mass control the absolute moment by the
positive moment. The lower estimate is needed only on each finite head. -/
theorem absolute_moment_of_positive_tests
    (b H : ℕ → ℝ) (T : ℕ → ℕ → ℝ) (c C : ℝ) (hc : 0 < c)
    (hH : ∀ n, 0 ≤ H n) (hT : ∀ N n, 0 ≤ T N n)
    (hhead : ∀ N n, n < N → c * H n ≤ T N n)
    (hmajor : ∀ N n, T N n ≤ C * H n)
    (hzero : ∀ N, HasSum (fun n => b n * T N n) 0)
    (hpos : Summable (fun n => max (b n) 0 * H n)) :
    Summable (fun n => |b n| * H n) ∧
      (∑' n, |b n| * H n) ≤ 2 * (C * ∑' n, max (b n) 0 * H n) / c := by
  let P := fun n => max (b n) 0
  let S := ∑' n, P n * H n
  have hP (n : ℕ) : 0 ≤ P n := le_max_right _ _
  have hscale : HasSum (fun n => C * (P n * H n)) (C * S) := hpos.hasSum.mul_left C
  have hnonneg (n : ℕ) : 0 ≤ |b n| * H n := mul_nonneg (abs_nonneg _) (hH n)
  have hbound (N : ℕ) : (∑ n ∈ Finset.range N, |b n| * H n) ≤ 2 * (C * S) / c := by
    have hu (n : ℕ) : P n * T N n ≤ C * (P n * H n) := by
      calc
        _ ≤ P n * (C * H n) := mul_le_mul_of_nonneg_left (hmajor N n) (hP n)
        _ = _ := by ring
    have hpT : Summable (fun n => P n * T N n) :=
      Summable.of_nonneg_of_le (fun n => mul_nonneg (hP n) (hT N n)) hu hscale.summable
    have habs_eq : (fun n => |b n| * T N n) =
        (fun n => 2 * (P n * T N n) - b n * T N n) := by
      funext n
      rcases le_total 0 (b n) with h | h
      · simp only [P, abs_of_nonneg h, max_eq_left h]
        ring
      · simp only [P, abs_of_nonpos h, max_eq_right h]
        ring
    have hsum : HasSum (fun n => |b n| * T N n) (2 * ∑' n, P n * T N n) := by
      rw [habs_eq]
      simpa only [sub_zero] using (hpT.hasSum.mul_left (2 : ℝ)).sub (hzero N)
    apply (le_div_iff₀ hc).2
    rw [Finset.sum_mul]
    calc
      _ ≤ ∑ n ∈ Finset.range N, |b n| * T N n := by
        apply Finset.sum_le_sum
        intro n hn
        calc
          _ = |b n| * (c * H n) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hhead N n (Finset.mem_range.mp hn)) (abs_nonneg _)
      _ ≤ ∑' n, |b n| * T N n := hsum.summable.sum_le_tsum _
        (fun n _ => mul_nonneg (abs_nonneg _) (hT N n))
      _ = 2 * ∑' n, P n * T N n := hsum.tsum_eq
      _ ≤ 2 * (C * S) := mul_le_mul_of_nonneg_left
        ((hpT.tsum_le_tsum hu hscale.summable).trans_eq hscale.tsum_eq) zero_le_two
  exact ⟨summable_of_sum_range_le hnonneg hbound, Real.tsum_le_of_sum_range_le hnonneg hbound⟩

end RiemannResearch.Analysis

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis

/-- On a finite head, a positively dominating balanced test turns a bound
on one sign of the charge into a bound on a signed pairing. The remaining
term is the ordinary total variation of the charge outside that head. -/
theorem pairing_le_one_sided_prefix_and_tail (b D T : ℕ → ℝ) (s : Finset ℕ)
    (m P Q K : ℝ) (hb : Summable b)
    (hm : HasSum (fun n => b n * D n) m) (hz : HasSum (fun n => b n * T n) 0)
    (hdom : ∀ n ∈ s, |D n| ≤ T n) (hP : ∀ n ∈ s, T n ≤ P * n)
    (hQ : ∀ n ∉ s, |T n| ≤ Q) (hK : ∀ n ∉ s, |D n| ≤ K) :
    |m| ≤ 2 * P * (∑ n ∈ s, max (b n) 0 * (n : ℝ)) +
      (Q + K) * ∑' n, if n ∈ s then 0 else |b n| := by
  classical
  let H : ℕ → ℝ := fun n => if n ∈ s then max (b n) 0 * (n : ℝ) else 0
  let R : ℕ → ℝ := fun n => if n ∈ s then 0 else |b n|
  have hHs : Summable H :=
    summable_of_ne_finset_zero (s := s) (fun n hn => by simp [H, hn])
  have hHe : (∑' n, H n) = ∑ n ∈ s, max (b n) 0 * (n : ℝ) := by
    rw [tsum_eq_sum (s := s) (fun n hn => by simp [H, hn])]
    exact Finset.sum_congr rfl (fun n hn => by simp [H, hn])
  have hH : HasSum H (∑ n ∈ s, max (b n) 0 * (n : ℝ)) := hHe ▸ hHs.hasSum
  have hR : Summable R := by
    apply Summable.of_nonneg_of_le _ _ hb.abs
    · intro n
      by_cases hn : n ∈ s <;> simp [R, hn, abs_nonneg]
    · intro n
      by_cases hn : n ∈ s <;> simp [R, hn, abs_nonneg]
  have hG := (hH.mul_left (2 * P)).add (hR.hasSum.mul_left (Q + K))
  have upper (v : ℕ → ℝ) (z : ℝ) (hs : HasSum (fun n => b n * v n) z)
      (hhead : ∀ n ∈ s, 0 ≤ v n ∧ v n ≤ 2 * (P * (n : ℝ)))
      (htail : ∀ n ∉ s, |v n| ≤ Q + K) :
      z ≤ 2 * P * (∑ n ∈ s, max (b n) 0 * (n : ℝ)) + (Q + K) * ∑' n, R n := by
    apply hasSum_le _ hs hG
    intro n
    by_cases hn : n ∈ s
    · obtain ⟨hv₀, hv⟩ := hhead n hn
      calc
        b n * v n ≤ max (b n) 0 * v n :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hv₀
        _ ≤ max (b n) 0 * (2 * (P * (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hv (le_max_right _ _)
        _ = _ := by simp only [H, R, if_pos hn, mul_zero, add_zero]; ring
    · calc
        b n * v n ≤ |b n * v n| := le_abs_self _
        _ ≤ |b n| * (Q + K) := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (htail n hn) (abs_nonneg _)
        _ = _ := by simp only [H, R, if_neg hn, mul_zero, zero_add]; ring
  have hp : HasSum (fun n => b n * (T n + D n)) m := by
    simpa only [mul_add, zero_add] using hz.add hm
  have hn : HasSum (fun n => b n * (T n - D n)) (-m) := by
    simpa only [mul_sub, zero_sub] using hz.sub hm
  have hpos := upper _ _ hp (fun n hn => by
    obtain ⟨hl, hr⟩ := abs_le.mp (hdom n hn)
    constructor <;> linarith [hP n hn]) (fun n hn =>
      (abs_add_le (T n) (D n)).trans (add_le_add (hQ n hn) (hK n hn)))
  have hneg := upper _ _ hn (fun n hn => by
    obtain ⟨hl, hr⟩ := abs_le.mp (hdom n hn)
    constructor <;> linarith [hP n hn]) (fun n hn => by
      have hh := (abs_add_le (T n) (-D n)).trans
        (add_le_add (hQ n hn) (show |-(D n)| ≤ K by simpa only [abs_neg] using hK n hn))
      simpa only [sub_eq_add_neg] using hh)
  change |m| ≤ 2 * P * (∑ n ∈ s, max (b n) 0 * (n : ℝ)) + (Q + K) * ∑' n, R n
  exact abs_le.mpr ⟨by linarith, hpos⟩

end RiemannResearch.Analysis

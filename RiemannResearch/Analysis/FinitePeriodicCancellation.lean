import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Exact incomplete-period cancellation

Source: elementary periodic block decomposition, used to repair the return
sampling hypothesis in Noack, `sdf_modified.pdf`, section 14.9.
The complete signed incomplete-period remainder is retained before bounding.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FinitePeriodicCancellation

/-- A whole period has the same sum from every translate. -/
theorem period_sum_shift (Q : ℕ) (g : ℕ → ℝ)
    (hg : ∀ n, g (n + Q) = g n) (a : ℕ) :
    (∑ i ∈ Finset.range Q, g (a + i)) = ∑ i ∈ Finset.range Q, g i := by
  induction a with
  | zero => simp
  | succ a ih =>
    have h1 := Finset.sum_range_succ (fun i => g (a + i)) Q
    have h2 := Finset.sum_range_succ' (fun i => g (a + i)) Q
    have he : (∑ i ∈ Finset.range Q, g (a + 1 + i)) =
        ∑ i ∈ Finset.range Q, g (a + (i + 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      omega
    rw [he]
    simp only [Nat.add_zero, hg] at h1 h2
    linarith

/-- Complete periods cancel; the final incomplete period is retained verbatim. -/
theorem centered_interval_exact (Q : ℕ) (g : ℕ → ℝ)
    (hg : ∀ n, g (n + Q) = g n)
    (hzero : (∑ i ∈ Finset.range Q, g i) = 0) (a k r : ℕ) :
    (∑ i ∈ Finset.range (k * Q + r), g (a + i)) =
      ∑ i ∈ Finset.range r, g (a + k * Q + i) := by
  have hz : ∀ b k, (∑ i ∈ Finset.range (k * Q), g (b + i)) = 0 := by
    intro b k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      have hshift := period_sum_shift Q g hg (b + k * Q)
      simpa [Nat.add_assoc, hzero] using hshift
  rw [Finset.sum_range_add, hz, zero_add]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  omega

/-- No power saving is claimed: the unconditional error is an incomplete-period error. -/
theorem centered_interval_bound (Q : ℕ) (g : ℕ → ℝ)
    (hg : ∀ n, g (n + Q) = g n)
    (hzero : (∑ i ∈ Finset.range Q, g i) = 0)
    (M : ℝ) (hM : ∀ n, |g n| ≤ M) (a k r : ℕ) :
    |∑ i ∈ Finset.range (k * Q + r), g (a + i)| ≤ r * M := by
  rw [centered_interval_exact Q g hg hzero]
  calc
    _ ≤ ∑ i ∈ Finset.range r, |g (a + k * Q + i)| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ _i ∈ Finset.range r, M := Finset.sum_le_sum (fun i hi => hM _)
    _ = _ := by simp

end RiemannResearch.Analysis.FinitePeriodicCancellation

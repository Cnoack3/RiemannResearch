import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Summable discrete summation by parts
Source: user-provided Pareto tail research argument, September 11, 2026.
This is consumed by the actual signed Pareto tail and bounded residue tests.
-/
namespace RiemannResearch.Analysis
noncomputable section
theorem summable_bounded_product {A g : ℕ → ℝ} {C : ℝ}
    (hA : Summable A) (hg : ∀ n, |g n| ≤ C) :
    Summable (fun n => A n * g n) := by
  apply (hA.abs.mul_right C).of_norm_bounded
  intro n
  simpa only [Real.norm_eq_abs, abs_mul] using
    mul_le_mul_of_nonneg_left (hg n) (abs_nonneg (A n))

theorem summable_discrete_summation_by_parts
    {A g : ℕ → ℝ} {C : ℝ} (hA : Summable A) (hzero : A 0 = 0)
    (hg : ∀ n, |g n| ≤ C) :
    (∑' n, (A n - A (n+1))*g n) =
      ∑' n, A n*(g n-g (n-1)) := by
  have hs : Summable (fun n => A n*g n) := summable_bounded_product hA hg
  have hAs : Summable (fun n => A (n+1)) := (summable_nat_add_iff 1).mpr hA
  have ht : Summable (fun n => A (n+1)*g n) := summable_bounded_product hAs hg
  have hu : Summable (fun n => A (n+1)*g (n+1)) :=
    (summable_nat_add_iff 1).mpr hs
  have hv : Summable (fun n => A n*(g n-g (n-1))) :=
    summable_bounded_product hA (fun n =>
      (abs_sub (g n) (g (n-1))).trans (add_le_add (hg n) (hg (n-1))))
  have hshift := hs.tsum_eq_zero_add
  simp only [hzero, zero_mul, zero_add] at hshift
  have hvshift := hv.tsum_eq_zero_add
  simp only [hzero, zero_mul, zero_add, Nat.add_sub_cancel] at hvshift
  calc
    _ = (∑' n, A n*g n) - ∑' n, A (n+1)*g n := by
      rw [← hs.tsum_sub ht]
      apply tsum_congr
      intro n
      ring
    _ = (∑' n, A (n+1)*g (n+1)) - ∑' n, A (n+1)*g n := by rw [hshift]
    _ = ∑' n, A (n+1)*(g (n+1)-g n) := by
      rw [← hu.tsum_sub ht]
      apply tsum_congr
      intro n
      ring
    _ = _ := hvshift.symm
end
end RiemannResearch.Analysis

/-! Ordered finite sums retain their boundary term and need only decay of A,
not summability of A. Source: the same signed-tail research direction above. -/
open scoped BigOperators
open Filter
namespace RiemannResearch.Analysis
theorem ordered_abel_finite (A g : ℕ → ℝ) (hzero : A 0 = 0) (N : ℕ) :
    (∑ n ∈ Finset.range N, A n * (g n - g (n-1))) =
      (∑ n ∈ Finset.range N, (A n - A (n+1)) * g n) + A N * g (N-1) := by
  induction N with
  | zero => simp [hzero]
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    simp only [Nat.add_sub_cancel]
    ring

theorem ordered_abel_tendsto {A g : ℕ → ℝ} {C : ℝ}
    (hzero : A 0 = 0)
    (hA : Tendsto A atTop (nhds 0))
    (hd : Summable (fun n => (A n-A (n+1))*g n))
    (hg : ∀ n, |g n| ≤ C) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, A n*(g n-g (n-1)))
      atTop (nhds (∑' n, (A n-A (n+1))*g n)) := by
  have hb : Tendsto (fun N => A N*g (N-1)) atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have ht : Tendsto (fun N => |A N| * C) atTop (nhds 0) := by
      simpa only [Real.norm_eq_abs, norm_zero, zero_mul] using hA.norm.mul_const C
    exact squeeze_zero (fun _ => norm_nonneg _) (fun N => by
      simpa only [Real.norm_eq_abs, abs_mul] using
        mul_le_mul_of_nonneg_left (hg (N-1)) (abs_nonneg (A N))) ht
  simpa only [ordered_abel_finite A g hzero, add_zero] using
    hd.hasSum.tendsto_sum_nat.add hb
end RiemannResearch.Analysis

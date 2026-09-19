import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A discrete Hardy estimate with the terminal boundary retained

Source: user-provided argument, Section 25.5 of
`RH_First_Coordinate_and_Tail_Capacity_Continuation_2026-09-19.md`.
The finite proof uses square completion. The infinite theorem requires the
weighted terminal square to vanish; its Pareto application supplies this from
the actual weighted Hilbert norm in `ParetoSignedTailRegularity`.
-/

noncomputable section
open scoped BigOperators
open Filter

namespace RiemannResearch.Analysis.DiscreteTailHardy

/-- Finite Hardy estimate; no summability or asymptotic hypothesis is hidden. -/
theorem prefix_le_with_boundary (a q : ℕ → ℝ)
    (hq : ∀ n, 0 ≤ q n)
    (hd : ∀ n : ℕ, 0 < n →
      (n : ℝ) ^ 2 * (a n - a (n + 1)) ^ 2 ≤ q n) (N : ℕ) :
    (∑ k ∈ Finset.range N, a (k + 1) ^ 2) ≤
      4 * (∑ k ∈ Finset.range (N + 1), q k) +
        (2 * (N : ℝ) + 1 / 2) * a (N + 1) ^ 2 := by
  induction N with
  | zero =>
      have hq0 := hq 0
      simp only [Finset.sum_range_zero, zero_add, Finset.sum_range_one,
        Nat.cast_zero, mul_zero]
      positivity
  | succ N ih =>
      have hdN := hd (N + 1) (Nat.succ_pos N)
      have hsquare := sq_nonneg
        (2 * ((N : ℝ) + 1) * (a (N + 1) - a (N + 1 + 1)) -
          (a (N + 1) + a (N + 1 + 1)) / 2)
      have hsquare' := sq_nonneg (a (N + 1) - a (N + 1 + 1))
      have hstep :
          (2 * (N : ℝ) + 3 / 2) * a (N + 1) ^ 2 ≤
            4 * q (N + 1) +
              (2 * (N : ℝ) + 5 / 2) * a (N + 1 + 1) ^ 2 := by
        push_cast at hdN
        nlinarith
      change (∑ k ∈ Finset.range (N + 1), a (k + 1) ^ 2) ≤
        4 * (∑ k ∈ Finset.range (N + 1 + 1), q k) +
          (2 * ((N + 1 : ℕ) : ℝ) + 1 / 2) * a (N + 1 + 1) ^ 2
      rw [Finset.sum_range_succ, Finset.sum_range_succ (f := q)]
      push_cast
      nlinarith

/-- Passing to a vanishing terminal boundary gives a uniform prefix bound. -/
theorem prefix_le (a q : ℕ → ℝ) (hqs : Summable q)
    (hq : ∀ n, 0 ≤ q n)
    (hd : ∀ n : ℕ, 0 < n →
      (n : ℝ) ^ 2 * (a n - a (n + 1)) ^ 2 ≤ q n)
    (hb : Tendsto (fun n : ℕ => (n : ℝ) * a n ^ 2) atTop (nhds 0))
    (N : ℕ) :
    (∑ k ∈ Finset.range N, a (k + 1) ^ 2) ≤ 4 * ∑' k, q k := by
  have hlim : Tendsto
      (fun M : ℕ => 4 * (∑' k, q k) +
        2 * (((M + 1 : ℕ) : ℝ) * a (M + 1) ^ 2))
      atTop (nhds (4 * ∑' k, q k)) := by
    simpa only [Function.comp_def, mul_zero, add_zero] using
      (tendsto_const_nhds.add ((hb.comp (tendsto_add_atTop_nat 1)).const_mul 2))
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [eventually_ge_atTop N] with M hNM
  have hmono : (∑ k ∈ Finset.range N, a (k + 1) ^ 2) ≤
      ∑ k ∈ Finset.range M, a (k + 1) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNM)
      (fun k _ _ => sq_nonneg _)
  have hfinite := prefix_le_with_boundary a q hq hd M
  have hsum := hqs.sum_le_tsum (Finset.range (M + 1)) (fun k _ => hq k)
  have hsq := sq_nonneg (a (M + 1))
  push_cast
  nlinarith

/-- Weighted discrete derivative control and a vanishing boundary imply l². -/
theorem positive_square_summable (a q : ℕ → ℝ) (hqs : Summable q)
    (hq : ∀ n, 0 ≤ q n)
    (hd : ∀ n : ℕ, 0 < n →
      (n : ℝ) ^ 2 * (a n - a (n + 1)) ^ 2 ≤ q n)
    (hb : Tendsto (fun n : ℕ => (n : ℝ) * a n ^ 2) atTop (nhds 0)) :
    Summable (fun k => a (k + 1) ^ 2) :=
  summable_of_sum_range_le (fun k => sq_nonneg _)
    (prefix_le a q hqs hq hd hb)

/-- The full Hardy bound on all positive coordinates, with constant four. -/
theorem positive_square_tsum_le (a q : ℕ → ℝ) (hqs : Summable q)
    (hq : ∀ n, 0 ≤ q n)
    (hd : ∀ n : ℕ, 0 < n →
      (n : ℝ) ^ 2 * (a n - a (n + 1)) ^ 2 ≤ q n)
    (hb : Tendsto (fun n : ℕ => (n : ℝ) * a n ^ 2) atTop (nhds 0)) :
    (∑' k, a (k + 1) ^ 2) ≤ 4 * ∑' k, q k := by
  apply le_of_tendsto (positive_square_summable a q hqs hq hd hb).hasSum.tendsto_sum_nat
  exact Filter.Eventually.of_forall (prefix_le a q hqs hq hd hb)

end RiemannResearch.Analysis.DiscreteTailHardy

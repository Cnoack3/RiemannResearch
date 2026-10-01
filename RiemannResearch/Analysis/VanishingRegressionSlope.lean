/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.WeightedScalarEnergy

/-!
# Bounded regression scatter with slopes tending to zero

Source: a fixed finite-head limit of nonnegative weighted squares.
No limit interchange of a moving or nonsummable series is used.
-/
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.WeightedScalarEnergy

theorem square_le_of_bounded_centered_prefixes
    (w a b t : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (ht : Tendsto t atTop (𝓝 0)) (B : ℝ)
    (hB : ∀ N, square (Finset.range N) w (fun n => b n - t N * a n) ≤ B)
    (M : ℕ) :
    square (Finset.range M) w b ≤ B := by
  have hlim : Tendsto
      (fun N => square (Finset.range M) w (fun n => b n - t N * a n))
      atTop (𝓝 (square (Finset.range M) w b)) := by
    unfold square
    apply tendsto_finsetSum
    intro n hn
    simpa using (tendsto_const_nhds (x := w n)).mul
      (((tendsto_const_nhds (x := b n)).sub (ht.mul_const (a n))).pow 2)
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop M] with N hMN
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hMN)
    (fun n _ _ => mul_nonneg (hw n) (sq_nonneg _))).trans (hB N)

theorem summable_of_bounded_centered_prefixes
    (w a b t : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (ht : Tendsto t atTop (𝓝 0)) (B : ℝ)
    (hB : ∀ N, square (Finset.range N) w (fun n => b n - t N * a n) ≤ B) :
    Summable (fun n => w n * (b n) ^ 2) := by
  apply summable_of_sum_range_le (fun n => mul_nonneg (hw n) (sq_nonneg _))
  intro M
  exact square_le_of_bounded_centered_prefixes w a b t hw ht B hB M

end RiemannResearch.Analysis.WeightedScalarEnergy

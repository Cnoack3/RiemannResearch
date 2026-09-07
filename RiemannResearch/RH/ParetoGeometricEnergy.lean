import RiemannResearch.RH.ParetoGeometricMixture
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Tactic.Ring

/-!
Finite-support Gram identity for the actual geometric mixture.
Source: user-provided total-variance research note, §4.
All sums over the complement are retained through the exact row-tail term.
-/
open scoped BigOperators
open MeasureTheory
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The finite geometric transform has exactly the rational Hankel Gram matrix. -/
theorem geometricKernel_gram_integral (s : Finset ℕ) (f : ℕ → ℝ) :
    (∫ t : ℝ in 0..1, (∑ n ∈ s, f n * geometricProbability n t) ^ 2) =
      ∑ n ∈ s, ∑ m ∈ s, f n * f m * geometricKernel n m := by
  have he : (fun t : ℝ => (∑ n ∈ s, f n * geometricProbability n t) ^ 2) =
      fun t : ℝ => ∑ n ∈ s, ∑ m ∈ s,
        (f n * f m) * (geometricProbability n t * geometricProbability m t) := by
    funext t
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  have hi (n m : ℕ) : IntervalIntegrable
      (fun t : ℝ => (f n * f m) *
        (geometricProbability n t * geometricProbability m t)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold geometricProbability
    fun_prop
  have hs (n : ℕ) : IntervalIntegrable
      (fun t : ℝ => ∑ m ∈ s, (f n * f m) *
        (geometricProbability n t * geometricProbability m t)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold geometricProbability
    fun_prop
  rw [he, intervalIntegral.integral_finsetSum (fun n hn => hs n)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [intervalIntegral.integral_finsetSum (fun m hm => hi n m)]
  apply Finset.sum_congr rfl
  intro m hm
  rw [intervalIntegral.integral_const_mul, geometricProbability_product_integral]

/-- Positivity of every actual rational-kernel finite Gram form. -/
theorem geometricKernel_positive_semidefinite (s : Finset ℕ) (f : ℕ → ℝ) :
    0 ≤ ∑ n ∈ s, ∑ m ∈ s, f n * f m * geometricKernel n m := by
  rw [← geometricKernel_gram_integral]
  exact intervalIntegral.integral_nonneg (by norm_num) (fun t ht => sq_nonneg _)

/-- Exact Dirichlet expansion on a finite index set, retaining the entire omitted-row mass. -/
theorem geometricKernel_finite_energy_identity (s : Finset ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ s, paretoWeight n * f n ^ 2) -
        (∑ n ∈ s, ∑ m ∈ s, f n * f m * geometricKernel n m) =
      (1 / 2 : ℝ) * (∑ n ∈ s, ∑ m ∈ s,
        geometricKernel n m * (f n - f m) ^ 2) +
      ∑ n ∈ s, (paretoWeight n - ∑ m ∈ s, geometricKernel n m) * f n ^ 2 := by
  have hswap : (∑ n ∈ s, ∑ m ∈ s, geometricKernel n m * f m ^ 2) =
      ∑ n ∈ s, ∑ m ∈ s, geometricKernel n m * f n ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    rw [geometricKernel_symm]
  have hsq : (∑ n ∈ s, ∑ m ∈ s, geometricKernel n m * (f n - f m) ^ 2) =
      2 * (∑ n ∈ s, ∑ m ∈ s, geometricKernel n m * f n ^ 2) -
      2 * (∑ n ∈ s, ∑ m ∈ s, f n * f m * geometricKernel n m) := by
    have he (n m : ℕ) : geometricKernel n m * (f n - f m) ^ 2 =
        geometricKernel n m * f n ^ 2 + geometricKernel n m * f m ^ 2 -
          2 * (f n * f m * geometricKernel n m) := by ring
    simp_rw [he, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hswap]
    ring

  have htail : (∑ n ∈ s,
      (paretoWeight n - ∑ m ∈ s, geometricKernel n m) * f n ^ 2) =
      (∑ n ∈ s, paretoWeight n * f n ^ 2) -
      ∑ n ∈ s, ∑ m ∈ s, geometricKernel n m * f n ^ 2 := by
    simp_rw [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [hsq, htail]
  ring

/-- For a cutoff the boundary is explicitly another Pareto tail, not an unknown remainder. -/
theorem geometricKernel_cutoff_energy_identity (N : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.range N, paretoWeight n * f n ^ 2) -
        (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, f n * f m * geometricKernel n m) =
      (1 / 2 : ℝ) * (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        geometricKernel n m * (f n - f m) ^ 2) +
      ∑ n ∈ Finset.range N, paretoWeight (n + N) * f n ^ 2 := by
  rw [geometricKernel_finite_energy_identity]
  simp_rw [geometricKernel_partial_sum, sub_sub_cancel]

/-- The exact boundary identity proves contraction for each finitely supported transform. -/
theorem geometricKernel_cutoff_gram_le (N : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, f n * f m * geometricKernel n m) ≤
      ∑ n ∈ Finset.range N, paretoWeight n * f n ^ 2 := by
  apply sub_nonneg.mp
  rw [geometricKernel_cutoff_energy_identity]
  apply add_nonneg
  · apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro n hn
    apply Finset.sum_nonneg
    intro m hm
    exact mul_nonneg (geometricKernel_pos n m).le (sq_nonneg _)
  · apply Finset.sum_nonneg
    intro n hn
    exact mul_nonneg (paretoWeight_pos (n + N)).le (sq_nonneg _)

end
end RiemannResearch.RH.Pareto

/-!
The full, untruncated rational-kernel energy identity for bounded sequences.
Source: user-provided total-variance research note §4. All infinite sums are
proved absolutely summable from the actual kernel marginals. No spectral
hypothesis is used. Boundedness covers finite legal residue-packet combinations.
-/
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The actual two-copy kernel is absolutely summable on the whole product. -/
theorem geometricKernel_prod_summable :
    Summable (fun p : ℕ × ℕ => geometricKernel p.1 p.2) := by
  apply (summable_prod_of_nonneg (fun p => (geometricKernel_pos p.1 p.2).le)).mpr
  constructor
  · intro n
    exact (geometricKernel_hasSum n).summable
  · simpa only [geometricKernel_tsum] using paretoWeight_hasSum.summable

/-- Multiplication by any bounded function preserves absolute kernel summability. -/
theorem geometricKernel_bounded_summable {h : ℕ × ℕ → ℝ} {C : ℝ}
    (hC : ∀ p, |h p| ≤ C) :
    Summable (fun p => geometricKernel p.1 p.2 * h p) := by
  apply (geometricKernel_prod_summable.mul_right C).of_norm_bounded
  intro p
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (geometricKernel_pos p.1 p.2).le]
  exact mul_le_mul_of_nonneg_left (hC p) (geometricKernel_pos p.1 p.2).le

private theorem bounded_square {f : ℕ → ℝ} {C : ℝ}
    (hC : ∀ n, |f n| ≤ C) (n : ℕ) : |f n ^ 2| ≤ C ^ 2 := by
  rw [abs_of_nonneg (sq_nonneg _)]
  have h0 : 0 ≤ C := le_trans (abs_nonneg (f n)) (hC n)
  have hsq := mul_le_mul (hC n) (hC n) (abs_nonneg _) h0
  simpa only [← pow_two, sq_abs] using hsq

private theorem bounded_cross {f : ℕ → ℝ} {C : ℝ}
    (hC : ∀ n, |f n| ≤ C) (n m : ℕ) : |f n * f m| ≤ C ^ 2 := by
  rw [abs_mul, pow_two]
  exact mul_le_mul (hC n) (hC m) (abs_nonneg _) (le_trans (abs_nonneg _) (hC n))

/-- The full squared-difference energy is finite for every bounded sequence. -/
theorem geometricKernel_difference_summable {f : ℕ → ℝ} {C : ℝ}
    (hC : ∀ n, |f n| ≤ C) :
    Summable (fun p : ℕ × ℕ => geometricKernel p.1 p.2 * (f p.1 - f p.2) ^ 2) := by
  have hA := geometricKernel_bounded_summable (fun p : ℕ × ℕ => bounded_square hC p.1)
  have hB := geometricKernel_bounded_summable (fun p : ℕ × ℕ => bounded_square hC p.2)
  have hX := geometricKernel_bounded_summable (fun p : ℕ × ℕ => bounded_cross hC p.1 p.2)
  apply ((hA.add hB).sub (hX.mul_left 2)).congr
  intro p
  ring

/-- Exact product-index energy, with both infinite tails and every cross term retained. -/
theorem geometricKernel_infinite_energy_identity {f : ℕ → ℝ} {C : ℝ}
    (hC : ∀ n, |f n| ≤ C) :
    (1 / 2 : ℝ) * (∑' p : ℕ × ℕ,
      geometricKernel p.1 p.2 * (f p.1 - f p.2) ^ 2) =
      (∑' n, paretoWeight n * f n ^ 2) -
      ∑' p : ℕ × ℕ, geometricKernel p.1 p.2 * (f p.1 * f p.2) := by
  have hA := geometricKernel_bounded_summable (fun p : ℕ × ℕ => bounded_square hC p.1)
  have hB := geometricKernel_bounded_summable (fun p : ℕ × ℕ => bounded_square hC p.2)
  have hX := geometricKernel_bounded_summable (fun p : ℕ × ℕ => bounded_cross hC p.1 p.2)
  have hleft : (∑' p : ℕ × ℕ, geometricKernel p.1 p.2 * f p.1 ^ 2) =
      ∑' n, paretoWeight n * f n ^ 2 := by
    rw [hA.tsum_prod]
    apply tsum_congr
    intro n
    simpa only [geometricKernel_tsum] using
      (geometricKernel_hasSum n).summable.tsum_mul_right (f n ^ 2)
  have hright : (∑' p : ℕ × ℕ, geometricKernel p.1 p.2 * f p.2 ^ 2) =
      ∑' n, paretoWeight n * f n ^ 2 := by
    have hswap : (∑' m, ∑' n, geometricKernel n m * f m ^ 2) =
        ∑' n, ∑' m, geometricKernel n m * f m ^ 2 :=
      Summable.tsum_comm (f := fun n m => geometricKernel n m * f m ^ 2) hB
    rw [hB.tsum_prod]
    calc
      _ = (∑' m, ∑' n, geometricKernel n m * f m ^ 2) := hswap.symm
      _ = _ := ?_
    apply tsum_congr
    intro n
    calc
      (∑' m, geometricKernel m n * f n ^ 2) =
          ∑' m, geometricKernel n m * f n ^ 2 := by
        apply tsum_congr
        intro m
        rw [geometricKernel_symm]
      _ = _ := by
        simpa only [geometricKernel_tsum] using
          (geometricKernel_hasSum n).summable.tsum_mul_right (f n ^ 2)
  have he : (fun p : ℕ × ℕ => geometricKernel p.1 p.2 * (f p.1 - f p.2) ^ 2) =
      fun p => (geometricKernel p.1 p.2 * f p.1 ^ 2 +
        geometricKernel p.1 p.2 * f p.2 ^ 2) -
        2 * (geometricKernel p.1 p.2 * (f p.1 * f p.2)) := by
    funext p
    ring
  rw [he, (hA.add hB).tsum_sub (hX.mul_left 2), hA.tsum_add hB,
    hX.tsum_mul_left, hleft, hright]
  ring

/-- The full double-series form used in the research note, with convergence discharged. -/
theorem geometricKernel_double_energy_identity {f : ℕ → ℝ} {C : ℝ}
    (hC : ∀ n, |f n| ≤ C) :
    (1 / 2 : ℝ) * (∑' n, ∑' m, geometricKernel n m * (f n - f m) ^ 2) =
      (∑' n, paretoWeight n * f n ^ 2) -
      ∑' n, ∑' m, geometricKernel n m * (f n * f m) := by
  have hE := geometricKernel_difference_summable hC
  have hX := geometricKernel_bounded_summable (fun p : ℕ × ℕ => bounded_cross hC p.1 p.2)
  rw [← hE.tsum_prod, ← hX.tsum_prod]
  exact geometricKernel_infinite_energy_identity hC

/-- Positivity holds for the complete double-series energy. -/
theorem geometricKernel_double_energy_nonneg (f : ℕ → ℝ) :
    0 ≤ (1 / 2 : ℝ) * (∑' n, ∑' m, geometricKernel n m * (f n - f m) ^ 2) := by
  apply mul_nonneg (by norm_num)
  apply tsum_nonneg
  intro n
  apply tsum_nonneg
  intro m
  exact mul_nonneg (geometricKernel_pos n m).le (sq_nonneg _)

end
end RiemannResearch.RH.Pareto

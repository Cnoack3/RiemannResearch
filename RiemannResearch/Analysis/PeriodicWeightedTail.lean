import RiemannResearch.Analysis.PeriodicWeightedMean
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Infinite weighted sums with certified periodic discrepancy

These theorems extend the finite exact Abel argument in
Analysis/PeriodicWeightedMean to convergent infinite sums. The periodic mean
and finite signed-prefix discrepancy remain explicit, so squared residue
combinations retain their signed cross terms. Summability and monotone positive
weights are hypotheses; no arithmetic asymptotic cost provider is assumed.
-/

open Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.PeriodicWeightedTail
open PeriodicWeightedMean

theorem infinite_abel_bound (f w : ℕ → ℝ) (B : ℝ)
    (hs : Summable (fun n => f n * w n))
    (hprefix : ∀ k, |partialSum f k| ≤ B)
    (hw : ∀ n, 0 ≤ w n)
    (hdec : ∀ n, w (n + 1) ≤ w n) :
    |∑' n, f n * w n| ≤ B * w 0 := by
  have ht := hs.hasSum.tendsto_sum_nat.abs
  apply le_of_tendsto ht
  exact Eventually.of_forall (fun n =>
    abel_bound f w n B (fun k _ => hprefix k) (hw n) (fun i _ => hdec i))

theorem infinite_weighted_mean_bound (f w : ℕ → ℝ) (a B : ℝ)
    (hs : Summable (fun n => f n * w n)) (hws : Summable w)
    (hprefix : ∀ k, |partialSum (fun i => f i - a) k| ≤ B)
    (hw : ∀ n, 0 ≤ w n)
    (hdec : ∀ n, w (n + 1) ≤ w n) :
    |(∑' n, f n * w n)-a * (∑' n, w n)| ≤ B * w 0 := by
  have hcs : Summable (fun n => (f n - a)*w n) := by
    simpa only [sub_mul] using hs.sub (hws.mul_left a)
  have he : (∑' n, (f n - a)*w n) = (∑' n, f n * w n)-a * (∑' n, w n) := by
    simp only [sub_mul, hs.tsum_sub (hws.mul_left a), tsum_mul_left]
  rw [← he]
  exact infinite_abel_bound _ w B hcs hprefix hw hdec

theorem periodic_weighted_mean_bound (f w : ℕ → ℝ) (r : ℕ) (a B : ℝ)
    (hr : 0 < r)
    (hper : ∀ i, f (i + r) = f i)
    (hblock : partialSum (fun i => f i - a) r = 0)
    (hshort : ∀ k < r, |partialSum (fun i => f i - a) k| ≤ B)
    (hs : Summable (fun n => f n * w n)) (hws : Summable w)
    (hw : ∀ n, 0 ≤ w n)
    (hdec : ∀ n, w (n + 1) ≤ w n) :
    |(∑' n, f n * w n)-a * (∑' n, w n)| ≤ B * w 0 := by
  apply infinite_weighted_mean_bound f w a B hs hws _ hw hdec
  exact periodic_prefix_bound (fun i => f i - a) r B hr
    (fun i => by rw [hper i]) hblock hshort

theorem nonnegative_periodic_weighted_mean_bound
    (f w : ℕ → ℝ) (r : ℕ) (a : ℝ)
    (hr : 0 < r) (ha : 0 ≤ a)
    (hpos : ∀ i, 0 ≤ f i)
    (hper : ∀ i, f (i + r) = f i)
    (hblock : partialSum f r = (r : ℝ) * a)
    (hs : Summable (fun n => f n * w n)) (hws : Summable w)
    (hw : ∀ n, 0 ≤ w n)
    (hdec : ∀ n, w (n + 1) ≤ w n) :
    |(∑' n, f n * w n)-a * (∑' n, w n)| ≤ ((r : ℝ) * a) * w 0 := by
  exact infinite_weighted_mean_bound f w a _ hs hws
    (nonnegative_periodic_discrepancy f r a hr ha hpos hper hblock) hw hdec

end RiemannResearch.Analysis.PeriodicWeightedTail

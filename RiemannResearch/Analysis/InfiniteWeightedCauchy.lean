import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Infinite weighted Cauchy-Schwarz from complete finite sums

Source: the standard finite Cauchy-Schwarz inequality in Mathlib and passage
through the three convergent complete series. Used by the actual inverse-square
reciprocal head-tail certificate. The signed pairing is never replaced by the
sum of absolute values.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.InfiniteWeightedCauchy

/-- Infinite weighted Cauchy-Schwarz, proved by limits of the exact finite sums. -/
theorem weighted_tsum_cauchy (r a b : ℕ → ℝ)
    (hr : Summable r) (ha : Summable a) (hb : Summable b)
    (ha0 : ∀ i, 0 ≤ a i) (hb0 : ∀ i, 0 ≤ b i)
    (hpoint : ∀ i, (r i) ^ 2 ≤ a i * b i) :
    (∑' i, r i) ^ 2 ≤ (∑' i, a i) * (∑' i, b i) := by
  apply le_of_tendsto_of_tendsto' (hr.hasSum.tendsto_sum_nat.pow 2)
    (ha.hasSum.tendsto_sum_nat.mul hb.hasSum.tendsto_sum_nat)
  intro M
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range M)
    (fun i _ => ha0 i) (fun i _ => hb0 i) (fun i _ => hpoint i)


end RiemannResearch.Analysis.InfiniteWeightedCauchy

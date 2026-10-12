import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Pareto weights and absolute summability

Source: the marginal-weight identities are moved verbatim from
`ParetoGeometricMixture`; the square-to-absolute-summability lemma and its
private helper are moved verbatim from `ParetoGibbsOperator`. These general
weighted-sequence facts are independent of the geometric-mixture and Gibbs
operator proofs. The index `n` represents the positive integer `n + 1`.
-/

open scoped BigOperators
open Filter

namespace RiemannResearch.RH.Pareto
noncomputable section

def paretoWeight (n : ℕ) : ℝ := 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))
theorem paretoWeight_pos (n : ℕ) : 0 < paretoWeight n := by unfold paretoWeight; positivity

/-- The Pareto marginal itself is a first difference. -/
theorem paretoWeight_eq_inv_sub (n : ℕ) :
    paretoWeight n = 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2) := by
  unfold paretoWeight
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  <;> ring

theorem paretoWeight_partial_sum (N : ℕ) :
    (∑ n ∈ Finset.range N, paretoWeight n) = 1 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, paretoWeight_eq_inv_sub]
      push_cast
      ring

private theorem reciprocal_shift_tendsto (a : ℕ) :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + a)) atTop (nhds 0) := by
  have h := tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  simpa only [Function.comp_def, Nat.cast_add, one_div] using h.comp (tendsto_add_atTop_nat a)

theorem paretoWeight_tendsto_zero : Tendsto paretoWeight atTop (nhds 0) := by
  have h := (reciprocal_shift_tendsto 1).sub (reciprocal_shift_tendsto 2)
  change Tendsto (fun n => paretoWeight n) atTop (nhds 0)
  simp_rw [paretoWeight_eq_inv_sub]
  simpa only [Nat.cast_one, Nat.cast_ofNat, sub_self] using h

/-- The full Pareto sequence is normalized; no truncation hypothesis is used. -/
theorem paretoWeight_hasSum : HasSum paretoWeight 1 := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => (paretoWeight_pos n).le) 1).mpr
  simp_rw [paretoWeight_partial_sum]
  simpa using tendsto_const_nhds.sub (reciprocal_shift_tendsto 1)

theorem paretoWeight_tsum : (∑' n, paretoWeight n) = 1 :=
  paretoWeight_hasSum.tsum_eq
private theorem abs_le_square_add_one (x : ℝ) : |x| ≤ x ^ 2 + 1 := by
  nlinarith [sq_nonneg (|x| - 1), sq_abs x]

/-- The full Hilbert-space square condition implies absolute Pareto summability. -/
theorem pareto_abs_summable_of_square {f : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * f n ^ 2)) :
    Summable (fun n => paretoWeight n * |f n|) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (paretoWeight_pos n).le (abs_nonneg _))
    (fun n => ?_) (hf.add paretoWeight_hasSum.summable)
  nlinarith [mul_le_mul_of_nonneg_left (abs_le_square_add_one (f n))
    (paretoWeight_pos n).le]


end
end RiemannResearch.RH.Pareto

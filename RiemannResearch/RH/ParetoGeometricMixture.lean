import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
Source: user-provided argument in
RH_Total_Variance_Geometric_Mixture_and_Hankel_Gap_2026-09-07.md, §§2 and 4.
The elementary beta integrals and the exact marginal telescoping are proved here.
Indices are shifted: n : ℕ represents the original positive integer k = n + 1.
This module does not assume or establish the external sharp Hankel spectral theorem.
-/

open scoped BigOperators
open Filter MeasureTheory

namespace RiemannResearch.RH.Pareto
noncomputable section

def paretoWeight (n : ℕ) : ℝ := 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))
def geometricKernel (n m : ℕ) : ℝ :=
  2 / (((n : ℝ) + m + 1) * ((n : ℝ) + m + 2) * ((n : ℝ) + m + 3))
def geometricProbability (n : ℕ) (t : ℝ) : ℝ := (1 - t) * t ^ n

theorem paretoWeight_pos (n : ℕ) : 0 < paretoWeight n := by unfold paretoWeight; positivity

theorem geometricKernel_pos (n m : ℕ) : 0 < geometricKernel n m := by unfold geometricKernel; positivity

theorem geometricKernel_symm (n m : ℕ) : geometricKernel n m = geometricKernel m n := by
  unfold geometricKernel
  congr 1 <;> ring

theorem geometricProbability_nonneg (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    0 ≤ geometricProbability n t := by
  exact mul_nonneg (sub_nonneg.mpr ht.2) (pow_nonneg ht.1 n)

/-- For every admissible latent parameter the geometric masses sum to one. -/
theorem geometricProbability_hasSum {t : ℝ} (ht : t ∈ Set.Ico 0 1) :
    HasSum (fun n => geometricProbability n t) 1 := by
  have ha : |t| < 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
  simpa only [geometricProbability, mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr ht.2))] using
    (hasSum_geometric_of_abs_lt_one ha).mul_left (1 - t)

private theorem pow_unit_integral (n : ℕ) :
    (∫ t : ℝ in 0..1, t ^ n) = 1 / ((n : ℝ) + 1) := by
  simp [integral_pow]

/-- Mixing the geometricProbability probability with a uniform parameter gives the Pareto mass. -/
theorem geometricProbability_integral (n : ℕ) :
    (∫ t : ℝ in 0..1, geometricProbability n t) = paretoWeight n := by
  have hp (r : ℕ) : IntervalIntegrable (fun t : ℝ => t ^ r) volume 0 1 :=
    (continuous_id.pow r).intervalIntegrable _ _
  have he : geometricProbability n = fun t : ℝ => t ^ n - t ^ (n + 1) := by
    funext t
    simp only [geometricProbability, pow_succ]
    ring
  rw [he, intervalIntegral.integral_sub (hp n) (hp (n + 1))]
  rw [pow_unit_integral, pow_unit_integral]
  unfold paretoWeight
  push_cast
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  <;> ring

/-- The product kernel is the beta integral B(n+m+1,3). -/
theorem geometricProbability_product_integral (n m : ℕ) :
    (∫ t : ℝ in 0..1, geometricProbability n t * geometricProbability m t) = geometricKernel n m := by
  have hp (r : ℕ) : IntervalIntegrable (fun t : ℝ => t ^ r) volume 0 1 :=
    (continuous_id.pow r).intervalIntegrable _ _
  have he : (fun t : ℝ => geometricProbability n t * geometricProbability m t) =
      fun t : ℝ => (t ^ (n + m) - 2 * t ^ (n + m + 1)) + t ^ (n + m + 2) := by
    funext t
    simp only [geometricProbability, pow_succ, pow_add]
    ring
  rw [he, intervalIntegral.integral_add ((hp (n+m)).sub ((hp (n+m+1)).const_mul 2))
    (hp (n+m+2))]
  rw [intervalIntegral.integral_sub (hp (n+m)) ((hp (n+m+1)).const_mul 2)]
  rw [intervalIntegral.integral_const_mul]
  rw [pow_unit_integral, pow_unit_integral, pow_unit_integral]
  unfold geometricKernel
  push_cast
  have h1 : (n : ℝ) + m + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + m + 2 ≠ 0 := by positivity
  have h3 : (n : ℝ) + m + 3 ≠ 0 := by positivity
  field_simp
  <;> ring

/-- Adjacent Pareto masses give exactly the two-copy mixture kernel. -/
theorem geometricKernel_eq_paretoWeight_sub (n m : ℕ) :
    geometricKernel n m = paretoWeight (n + m) - paretoWeight (n + m + 1) := by
  unfold geometricKernel paretoWeight
  push_cast
  have h1 : (n : ℝ) + m + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + m + 2 ≠ 0 := by positivity
  have h3 : (n : ℝ) + m + 3 ≠ 0 := by positivity
  field_simp
  <;> ring

/-- Every finite row sum retains its exact positive tail. -/
theorem geometricKernel_partial_sum (n N : ℕ) :
    (∑ m ∈ Finset.range N, geometricKernel n m) = paretoWeight n - paretoWeight (n + N) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, geometricKernel_eq_paretoWeight_sub]
      simp only [Nat.succ_eq_add_one, Nat.add_assoc]
      ring

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

/-- Exact infinite row marginal of the beta-geometric two-copy kernel. -/
theorem geometricKernel_hasSum (n : ℕ) : HasSum (geometricKernel n) (paretoWeight n) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun m => (geometricKernel_pos n m).le) (paretoWeight n)).mpr
  simp_rw [geometricKernel_partial_sum]
  have h : Tendsto (fun N => paretoWeight (n + N)) atTop (nhds 0) := by
    simpa only [Function.comp_def, Nat.add_comm] using paretoWeight_tendsto_zero.comp (tendsto_add_atTop_nat n)
  simpa using tendsto_const_nhds.sub h

theorem geometricKernel_tsum (n : ℕ) :
    (∑' m, geometricKernel n m) = paretoWeight n :=
  (geometricKernel_hasSum n).tsum_eq

theorem paretoWeight_tsum : (∑' n, paretoWeight n) = 1 :=
  paretoWeight_hasSum.tsum_eq

end
end RiemannResearch.RH.Pareto

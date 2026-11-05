/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.MertensDefectPowerArithmetic
import RiemannResearch.RH.ParetoWeights
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MobiusReciprocal
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MertensAllLogPowers
import RiemannResearch.NumberTheory.PrimeNumberTheorem.Wiener

/-!
# The signed Möbius head correction is a conditional Pareto mean

Discrete Abel summation gives the finite identity. The repository's prime
number theorem makes its total mean zero. Its logarithmic Mertens bound of
order two makes the conditional Pareto expectation absolutely integrable.
The physical integer at zero-based index `j` is `j+1`.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- The finite Abel boundary term with the physical Pareto weights. -/
theorem mertens_pareto_finite_abel (N : ℕ) :
    (∑ j ∈ Finset.range N, paretoWeight j * M ((j+1 : ℕ) : ℝ)) =
      mobiusReciprocalSum N - M (N : ℝ) / ((N : ℝ)+1) := by
  induction N with
  | zero =>
    have hI : Finset.Iic (0 : ℕ) = {0} := by ext k; simp
    simp [mobiusReciprocalSum, M, hI]
  | succ N ih =>
    have hstep : M ((N+1 : ℕ) : ℝ) = M (N : ℝ) + (ArithmeticFunction.moebius (N+1) : ℝ) := by
      rw [M_nat_eq_sum_range, M_nat_eq_sum_range, Finset.sum_range_succ]
    rw [Finset.sum_range_succ, ih, mobiusReciprocalSum_succ, hstep]
    simp only [paretoWeight, Nat.cast_add, Nat.cast_one, Nat.cast_succ]
    rw [show (N : ℝ)+1+1 = (N : ℝ)+2 by ring]
    field_simp [show (N : ℝ)+1 ≠ 0 by positivity, show (N : ℝ)+2 ≠ 0 by positivity]
    <;> ring

/-- The ordinary Mertens function is absolutely integrable against the
physical Pareto probability, unconditionally. -/
theorem mertens_pareto_summable :
    Summable (fun j : ℕ => paretoWeight j * M ((j+1 : ℕ) : ℝ)) := by
  obtain ⟨B, hB, hM⟩ := M_shiftedLog_all_nat_powers 2
  have hphysical : Summable (fun n : ℕ => M (n : ℝ) / ((n : ℝ) * ((n : ℝ)+1))) := by
    apply (summable_inv_mul_log_sq.mul_left B).of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hn0 : (0 : ℝ) < n := by linarith
    have hl := Real.log_pos hn1
    have hsq : (Real.log (n : ℝ))^2 ≤ (6 + Real.log (n : ℝ))^2 := by nlinarith
    have hM' := (mul_le_mul_of_nonneg_left hsq (abs_nonneg (M (n : ℝ)))).trans (hM (n : ℝ) hn1.le)
    change ‖M (n : ℝ) / ((n : ℝ) * ((n : ℝ)+1))‖ ≤ B * ((n : ℝ) * Real.log (n : ℝ)^2)⁻¹
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hn0 (by positivity)), ← div_eq_mul_inv]
    calc
      _ ≤ |M (n : ℝ)| / ((n : ℝ)*(n : ℝ)) :=
        div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hn0 hn0)
          (mul_le_mul_of_nonneg_left (by linarith) hn0.le)
      _ ≤ _ := (div_le_div_iff₀ (mul_pos hn0 hn0) (mul_pos hn0 (sq_pos_of_pos hl))).2 (by
        nlinarith only [mul_le_mul_of_nonneg_left hM' hn0.le])
  apply ((summable_nat_add_iff 1).mpr hphysical).congr
  intro j
  simp only [paretoWeight, Nat.cast_add, Nat.cast_one]
  rw [show (j : ℝ)+1+1 = (j : ℝ)+2 by ring]
  ring

/-- The signed full Pareto mean of M is zero. -/
theorem mertens_pareto_tsum_zero :
    (∑' j : ℕ, paretoWeight j * M ((j+1 : ℕ) : ℝ)) = 0 := by
  have hrat : Tendsto (fun N : ℕ => M (N : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
    M_isLittleO.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hboundary : Tendsto (fun N : ℕ => M (N : ℝ) / ((N : ℝ)+1)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun N : ℕ => |M (N : ℝ) / (N : ℝ)|) _ (by simpa using hrat.abs)
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    rw [Real.norm_eq_abs, abs_div, abs_div, abs_of_pos hN0, abs_of_pos (show 0 < (N : ℝ)+1 by positivity)]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hN0 (by linarith)
  have ht : Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, paretoWeight j * M ((j+1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [mertens_pareto_finite_abel, sub_zero] using mobiusReciprocalSum_tendsto_zero.sub hboundary
  exact tendsto_nhds_unique mertens_pareto_summable.hasSum.tendsto_sum_nat ht

/-- The tail weights in the signed correction have total mass one. -/
theorem mertens_conditional_pareto_mass (N : ℕ) :
    (∑' j : ℕ, ((N : ℝ)+1) * paretoWeight (j+N)) = 1 := by
  have hs := paretoWeight_hasSum.summable.sum_add_tsum_nat_add N
  rw [paretoWeight_tsum, paretoWeight_partial_sum] at hs
  have htail : (∑' j : ℕ, paretoWeight (j+N)) = 1 / ((N : ℝ)+1) := by linarith only [hs]
  rw [tsum_mul_left, htail]
  field_simp

/-- The correction in the exact canonical Möbius head equals minus the
expectation of M under the Pareto law conditioned on the physical site exceeding N. -/
theorem mobius_head_correction_eq_neg_conditional_pareto_mean (N : ℕ) :
    ((N : ℝ)+1) * mobiusReciprocalSum N - M (N : ℝ) =
      -(((N : ℝ)+1) * ∑' j : ℕ, paretoWeight (j+N) * M ((j+N+1 : ℕ) : ℝ)) := by
  have hs := mertens_pareto_summable.sum_add_tsum_nat_add N
  rw [mertens_pareto_tsum_zero, mertens_pareto_finite_abel] at hs
  change mobiusReciprocalSum N - M (N : ℝ) / ((N : ℝ)+1) +
    (∑' j : ℕ, paretoWeight (j+N) * M ((j+N+1 : ℕ) : ℝ)) = 0 at hs
  field_simp [show (N : ℝ)+1 ≠ 0 by positivity] at hs
  nlinarith only [hs]

/-- The whole exact-head defect is a sum of conditionally centered Mertens
values. The centering mean depends on the head alone. -/
theorem canonicalMobiusHead_defect_eq_conditionally_centered_sum
    (N n : ℕ) (hn : 0 < n) :
    1 - canonicalMobiusHead N n = ∑ k ∈ Finset.Icc 1 (n / (N + 1)),
      (M ((n / k : ℕ) : ℝ) -
        ((N : ℝ) + 1) * ∑' j : ℕ, paretoWeight (j + N) * M ((j + N + 1 : ℕ) : ℝ)) := by
  have hN : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by simp
  rw [canonicalMobiusHead_defect_eq_grouped_mertens_sum N n hn, hN,
    mobius_head_correction_eq_neg_conditional_pareto_mean N, Finset.sum_sub_distrib]
  simp [Nat.card_Icc, nsmul_eq_mul]
  <;> ring

end RiemannResearch.RH.Pareto

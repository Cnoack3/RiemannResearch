import RiemannResearch.NumberTheory.PrimeNumberTheorem.PrimeErrorInverseLogSq
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MobiusLogarithmicRateBridge
import RiemannResearch.RH.MobiusReciprocalLogRate
import RiemannResearch.RH.MobiusReciprocalCutoff

/-!
# Unconditional quantitative Möbius rate assembly

The imported MediumPNT error bound, finite logarithmic kernel estimate,
and exact finite Möbius identities give the rate needed for the raw
Hardy endpoint correction. Statement and proof assembly are documented in
HardyEndpointFormalization20260924.md; the PNT source is cited at its import.
-/

noncomputable section
open Filter Finset Asymptotics Real
open scoped Topology BigOperators

namespace RiemannResearch.NumberTheory.PrimeNumberTheorem

theorem M_mul_log_isBigO_from_quantitative_PNT :
    (fun x : ℝ => M x * Real.log x) =O[atTop] id := by
  obtain ⟨C, hC, hR⟩ := R_inverseLogSq_bound
  apply M_mul_log_isBigO_of_sum_abs_R_isBigO
  apply Asymptotics.IsBigO.of_bound (3*C)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  change |∑ k ∈ Finset.Iic ⌊x⌋₊, abs (R (x/k))| ≤ (3*C)*|x|
  rw [abs_of_nonneg (Finset.sum_nonneg (fun k hk => abs_nonneg _)),
    abs_of_nonneg (show 0 ≤ x by linarith)]
  exact sum_abs_R_le_of_log_square_bound hC.le hR x hx

theorem exists_M_mul_log_bound_from_quantitative_PNT :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ y : ℝ in atTop, |M y * Real.log y| ≤ C*y := by
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp M_mul_log_isBigO_from_quantitative_PNT
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  filter_upwards [hC, eventually_ge_atTop (0 : ℝ)] with y hy hy0
  change |M y * Real.log y| ≤ C*|y| at hy
  rw [abs_of_nonneg hy0] at hy
  exact hy.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hy0)

end RiemannResearch.NumberTheory.PrimeNumberTheorem

namespace RiemannResearch.RH.Pareto

/-- Unconditional square-log decay sufficient for the raw Hardy endpoint. -/
theorem mobiusReciprocalSum_sq_mul_log_tendsto_zero :
    Tendsto (fun N : ℕ => (mobiusReciprocalSum N)^2 * Real.log N)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hM⟩ :=
    NumberTheory.PrimeNumberTheorem.exists_M_mul_log_bound_from_quantitative_PNT
  exact square_mul_log_tendsto_zero_of_cutoff_bound mobiusReciprocalSum C hC
    (NumberTheory.PrimeNumberTheorem.mobiusReciprocalSum_eventual_cutoff_bound_of_M_log_bound
      C hC hM)

/-- The exact factor in the normalized raw endpoint correction tends to zero. -/
theorem mobiusReciprocalSum_sq_mul_log_succ_add_half_tendsto_zero :
    Tendsto (fun N : ℕ => (mobiusReciprocalSum N)^2 *
      (Real.log ((N : ℝ)+1) + 1/2)) atTop (𝓝 0) :=
  square_mul_log_succ_add_half_tendsto_zero mobiusReciprocalSum
    mobiusReciprocalSum_sq_mul_log_tendsto_zero

/-- The finite harmonic expression used by the raw endpoint head estimate
has unconditional decay. -/
theorem mobiusReciprocalSum_sq_mul_harmonic_tendsto_zero :
    Tendsto (fun N : ℕ => (mobiusReciprocalSum N)^2 *
      ((∑ n ∈ Finset.range (N+1), 1/(n : ℝ)) + 1)) atTop (𝓝 0) := by
  have he (N : ℕ) :
      (∑ n ∈ Finset.range (N+1), 1/(n : ℝ)) = (harmonic N : ℝ) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, div_zero, add_zero, zero_add]
    simp [harmonic, one_div]
  have hsq : Tendsto (fun N : ℕ => (mobiusReciprocalSum N)^2) atTop (𝓝 0) := by
    simpa using mobiusReciprocalSum_tendsto_zero.pow 2
  have hlim : Tendsto (fun N : ℕ =>
      (mobiusReciprocalSum N)^2 * Real.log N + 2*(mobiusReciprocalSum N)^2)
      atTop (𝓝 0) := by
    simpa using mobiusReciprocalSum_sq_mul_log_tendsto_zero.add (hsq.const_mul 2)
  apply squeeze_zero
    (fun N => mul_nonneg (sq_nonneg _) (add_nonneg
      (Finset.sum_nonneg (fun n hn => by positivity)) zero_le_one)) _ hlim
  intro N
  rw [he N]
  have hH := harmonic_le_one_add_log N
  have hp := mul_le_mul_of_nonneg_left hH (sq_nonneg (mobiusReciprocalSum N))
  nlinarith

end RiemannResearch.RH.Pareto

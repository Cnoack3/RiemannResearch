import RiemannResearch.RH.PrimeOnlyArithmeticBridge
import RiemannResearch.Analysis.FiniteWeightedEnergyComparison
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-! Exact paired Pareto grouping and an unconditional fixed signed-error budget
for the actual corrected prime-only dyadic reduction. -/
noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.PrimeOnlyDyadicEnergy

private theorem weight_nonneg (n : ℕ) : 0 ≤ weight n := by
  unfold weight
  positivity

/-- Pairing both preimages of floor(m/2) gives the exact factor 1/2. -/
theorem paired_weight_error (e : ℕ → ℝ) (he0 : e 0 = 0) (k : ℕ) :
    weight (2 * k) * e ((2 * k) / 2) ^ 2 +
      weight (2 * k + 1) * e ((2 * k + 1) / 2) ^ 2 =
      (1 / 2 : ℝ) * weight k * e k ^ 2 := by
  have heven : 2 * k / 2 = k := by omega
  have hodd : (2 * k + 1) / 2 = k := by omega
  rw [heven, hodd]
  rcases k with _ | k
  · simp [weight, he0]
  · have hk : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
    unfold weight
    push_cast
    field_simp; ring

/-- The finite paired identity retains the complete last odd coordinate. -/
theorem dyadic_shift_even_head (e : ℕ → ℝ) (he0 : e 0 = 0) (N : ℕ) :
    (∑ m ∈ Finset.range (2 * N), weight m * e (m / 2) ^ 2) =
      (1 / 2 : ℝ) * ∑ k ∈ Finset.range N, weight k * e k ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hstep : 2 * (N + 1) = (2 * N + 1) + 1 := by omega
    rw [hstep, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    nlinarith [paired_weight_error e he0 N]

/-- Every finite head of the dyadic shift is controlled by half the complete
error energy. The endpoint is covered by a complete even/odd pair. -/
theorem dyadic_shift_head_le (e : ℕ → ℝ) (he0 : e 0 = 0)
    (he : Summable (fun m => weight m * e m ^ 2)) (N : ℕ) :
    (∑ m ∈ Finset.range N, weight m * e (m / 2) ^ 2) ≤
      (1 / 2 : ℝ) * ∑' m : ℕ, weight m * e m ^ 2 := by
  calc
    _ ≤ ∑ m ∈ Finset.range (2 * (N + 1)), weight m * e (m / 2) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega))
      intro m _ _
      exact mul_nonneg (weight_nonneg m) (sq_nonneg _)
    _ = (1 / 2 : ℝ) * ∑ k ∈ Finset.range (N + 1), weight k * e k ^ 2 :=
      dyadic_shift_even_head e he0 (N + 1)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (he.sum_le_tsum _ (fun m _ => mul_nonneg (weight_nonneg m) (sq_nonneg _)))
      (by norm_num)

/-- A fixed complete error energy gives a fixed finite dyadic difference budget. -/
theorem dyadic_difference_head_le (e : ℕ → ℝ) (he0 : e 0 = 0)
    (he : Summable (fun m => weight m * e m ^ 2)) (N : ℕ) :
    (∑ m ∈ Finset.range N, weight m * (e m - e (m / 2)) ^ 2) ≤
      3 * ∑' m : ℕ, weight m * e m ^ 2 := by
  have hsq : (∑ m ∈ Finset.range N, weight m * (e m - e (m / 2)) ^ 2) ≤
      2 * (∑ m ∈ Finset.range N, weight m * e m ^ 2) +
        2 * ∑ m ∈ Finset.range N, weight m * e (m / 2) ^ 2 := by
    calc
      _ ≤ ∑ m ∈ Finset.range N,
          (2 * (weight m * e m ^ 2) + 2 * (weight m * e (m / 2) ^ 2)) := by
        apply Finset.sum_le_sum
        intro m hm
        have hp : (e m - e (m / 2)) ^ 2 ≤ 2 * e m ^ 2 + 2 * e (m / 2) ^ 2 := by
          nlinarith [sq_nonneg (e m + e (m / 2))]
        have h := mul_le_mul_of_nonneg_left hp (weight_nonneg m)
        nlinarith
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have hhead := he.sum_le_tsum (Finset.range N)
    (fun m _ => mul_nonneg (weight_nonneg m) (sq_nonneg _))
  have hshift := dyadic_shift_head_le e he0 he N
  linarith

/-- The actual arithmetic error budget is independent of the prime cutoff. -/
theorem actual_dyadic_error_budget (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, weight m *
      (psiWindowResidual m - residual N m) ^ 2) ≤
      3 * ∑' m : ℕ, weight m * higherPowerError m ^ 2 := by
  have he0 : higherPowerError 0 = 0 := by
    simp [higherPowerError, psi_eq_chebyshev, theta_eq_chebyshev]
  have hid : (∑ m ∈ Finset.Icc 1 N, weight m *
      (psiWindowResidual m - residual N m) ^ 2) =
      ∑ m ∈ Finset.Icc 1 N, weight m *
        (higherPowerError m - higherPowerError (m / 2)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro m hm
    have h := actual_prime_power_window_identity N m (Finset.mem_Icc.mp hm).2
    rw [h]
    ring
  rw [hid]
  calc
    _ ≤ ∑ m ∈ Finset.range (N + 1), weight m *
      (higherPowerError m - higherPowerError (m / 2)) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        simp only [Finset.mem_Icc, Finset.mem_range] at hm ⊢
        omega
      · intro m _ _
        exact mul_nonneg (weight_nonneg m) (sq_nonneg _)
    _ ≤ _ := dyadic_difference_head_le higherPowerError he0
      summable_higherPowerError_energy (N + 1)

/-- The actual full psi window and corrected prime-only window have equivalent
finite energy bounds up to a fixed unconditional additive error. -/
theorem actual_prime_only_energy_comparison (N : ℕ) :
    ((∑ m ∈ Finset.Icc 1 N, weight m * psiWindowResidual m ^ 2) ≤
      2 * (∑ m ∈ Finset.Icc 1 N, weight m * residual N m ^ 2) +
        6 * ∑' m : ℕ, weight m * higherPowerError m ^ 2) ∧
    ((∑ m ∈ Finset.Icc 1 N, weight m * residual N m ^ 2) ≤
      2 * (∑ m ∈ Finset.Icc 1 N, weight m * psiWindowResidual m ^ 2) +
        6 * ∑' m : ℕ, weight m * higherPowerError m ^ 2) := by
  have h := RiemannResearch.Analysis.sum_weighted_sq_comparison_of_sub_sq_le
    (Finset.Icc 1 N) weight psiWindowResidual (residual N)
    (fun m _ => weight_nonneg m)
    (3 * ∑' m : ℕ, weight m * higherPowerError m ^ 2) (actual_dyadic_error_budget N)
  simpa only [← mul_assoc, show (2 : ℝ) * 3 = 6 by norm_num] using h


/-- The signed energy difference has the sharper square-root comparison.
The cross term is the complete signed weighted pairing with the actual error. -/
theorem actual_prime_only_energy_difference (N : ℕ) :
    |(∑ m ∈ Finset.Icc 1 N, weight m * psiWindowResidual m ^ 2) -
      (∑ m ∈ Finset.Icc 1 N, weight m * residual N m ^ 2)| ≤
      2 * Real.sqrt ((3 * ∑' m : ℕ, weight m * higherPowerError m ^ 2) *
        (∑ m ∈ Finset.Icc 1 N, weight m * residual N m ^ 2)) +
          3 * ∑' m : ℕ, weight m * higherPowerError m ^ 2 := by
  let d : ℝ := ∑ m ∈ Finset.Icc 1 N, weight m *
    (psiWindowResidual m - residual N m) ^ 2
  let c : ℝ := ∑ m ∈ Finset.Icc 1 N, weight m * residual N m *
    (psiWindowResidual m - residual N m)
  have hd0 : 0 ≤ d := Finset.sum_nonneg
    (fun m _ => mul_nonneg (weight_nonneg m) (sq_nonneg _))
  have hd : d ≤ 3 * ∑' m : ℕ, weight m * higherPowerError m ^ 2 :=
    actual_dyadic_error_budget N
  have hp0 : 0 ≤ ∑ m ∈ Finset.Icc 1 N, weight m * residual N m ^ 2 :=
    Finset.sum_nonneg (fun m _ => mul_nonneg (weight_nonneg m) (sq_nonneg _))
  have hcs := RiemannResearch.Analysis.sum_weighted_mul_sq_le
    (Finset.Icc 1 N) weight (residual N)
    (fun m => psiWindowResidual m - residual N m) (fun m _ => weight_nonneg m)
  have hc : c ^ 2 ≤
      (3 * ∑' m : ℕ, weight m * higherPowerError m ^ 2) *
        (∑ m ∈ Finset.Icc 1 N, weight m * residual N m ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_left hd hp0
    dsimp [c, d] at *
    nlinarith [hcs]
  have hca : |c| ≤ Real.sqrt
      ((3 * ∑' m : ℕ, weight m * higherPowerError m ^ 2) *
        (∑ m ∈ Finset.Icc 1 N, weight m * residual N m ^ 2)) := by
    simpa only [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt hc
  have hid :
      (∑ m ∈ Finset.Icc 1 N, weight m * psiWindowResidual m ^ 2) -
        (∑ m ∈ Finset.Icc 1 N, weight m * residual N m ^ 2) = 2 * c + d := by
    dsimp [c, d]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  rw [hid]
  calc
    |2 * c + d| ≤ |2 * c| + |d| := abs_add_le _ _
    _ = 2 * |c| + d := by rw [abs_mul, abs_of_nonneg hd0]; norm_num
    _ ≤ _ := by linarith

end RiemannResearch.RH.PrimeOnlyDyadicEnergy

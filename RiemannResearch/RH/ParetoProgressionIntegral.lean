import RiemannResearch.RH.ParetoProgressionTails
import RiemannResearch.RH.ParetoGeometricMixture
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Exact beta-integral representations of the positive Pareto progression mass.
Positive representatives include r = Q for the zero residue. The singular
quotient at x = 1 is changed only on a null endpoint in the integral.
-/

open scoped BigOperators
open MeasureTheory Set

namespace RiemannResearch.RH.Pareto
noncomputable section

private theorem positiveWeight_geometric_integral (n : ℕ) (hn : 0 < n) :
    (∫ x : ℝ in 0..1, geometricProbability (n - 1) x) = positiveWeight n := by
  rw [geometricProbability_integral]
  simp only [paretoWeight, positiveWeight, Nat.cast_sub (by omega : 1 ≤ n),
    Nat.cast_one]
  congr 1
  ring

private theorem integral_unit_eq_Ioo (f : ℝ → ℝ) :
    (∫ x : ℝ in 0..1, f x) = ∫ x in Ioo (0 : ℝ) 1, f x := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

private theorem progression_geometric_tsum (Q r : ℕ) (hQ : 0 < Q) (hr : 0 < r)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (∑' j : ℕ, geometricProbability (r + Q*j - 1) x) =
      x ^ (r - 1) * (1 - x) / (1 - x ^ Q) := by
  have hpow : |x ^ Q| < 1 := by
    rw [abs_of_nonneg (pow_nonneg hx.1.le Q)]
    exact pow_lt_one₀ hx.1.le hx.2 (by omega)
  have he (j : ℕ) : geometricProbability (r + Q*j - 1) x =
      (x ^ (r - 1) * (1 - x)) * (x ^ Q) ^ j := by
    have hn : r + Q*j - 1 = r - 1 + Q*j := by omega
    simp only [geometricProbability, hn, pow_add, pow_mul]
    ring
  simp_rw [he]
  simpa only [div_eq_mul_inv] using
    ((hasSum_geometric_of_abs_lt_one hpow).mul_left
      (x ^ (r - 1) * (1 - x))).tsum_eq

/-- The actual progression mass is the integral of its geometric residue kernel.
The exchange of integral and infinite sum uses the summable actual Pareto masses. -/
theorem progressionWeight_eq_integral_geometric (Q r : ℕ) (hQ : 0 < Q) (hr : 0 < r) :
    progressionWeight Q r =
      ∫ x : ℝ in 0..1, x ^ (r - 1) * (1 - x) / (1 - x ^ Q) := by
  let F : ℕ → ℝ → ℝ := fun j x => geometricProbability (r + Q*j - 1) x
  have hint (j : ℕ) : IntegrableOn (F j) (Ioo (0 : ℝ) 1) := by
    have hc : Continuous (F j) := by
      dsimp [F, geometricProbability]
      exact (continuous_const.sub continuous_id).mul (continuous_id.pow _)
    exact (hc.intervalIntegrable 0 1).1.mono_set Ioo_subset_Ioc_self
  have hmass (j : ℕ) : (∫ x in Ioo (0 : ℝ) 1, F j x) =
      positiveWeight (r + Q*j) := by
    rw [← integral_unit_eq_Ioo]
    exact positiveWeight_geometric_integral _ (by omega)
  have hnorm (j : ℕ) : (∫ x in Ioo (0 : ℝ) 1, ‖F j x‖) =
      positiveWeight (r + Q*j) := by
    rw [← hmass j]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    change ‖F j x‖ = F j x
    rw [Real.norm_eq_abs]
    exact abs_of_nonneg (geometricProbability_nonneg _ ⟨hx.1.le, hx.2.le⟩)
  have hsum : Summable (fun j : ℕ => ∫ x in Ioo (0 : ℝ) 1, ‖F j x‖) := by
    simp_rw [hnorm]
    exact progressionWeight_summable Q r hQ
  calc
    progressionWeight Q r = ∑' j : ℕ, ∫ x in Ioo (0 : ℝ) 1, F j x := by
      simp_rw [hmass]
      rfl
    _ = ∫ x in Ioo (0 : ℝ) 1, ∑' j : ℕ, F j x :=
      integral_tsum_of_summable_integral_norm hint hsum
    _ = ∫ x in Ioo (0 : ℝ) 1, x ^ (r - 1) * (1 - x) / (1 - x ^ Q) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      exact progression_geometric_tsum Q r hQ hr hx
    _ = _ := (integral_unit_eq_Ioo _).symm

private theorem geometric_denominator_identity (Q : ℕ) (x : ℝ) :
    (∑ j ∈ Finset.range Q, x ^ j) * (1 - x) = 1 - x ^ Q := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [Finset.sum_range_succ, add_mul, ih, pow_succ]
    ring

/-- Cancellation of the geometric factor gives a denominator that is strictly
positive throughout the closed unit interval, including the endpoint x = 1. -/
theorem progressionWeight_eq_integral_polynomial_denominator
    (Q r : ℕ) (hQ : 0 < Q) (hr : 0 < r) :
    progressionWeight Q r =
      ∫ x : ℝ in 0..1, x ^ (r - 1) / (∑ j ∈ Finset.range Q, x ^ j) := by
  rw [progressionWeight_eq_integral_geometric Q r hQ hr]
  apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
  intro x hx
  change x ^ (r - 1) * (1 - x) / (1 - x ^ Q) =
    x ^ (r - 1) / (∑ j ∈ Finset.range Q, x ^ j)
  have hx1 : 1 - x ≠ 0 := sub_ne_zero.mpr (ne_of_gt hx.2)
  rw [← geometric_denominator_identity Q x]
  exact mul_div_mul_right _ _ hx1

end
end RiemannResearch.RH.Pareto

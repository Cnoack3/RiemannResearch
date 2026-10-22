import Mathlib.Probability.CondVar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact conditional variance error decomposition

Source: user-provided argument, RH_Total_Variance_Geometric_Mixture_and_Hankel_Gap_2026-09-07.md,
§2. The law of total variance is Mathlib's classical probability theorem.
These results concern actual integrals and conditional expectations on a probability space.
The optional contraction bound is an explicit hypothesis; no Hankel spectral bound is proved here.
-/

open MeasureTheory
open scoped ProbabilityTheory

namespace ProbabilityTheory

variable {Ω : Type*} {m₀ m : MeasurableSpace Ω} {μ : Measure[m₀] Ω}
  [IsProbabilityMeasure μ] {X : Ω → ℝ}

/-- Exact bias/variance decomposition, with target any real constant. -/
theorem integral_const_sub_sq_eq_bias_sq_add_variance (hX : MemLp X 2 μ) (c : ℝ) :
    (∫ ω, (c - X ω) ^ 2 ∂μ) = (c - ∫ ω, X ω ∂μ) ^ 2 + variance X μ := by
  have hY : MemLp (fun ω => c - X ω) 2 μ := (memLp_const c).sub hX
  have hv := variance_eq_sub hY
  have hmean : (∫ ω, (c - X ω) ∂μ) = c - ∫ ω, X ω ∂μ := by
    rw [integral_sub (integrable_const c) (hX.integrable one_le_two)]
    simp
  simp only [Pi.pow_apply] at hv
  rw [variance_const_sub hX.aestronglyMeasurable c, hmean] at hv
  linarith

/-- Exact law of total variance with every term of the approximation error retained. -/
theorem integral_const_sub_sq_total_variance (hm : m ≤ m₀) (hX : MemLp X 2 μ) (c : ℝ) :
    (∫ ω, (c - X ω) ^ 2 ∂μ) =
      (c - ∫ ω, X ω ∂μ) ^ 2 +
      (∫ ω, condVar m X μ ω ∂μ) + variance (μ[X | m]) μ := by
  rw [integral_const_sub_sq_eq_bias_sq_add_variance hX]
  have h := integral_condVar_add_variance_condExp hm hX
  linarith

/-- Conditional expectation gives exact Pythagoras for squared error to constants. -/
theorem integral_const_sub_sq_condExp_pythagoras (hm : m ≤ m₀)
    (hX : MemLp X 2 μ) (c : ℝ) :
    (∫ ω, (c - X ω) ^ 2 ∂μ) =
      (∫ ω, (c - μ[X | m] ω) ^ 2 ∂μ) + (∫ ω, condVar m X μ ω ∂μ) := by
  rw [integral_const_sub_sq_total_variance hm hX,
    integral_const_sub_sq_eq_bias_sq_add_variance (hX.condExp one_le_two),
    integral_condExp hm]
  ring

/-- The expected conditional variance never exceeds the original variance. -/
theorem integral_condVar_le_variance (hm : m ≤ m₀) (hX : MemLp X 2 μ) :
    (∫ ω, condVar m X μ ω ∂μ) ≤ variance X μ := by
  have h := integral_condVar_add_variance_condExp hm hX
  have hnonneg := variance_nonneg (μ[X | m]) μ
  linarith

/-- Expected conditional variance is the actual squared residual integral. -/
theorem integral_condVar_eq_integral_sq_residual (hm : m ≤ m₀) :
    (∫ ω, condVar m X μ ω ∂μ) = (∫ ω, (X ω - μ[X | m] ω) ^ 2 ∂μ) := by
  rw [condVar, integral_condExp hm]
  rfl

/-- Positivity follows from the residual integral without any spectral hypothesis. -/
theorem integral_condVar_nonneg (hm : m ≤ m₀) :
    0 ≤ (∫ ω, condVar m X μ ω ∂μ) := by
  rw [integral_condVar_eq_integral_sq_residual hm]
  exact integral_nonneg (fun ω => sq_nonneg _)

/-- CONDITIONAL REDUCTION: a separately proved conditional-mean contraction supplies
an energy gap. Its contraction hypothesis is not established in this theorem. -/
theorem conditional_energy_gap_of_variance_contraction (hm : m ≤ m₀)
    (hX : MemLp X 2 μ) {ρ : ℝ}
    (hcontract : variance (μ[X | m]) μ ≤ ρ * variance X μ) :
    (1 - ρ) * variance X μ ≤ (∫ ω, condVar m X μ ω ∂μ) := by
  have h := integral_condVar_add_variance_condExp hm hX
  nlinarith

/-- CONDITIONAL REDUCTION: once a strict contraction has an actual provider,
conditional energy controls the entire squared approximation error. -/
theorem integral_const_sub_sq_le_bias_add_conditional_energy (hm : m ≤ m₀)
    (hX : MemLp X 2 μ) (c : ℝ) {ρ : ℝ} (hρ : ρ < 1)
    (hcontract : variance (μ[X | m]) μ ≤ ρ * variance X μ) :
    (∫ ω, (c - X ω) ^ 2 ∂μ) ≤
      (c - ∫ ω, X ω ∂μ) ^ 2 + (∫ ω, condVar m X μ ω ∂μ) / (1 - ρ) := by
  rw [integral_const_sub_sq_eq_bias_sq_add_variance hX]
  apply add_le_add le_rfl
  apply (le_div_iff₀ (sub_pos.mpr hρ)).2
  have h := conditional_energy_gap_of_variance_contraction hm hX hcontract
  nlinarith

end ProbabilityTheory

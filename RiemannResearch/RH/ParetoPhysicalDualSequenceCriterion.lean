import RiemannResearch.RH.ParetoPhysicalDualCoefficients
import RiemannResearch.RH.ParetoPhysicalDualSupportLimit
import RiemannResearch.RH.ParetoNormClosure

/-! Exact moving-support inverse-defect criterion for the full physical dictionary.
Source: user-provided manuscript, Theorem "Exact finite-support transfer".
The closure/saturation condition remains RH strength; no vanishing defect is proved.
-/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

theorem physicalPrefixInverseDefect_tendsto_zero_iff
    (k n : ℕ → ℕ) (hkn : ∀ j, k j ≤ n j)
    (a : (j : ℕ) → Fin (k j) → ℝ)
    (hn : Tendsto n atTop atTop)
    (ha : Tendsto (fun j => ‖hilbertOne - physicalDualCombination (k j) (a j)‖)
      atTop (𝓝 0)) :
    Tendsto (fun j => physicalPrefixInverseDefect (k j) (n j) (hkn j) (a j))
      atTop (𝓝 0) ↔ hilbertOne ∈ closedSpace := by
  have hineq (j : ℕ) := physicalPrefixInverseDefect_support_transfer
    (k j) (n j) (hkn j) (a j)
  have hleft (j : ℕ) : ‖completeResidual (n j) hilbertOne‖ ≤
      ‖hilbertOne - physicalDualCombination (k j) (a j)‖ +
        Real.sqrt (physicalPrefixInverseDefect (k j) (n j) (hkn j) (a j)) := by
    have h := (abs_le.mp (hineq j)).2
    linarith
  have hright (j : ℕ) :
      Real.sqrt (physicalPrefixInverseDefect (k j) (n j) (hkn j) (a j)) ≤
        ‖hilbertOne - physicalDualCombination (k j) (a j)‖ +
          ‖completeResidual (n j) hilbertOne‖ := by
    have h := (abs_le.mp (hineq j)).1
    linarith
  constructor
  · intro he
    have hsqrt : Tendsto (fun j =>
        Real.sqrt (physicalPrefixInverseDefect (k j) (n j) (hkn j) (a j)))
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, Real.sqrt_zero] using
        (Real.continuous_sqrt.tendsto (0 : ℝ)).comp he
    have hr : Tendsto (fun j => ‖completeResidual (n j) hilbertOne‖)
        atTop (𝓝 0) :=
      squeeze_zero (fun j => norm_nonneg _) hleft (by simpa using ha.add hsqrt)
    have hl : Tendsto (fun j => ‖completeResidual (n j) hilbertOne‖)
        atTop (𝓝 ‖limitResidual‖) := by
      simpa only [Function.comp_def, completeResidual, projection] using projection_norm_error_tendsto.comp hn
    have hz : ‖limitResidual‖ = 0 := tendsto_nhds_unique hl hr
    apply projection_norm_tendsto_zero_iff_mem.mp
    simpa only [hz] using projection_norm_error_tendsto
  · intro hm
    have hr : Tendsto (fun j => ‖completeResidual (n j) hilbertOne‖)
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, completeResidual, projection] using
        (projection_norm_tendsto_zero_iff_mem.mpr hm).comp hn
    have hsqrt : Tendsto (fun j =>
        Real.sqrt (physicalPrefixInverseDefect (k j) (n j) (hkn j) (a j)))
        atTop (𝓝 0) :=
      squeeze_zero (fun j => Real.sqrt_nonneg _) hright (by simpa using ha.add hr)
    have ht := hsqrt.pow 2
    have heq (j : ℕ) :
        Real.sqrt (physicalPrefixInverseDefect (k j) (n j) (hkn j) (a j)) ^ 2 =
          physicalPrefixInverseDefect (k j) (n j) (hkn j) (a j) :=
      Real.sq_sqrt (physicalPrefixInverseDefect_nonneg (k j) (n j) (hkn j) (a j))
    simpa only [heq, zero_pow (by omega : 2 ≠ 0)] using ht

/-- Every unbounded support/cutoff pair retains all composites in its inverse. -/
theorem physicalDualProjection_inverse_criterion
    (k n : ℕ → ℕ) (hkn : ∀ j, k j ≤ n j) (hk : Tendsto k atTop atTop) :
    Tendsto (fun j => physicalPrefixInverseDefect (k j) (n j) (hkn j)
      (physicalDualProjectionCoeff (k j))) atTop (𝓝 0) ↔
        hilbertOne ∈ closedSpace := by
  have hn : Tendsto n atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [tendsto_atTop.mp hk b] with j hj
    exact hj.trans (hkn j)
  have ha : Tendsto (fun j =>
      ‖hilbertOne - physicalDualCombination (k j) (physicalDualProjectionCoeff (k j))‖)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, ← physicalDualProjectionCoeff_spec, physicalDualProjectionResidual] using
      physicalDualProjectionResidual_norm_tendsto_zero.comp hk
  exact physicalPrefixInverseDefect_tendsto_zero_iff k n hkn _ hn ha

/-- Conditional RH consumer: the moving inverse defect is the only open input. -/
theorem riemannHypothesis_of_physicalDualProjection_inverse_defect
    (k n : ℕ → ℕ) (hkn : ∀ j, k j ≤ n j) (hk : Tendsto k atTop atTop)
    (he : Tendsto (fun j => physicalPrefixInverseDefect (k j) (n j) (hkn j)
      (physicalDualProjectionCoeff (k j))) atTop (𝓝 0)) : RiemannHypothesis := by
  have hm := (physicalDualProjection_inverse_criterion k n hkn hk).mp he
  apply riemannHypothesis_of_projection_norm_tendsto_zero
  exact projection_norm_tendsto_zero_iff_mem.mpr hm

end RiemannResearch.RH.Pareto.CoefficientStabilization

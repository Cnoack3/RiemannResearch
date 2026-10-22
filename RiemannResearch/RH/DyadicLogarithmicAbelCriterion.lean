import RiemannResearch.Analysis.LogarithmicAbelGrowth
import RiemannResearch.RH.DyadicRegularizedNormReduction

/-! Actual damping and complete norm criterion from logarithmic integer-conductor
growth. Source: user-provided FourierBridgeUniformSignedEnergy20260910.md,
Sections 9–10. The conductor estimate and the actual-vector identification
are explicit unproved provider hypotheses in the final application. -/

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis
open scoped BigOperators
noncomputable section

/-- The actual damping ratio, with the same real-power convention as the project. -/
theorem triadicDampingRatio_eq_exp (ε : ℝ) :
    triadicDampingRatio ε = Real.exp (-(ε * Real.log 3)) := by
  unfold triadicDampingRatio
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-- Uniform boundedness of the first moment uses no zeta estimate. -/
theorem triadic_damping_first_moment_le_two
    {ε : ℝ} (hε : 0 < ε) (hhalf : ε ≤ 1 / 2) :
    ε * Real.log 3 / (1 - triadicDampingRatio ε) ≤ 2 := by
  rw [triadicDampingRatio_eq_exp]
  apply damping_first_moment_le_two
  · exact mul_pos hε (Real.log_pos (by norm_num))
  · have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    have hlpos : 0 < Real.log 3 := Real.log_pos (by norm_num)
    nlinarith

section BanachUniform

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Uniform full-vector estimate from logarithmic conductor growth. -/
theorem signedIntegerDilationAbel_norm_le_four_mul
    {ε C : ℝ} (hε : 0 < ε) (hhalf : ε ≤ 1 / 2) (hC : 0 ≤ C) (V : ℕ → E)
    (hV : ∀ A : ℕ, 1 ≤ A → ‖V A‖ ≤ C * (1 + ε * Real.log A)) :
    ‖signedIntegerDilationAbel (triadicDampingRatio ε) V‖ ≤ 4 * C := by
  have hq0 : 0 ≤ triadicDampingRatio ε := by
    rw [triadicDampingRatio_eq_exp]
    exact (Real.exp_pos _).le
  have hq1 : triadicDampingRatio ε < 1 := by
    rw [triadicDampingRatio_eq_exp, Real.exp_lt_one_iff]
    exact neg_lt_zero.mpr (mul_pos hε (Real.log_pos (by norm_num)))
  calc
    _ ≤ C * (2 + ε * Real.log 3 / (1 - triadicDampingRatio ε)) :=
      signedIntegerDilationAbel_norm_le_of_log hq0 hq1 V hV
    _ ≤ C * (2 + 2) := by
      apply mul_le_mul_of_nonneg_left _ hC
      have hm := triadic_damping_first_moment_le_two hε hhalf
      linarith
    _ = 4 * C := by ring

omit [CompleteSpace E] in
/-- The energy conclusion is obtained from the norm of the complete signed vector. -/
theorem signedIntegerDilationAbel_energy_le
    {ε C : ℝ} (hε : 0 < ε) (hhalf : ε ≤ 1 / 2) (hC : 0 ≤ C) (V : ℕ → E)
    (hV : ∀ A : ℕ, 1 ≤ A → ‖V A‖ ≤ C * (1 + ε * Real.log A)) :
    (1 / 4 : ℝ) * ‖signedIntegerDilationAbel (triadicDampingRatio ε) V‖ ^ 2
      ≤ 4 * C ^ 2 := by
  have h := signedIntegerDilationAbel_norm_le_four_mul hε hhalf hC V hV
  have hn := norm_nonneg (signedIntegerDilationAbel (triadicDampingRatio ε) V)
  have hs := mul_le_mul h h hn (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hC)
  nlinarith

end BanachUniform

/-- Conditional application to the actual project family. The new mathematical
obligations are exactly the logarithmic estimate and the vector identification;
both appear as hypotheses, and neither is replaced by an assumed final bound. -/
theorem dyadicRegularized_norm_obligations_of_logarithmic_Abel
    (C : ℝ) (hC : 0 ≤ C) (V : ℝ → ℕ → ThresholdHilbert)
    (hlog : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ A : ℕ, 1 ≤ A →
      ‖V ε A‖ ≤ C * (1 + ε * Real.log A))
    (hidentify : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      dyadicRegularizedFamily ε -
        (dyadicQuotientProjection hilbertOne +
          (Real.log 2)⁻¹ • dyadicQuotientProjection (hilbertResidue 2 (by norm_num)) -
          dyadicStepAbelOrbit ε) =
        signedIntegerDilationAbel (triadicDampingRatio ε) (V ε)) :
    DyadicRegularizedSeriesSummable ∧ DyadicRegularizedNormBound ∧
      DyadicTailRegularizedSeriesSummable ∧ DyadicTailRegularizedNormBound := by
  apply dyadicRegularized_norm_obligations_of_bounded_error (4 * C) (by positivity)
  intro ε hε hhalf
  rw [hidentify ε hε hhalf]
  exact signedIntegerDilationAbel_norm_le_four_mul hε hhalf hC (V ε) (hlog ε hε hhalf)

end
end RiemannResearch.RH.Pareto

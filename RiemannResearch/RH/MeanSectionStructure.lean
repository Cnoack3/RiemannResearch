import RiemannResearch.RH.MixedConductorMetricLifting

noncomputable section

namespace RiemannResearch.RH.Pareto.PrimePowerSchur

open CoefficientStabilization

/-- Every continuous linear section of the legal mean differs from the canonical
screened section by a unique mixed-conductor vector. -/
theorem every_mean_section_eq_screened_plus_mixed
    (s : ℝ →L[ℝ] closedSpace)
    (hs : legalPacketMean.comp s = ContinuousLinearMap.id ℝ ℝ) :
    ∃ m : mixedClosure,
      ∀ a : ℝ,
        s a = a •
          (⟨normalizedScreenedTwo,
            screenedPrimeClosure_le_closedSpace
              normalizedScreenedTwo_mem_screenedPrimeClosure⟩ +
            ⟨(m : ThresholdHilbert), mixedClosure_le_closedSpace m.property⟩) := by
  let m : mixedClosure := ⟨(s 1 : ThresholdHilbert) - normalizedScreenedTwo, by
    apply (mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).2
    refine ⟨closedSpace.sub_mem (s 1).property
      (screenedPrimeClosure_le_closedSpace normalizedScreenedTwo_mem_screenedPrimeClosure), ?_⟩
    have hmean : inner ℝ (s 1 : ThresholdHilbert) hilbertOne = 1 := by
      have h := congrArg (fun f : ℝ →L[ℝ] ℝ => f 1) hs
      exact h
    rw [inner_sub_left, hmean, normalizedScreenedTwo_mean, sub_self]⟩
  refine ⟨m, ?_⟩
  intro a
  have hsa : s a = a • s 1 := by
    have h := s.map_smul a (1 : ℝ)
    simpa using h
  rw [hsa]
  congr 1
  apply Subtype.ext
  change (s 1 : ThresholdHilbert) =
    normalizedScreenedTwo + ((m : ThresholdHilbert))
  change (s 1 : ThresholdHilbert) =
    normalizedScreenedTwo + ((s 1 : ThresholdHilbert) - normalizedScreenedTwo)
  abel

/-- The canonical screened section is the unique minimum-norm right inverse
of the legal mean. -/
theorem screenedMeanSection_unique_minimizer
    (s : ℝ →L[ℝ] closedSpace)
    (hs : legalPacketMean.comp s = ContinuousLinearMap.id ℝ ℝ) :
    ‖screenedMeanSection‖ ≤ ‖s‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_screenedMeanSection, legalMeanSection_norm_sq s hs]
  exact le_add_of_nonneg_right (sq_nonneg _)

end RiemannResearch.RH.Pareto.PrimePowerSchur

import RiemannResearch.RH.MixedCaptureLegalTrials
import RiemannResearch.RH.ParetoMellinZeroPairObstruction

/-!
# An explicit upper bound on parity capture from a zeta zero

The physical residual of the optimal legal projection obeys the two-conjugate-zero
Mellin obstruction. Its exact relation to full mixed capture transfers that
obstruction to the conductor-two problem, with a positive numerical gap.
-/

noncomputable section

namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization RiemannResearch.RH.ParetoBeurlingMellinObstruction

private theorem limitProjection_mem_normalizedResidueClosure :
    limitProjection ∈ normalizedResidueClosure := by
  have ha : Set.range residueAtom ⊆ normalizedResidueAtoms := by
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨i + 2, by omega⟩, rfl⟩
  have hs : Submodule.span ℝ (Set.range residueAtom) ≤ normalizedResidueSpan :=
    Submodule.span_mono ha
  have ht := closure_mono (show (↑(Submodule.span ℝ (Set.range residueAtom)) :
    Set ThresholdHilbert) ⊆ normalizedResidueSpan from hs)
  exact ht (closedSpace.starProjection_apply_mem hilbertOne)

/-- A nonreal zero to the right of the line puts a computable positive gap
between the full mixed parity capture and its saturation value. -/
theorem full_mixed_capture_upper_of_zeta_zero (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hi : s.im ≠ 0) (hz : riemannZeta s = 0) :
    ‖mixedClosure.starProjection (ramanujanPacketHilbert 2)‖ ^ 2 ≤
      Real.log 2 - (Real.log 2) ^ 2 / (1 - mellinZeroPairCharge s) ∧
    Real.log 2 - (Real.log 2) ^ 2 / (1 - mellinZeroPairCharge s) <
      Real.log 2 - (Real.log 2) ^ 2 := by
  have he : mellinZeroPairCharge s ≤ limitEnergy :=
    normalizedResidue_error_zeroPair_lower_bound s hs hi hz limitProjection
      limitProjection_mem_normalizedResidueClosure
  have hd := limitEnergy_lt_period5040_bound
  have hp := mellinZeroPairCharge_pos s hs hi
  have hlog : 0 < (Real.log 2) ^ 2 := sq_pos_of_pos (Real.log_pos (by norm_num))
  constructor
  · rw [full_mixed_capture_eq_limitEnergy]
    apply sub_le_sub_left
    exact div_le_div_of_nonneg_left hlog.le (by linarith) (by linarith)
  · apply sub_lt_sub_left
    exact (lt_div_iff₀ (by linarith)).mpr (by nlinarith [mul_pos hlog hp])

end RiemannResearch.RH.Pareto.PrimePowerSchur

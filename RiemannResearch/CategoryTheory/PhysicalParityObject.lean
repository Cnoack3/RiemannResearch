import RiemannResearch.RH.CenteredMeanSquarefreeConverse
import RiemannResearch.RH.CenteredMeanStageSnake
import RiemannResearch.RH.MixedConductorBilinear
import RiemannResearch.RH.PhysicalHeadBoundaryCoordinates
import RiemannResearch.RH.PhysicalHeadQuotientMeasureChange
import RiemannResearch.RH.ScreenedSectionDescent
import RiemannResearch.RH.CanonicalCarryGram
import RiemannResearch.RH.MixedCanonicalCarryCapture

/-!
# The physical parity object in the categorical reconstruction

The same legal and ambient mean rows give the stage snake, the product snake,
the mixed digamma energy and the native Q tests. This interface uses the actual
squarefree converse for the reverse RH implications. All four ordinary mean rows
have zero middle homology independently of the connecting morphism.
-/

noncomputable section
open Filter CategoryTheory CategoryTheory.Limits
open scoped BigOperators Topology
open RiemannResearch.RH RiemannResearch.RH.Pareto RiemannResearch.RH.Pareto.PrimePowerSchur
open RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
open RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis

namespace RiemannResearch.CategoryTheory.PhysicalParityObject

/-- Exact mean rows before and after descent by any mixed submodule. -/
theorem mean_rows_homology_zero (S : Submodule ℝ mixedClosure) :
    IsZero legalMeanComplex.homology ∧ IsZero ambientMeanComplex.homology ∧
    IsZero (Stage.upperRow S).homology ∧ IsZero (Stage.lowerRow S).homology :=
  ⟨legalMeanComplex.exact_iff_isZero_homology.mp legalMean_shortExact.exact,
    ambientMeanComplex.exact_iff_isZero_homology.mp ambientMean_shortExact.exact,
    (Stage.upperRow S).exact_iff_isZero_homology.mp (Stage.upper_shortExact S).exact,
    (Stage.lowerRow S).exact_iff_isZero_homology.mp (Stage.lower_shortExact S).exact⟩

/-- RH, the thirteen original mean conditions and their physical descent,
bilinear, carry, and native-metric equivalents, at any prescribed stage. -/
theorem physical_conditions_tfae (n : ℕ) :
    List.TFAE [
      RiemannHypothesis,
      stageMeanBoundary n 1 = 0,
      boundary = 0,
      normalizedScreenedTwo = hilbertOne,
      hilbertOne ∈ closedSpace,
      limitEnergy = 0,
      Subsingleton BoundaryTarget,
      ∃ s : ℝ →L[ℝ] closedSpace,
        legalPacketMean.comp s = ContinuousLinearMap.id ℝ ℝ ∧ ‖s‖ ≤ 1,
      LegalMeanFactorizationBound 1,
      ∀ ε : ℝ, 0 < ε → ∃ k, ‖parityQuotientClass k‖ ^ 2 < ε,
      BaezDuarte.NaturalApproximation,
      normalizedParityCapture = Real.sqrt (1 / Real.log 2 - 1),
      Tendsto (fun k => packetHeadDeterminant k 1) atTop (𝓝 0),
      packetProductAgrees 2 3 (by decide) (by decide),
      Epi (TopModuleCat.ofHom boundary),
      ∀ v w : closedSpace, Bilinear.defectForm v.val w.val = 0,
      Bilinear.legalPairing = mixedOrthogonalMean.smulRight legalPacketMean,
      ∃ C : ℝ, ∀ k : ℕ, ∃ m ≥ k, ScreenedSectionDescent.tailVariance m normalizedScreenedTwo ≤ C,
      (∑' q : Index, (DigammaParseval.digammaRow q 2) ^ 2) = Real.log 2 - (Real.log 2)^2,
      PhysicalHeadStageAlgebra.productSnake 1 = 0,
      Summable (fun i => (PhysicalHeadBoundaryCoordinates.signedCarry i)^2),
      Summable (fun i : ℕ => ‖PhysicalHeadStageAlgebra.MeasureChange.qRelativeClass (Nat.le_succ i)‖^2),
      Tendsto (fun i => ‖(MixedConductorBasis.MeasureChange.qStage i).mkQ
        MixedConductorBasis.MeasureChange.qParity‖^2) atTop (𝓝 0),
      (∑' i, ‖(MixedConductorBasis.MeasureChange.qLayer i).starProjection
        MixedConductorBasis.MeasureChange.qParity‖^2) =
        (3 / 4 : ℝ) * ((Real.log 2)⁻¹ - 1)^2 + 1 / 4,
      (⨆ F : Finset PhysicalPrimePowerCarryProjection.MixedConductor,
        ENNReal.ofReal (CanonicalCarryClosure.rawUnitGramCost F)) = 1] := by
  have h := categoricalMean_tfae n
  tfae_have 1 ↔ 2 := (stageUnit_zero_iff_RH n).symm
  tfae_have 2 ↔ 3 := h.out 0 1
  tfae_have 2 ↔ 4 := h.out 0 2
  tfae_have 2 ↔ 5 := h.out 0 3
  tfae_have 2 ↔ 6 := h.out 0 4
  tfae_have 2 ↔ 7 := h.out 0 5
  tfae_have 2 ↔ 8 := h.out 0 6
  tfae_have 2 ↔ 9 := h.out 0 7
  tfae_have 2 ↔ 10 := h.out 0 8
  tfae_have 2 ↔ 11 := h.out 0 9
  tfae_have 2 ↔ 12 := h.out 0 10
  tfae_have 2 ↔ 13 := h.out 0 11
  tfae_have 2 ↔ 14 := h.out 0 12
  tfae_have 15 ↔ 1 := boundary_epi_iff_RH
  tfae_have 16 ↔ 4 := Bilinear.defectForm_vanishes_iff
  tfae_have 17 ↔ 4 := Bilinear.legalPairing_eq_meanProduct_iff
  tfae_have 18 ↔ 1 := ScreenedSectionDescent.inner_self_eq_one_iff_cofinal_tailVariance.symm.trans
    ScreenedSectionDescent.inner_self_eq_one_iff_rh
  tfae_have 19 ↔ 5 := DigammaParseval.parity_endpoint_iff_one_mem
  tfae_have 20 ↔ 1 := PhysicalHeadStageAlgebra.productSnake_one_eq_zero_iff_rh
  tfae_have 21 ↔ 1 := PhysicalHeadBoundaryCoordinates.summable_signedCarry_iff_rh
  tfae_have 20 ↔ 22 := PhysicalHeadStageAlgebra.MeasureChange.productSnake_zero_iff_qRelative_summable
  tfae_have 1 ↔ 23 := MixedConductorBasis.MeasureChange.riemannHypothesis_iff_q_parity_descent
  tfae_have 1 ↔ 24 := MixedConductorBasis.MeasureChange.riemannHypothesis_iff_q_layer_saturation
  tfae_have 1 ↔ 25 := CanonicalCarryClosure.riemannHypothesis_iff_rawUnitGramCost_saturates
  tfae_finish

/-- The raw Gram test and the finite corrected-carry capture have the same endpoint. -/
theorem rawGram_iff_correctedCarryCapture :
    (⨆ F : Finset PhysicalPrimePowerCarryProjection.MixedConductor,
      ENNReal.ofReal (CanonicalCarryClosure.rawUnitGramCost F)) = 1 ↔
    Tendsto (fun N : ℕ => ‖(correctedCarrySpace N).starProjection (ramanujanPacketHilbert 2)‖ ^ 2)
      atTop (𝓝 (Real.log 2 - (Real.log 2) ^ 2)) := by
  rw [correctedCarry_capture_tendsto_iff, ← CanonicalCarryClosure.physical_rawCarry_closures.1]
  exact CanonicalCarryClosure.riemannHypothesis_iff_rawUnitGramCost_saturates.symm.trans
    CanonicalCarryClosure.riemannHypothesis_iff_one_mem_canonicalCarryClosure

end RiemannResearch.CategoryTheory.PhysicalParityObject

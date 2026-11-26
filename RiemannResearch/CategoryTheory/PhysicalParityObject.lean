import RiemannResearch.RH.CenteredMeanSquarefreeConverse
import RiemannResearch.RH.CenteredMeanStageSnake
import RiemannResearch.RH.MixedConductorBilinear
import RiemannResearch.RH.PhysicalHeadBoundaryCoordinates
import RiemannResearch.RH.PhysicalHeadQuotientMeasureChange
import RiemannResearch.RH.ScreenedSectionDescent
import RiemannResearch.RH.CanonicalCarryGram
import RiemannResearch.RH.MixedCanonicalCarryCapture
import RiemannResearch.RH.MixedReciprocalDensity

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

open RiemannResearch.RH.ZetaTwoHilbert RiemannResearch.RH.QParetoEquivalence
open RiemannResearch.RH.QPhysicalQuotientMetric
open MeasureChange (qMixed)

/-- The scalar of a physical carry is its transported Pareto mean. -/
def carryMeanQ (v : QHilbert) : ℝ := inner ℝ (paretoEquiv v) hilbertOne

/-- The physical sequence of the Pareto mean-one section. -/
def transportedCarry : QHilbert := paretoEquiv.symm normalizedScreenedTwo

/-- The native Q orthogonal representative of the same scalar class. -/
def nativeCarry : QHilbert := transportedCarry - qMixed.starProjection transportedCarry

theorem transportedCarry_mean : carryMeanQ transportedCarry = 1 := by
  simpa only [carryMeanQ, transportedCarry, paretoEquiv.apply_symm_apply] using
    normalizedScreenedTwo_mean

theorem nativeCarry_data :
    nativeCarry ∈ physicalSpace closedSpace ∧ nativeCarry ∈ qMixedᗮ ∧
      carryMeanQ nativeCarry = 1 := by
  have hp : paretoEquiv (qMixed.starProjection transportedCarry) ∈ mixedClosure :=
    qMixed.starProjection_apply_mem transportedCarry
  have hpu := (mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mp hp
  have hu := screenedPrimeClosure_le_closedSpace normalizedScreenedTwo_mem_screenedPrimeClosure
  refine ⟨?_, qMixed.sub_starProjection_mem_orthogonal _, ?_⟩
  · change paretoEquiv (transportedCarry - qMixed.starProjection transportedCarry) ∈ closedSpace
    rw [map_sub, transportedCarry, paretoEquiv.apply_symm_apply]
    exact closedSpace.sub_mem hu hpu.1
  · change inner ℝ (paretoEquiv (transportedCarry - qMixed.starProjection transportedCarry))
      hilbertOne = 1
    rw [map_sub, inner_sub_left, hpu.2, sub_zero]
    exact transportedCarry_mean

/-- Screen any legal physical input in native Q using its Pareto carry scalar. -/
theorem nativeCarry_screen {v : QHilbert} (hv : v ∈ physicalSpace closedSpace) :
    v - qMixed.starProjection v = carryMeanQ v • nativeCarry := by
  have h := nativeCarry_data
  have hm : v - carryMeanQ v • nativeCarry ∈ qMixed := by
    change paretoEquiv (v - carryMeanQ v • nativeCarry) ∈ mixedClosure
    apply (mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).2
    rw [map_sub, map_smul]
    refine ⟨closedSpace.sub_mem hv (closedSpace.smul_mem _ h.1), ?_⟩
    rw [inner_sub_left, real_inner_smul_left]
    change carryMeanQ v - carryMeanQ v * carryMeanQ nativeCarry = 0
    rw [h.2.2, mul_one, sub_self]
  have he := qMixed.starProjection_eq_self_iff.mpr hm
  rw [map_sub, map_smul,
    qMixed.starProjection_apply_eq_zero_iff.mpr h.2.1, smul_zero, sub_zero] at he
  rw [he]
  abel

/-- The native Q normal line inside the legal physical space. -/
theorem nativeCarry_normal_line :
    physicalSpace closedSpace ⊓ qMixedᗮ = Submodule.span ℝ {nativeCarry} := by
  apply le_antisymm
  · intro v hv
    obtain ⟨hlegal, horth⟩ := hv
    have he := nativeCarry_screen hlegal
    rw [qMixed.starProjection_apply_eq_zero_iff.mpr horth, sub_zero] at he
    exact Submodule.mem_span_singleton.mpr ⟨carryMeanQ v, he.symm⟩
  · apply Submodule.span_le.mpr
    rintro v (rfl : v = nativeCarry)
    exact ⟨nativeCarry_data.1, nativeCarry_data.2.1⟩

/-- Only the zero physical vector can be orthogonal to the mixed dictionary in both metrics. -/
theorem mixed_orthogonal_both_eq_zero {v : QHilbert}
    (hp : paretoEquiv v ∈ mixedClosureᗮ) (hq : v ∈ qMixedᗮ) : v = 0 := by
  let F := (innerSL ℝ (paretoEquiv v)).comp paretoEquiv.toContinuousLinearMap
  have hm : MixedReciprocalDensity.mixed ≤ F.ker := by
    intro m hm'
    change inner ℝ (paretoEquiv v) (paretoEquiv m) = 0
    exact (real_inner_comm _ _).trans (hp _ hm')
  have hb : MixedReciprocalDensity.mixed.map QDensityMetric.B.toLinearMap ≤ F.ker := by
    rintro _ ⟨m, hm', rfl⟩
    change inner ℝ (paretoEquiv v) (paretoEquiv (QDensityMetric.B m)) = 0
    simp only [paretoEquiv_apply]
    rw [← QDensityMetricInverse.q_inner_density]
    exact (real_inner_comm _ _).trans (hq m hm')
  have ht := Submodule.topologicalClosure_minimal _ (sup_le hm hb) F.isClosed_ker
  rw [MixedReciprocalDensity.mixed_augmented_dense] at ht
  have hz : inner ℝ (paretoEquiv v) (paretoEquiv v) = 0 :=
    ht (show v ∈ (⊤ : Submodule ℝ QHilbert) from trivial)
  have h := (inner_self_eq_zero (𝕜 := ℝ)).mp hz
  exact paretoEquiv.injective (h.trans paretoEquiv.map_zero.symm)

/-- The two mean-one representatives genuinely differ on the same physical sites. -/
theorem nativeCarry_ne_transportedCarry : nativeCarry ≠ transportedCarry := by
  intro he
  have hp : paretoEquiv transportedCarry ∈ mixedClosureᗮ := by
    rw [transportedCarry, paretoEquiv.apply_symm_apply, normalizedScreenedTwo,
      ← fullScreening_packet]
    exact mixedClosure.orthogonal.smul_mem _ (fullScreening_mem_orthogonal _)
  have hq := nativeCarry_data.2.1
  rw [he] at hq
  have hz := mixed_orthogonal_both_eq_zero hp hq
  have hmean := transportedCarry_mean
  rw [hz, carryMeanQ, map_zero, inner_zero_left] at hmean
  exact zero_ne_one hmean

/-- The entire physical change in the mixed fit on legal inputs has rank one. -/
theorem native_minus_pareto_fit {v : QHilbert} (hv : v ∈ physicalSpace closedSpace) :
    qMixed.starProjection v - paretoEquiv.symm (mixedClosure.starProjection (paretoEquiv v)) =
      carryMeanQ v • (transportedCarry - nativeCarry) := by
  have h := fullScreening_eq_mean_smul (show paretoEquiv v ∈ closedSpace from hv)
  change paretoEquiv v - mixedClosure.starProjection (paretoEquiv v) =
    carryMeanQ v • normalizedScreenedTwo at h
  have hp := congrArg (fun x => paretoEquiv.symm x) h
  simp only [map_sub, map_smul, paretoEquiv.symm_apply_apply] at hp
  change v - paretoEquiv.symm (mixedClosure.starProjection (paretoEquiv v)) =
    carryMeanQ v • transportedCarry at hp
  rw [smul_sub, ← hp, ← nativeCarry_screen hv]
  abel

/-- Every actual packet has its von Mangoldt scalar on the native Q carry line. -/
theorem nativeCarry_packet (q : ℕ) (hq : 1 < q) :
    let x := paretoEquiv.symm (ramanujanPacketHilbert q)
    x - qMixed.starProjection x = ArithmeticFunction.vonMangoldt q • nativeCarry := by
  let x := paretoEquiv.symm (ramanujanPacketHilbert q)
  have hv : x ∈ physicalSpace closedSpace := by
    change paretoEquiv (paretoEquiv.symm (ramanujanPacketHilbert q)) ∈ closedSpace
    rw [paretoEquiv.apply_symm_apply]
    exact packet_mem_closedSpace q hq
  have hm : carryMeanQ x = ArithmeticFunction.vonMangoldt q := by
    change inner ℝ (paretoEquiv (paretoEquiv.symm (ramanujanPacketHilbert q))) hilbertOne = _
    rw [paretoEquiv.apply_symm_apply, hilbert_inner_one,
      hilbertSequence_ramanujanPacketHilbert, paretoMean_ramanujanPacket]
  exact (nativeCarry_screen hv).trans (congrArg (fun a : ℝ => a • nativeCarry) hm)

end RiemannResearch.CategoryTheory.PhysicalParityObject

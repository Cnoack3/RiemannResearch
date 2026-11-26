import Lean.Elab.Command
import Lean.AddDecl
import Lean.Util.ReplaceExpr
import RiemannResearch.GroupTheory.AddSubgroupCRT
import RiemannResearch.LinearAlgebra.WeightedFiniteQuotient
import RiemannResearch.LinearAlgebra.WeightedQuotientDefectRank
import RiemannResearch.Analysis.ContinuousBiorthogonalDeletion
import RiemannResearch.RH.PhysicalHeadResidualLift
import RiemannResearch.NumberTheory.GeneralizedCRTDescentTargets
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.LinearAlgebra.WeightedQuotientHilbert
import RiemannResearch.RH.NaturalMobiusSourceLimits
import RiemannResearch.NumberTheory.SquarefreeCumulantPair
import RiemannResearch.NumberTheory.SquarefreeCumulantTower
import RiemannResearch.NumberTheory.SquarefreeCumulantLimit
import RiemannResearch.RH.SquarefreeMobiusProjection
import RiemannResearch.RH.QConductorCoefficientMass
import RiemannResearch.RH.QSimultaneousCRT
import RiemannResearch.Analysis.FiniteWeightedPushforward
import RiemannResearch.Analysis.FiniteWeightedRefinement
import RiemannResearch.RH.QWeightedResidueMaps
import RiemannResearch.NumberTheory.PrimeResidueTopology
import RiemannResearch.NumberTheory.FiniteGeneralizedCRT
import RiemannResearch.NumberTheory.ProfiniteGeneralizedCRT
import RiemannResearch.NumberTheory.ProfiniteCRT
import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.QFullDivisorProjection
import RiemannResearch.RH.QInfiniteSquarefreeCarry
import RiemannResearch.NumberTheory.ProfiniteCRTUniversal
import RiemannResearch.RH.QDisplacementProfiniteContinuity
import RiemannResearch.Analysis.ResidualCorrectionCost
import RiemannResearch.Logic.EquivalenceRelationCRT
import RiemannResearch.RH.QFullResidualCorrectionCost
import RiemannResearch.Topology.CompactConstraintGluing
import RiemannResearch.Analysis.CompactConstraintEnergy
import RiemannResearch.Analysis.FiniteCoordinateCompletion
import RiemannResearch.Analysis.FiniteMoorePenrose
import RiemannResearch.Analysis.HilbertConstraintReconstruction
import RiemannResearch.Analysis.ResidualCorrelationCost
import RiemannResearch.CategoryTheory.FiniteFamilyCRT
import RiemannResearch.CategoryTheory.LocalFamilyCRT
import RiemannResearch.LinearAlgebra.CRTReconstructionObstructions
import RiemannResearch.NumberTheory.InfiniteCRTObstruction
import RiemannResearch.Analysis.CompactMatchingQuotient
import RiemannResearch.Analysis.FiniteSingularGramReconstruction
import RiemannResearch.Analysis.WeakCompactConstraints
import RiemannResearch.CategoryTheory.FunctorCRT
import RiemannResearch.CategoryTheory.QuotientMatchingCRT
import RiemannResearch.Analysis.HilbertConstraintEnergy
import RiemannResearch.CategoryTheory.OverlapEqualizerCRT
import RiemannResearch.CategoryTheory.RegularCategoryCRT
import RiemannResearch.RH.QFullCorrectionBudgetDescent
import RiemannResearch.RH.PrimePowerPacketSummation
import RiemannResearch.RH.ScreenedPrimePowerTelescope
import RiemannResearch.RH.MixedConductorCaptureGains
import RiemannResearch.CategoryTheory.AtomCarryPresentation
import RiemannResearch.NumberTheory.PrimePowerCRTDecomposition
import RiemannResearch.RH.RamanujanFiniteIdentities
import RiemannResearch.RH.ResidueAtomIndependence
import RiemannResearch.RH.CRTCarryRamanujanCoordinates
import RiemannResearch.RH.FiniteAtomCarryCRT
import RiemannResearch.RH.MixedParityProjectionDPP
import RiemannResearch.RH.FullConductorRamanujanTransform
import RiemannResearch.RH.UniversalAtomCarryPresentation
import RiemannResearch.RH.AllCertifiedCarrySpan
import RiemannResearch.RH.CertifiedCarryComposition
import RiemannResearch.RH.FiniteCarryRamanujanDictionary
import RiemannResearch.RH.UniversalCarryRamanujanSynthesis
import RiemannResearch.RH.ArithmeticResidueMomentEnergy
import RiemannResearch.RH.ConductorReconstructionEnergy
import RiemannResearch.RH.ConductorTowerCompletions
import RiemannResearch.RH.FiniteAtomCarryRefinement
import RiemannResearch.RH.PhysicalCarryGram
import RiemannResearch.RH.PhysicalPrimePowerCarryProjection
import RiemannResearch.RH.QFullDisplacementFiniteHeads
import RiemannResearch.RH.MixedCanonicalCarryCapture
import RiemannResearch.RH.MixedParityCarry
import RiemannResearch.RH.MixedParityCofinalSubpower
import RiemannResearch.RH.MixedConductorContractiveSection
import RiemannResearch.RH.MixedConductorMetricLifting
import RiemannResearch.RH.MeanSectionStructure
import RiemannResearch.RH.EveryMeanSectionDecomposition
import RiemannResearch.RH.MixedConductorSplitExact
import RiemannResearch.RH.FiniteAtomCarryFunctor
import RiemannResearch.CategoryTheory.All
import RiemannResearch.RH.MixedConductorSquareZero
import RiemannResearch.RH.MixedConductorMetricCokernel
import RiemannResearch.RH.MixedConductorHilbertBasis
import RiemannResearch.RH.MixedConductorBlockSplitting
import RiemannResearch.RH.MixedConductorPrimeSupport
import RiemannResearch.RH.CenteredMeanSnake
import RiemannResearch.RH.CenteredMeanQuotients
import RiemannResearch.RH.MixedParitySupportBounds
import RiemannResearch.RH.MixedConductorGlobalParseval
import RiemannResearch.RH.MixedConductorSupportSnake
import RiemannResearch.RH.PrimeSupportCokernel
import RiemannResearch.RH.PrimeSupportParityQuotient
import RiemannResearch.RH.PrimeSupportParityDescent
import RiemannResearch.RH.MixedConductorPolarizedParseval
import RiemannResearch.RH.MixedConductorGramBoundary
import RiemannResearch.RH.MixedConductorGramZeroFree
import RiemannResearch.RH.MixedConductorProjectedGram
import RiemannResearch.RH.MixedConductorAbsoluteBoundary
import RiemannResearch.RH.MixedConductorGramSites
import RiemannResearch.RH.MixedOrthogonalMean
import RiemannResearch.CategoryTheory.SquarefreeResidueCRT
import RiemannResearch.RH.CenteredMeanLongExact
import RiemannResearch.RH.PrimeSupportAlgebraDescent
import RiemannResearch.RH.CenteredMeanRHCriteria
import RiemannResearch.RH.ParetoAffineHeadTower
import RiemannResearch.RH.ZetaTwoAffineHeadTower
import RiemannResearch.RH.CenteredParityFiniteTrials
import RiemannResearch.RH.CenteredMeanFiniteDescent
import RiemannResearch.RH.SiteGramStrictStages
import RiemannResearch.RH.CenteredMeanAmbientGeometry
import RiemannResearch.RH.MixedConductorBimodule
import RiemannResearch.RH.ConductorTowerLimit
import RiemannResearch.RH.HausdorffSupportColimit
import RiemannResearch.RH.AlgebraicSupportColimit
import RiemannResearch.RH.CenteredMeanStageSnake
import RiemannResearch.RH.MixedConductorStrictDescent
import RiemannResearch.RH.TernaryMixedOrbitObstruction
import RiemannResearch.RH.MixedPrimeCorrelationSeries
import RiemannResearch.RH.CenteredMeanDigammaSection
import RiemannResearch.RH.CenteredMeanDyadicGram
import RiemannResearch.RH.CenteredMeanGramUpperBound
import RiemannResearch.RH.ScreenedMeanDilationTests
import RiemannResearch.RH.CenteredMeanQuotientNorm
import RiemannResearch.RH.CenteredMeanQuotientTail
import RiemannResearch.RH.CenteredMeanGramTail
import RiemannResearch.RH.CenteredMeanPeriodicGramTail
import RiemannResearch.RH.CenteredMeanMellinDescent
import RiemannResearch.RH.CenteredMeanMovingGramTail
import RiemannResearch.RH.CenteredMeanDriftWindows
import RiemannResearch.RH.CenteredMeanMellinCharacters
import RiemannResearch.RH.CenteredMeanProgressionGramTail
import RiemannResearch.RH.DyadicParityGramRow
import RiemannResearch.RH.MixedConductorL1Closure
import RiemannResearch.RH.CenteredMeanParityGramSix
import RiemannResearch.RH.DyadicParityGramCapacity
import RiemannResearch.RH.DyadicParityTwoStageGram
import RiemannResearch.RH.LegalTailMeanCapacity
import RiemannResearch.RH.CenteredMeanDriftCutoffs
import RiemannResearch.RH.CenteredParityDilationCapacity
import RiemannResearch.RH.LegalTailMeanCapacityMellin
import RiemannResearch.RH.CenteredMeanDyadicDrift
import RiemannResearch.RH.CenteredMeanLateSolveBarrier
import RiemannResearch.RH.CenteredMeanBurnolStageBarrier
import RiemannResearch.RH.MixedConductorBilinear
import RiemannResearch.RH.CenteredMeanSquarefreeConverse
import RiemannResearch.RH.CenteredMeanTwoSeedConverse
import RiemannResearch.RH.LegalTailMeanCapacityConjugate
import RiemannResearch.RH.LegalTailMeanCapacityDilation
import RiemannResearch.RH.CenteredMeanUnitNorm
import RiemannResearch.RH.PrimeMultipleGramRepair
import RiemannResearch.RH.MixedPacketDensityTests
import RiemannResearch.RH.PhysicalHeadMixedInterpolation
import RiemannResearch.RH.PhysicalHeadSnakeSections
import RiemannResearch.RH.PhysicalHeadSectionGrowth
import RiemannResearch.RH.PhysicalHeadFiniteMinimum
import RiemannResearch.RH.PhysicalHeadSectionLog
import RiemannResearch.RH.PhysicalHeadPacketSquare
import RiemannResearch.RH.PhysicalHeadStageAlgebra
import RiemannResearch.RH.PhysicalHeadStageAlgebraComparison
import RiemannResearch.RH.PhysicalHeadAlgebraSnake
import RiemannResearch.RH.PhysicalHeadLayerIsometry
import RiemannResearch.RH.PhysicalHeadProductSnake
import RiemannResearch.RH.PhysicalHeadInfiniteBoundary
import RiemannResearch.RH.PhysicalHeadSequenceCokernel
import RiemannResearch.RH.PhysicalHeadBoundaryCoordinates
import RiemannResearch.RH.MixedParityDigammaParseval
import RiemannResearch.RH.CanonicalCarryClosure
import RiemannResearch.RH.CanonicalCarryGram
import RiemannResearch.RH.MixedParityQuotientDescent

/-!
# Chronological reconstruction of the categorical RH development

This module rechecks the authored declarations in the categorical CRT, carry,
quotient, section, and boundary development and its indexed applications.
The original inventory uses `91f07fdffb60bc8a9b820800dbfa3ef33b14278d`.
The final entry adds the physical quotient descent at `e684cf2b1d15c084044dff7d3e15cb406bac2ad6`.
Each heading gives the first recorded occurrence. Historical imports order modules
within a commit, paths break ties, and declarations follow their original source order.

The Lean kernel checks the current stored proof or defining term against its
type in the imported dependency environment. Each check uses a temporary
name and discards the resulting environment. Inductive families are rebuilt
with their constructors, and explicit field projections are checked next.
Git links in the declaration index recover earlier statements and proofs.
The kernel operation follows Lean's own `Lean.Replay` implementation.
-/

open Lean Elab Command

namespace RiemannResearch.CategoryTheory.Rebuild

private def replayName (name : Name) : Name :=
  `RiemannResearch.TemporaryKernelReplay ++ name

private def inductiveReplay (env : Kernel.Environment) (v : InductiveVal) : CommandElabM Declaration := do
  let renameType := Expr.replace fun e => match e with
    | .const n us => if v.all.contains n then some (.const (replayName n) us) else none
    | _ => none
  let types ← v.all.mapM fun n => do
    let some (.inductInfo member) := env.find? n | throwError "missing inductive {n}"
    let ctors ← member.ctors.mapM fun c => do
      let some (.ctorInfo ctor) := env.find? c | throwError "missing constructor {c}"
      pure ({ name := replayName c, type := renameType ctor.type } : Constructor)
    pure ({ name := replayName n, type := renameType member.type, ctors } : InductiveType)
  return .inductDecl v.levelParams v.numParams types false

/-- Recheck each original body or inductive family in the current dependency environment.
    Each kernel environment returned by the check is discarded. -/
elab "#recheck_categorical " owner:ident " in " scope:ident " [" ids:ident,* "]" : command => do
  let fullEnv ← getEnv
  let env := fullEnv.toKernelEnv
  let ownerName := owner.getId
  let some idx := fullEnv.getModuleIdx? ownerName | throwError "module {ownerName} is not imported"
  let data := fullEnv.header.moduleData[idx]!
  let ns := if scope.getId.toString == "_root_" then Name.anonymous else scope.getId
  for id in ids.getElems do withRef id do
    let publicName := ns ++ id.getId
    let names := [publicName, mkPrivateNameCore ownerName publicName]
    let candidates := names.filterMap fun n => data.constants.find? fun c => c.name == n
    let [ci] := candidates |
      throwError "expected one declaration {publicName} in {ownerName}"
    let n := ci.name
    if ci.isUnsafe || ci.isPartial then throwError "unexpected declaration safety for {n}"
    let d : Declaration ← match ci with
      | .thmInfo v => pure (.thmDecl { v with name := replayName n })
      | .defnInfo v => pure (.defnDecl { v with name := replayName n })
      | .opaqueInfo v => pure (.opaqueDecl { v with name := replayName n })
      | .inductInfo v => inductiveReplay env v
      | _ => throwError "expected a definition, theorem, or inductive family at {n}"
    if let .error ex := env.addDeclCore 0 0 d none then
      throwError "kernel rejected {n}: {ex.toMessageData {}}"

end RiemannResearch.CategoryTheory.Rebuild

-- 2026-08-15 | e6c4b45efe653ec4bd457945cfe37a7edce7456a | Formalize exact prime-phase Chinese remainder theorem
#recheck_categorical RiemannResearch.GroupTheory.AddSubgroupCRT
  in RiemannResearch.GroupTheory.AddSubgroupCRT [
    diagonal,
    leftToSup,
    rightToSup,
    difference,
    diagonal_apply,
    leftToSup_mk,
    rightToSup_mk,
    difference_mk_mk,
    exists_diagonal_eq_iff,
    diagonal_ker,
    diagonal_injective_iff,
    difference_surjective]

-- 2026-09-08 | ed5fb41264342d2107de7101998c980f43a0648f | Formalize weighted Hilbert dilations, CRT defects, phase bounds and spectral repair calculus
#recheck_categorical RiemannResearch.LinearAlgebra.WeightedFiniteQuotient
  in RiemannResearch.LinearAlgebra.WeightedFiniteQuotient [
    pushforward,
    average,
    averageMatrix,
    repeatMatrix,
    pushforward_pairing,
    pushforward_total,
    pushforward_mul_pullback,
    pushforward_comp,
    average_mass,
    average_pullback,
    average_preserves_sum,
    average_tower,
    averageMatrix_apply,
    repeatMatrix_apply,
    averaging_after_repetition,
    weighted_adjoint,
    pullback_energy,
    residual_orthogonal,
    error_decomposition]

#recheck_categorical RiemannResearch.LinearAlgebra.WeightedQuotientDefectRank
  in RiemannResearch.LinearAlgebra.WeightedFiniteQuotient [
    pushforward_add,
    pushforward_smul,
    averageLinearMap,
    repeatLinearMap,
    defectLinearMap,
    averageLinearMap_surjective,
    defectLinearMap_apply,
    defect_range_eq_average_ker,
    defect_finrank]

-- 2026-09-14 | 333b01ce37688b66f62e3c9ae045a01e7b261ade | Formalize minimal seeds, balanced coordinates, and charge obstructions
#recheck_categorical RiemannResearch.Analysis.ContinuousBiorthogonalDeletion
  in RiemannResearch.Analysis [
    dictionarySpan,
    dictionaryClosure,
    dictionaryClosure_mono,
    continuous_biorthogonal_linearIndependent,
    continuous_coordinate_tendsto,
    biorthogonal_coordinate_zero_of_omitted,
    biorthogonal_nonzero_target_mem,
    dictionary_delete_one_of_coordinate,
    biorthogonal_delete_one,
    biorthogonal_delete_one_iff,
    biorthogonal_delete_finite_iff,
    IsMinimalTargetFamily,
    biorthogonal_minimal_family_eq_support,
    biorthogonal_support_minimal_iff,
    biorthogonal_exists_minimal_iff_support_approximates,
    biorthogonal_deleted_generator_not_mem]

-- 2026-09-16 | 017523df812e6fb35022663adcd29dabd6610b65 | Recover coupled residual proofs and formalize fresh blocks, actual Laplace data, and explicit logarithmic targets
#recheck_categorical RiemannResearch.RH.PhysicalHeadResidualLift
  in RiemannResearch.RH.Pareto.CoupledResidual [
    physicalHead,
    physicalHead_finiteDimensional,
    physicalHead_atom_mem,
    physicalHead_zero_after,
    physicalHead_projection_coordinate,
    physicalHead_projection_apply,
    physicalHead_projection_zero_iff,
    physicalHead_projection_eq_of_coordinates,
    budget_physicalHead_surjective,
    actual_compressed_head_unique,
    budget_add_physical_tail,
    physical_tail_screening_surjective,
    actual_residual_raw_tail_exists,
    actual_residual_raw_tail_minimum]

-- 2026-09-18 | 630e9c81ce5d8c977fa2b2362f47044c614b931b | Add explicit CRT and coupled-residual open declarations
#recheck_categorical RiemannResearch.NumberTheory.GeneralizedCRTDescentTargets
  in RiemannResearch.NumberTheory.GeneralizedCRT [
    IsTopologicalRingCRT,
    IsEffectiveDescent]

-- 2026-09-19 | 2d45635e0f207fd0c8dec922baab33e1fa13467e | Prove Mobius coefficient stabilization and exact residual criteria for RH
#recheck_categorical RiemannResearch.RH.MobiusCoefficientStabilization
  in RiemannResearch.RH.Pareto.CoefficientStabilization [
    residueAtom,
    coefficientCLM,
    coefficientCLM_biorthogonal,
    residueAtom_linearIndependent,
    coefficient_finite_sum,
    finiteSpace,
    closedSpace,
    projection,
    limitProjection,
    limitResidual,
    coefficient,
    limitCoefficient,
    energy,
    limitEnergy,
    finiteSpace_expansion,
    projection_expansion,
    projection_coefficients_unique,
    projection_tendsto,
    coefficient_tendsto,
    energy_tendsto,
    energy_antitone,
    energy_eq_limit_add,
    limitResidual_mem_orthogonal,
    limitCoefficient_eq_residual,
    limitCoefficient_eq_divisor_sum,
    coefficient_error_bound,
    limitCoefficient_defect_bound,
    coefficient_error_bound_explicit,
    limitCoefficient_defect_bound_explicit,
    limitCoefficients_eq_mobius_iff_residual_zero,
    limitResidual_zero_iff_energy_zero,
    limitEnergy_zero_iff_mem,
    limitCoefficients_eq_mobius_iff_mem,
    limitCoefficients_eq_mobius_iff_energy_tendsto_zero,
    coefficients_tendsto_mobius_iff,
    residueAtom_mem_legal,
    closedSpace_le_legalClosure,
    riemannHypothesis_of_limitCoefficients,
    riemannHypothesis_of_coefficients_tendsto_mobius,
    residual_zero_of_mobiusRiesz_mem,
    riemannHypothesis_of_mobiusRiesz_mem,
    exists_coefficient_defect_of_not_rh]

-- 2026-09-19 | 2fcf31b96a6830a2cd5a7a3e48cd28c223538e0e | Formalize exact conductor Schur spectrum, omitted-prime obstruction, and cumulative gain criterion
#recheck_categorical RiemannResearch.LinearAlgebra.WeightedQuotientHilbert
  in RiemannResearch.LinearAlgebra.WeightedQuotientHilbert [
    coordinates,
    coordinates_apply,
    coordinates_inner,
    repetition,
    coarseSpace,
    conditional_vector_mem,
    conditional_residual_orthogonal,
    conditional_vector_eq_projection]

-- 2026-09-24 | 8e8bd48e09586fc72408739f9400a713dbe0d157 | Prove logarithmic Mobius mean and fixed Gram-source decay; add residual primitive criteria
#recheck_categorical RiemannResearch.RH.NaturalMobiusSourceLimits
  in RiemannResearch.RH.Pareto [
    normalizedResidueHilbert_inner_one,
    rawMobiusResidual_inner_one_eq_logarithmicMean,
    rawMobiusResidual_inner_one_tendsto_zero,
    rawMobiusResidual_residue_inner_tendsto_zero]

-- 2026-09-24 | c290e04758e8609b879621bb453772bc11ee6837 | Isolate signed Mobius Gram obstruction; prove fixed-head limits and reciprocal far-tail transfer
#recheck_categorical RiemannResearch.RH.NaturalMobiusSourceLimits
  in RiemannResearch.RH.Pareto [
    rawMobiusResidual_inner_rawMobius_tendsto_zero,
    rawMobius_tail_inner_head_tendsto]

-- 2026-10-17 | de3660c827e46ba5a145f2acd93e8ba9e2134123 | Formalize squarefree cumulant coordinates and legal Q lattice packets
#recheck_categorical RiemannResearch.NumberTheory.SquarefreeCumulantPair
  in RiemannResearch.NumberTheory.SquarefreeCumulantPair [
    Coordinates,
    star,
    logStar,
    expStar,
    logStar_expStar,
    expStar_logStar,
    logStar_star,
    expStar_add,
    star_assoc,
    star_comm,
    reciprocalSlope,
    reciprocalSlope_expStar,
    reciprocalSlope_expStar_eq_zero_iff,
    reciprocalSlope_singleton_defect]

-- 2026-10-17 | 5873a31797dc426d57071105f2b76bd65b421ce9 | Formalize all-order squarefree cumulants, projective completion, and exact physical Q realization criteria
#recheck_categorical RiemannResearch.NumberTheory.SquarefreeCumulantTower
  in RiemannResearch.NumberTheory.SquarefreeCumulantTower [
    Algebra,
    nextRing,
    algebraRing,
    Coordinates,
    productGroup,
    coordinateGroup,
    snd_mul,
    moment,
    exponential,
    exponential_add,
    exponential_zero,
    exponential_neg_mul,
    exponential_mul_neg,
    expStar,
    logStar,
    moment_expStar,
    logStar_expStar,
    expStar_logStar,
    star,
    expStar_add,
    logStar_star,
    logExpEquiv,
    moment_star,
    moment_injective,
    star_assoc,
    star_comm,
    dropAlgebra,
    augmentation,
    power_snd,
    augmentation_nilpotent,
    augmentation_exponential,
    fromPair,
    expStar_pair,
    logStar_pair,
    Index,
    nextFintype,
    indexFintype,
    coefficient,
    assemble,
    coefficient_assemble,
    assemble_coefficient,
    coefficientEquiv,
    coefficient_add,
    convolution,
    coefficient_mul,
    augmentation_moment,
    coordinatesOf,
    coordinatesOf_moment,
    moment_coordinatesOf,
    emptyIndex,
    nextDecidableEq,
    indexDecidableEq,
    scalar,
    coefficient_zero,
    coefficient_scalar,
    coefficient_empty]

#recheck_categorical RiemannResearch.NumberTheory.SquarefreeCumulantLimit
  in RiemannResearch.NumberTheory.SquarefreeCumulantLimit [
    dualMap,
    restrictAlgebra,
    restrictCoordinates,
    restrictCoordinates_add,
    restrictCoordinates_neg,
    moment_restrict,
    exponential_restrict,
    expStar_restrict,
    logStar_restrict,
    star_restrict,
    intersection,
    restrictAlgebra_comp,
    restrictCoordinates_comp,
    projectiveAlgebra,
    Completion,
    projectiveCoordinates,
    CompletedCoordinates,
    evaluation,
    lift,
    lift_unique,
    expStarLimit,
    logStarLimit,
    starLimit,
    momentLimit,
    logStarLimit_expStarLimit,
    expStarLimit_logStarLimit,
    expStarLimit_add,
    logStarLimit_star,
    momentLimit_star,
    completedLogExpEquiv,
    singletonArray,
    singletonCompletion,
    singletonArray_augmentation,
    singletonCoordinates,
    singletonCoordinates_moment,
    truncatedFamily,
    truncatedFamily_eq,
    finiteApproximation,
    finiteApproximation_stabilizes]

-- 2026-10-17 | 29d8b7f7b1897d2b0c79a3103f5a80eceaf07243 | Formalize squarefree Pareto/Q coefficient and gain criteria [skip ci]
#recheck_categorical RiemannResearch.RH.SquarefreeMobiusProjection
  in RiemannResearch.RH.SquarefreeMobiusProjection [
    pAtom,
    pProjection,
    pLimitProjection,
    pCoefficient,
    pLimitCoefficient,
    qCoefficientCLM,
    qCoefficient,
    qLimitCoefficient,
    pareto_coordinates_separate,
    q_coordinates_separate,
    p_target_coordinate,
    q_target_coordinate,
    p_omitted_atom_coordinate,
    q_omitted_atom_coordinate,
    q_coordinate_biorthogonal,
    q_omitted_coordinate_zero,
    q_nonsquarefree_atom_not_mem,
    pCoefficient_tendsto,
    qCoefficient_tendsto,
    q_limit_values_iff_coefficient_limits,
    p_coefficient_limits_iff_closure,
    q_coefficient_limits_iff_closure,
    p_q_coefficient_limits_iff,
    qCoefficient_eq_inverseCapacity_coefficient,
    qLimitCoefficient_eq_residual,
    qCoefficient_error_bound,
    q_coefficient_limits_iff_inverseCapacity,
    riemannHypothesis_of_squarefree_coefficient_limits]

-- 2026-10-17 | a7daeea58384c1b522d034192ab8c2d0a3b3e7a2 | Prove squarefree canonical affine exhaustion and prime-only incompleteness; record iteration 4 of 5
#recheck_categorical RiemannResearch.RH.MobiusCoefficientStabilization
  in RiemannResearch.RH.Pareto.CoefficientStabilization [
    coefficient_normalizedResidue]

-- 2026-10-19 | 4650466d6a7d65d9bbd49f217b094b9e1063d9cd | Prove complete-Q conductor coefficient-mass obstruction and scaled carry bounds [skip ci]
#recheck_categorical RiemannResearch.RH.QConductorCoefficientMass
  in RiemannResearch.RH.ZetaTwoHilbert [
    qResidue_unweighted_head,
    qResidue_norm_sq_head_tail,
    qResidue_norm_sq_le_two_div,
    qResidue_sum_norm_le_mass,
    qResidue_sum_mass_lower]

-- 2026-10-25 | 9aa7ef25d0ecfffb5a370567f8501c33199d3a18 | Apply simultaneous CRT and prove unordered atom-series obstruction
#recheck_categorical RiemannResearch.RH.QSimultaneousCRT
  in RiemannResearch.RH.QSimultaneousCRT [
    SquarefreeConductor,
    primeSynthesis,
    canonicalCarry,
    canonicalCarry_eq,
    residue_eq_prime_sub_carry,
    canonicalCarry_sequence,
    primeSpan,
    carrySpan,
    primeSynthesis_mem_primeSpan,
    primeSpan_le_squarefreeSpan,
    canonicalCarry_mem_squarefreeSpan,
    carrySpan_le_squarefreeSpan,
    squarefreeSpan_eq_prime_sup_carry,
    squarefreeClosedSpan_eq_prime_carry_closedSpan,
    finite_synthesis_identity,
    hasSum_of_separated_prime_carry_sums,
    separated_prime_carry_difference_ne_one]

-- 2026-11-01 | 921ce8ee5ef18d6bea2830249aa901c6d7ce04ca | Prove complete periodic primitive residue energy identity (2/10)
#recheck_categorical RiemannResearch.Analysis.FiniteWeightedPushforward
  in RiemannResearch.Analysis.FiniteWeightedPushforward [
    pushWeight,
    integral_pushWeight,
    summable_weighted_comp]

-- 2026-11-01 | b241317f8b98f75d132d27e64b907f9eb9592892 | Prove positive arithmetic residue weights and exact refinement (3/10)
#recheck_categorical RiemannResearch.Analysis.FiniteWeightedPushforward
  in RiemannResearch.Analysis.FiniteWeightedPushforward [
    pushWeight_comp]

-- 2026-11-01 | a153102b3567fe8487766a8b293e72764dfa3c7f | Prove weighted residue pullback isometry (4/10)
#recheck_categorical RiemannResearch.Analysis.FiniteWeightedRefinement
  in RiemannResearch.Analysis.FiniteWeightedRefinement [
    pairing,
    energy,
    average,
    pullback_energy,
    pullback_pairing]

#recheck_categorical RiemannResearch.RH.QWeightedResidueMaps
  in RiemannResearch.RH.QWeightedResidueMaps [
    reduction,
    pushed_residueWeight,
    residue_pullback_energy]

-- 2026-11-01 | f4d934896b125249d5575a1260553128094c6b85 | Prove the arithmetic weighted adjoint and left inverse (5/10)
#recheck_categorical RiemannResearch.Analysis.FiniteWeightedRefinement
  in RiemannResearch.Analysis.FiniteWeightedRefinement [
    average_pullback,
    adjoint_identity]

#recheck_categorical RiemannResearch.RH.QWeightedResidueMaps
  in RiemannResearch.RH.QWeightedResidueMaps [
    residueAverage,
    residue_adjoint_identity,
    residue_average_pullback]

-- 2026-11-01 | e55a2af442b819f28352fdd6630cef64c55822ba | Prove complete weighted projection Pythagorean identity (6/10)
#recheck_categorical RiemannResearch.Analysis.FiniteWeightedRefinement
  in RiemannResearch.Analysis.FiniteWeightedRefinement [
    energy_sub_exact,
    pythagorean]

#recheck_categorical RiemannResearch.RH.QWeightedResidueMaps
  in RiemannResearch.RH.QWeightedResidueMaps [
    residue_pythagorean,
    residue_average_energy_le]

-- 2026-11-01 | 6f47f426107bf5a48112799290ce03771fc1dc6f | Prove tower law for exact arithmetic residue averages (7/10)
#recheck_categorical RiemannResearch.Analysis.FiniteWeightedRefinement
  in RiemannResearch.Analysis.FiniteWeightedRefinement [
    average_tower]

#recheck_categorical RiemannResearch.RH.QWeightedResidueMaps
  in RiemannResearch.RH.QWeightedResidueMaps [
    residue_average_tower]

-- 2026-11-04 | 2898b6199f6d0750f382970cf49459381bc78a8a | Formalize infinite CRT extension, displacement continuity criteria, and reciprocal obstruction
#recheck_categorical RiemannResearch.NumberTheory.PrimeResidueTopology
  in RiemannResearch.NumberTheory.PrimeResidueTopology [
    factorial_shift_cofinal,
    factorial_shift_tendsto,
    continuous_trace_limit_constant,
    finite_crt_large,
    exists_cofinal_crt_sequence,
    dense_positive_integers,
    continuous_extension_unique,
    residueUniformSpace,
    positiveEmbedding,
    positiveCongruenceUniformity,
    instUniformSpaceSubtypeNatLeOfNat_riemannResearch,
    instTopologicalSpaceSubtypeNatLeOfNat_riemannResearch,
    CRTUniformContinuous,
    exists_unique_extension_of_uniformContinuous,
    exists_extension_iff_uniformContinuous]

-- 2026-11-04 | 70cd8574c9353eec5df39afdf9406b1d8a126bf7 | Formalize displacement recurrence, CRT blow-up, and squarefree projection order obstruction
#recheck_categorical RiemannResearch.NumberTheory.PrimeResidueTopology
  in RiemannResearch.NumberTheory.PrimeResidueTopology [
    positiveCRTCompletion,
    positiveCRTCompletionEquiv]

-- 2026-11-09 | 337f57c374c532269cd82f1f3825f022ad5a32b3 | Formalize full conductor CRT and split moving Ramanujan screening errors
#recheck_categorical RiemannResearch.NumberTheory.FiniteGeneralizedCRT
  in RiemannResearch.NumberTheory.GeneralizedCRT [
    gcd_lcm_distrib,
    gcd_finset_lcm,
    exists_pair,
    int_modEq_lcm_iff,
    exists_int_modEq_iff_pairwise,
    int_solution_class,
    existsUnique_int_modEq_of_pairwise]

#recheck_categorical RiemannResearch.NumberTheory.ProfiniteGeneralizedCRT
  in RiemannResearch.NumberTheory.GeneralizedCRT [
    PositiveModulus,
    instNeZeroNatValNeOfNat_riemannResearch,
    profiniteRing,
    ProfiniteInt,
    reduce,
    reduce_compatible,
    continuous_reduce,
    isClosed_profiniteRing,
    instCompactSpaceProfiniteInt,
    exists_profiniteInt_iff_pairwise,
    profiniteInt_ext_of_lcm_cofinal]

#recheck_categorical RiemannResearch.NumberTheory.ProfiniteCRT
  in RiemannResearch.NumberTheory.GeneralizedCRT [
    instFactPrimeValNat_riemannResearch,
    primePowerModulus,
    primePowers_cofinal,
    padicProjection,
    padicProjection_toZModPow,
    continuous_padicProjection,
    toPadicProduct,
    toPadicProduct_injective,
    toPadicProduct_surjective,
    profinitePadicEquiv,
    profinitePadicEquiv_apply,
    isTopologicalRingCRT_profinitePadicEquiv]

-- 2026-11-09 | e4a5c50eab8ff3454177a6c643ca66259a0b7b5c | Prove rank-one Ramanujan screening and a fixed-conductor RH criterion
#recheck_categorical RiemannResearch.RH.MixedConductorRankOne
  in RiemannResearch.RH.Pareto.PrimePowerSchur [
    residuePairing_eq_log,
    packet_pairing_eq_of_residue_log,
    normalizedScreenedTwo,
    normalizedScreenedTwo_mean,
    normalizedScreenedTwo_mem_screenedPrimeClosure,
    fullScreening_packet_eq_mangoldt_smul,
    screenedPrimeClosure_eq_span_two,
    one_mem_closedSpace_iff_normalizedScreenedTwo,
    riemannHypothesis_of_normalizedScreenedTwo,
    fullScreening_eq_mean_smul,
    mem_mixedClosure_iff_mem_closedSpace_and_mean_zero,
    normalizedScreenedTwo_error_sq_eq_limitEnergy,
    fixedTwoTrial,
    fixedTwoTrial_tendsto,
    fixedTwoTrial_tendsto_one_iff,
    ramanujanPacketHilbert_two_norm_sq,
    fixedTwo_error_eq_capture,
    fixedTwoTrial_error_eq_capture,
    full_capture_saturation_iff,
    fixed_capture_tendsto_saturation_iff,
    fixed_capture_tendsto_saturation_iff_naturalApproximation,
    riemannHypothesis_of_fixed_capture_saturation]

#recheck_categorical RiemannResearch.RH.MixedConductorRankOne
  in RiemannResearch.RH.Pareto.PsiNormalizedRamanujan [
    fullScreening_centeredInput,
    fullCovarianceMass_eq_fixed_error,
    fullCovarianceMass_normalized_tendsto_fixed_error,
    fullCovarianceMass_subquadratic_iff_one_mem,
    riemannHypothesis_of_fullCovarianceMass_subquadratic,
    covarianceMass_eq_fixed_error_add_diagonal_tail]

-- 2026-11-09 | 3271cb4caa0af8abd83dc73bea7ab78cb8790699 | Verify mixed Ramanujan head bounds, folded Gram optimization, and seed obstructions
#recheck_categorical RiemannResearch.RH.MixedConductorRankOne
  in RiemannResearch.RH.Pareto.PrimePowerSchur [
    hilbertDilation_sub_self_mem_mixedClosure,
    fullScreening_hilbertDilation_eq,
    screenedPrimeClosure_eq_inf_orthogonal,
    mixed_sup_screenedPrimeClosure,
    mixed_inf_screenedPrimeClosure]

-- 2026-11-10 | 400f31ac10335de7029ff4ae317e6105dcdb8014 | Construct canonical full-conductor divisor projections and profinite lifts
#recheck_categorical RiemannResearch.RH.QFullDivisorProjection
  in RiemannResearch.RH.QFullDivisorProjection [
    divisorStage_finiteDimensional,
    paretoStage,
    paretoStage_finiteDimensional,
    qOptimizer,
    pOptimizer,
    toPareto_mem_stage_iff,
    qOptimizer_mem,
    pOptimizer_mem,
    sequence_mod_of_mem,
    sequence_zero_of_dvd,
    divisorStage_le_full,
    iSup_divisorStage_eq_full,
    qOptimizer_tendsto,
    paretoStage_mono,
    iSup_paretoStage_eq_full,
    pOptimizer_tendsto,
    displacement,
    displacement_mem,
    displacement_tendsto,
    lcmPeriod,
    lcmPeriod_nested,
    lcmPeriod_exhausts,
    lcm_displacement_tendsto,
    residueValues,
    factors_through_residue,
    profiniteLift,
    continuous_profiniteLift,
    profiniteLift_natCast,
    profiniteLift_zero,
    positive_site_error_one,
    no_uniform_approximation_to_one]

-- 2026-11-10 | 30efc108c27f84e3130b07bb838778da91d438cd | Formalize absolute convergence of squarefree CRT carry paths
#recheck_categorical RiemannResearch.RH.QInfiniteSquarefreeCarry
  in RiemannResearch.RH.CRTCarryArithmetic.NormalizedCarryChain [
    qParentTerm,
    qPrimeContribution,
    qCarryTerm,
    root_mul_pow_le,
    conductor_pos,
    qCarry_step,
    qCarry_telescope,
    qParentTerm_norm_sq_le,
    qPrimeCoefficient_bound,
    qPrimeContribution_norm_sq_le,
    norm_le_geometric,
    geometric_summable,
    qParentTerm_norm_le,
    qParentTerm_norm_summable,
    qParentTerm_tendsto_zero,
    qInfinite_carry_expansion,
    paretoInfinite_carry_expansion,
    projected_qCarry_sum,
    qCharge,
    qCharge_apply,
    primeClosure_le_charge_ker,
    composite_charge_projected_qResidue,
    projected_qCarry_sum_eq_zero_iff,
    squarefree_conductors]

#recheck_categorical RiemannResearch.RH.QInfiniteSquarefreeCarry
  in RiemannResearch.RH.CRTCarryArithmetic [
    pathConductor,
    pathConductor_two_le,
    pathWeight,
    pathWeight_pos,
    pathWeight_succ_le,
    pathWeight_abs_le_one,
    euclidConductor,
    euclidPrime,
    euclidMultiplier,
    euclidConductor_two_le,
    euclidPrime_prime,
    euclidMultiplier_mul,
    euclidMultiplier_pos,
    euclidChain,
    euclidChain_D_zero,
    euclidChain_w_zero,
    euclidChain_prime,
    euclidChain_prime_dvd,
    euclidChain_prime_not_dvd,
    euclidChain_squarefree,
    euclidChain_radix_le,
    euclidChain_weight_pos,
    euclidChain_weight_succ_le,
    euclidChain_primeContribution,
    euclidChain_prime_norm_sq_le,
    euclidChain_q_expansion,
    euclidChain_pareto_expansion,
    euclidChain_projected_carry_sum,
    euclidChain_projected_carry_eq_zero_iff,
    PrimeAboveFactors,
    exists_primeAboveFactors_le,
    exists_primeAboveFactors,
    orderedRadix,
    orderedRadix_spec,
    orderedRadix_min,
    orderedRadix_pos,
    orderedConductor,
    orderedConductor_two_le,
    orderedConductor_pos,
    orderedInverse_exists,
    orderedMultiplier,
    orderedMultiplier_mod,
    orderedMultiplier_pos,
    orderedChain,
    orderedChain_D_zero,
    orderedChain_w_zero,
    orderedChain_least_prime,
    orderedChain_radix_le,
    orderedChain_squarefree,
    orderedChain_q_expansion,
    orderedChain_pareto_expansion]

-- 2026-11-12 | 7d9b56b01f3e8f5fd0e8fe12f18c07455e9c91ed | Integrate Pareto-first forcing certificates and CRT limits with current main
#recheck_categorical RiemannResearch.NumberTheory.ProfiniteCRTUniversal
  in RiemannResearch.NumberTheory.GeneralizedCRT [
    compatibleLift,
    reduce_compatibleLift,
    compatibleLift_unique,
    continuous_compatibleLift,
    existsUnique_continuous_lift,
    compatibleLift_comp,
    instFactPrimeValNat_riemannResearch_1,
    padicFamilyLift,
    padicProjection_familyLift,
    padicFamilyLift_unique,
    continuous_padicFamilyLift]

-- 2026-11-12 | ac1bee28482212700b25cb401ff8e3263868eda1 | Audit reciprocal density manuscript and strengthen D-cost, sieve, and CRT criteria
#recheck_categorical RiemannResearch.NumberTheory.ProfiniteGeneralizedCRT
  in RiemannResearch.NumberTheory.GeneralizedCRT [
    existsUnique_profiniteInt_iff_pairwise_of_lcm_cofinal,
    tendsto_iff_eventually_reduce_eq]

#recheck_categorical RiemannResearch.NumberTheory.ProfiniteCRT
  in RiemannResearch.NumberTheory.GeneralizedCRT [
    tendsto_iff_padicProjection]

-- 2026-11-13 | 8b94e4c6fcadf811881e42aa2999f5c099b643c4 | Prove actual displacement rigidity for full profinite continuity
#recheck_categorical RiemannResearch.RH.QDisplacementProfiniteContinuity
  in RiemannResearch.RH.QDisplacementProfiniteContinuity [
    HasContinuousProfiniteExtension]

#recheck_categorical RiemannResearch.RH.QDisplacementProfiniteContinuity
  in RiemannResearch.RH.QDisplacementProfiniteContinuity.Full [
    zero_of_compact_bounded_error,
    profinite_extension_iff_zero,
    rh_of_profinite_extension,
    unbounded_error_of_ne_zero]

#recheck_categorical RiemannResearch.RH.QDisplacementProfiniteContinuity
  in RiemannResearch.RH.QDisplacementProfiniteContinuity.Squarefree [
    zero_of_compact_bounded_error,
    profinite_extension_iff_zero,
    rh_of_profinite_extension,
    unbounded_error_of_ne_zero]

-- 2026-11-14 | ab7f34dc8f5b6164804844f46c1792f95155e009 | Formalize finite CRT gluing and exact Q residual correction costs
#recheck_categorical RiemannResearch.Analysis.ResidualCorrectionCost
  in RiemannResearch.Analysis.ResidualCorrectionCost [
    pairing_projection,
    optimal,
    optimal_mem,
    optimal_signal,
    optimal_energy,
    cost_completion,
    cost_isLeast,
    no_correction_iff,
    normalized_budget_iff,
    logarithmic_budget_iff,
    mem_of_eventual_uniform_budget]

#recheck_categorical RiemannResearch.Logic.EquivalenceRelationCRT
  in RiemannResearch.Logic.FamilyCRT [
    PairwiseCompatible,
    HereditaryCRT,
    MeetComposition,
    hereditaryCRT_of_meetComposition,
    meetComposition_of_hereditaryCRT,
    hereditaryCRT_iff_meetComposition,
    meet_composition_iff,
    solution_iff_intersection,
    kernelFamily,
    exists_joint_of_pairwise]

#recheck_categorical RiemannResearch.RH.QFullResidualCorrectionCost
  in RiemannResearch.RH.QFullResidualCorrectionCost [
    residual,
    stage_mono,
    projected_residual,
    residual_energy_completion,
    correction_cost_isLeast,
    correction_budget_iff_gain,
    logarithmic_correction_budget_iff_gain,
    riemannHypothesis_of_uniform_legal_correction_budget]

#recheck_categorical RiemannResearch.Topology.CompactConstraintGluing
  in RiemannResearch.Topology.CompactConstraintGluing [
    exists_of_finite_constraints,
    exists_energy_le_iff,
    exists_joint_of_finite,
    exists_joint_of_pairwise]

-- 2026-11-14 | 1dc035f2b4dbc3761762b36dad30a8a0bd73db90 | Complete categorical CRT and exact Hilbert reconstruction coverage
#recheck_categorical RiemannResearch.Analysis.CompactConstraintEnergy
  in CompactConstraintEnergy [
    exists_mem_all_iff_finite,
    optimum,
    optimum_le,
    exists_minimizer,
    finiteFeasible,
    exists_global_minimizer,
    optimum_iInter_eq_iSup_finite,
    exists_global_le_iff_finite_optimum_le,
    exists_lift_iff_finite,
    exists_lift_iff_pairwise]

#recheck_categorical RiemannResearch.Analysis.FiniteCoordinateCompletion
  in FiniteCoordinate [
    Compatible,
    Completion,
    toCompletion,
    Image,
    Coherent,
    ImageLimit,
    toImageLimit,
    fromImageLimit,
    completionEquivImageLimit,
    completionHomeomorphImageLimit,
    PairwiseCompatible,
    HasFiniteCRT,
    compatible_iff_pairwise,
    completionHomeomorphMatching,
    compatible_operation,
    completionOperation,
    toCompletion_operation,
    continuous_completionOperation,
    compatible_iff_mem_closure,
    isClosed_compatible,
    completionCompactSpace,
    toCompletion_denseRange]

#recheck_categorical RiemannResearch.Analysis.FiniteMoorePenrose
  in LinearMap [
    orthogonalGeneralizedInverse,
    orthogonalGeneralizedInverse_mem,
    orthogonalGeneralizedInverse_normal,
    orthogonalGeneralizedInverse_unique,
    moorePenrose,
    moorePenrose_normal,
    moorePenrose_mem,
    moorePenrose_apply_map,
    map_moorePenrose_map,
    moorePenrose_map_moorePenrose,
    projection_symmetric,
    map_moorePenrose_symmetric,
    moorePenrose_map_symmetric]

#recheck_categorical RiemannResearch.Analysis.HilbertConstraintReconstruction
  in Submodule [
    exists_mem_of_bounded_test_net,
    bounded_finset_test_feasibility_iff]

#recheck_categorical RiemannResearch.Analysis.HilbertConstraintReconstruction
  in RiemannResearch.Analysis.HilbertConstraintReconstruction [
    finiteSpan,
    finiteSpan_finiteDimensional,
    finiteSpan_mono,
    finiteSpan_le,
    iSup_finiteSpan,
    closedSpan,
    IsSolution,
    closedSpan_hasOrthogonalProjection,
    finiteProjection_tendsto,
    finiteProjection_energy_increment,
    finiteProjection_error,
    mem_closedSpan,
    mem_closedSpan_orthogonal_iff,
    isSolution_iff_sub_mem_orthogonal,
    projection_isSolution,
    solution_projection_eq,
    solution_energy_decomposition,
    canonical_minimizes,
    canonical_unique_minimizer,
    bounded_solution_iff_finite]

#recheck_categorical RiemannResearch.Analysis.ResidualCorrelationCost
  in RiemannResearch.Analysis.CorrelationCorrection [
    projected_correlation,
    projected_self_correlation,
    projection_zero_infeasible,
    residual_ratio_lower,
    residual_ratio_attained,
    residualCorrelationCost,
    residualCorrelationCost_zero,
    residualCorrelationCost_nonzero,
    residualCorrelationCost_eq,
    normalized_cost_bound_iff,
    logarithmic_cost_bound_iff,
    residualCorrelationCost_inverse]

#recheck_categorical RiemannResearch.CategoryTheory.FiniteFamilyCRT
  in Setoid [
    crtComp,
    CRTCompatible,
    HasFiniteCRT,
    CRTGluing,
    hasFiniteCRT_of_crtGluing,
    crtGluing_of_hasFiniteCRT,
    hasFiniteCRT_iff_crtGluing,
    crtCompatible_of_solution,
    solution_iff_common_relation,
    crtKernel,
    CRTMatching,
    crtAllKernel,
    crtQuotientMap,
    crtQuotientMap_injective,
    crtQuotientMap_surjective,
    crtQuotientEquiv,
    existsUnique_solution,
    CRTPermutes,
    crtCompositeSetoid,
    crtCompositeSetoid_eq_sup,
    crtComp_iff_sup,
    crtGluing_of_distributive_permutable,
    crtOverlapLeft,
    crtOverlapRight,
    crt_overlap_eq_iff_pair,
    CRTOverlapMatching,
    crtMatchingEquivOverlap,
    crtQuotientOverlapEquiv,
    crt_extend_solution]

#recheck_categorical RiemannResearch.CategoryTheory.LocalFamilyCRT
  in CategoryTheory [
    RegularCoverCalculus,
    RegularCoverCalculus.comp,
    RegularCoverCalculus.pullback,
    GeneralizedEquivalence,
    GeneralizedEquivalence.rel,
    GeneralizedEquivalence.precomp]

#recheck_categorical RiemannResearch.CategoryTheory.LocalFamilyCRT
  in CategoryTheory.GeneralizedEquivalence [
    LocalComp,
    LocalSolution,
    LocalCompatible,
    HasLocalFiniteCRT,
    LocalGluing,
    localComp_self,
    localComp_swap,
    localComp_precomp,
    localComp_left_trans,
    hasLocalFiniteCRT_of_localGluing,
    localGluing_of_hasLocalFiniteCRT,
    hasLocalFiniteCRT_iff_localGluing,
    kernel]

#recheck_categorical RiemannResearch.CategoryTheory.LocalFamilyCRT
  in CategoryTheory [
    InternalEquivalencePresentation,
    InternalEquivalencePresentation.object,
    InternalEquivalencePresentation.left,
    InternalEquivalencePresentation.right,
    InternalEquivalencePresentation.joint_monic,
    InternalEquivalencePresentation.diagonal,
    InternalEquivalencePresentation.diagonal_left,
    InternalEquivalencePresentation.diagonal_right,
    InternalEquivalencePresentation.swap,
    InternalEquivalencePresentation.swap_left,
    InternalEquivalencePresentation.swap_right,
    InternalEquivalencePresentation.trans,
    InternalEquivalencePresentation.trans_left,
    InternalEquivalencePresentation.trans_right]

#recheck_categorical RiemannResearch.CategoryTheory.LocalFamilyCRT
  in CategoryTheory.InternalEquivalencePresentation [
    Holds,
    toGeneralized,
    finite_crt_iff_gluing]

#recheck_categorical RiemannResearch.CategoryTheory.LocalFamilyCRT
  in CategoryTheory [
    equal_of_kernelPair,
    isRegularEpi_of_cover_factor]

#recheck_categorical RiemannResearch.CategoryTheory.LocalFamilyCRT
  in CategoryTheory.GeneralizedEquivalence [
    localSolution_map,
    localComp_map,
    local_extend_solution]

#recheck_categorical RiemannResearch.LinearAlgebra.CRTReconstructionObstructions
  in CRTReconstruction [
    leftPartition,
    rightPartition,
    join_compatible_not_pair_solvable,
    three_linear_constraints_obstruction,
    firstKernel,
    secondKernel,
    sumKernel,
    kernel_meet_eq_bot,
    kernel_binary_sums_top,
    kernel_distributivity_failure,
    nearSingularEquiv,
    nearSingular_target_inverse,
    euclideanEnergy,
    nearSingular_target_energy,
    isomorphism_reconstruction_cost_unbounded,
    finite_unit_data_energy,
    infinite_unit_data_not_square_summable,
    finite_unit_data_minimal_energy]

#recheck_categorical RiemannResearch.NumberTheory.InfiniteCRTObstruction
  in InfiniteCRT [
    finite_power_two_and_three_solvable,
    eq_zero_of_all_power_two_dvd,
    no_integer_power_two_and_three_solution]

#recheck_categorical RiemannResearch.Analysis.CompactMatchingQuotient
  in CompactConstraintEnergy [
    quotientHomeomorph,
    quotientHomeomorph_mk,
    MatchingSpace,
    commonKernel,
    commonKernel_iff,
    toMatching,
    continuous_toMatching,
    matchingQuotientHomeomorph,
    matchingQuotientHomeomorph_mk]

#recheck_categorical RiemannResearch.Analysis.FiniteSingularGramReconstruction
  in RiemannResearch.Analysis.FiniteHilbertGram [
    exists_gram_eq_of_null_compatible,
    finite_feasible_iff_gram_range,
    gram_solution_energy,
    gram_solution_completion,
    finite_dual_bound_iff,
    gramPseudoinverse,
    gramPseudoinverse_normal,
    gramMinimumVector,
    gramMinimumVector_observation,
    gramMinimumVector_energy,
    gramMinimumVector_completion,
    gramMinimumVector_unique,
    finiteConstraintEnergy,
    finiteConstraintEnergy_feasible,
    finiteConstraintEnergy_infeasible,
    finiteConstraintEnergy_eq]

#recheck_categorical RiemannResearch.Analysis.WeakCompactConstraints
  in CompactConstraintEnergy [
    exists_weakDual_norm_le_iff_finite,
    exists_weakHilbert_norm_le_iff_finite,
    isCompact_closedBall_weak_of_bidual_surjective,
    exists_weakReflexive_norm_le_iff_finite]

#recheck_categorical RiemannResearch.CategoryTheory.FunctorCRT
  in CategoryTheory.InternalEquivalencePresentation [
    mapRelation,
    holds_map,
    localSolution_map_internal,
    localComp_map_internal]

#recheck_categorical RiemannResearch.CategoryTheory.QuotientMatchingCRT
  in CategoryTheory.GeneralizedEquivalence [
    QuotientPair,
    finite_local_lifts,
    quotientPair_kernel,
    quotient_crt_local_lift,
    quotient_matching_isRegularEpi,
    quotient_matching_kernel,
    quotient_matching_isIso,
    quotient_image_matching_universal,
    quotient_image_pairwise,
    quotient_matching_pullback]

#recheck_categorical RiemannResearch.Analysis.HilbertConstraintEnergy
  in RiemannResearch.Analysis.HilbertConstraintReconstruction [
    norm_sq_le_iff_norm_le_sqrt,
    finiteOptimum,
    finiteOptimum_empty,
    finiteOptimum_mono,
    finiteOptimum_le_ofReal_iff,
    DualBound,
    bounded_solution_sq_iff_finite,
    bounded_solution_iff_dualBound,
    exists_solution_iff_dualBound,
    finiteOptimum_le_of_solution,
    exists_solution_iff_iSup_finiteOptimum_lt_top,
    globalOptimum,
    globalOptimum_eq_iSup_finiteOptimum,
    globalOptimum_eq_canonical_energy,
    canonical_energy_eq_iSup,
    finiteSpan_eq_synthesisSpan,
    finiteMinimum,
    finiteMinimum_eq_projection,
    finiteOptimum_eq_finiteMinimum_energy,
    finiteMinimum_tendsto,
    finiteMinimum_tendsto_of_cofinal,
    finiteMinimum_energy_increment,
    finiteMinimum_exact_error,
    finiteOptimum_toReal_tendsto,
    canonical_energy_isLeast_dualBound,
    existsUnique_solution_in_closedSpan]

#recheck_categorical RiemannResearch.CategoryTheory.OverlapEqualizerCRT
  in CategoryTheory.GeneralizedEquivalence [
    overlapProductLeft,
    overlapProductRight,
    exists_overlap_equalizer_quotient]

#recheck_categorical RiemannResearch.CategoryTheory.RegularCategoryCRT
  in CategoryTheory [
    RegularImageFactorization,
    RegularImageFactorization.object,
    RegularImageFactorization.epi,
    RegularImageFactorization.mono,
    RegularImageFactorization.fac,
    RegularImageFactorization.epi_regular,
    RegularImageFactorization.mono_monic,
    HasRegularImageFactorizations,
    HasRegularImageFactorizations.exists_factorization]

#recheck_categorical RiemannResearch.CategoryTheory.RegularCategoryCRT
  in CategoryTheory.GeneralizedEquivalence [
    exists_matching_quotient]

#recheck_categorical RiemannResearch.CategoryTheory.RegularCategoryCRT
  in CategoryTheory [
    isIso_mono_of_regularEpi_factor,
    regularEpi_comp_of_regularImages,
    RegularCategoryStructure,
    RegularCategoryStructure.regularEpi_pullback,
    regularCoverCalculusOfRegular]

#recheck_categorical RiemannResearch.CategoryTheory.RegularCategoryCRT
  in CategoryTheory.InternalEquivalencePresentation [
    finite_crt_iff_gluing_of_regular]

#recheck_categorical RiemannResearch.CategoryTheory.RegularCategoryCRT
  in CategoryTheory.GeneralizedEquivalence [
    exists_matching_quotient_of_regular]

-- 2026-11-15 | 33d9589ba742578c3ce8b690fc56ee04aebe0339 | Prove actual-Q residual descent from growing correction budgets
#recheck_categorical RiemannResearch.RH.QFullCorrectionBudgetDescent
  in RiemannResearch.RH.QFullCorrectionBudgetDescent [
    energy,
    CorrectionBudget,
    correctionBudget_iff_loss,
    energy_lower_bound,
    qOne_mem_closure_of_subsequence_energy_tendsto_zero,
    correction_budget_accounting,
    energy_le_exp_neg_reciprocal_sum,
    energy_le_exp_neg_harmonic_of_linear_budgets,
    reciprocal_sum_le_of_positive_limiting_energy,
    energy_tendsto_zero_of_reciprocal_budgets,
    riemannHypothesis_of_reciprocal_budgets,
    reciprocal_linear_budget_not_summable,
    riemannHypothesis_of_linear_budgets,
    CorrectionBudget.mono,
    riemannHypothesis_of_logarithmic_budgets,
    riemannHypothesis_of_geometric_scale_logarithmic_budgets,
    summable_reciprocal_budgets_of_not_riemannHypothesis]

-- 2026-11-18 | 58b9d495d586ee8b7a5ea5d1ac6823eb5cdd1a47 | Prove screened prime-power telescopes and exact first mixed capture
#recheck_categorical RiemannResearch.RH.PrimePowerPacketSummation
  in RiemannResearch.RH.Pareto [
    sum_ramanujanPacket_prime_powers,
    weighted_sum_ramanujanPacket_prime_powers]

#recheck_categorical RiemannResearch.RH.ScreenedPrimePowerTelescope
  in RiemannResearch.RH.Pareto.PrimePowerSchur [
    primePower_packet_telescope,
    fullScreening_rawResidue_eq_log_smul,
    screenedPrimeClosure_eq_span_primePower,
    one_mem_iff_centered_residue_mem_mixedClosure,
    logNormalizedResidue,
    fullScreening_logNormalizedResidue,
    finiteScreening_centered_gram,
    finiteScreening_logNormalizedResidue_error,
    one_mem_iff_exists_logNormalizedResidue_cutoffs,
    mixedSpace_evaluation_eq_zero_of_common_multiple,
    normalizedResidue_error_at_site,
    logNormalizedResidue_error_partition,
    scaled_site_cost_lower,
    logNormalizedResidue_error_ge_common_multiples,
    packet_two_six_inner_and_norm,
    conductor_six_mixed_fit_error,
    mixedSpace_six_eq_span,
    fixedTwo_mixed_capture_at_six]

-- 2026-11-18 | d5e8809003e6dc6bb6a0bc16b6dce21294e9cbc8 | Bound the mixed-conductor capture of parity and prove the fixed odd-period obstruction
#recheck_categorical RiemannResearch.RH.MixedConductorCaptureGains
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CaptureGains [
    centeredParity,
    deficit,
    gain,
    project_centeredParity,
    centeredParity_norm_sq,
    deficit_add_capture,
    common_multiple_floor,
    deficit_pos,
    deficit_step,
    relativeGain,
    relativeGain_bounds,
    deficit_recurrence,
    deficit_product,
    fixed_capture_saturation_iff_relativeGain_not_summable,
    riemannHypothesis_of_mixed_relativeGain_not_summable,
    correlation_sq_le_gain_mul_norm_sq,
    correlationShare,
    correlationShare_le_relativeGain,
    riemannHypothesis_of_mixed_correlation_shares]

-- 2026-11-18 | ad3e1c4e6ba2d88b3b8a44abb9a675a7dfdb6946 | Formalize finite atom-carry CRT and canonical Ramanujan coordinates
#recheck_categorical RiemannResearch.CategoryTheory.AtomCarryPresentation
  in RiemannResearch.CategoryTheory.AtomCarryPresentation [
    Presentation,
    Presentation.Coeff,
    Presentation.addCommGroup,
    Presentation.moduleStruct,
    Presentation.finite,
    Presentation.synthesis,
    PresentationHom,
    PresentationHom.map,
    PresentationHom.preserves,
    instCategoryPresentation,
    ofSynthesis,
    coordinateIso,
    crtEquiv,
    crtEquiv_apply,
    crtEquiv_involutive,
    carrySynthesis,
    carrySynthesis_apply,
    crt_synthesis,
    crtIso,
    crt_range,
    crt_injective,
    crt_disjoint,
    coefficientSynthesis,
    family_carrySynthesis,
    family_coprod_injective,
    family_crt_span,
    family_crt_disjoint]

#recheck_categorical RiemannResearch.NumberTheory.PrimePowerCRTDecomposition
  in RiemannResearch.NumberTheory.PrimePowerCRT [
    modulus,
    modulus_pos,
    modulus_dvd,
    modulus_one_lt,
    cofactor_coprime,
    moduli_coprime,
    product_moduli,
    coefficient,
    coefficient_inverse,
    coefficient_bounds,
    canonical_modular_certificate,
    cleared_reciprocal_identity,
    reciprocal_identity,
    canonicalCarry,
    atom_reconstruction,
    mixed_not_dvd_prime_pow]

#recheck_categorical RiemannResearch.RH.RamanujanFiniteIdentities
  in RiemannResearch.RH.Pareto [
    ramanujanSum_divisor_sum,
    ramanujanPacket_prefix_with_constant]

#recheck_categorical RiemannResearch.RH.ResidueAtomIndependence
  in RiemannResearch.RH.ArithmeticCumulative [
    mobiusDifference_fintype,
    residueFraction_linearIndependent]

#recheck_categorical RiemannResearch.RH.CRTCarryRamanujanCoordinates
  in RiemannResearch.RH.CRTCarryRamanujan [
    fraction_packets,
    packetCoefficient,
    carry_packet_expansion,
    packetCoefficient_of_absent,
    mixed_packetCoefficient,
    canonicalCarry_packet_expansion,
    canonical_mixed_packetCoefficient]

#recheck_categorical RiemannResearch.RH.FiniteAtomCarryCRT
  in RiemannResearch.RH.FiniteAtomCarryCRT [
    primeConductors,
    mem_primeConductors_iff,
    mixedConductors,
    PrimeIndex,
    MixedIndex,
    primeAtom,
    mixedAtom,
    carryVector,
    atomSpan,
    combined_atoms_independent,
    mixed_card_ge_two,
    factorIndex,
    rowCoefficients,
    row_synthesis,
    carry_eq_row_sub_atom,
    atomSpan_eq_partition,
    atomSpan_eq_prime_sup_carry,
    prime_carry_disjoint,
    presentationIso]

-- 2026-11-19 | ced8aa1bb957e41ee5ff4e1b3dea01ee7bb1dc7f | Identify the prime-frequency zero DPP and prove Montgomery window and RH criteria
#recheck_categorical RiemannResearch.RH.MixedParityProjectionDPP
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CaptureGains.MixedProbe [
    target,
    occupancy,
    fullOccupancy,
    target_pos,
    one_sub_occupancy,
    occupancy_bounds,
    occupancy_monotone,
    occupancy_tendsto,
    fullOccupancy_bounds,
    thresholdLaw,
    thresholdLaw_probability,
    probe,
    threshold_interval_mass,
    probe_isDPP,
    finite_probe_vacancy,
    entry_ratio_eq_relativeGain,
    full_probe_vacancy_eq_limitEnergy,
    full_probe_vacancy_pos_of_zero,
    full_probe_ae_iff_relativeGain_not_summable,
    riemannHypothesis_of_full_probe_ae]

-- 2026-11-19 | 8052addab64cae393f5a834c5bd9d5037444f1d3 | Prove universal CRT carry relations and full-conductor Ramanujan inversion
#recheck_categorical RiemannResearch.RH.FullConductorRamanujanTransform
  in RiemannResearch.RH.Pareto.FullConductorRamanujan [
    divisor_sum_injective,
    divisor_indicator_gram,
    totient_diagonal_divisor_sum,
    primitive_period_orthogonality,
    primitive_gcd_orthogonality,
    conductor_kernel,
    dual_pairing,
    polarized_plancherel,
    plancherel,
    transform_inverse]

#recheck_categorical RiemannResearch.RH.UniversalAtomCarryPresentation
  in RiemannResearch.RH.UniversalAtomCarry [
    Atom,
    atom,
    atomSpan,
    Certificate,
    Certificate.arity,
    Certificate.input,
    Certificate.input_gt_one,
    Certificate.coeff,
    Certificate.output,
    Certificate.output_gt_one,
    Certificate.charge,
    Certificate.reciprocal,
    Certificate.carry,
    Certificate.carry_eq,
    Label,
    Word,
    atomSymbol,
    carrySymbol,
    Certificate.expression,
    atomSynthesis,
    includeAtoms,
    eliminate,
    synthesis,
    eliminate_atomSymbol,
    eliminate_carrySymbol,
    eliminate_includeAtoms,
    synthesis_atomSymbol,
    synthesis_carrySymbol,
    synthesis_eq_realized,
    atom_linearIndependent,
    relation,
    relation_eq,
    relations,
    residual,
    residual_mem,
    relations_eq_ker,
    range_synthesis,
    quotientEquivAtomSpan,
    quotientEquivAtomSpan_mk]

#recheck_categorical RiemannResearch.RH.AllCertifiedCarrySpan
  in RiemannResearch.RH.UniversalAtomCarry [
    adjacent_output_gt_one,
    adjacentMinus,
    adjacentPlus,
    adjacentMinus_floor_identity,
    adjacentPlus_floor_identity,
    adjacent_carry_difference,
    allCarrySpan,
    Certificate.carry_mem_atomSpan,
    residueFraction_mem_allCarrySpan,
    allCarrySpan_eq_atomSpan]

#recheck_categorical RiemannResearch.RH.CertifiedCarryComposition
  in RiemannResearch.RH.UniversalAtomCarry.Certificate [
    leafEquiv,
    sum_leaves,
    flatten,
    flatten_carry]

#recheck_categorical RiemannResearch.RH.CertifiedCarryComposition
  in RiemannResearch.RH.CRTCarryArithmetic [
    recursivePrimeCarry_reciprocal_charge,
    recursivePrimeCarry_flattened]

#recheck_categorical RiemannResearch.RH.FiniteCarryRamanujanDictionary
  in RiemannResearch.RH.FiniteCarryRamanujanDictionary [
    commonPacketCoefficient,
    commonPacketCoefficient_of_dvd,
    multiple_atom_expansion,
    carry_common_packet_expansion,
    certificate_packet_expansion,
    certificate_packet_coefficient_one,
    packet_one,
    packet_coefficients_unique,
    packet_coefficients_unique_on_period,
    certificate_packet_unique,
    certificate_cumulative_gcd_expansion,
    certificate_pairing_conductor_scores,
    weighted_gcd_cells_orthogonal,
    prime_sum,
    modulo_six_primitive_and_integrated_gram]

#recheck_categorical RiemannResearch.RH.UniversalCarryRamanujanSynthesis
  in RiemannResearch.RH.UniversalAtomCarry [
    wordPacketCoefficient,
    wordPeriod,
    wordPeriod_pos,
    dvd_wordPeriod,
    word_packet_expansion,
    mem_relations_iff_nontrivial_packets_vanish]

-- 2026-11-19 | 5b61254f6d0328fd74bd1b31c23c0d4477db1b52 | Complete physical atom/carry CRT, conductor towers and reconstruction energy
#recheck_categorical RiemannResearch.RH.ArithmeticResidueMomentEnergy
  in RiemannResearch.RH.ArithmeticResidueMomentEnergy [
    residueMoment,
    pInverseWeight,
    qInverseWeight,
    inverse_weight_energy,
    pEnergy_summable,
    qEnergy_summable,
    pMomentVector,
    qMomentVector,
    pMomentVector_sequence,
    qMomentVector_sequence,
    pMomentVector_energy,
    qMomentVector_energy,
    pMoment_integrand,
    qMoment_integrand,
    residueMoment_summable,
    pMomentVector_observation,
    qMomentVector_observation,
    residueMoment_dualBounds,
    residueEvaluation_dualBounds,
    HasSignedMomentRepresentation,
    pMass_square_le,
    qMass_square,
    pareto_solution_iff_signedMoment,
    q_solution_iff_signedMoment]

#recheck_categorical RiemannResearch.RH.ConductorReconstructionEnergy
  in RiemannResearch.RH.ConductorReconstructionEnergy [
    stage,
    mem_stage,
    stage_tendsto,
    gramCost,
    finite_gram_range,
    finiteOptimum_eq_gramCost,
    globalOptimum_eq_stage_cost,
    reconstruction_iff_stage_cost,
    qAtom,
    p_finite_independent,
    q_finite_independent,
    physical_reconstruction_criteria,
    compare_synthesis,
    physical_dual_bound_transfer,
    physical_solvability_iff,
    qAtom_tendsto,
    pAtom_tendsto,
    target_tendsto,
    nondecay_unbounded_costs,
    scaled_target_tendsto,
    reciprocal_sqrt_costs_unbounded]

#recheck_categorical RiemannResearch.RH.ConductorTowerCompletions
  in RiemannResearch.RH.ConductorTowerCompletions [
    instFactPrimeValNat_riemannResearch,
    towerRing,
    towerRestriction,
    continuous_towerRestriction,
    towerRestriction_surjective,
    cofinalTowerEquiv,
    lcmModulus,
    lcmTowerPadicEquiv,
    primorialModulus,
    primeModulus,
    prime_dvd_stage,
    primorialPrimeMap,
    primorialPrimeMap_restrict,
    componentReduction,
    full_to_squarefree_apply,
    residue_ext_squarefree,
    primorialTowerEquiv,
    instUniformSpaceZModValNatPrime_riemannResearch,
    instUniformSpaceSubtypeNatLeOfNat_riemannResearch,
    positiveCompletionPrimorialEquiv,
    primorialTowerEquiv_bicontinuous,
    lcmTowerPadicEquiv_bicontinuous,
    twoSupported,
    prime_zero_mod_four_two,
    primorialRestriction_not_injective]

#recheck_categorical RiemannResearch.RH.FiniteAtomCarryRefinement
  in RiemannResearch.RH.FiniteAtomCarryCRT [
    refineDivisor,
    primeEmbedding,
    mixedEmbedding,
    extendCoefficients,
    extend_at,
    extend_outside,
    sum_extend_mul,
    rowCoefficients_refine,
    rowCoefficients_refine_outside,
    StageCoefficients,
    refineCoefficients,
    refineCoefficients_injective,
    crtEquiv_refine,
    pullResidue,
    reduction_val,
    fraction_reduction,
    carry_reduction,
    residueAtomSynthesis,
    residueCarrySynthesis,
    residueAtomSynthesis_refine,
    residueCarrySynthesis_refine,
    packetSynthesis_refine,
    packetCoordinates_refine,
    canonicalCarry_packetCoordinates_refine,
    word_packetCoordinates_refine]

#recheck_categorical RiemannResearch.RH.PhysicalCarryGram
  in RiemannResearch.RH.PhysicalCarryGram [
    columns,
    gramMatrix,
    observations,
    observations_columns,
    gramMatrix_columns,
    observed_iff,
    gram_feasible_columns_iff,
    minimum_energy_columns,
    minimum_vector_columns,
    StageIndex,
    conductor,
    conductor_pos,
    stageChange,
    stageChange_involution,
    pAtoms,
    qAtoms,
    stage_columns_prime,
    stage_columns_mixed,
    mixed_column_sequence,
    p_mixed_column_sequence,
    q_mixed_column_sequence,
    physical_gram_and_targets,
    stage_inverse_energy,
    p_atom_gram_uniform_defect,
    p_packet_gram_green_boundary_tail,
    q_packet_gram_weighted,
    q_packet_gram_trigamma,
    q_atom_gram_weighted]

#recheck_categorical RiemannResearch.RH.PhysicalPrimePowerCarryProjection
  in RiemannResearch.RH.PhysicalPrimePowerCarryProjection [
    PrimePowerConductor,
    MixedConductor,
    primePowerConductor_iff,
    certifiedVector,
    canonicalVector,
    evaluate_certified,
    evaluate_canonical,
    fullClosure,
    powerClosure,
    powerClosure_le_full,
    projected_power,
    projected_canonical,
    projectedMixedSpan,
    complement_eq_closed_mixed,
    orthogonal_decomposition,
    pAtom,
    pAtom_sequence,
    physical_certified_floors,
    physical_canonical_floors,
    physical_projected_canonical,
    fullClosure_eq_shift,
    physical_full_closures,
    physical_decompositions]

#recheck_categorical RiemannResearch.RH.QFullDisplacementFiniteHeads
  in RiemannResearch.RH.QFullDisplacementFiniteHeads [
    HeadBound,
    eventual_bad_pair_of_no_extension,
    extension_iff_frequent_head_bound,
    lcm_extension_iff_frequent_head_bound,
    rh_of_lcm_frequent_head_bound]

-- 2026-11-19 | 5275d6a0c2dbe705d1b648500cac223fb72bbc1c | Distinguish composite packet screening and prove a codimension-one RH criterion
#recheck_categorical RiemannResearch.RH.MixedConductorRankOne
  in RiemannResearch.RH.Pareto.PrimePowerSchur [
    screenedPrimeSpan_eq_span_two,
    legalPacketMean,
    screenedMeanSection,
    legalPacketMean_comp_screenedMeanSection,
    legalPacketMean_ker,
    mixed_orthogonal_eq_screened_sup_legal_orthogonal,
    mixed_orthogonal_eq_target_sup_legal_orthogonal,
    screened_sup_ambient_orthogonal_ne_mixed_orthogonal,
    mixed_orthogonal_span_one_iff_residual_spans]

-- 2026-11-19 | fde8648d5444656e9d1e57a39c57003a546118f5 | Prove one-sided rigidity for screened Pareto parity and certify its distance
#recheck_categorical RiemannResearch.RH.MixedConductorRankOne
  in RiemannResearch.RH.Pareto.PrimePowerSchur [
    limitProjection_inner_one,
    limitProjection_eq_scaled_screenedTwo,
    instHasOrthogonalProjectionRealSubtypePreLpNatMemAddSubgroupThresholdHilbertScreenedPrimeClosure,
    mixed_starProjection_screenedTwo,
    mixedOrthogonal_starProjection_one,
    screenedPrimeClosure_starProjection_one,
    normalizedScreenedTwo_eq_limitProjection_iff]

-- 2026-11-20 | aeaa7c822dd0af6a8980c91ecbc36ef2e6cbdf17 | Identify mixed packet projections in carry coordinates and certify the normalized parity norm
#recheck_categorical RiemannResearch.RH.MixedCanonicalCarryCapture
  in RiemannResearch.RH.Pareto.PrimePowerSchur [
    mixedDivisors,
    card_of_mixed_divisor,
    canonicalCarryPacketWeight,
    correctedCanonicalCarry,
    correctedCanonicalCarry_eq_divisor_sum,
    correctedCarryHilbert,
    hilbertSequence_correctedCarry,
    correctedCarrySpace,
    correctedCarrySpace_eq_mixedSpace,
    mixedClosure_eq_correctedCarryClosure,
    instHasOrthogonalProjectionRealSubtypePreLpNatMemAddSubgroupThresholdHilbertCorrectedCarrySpace,
    correctedCarry_capture_tendsto_iff]

#recheck_categorical RiemannResearch.RH.MixedParityCarry
  in RiemannResearch.RH.Pareto.MixedParityCarry [
    carrySpan,
    carry_mem,
    adjacent_difference,
    adjacent_difference_two,
    carrySpan_closure,
    centered_adjacent_mem_iff,
    projectedParity,
    norm_sq_add_error,
    norm_sq_bounds,
    norm_sq_endpoint_iff_mem,
    norm_sq_endpoint_iff_carry_trials,
    norm_sq_endpoint_iff_corrected_capture]

-- 2026-11-20 | b7a28727772b31c78d2659a1d1cef0856af6cda4 | Prove the norm dichotomy for the normalized screened Pareto packet
#recheck_categorical RiemannResearch.RH.MixedConductorRankOne
  in RiemannResearch.RH.Pareto.PrimePowerSchur [
    mixedOrthogonal_starProjection_closedSpace,
    mixedOrthogonal_limitProjection_eq_one_iff]

-- 2026-11-21 | cb4aa7340aa4c7ccbe01b9f514e230642605fd88 | Reduce Pareto parity attainment to a single dyadic adjoint and bounded GCD head lifts
#recheck_categorical RiemannResearch.RH.MixedConductorRankOne
  in RiemannResearch.RH.Pareto.PrimePowerSchur [
    normalizedScreenedTwo_energy_product,
    one_sub_limitEnergy_pos]

-- 2026-11-21 | 71f2429a0ca96a279c7b6c160071cc88718ae9b8 | Prove sharp first-site and dyadic Pareto identities and verify the conductor-768 transfer
#recheck_categorical RiemannResearch.RH.MixedParityCofinalSubpower
  in RiemannResearch.RH.Pareto.PrimePowerSchur [
    mixed_parity_agenda_cost_barrier,
    rh_of_mixed_agenda_cofinal_subpower]

-- 2026-11-21 | 24b753ef4f583f094df503f76622e9a20b39087f | Characterize the screened constant line by the adjoint and contractive sections
#recheck_categorical RiemannResearch.RH.MixedConductorContractiveSection
  in RiemannResearch.RH.Pareto.PrimePowerSchur [
    legalClosedSpace_completeSpace,
    meanSection_norm_at_one,
    meanSection_mean_one,
    legalMeanSection_norm_sq,
    screenedPrimeClosure_eq_constantLine_iff_contractive_section,
    legalPacketMean_adjoint_eq_scaled_section,
    legalPacketMean_comp_adjoint,
    screenedPrimeClosure_eq_constantLine_iff_coisometry,
    exists_legalMeanSection_norm_sq_dilation]

-- 2026-11-21 | a97cdcafb2a0cfe18c1179eccdcaf532f81b67e3 | Prove sharp Pareto metric lifting bounds and finite Mellin zero obstruction
#recheck_categorical RiemannResearch.RH.MixedConductorMetricLifting
  in RiemannResearch.RH.Pareto.PrimePowerSchur [
    legalPacketMean_fiber_bound,
    legalPacketMean_unitBall_image,
    normalized_legalPacketMean_isometric_section,
    exists_legalMeanSection_period5040,
    riemannHypothesis_of_legalMeanSection,
    exists_contractive_legalMeanSection_iff_riemannHypothesis,
    legalMeanSection_finite_zero_product]

-- 2026-11-21 | 9f6be2d6c2bde2fba85eede90b301dfe5ecf76a9 | Characterize contractive Pareto mean sections by bounded parity periods
#recheck_categorical RiemannResearch.RH.MixedConductorMetricLifting
  in RiemannResearch.RH.Pareto.PrimePowerSchur [
    norm_screenedMeanSection,
    exists_legalMeanSection_norm_le_iff,
    exists_contractive_legalMeanSection_iff_unitBall_lifts_one,
    exists_contractive_legalMeanSection_iff_limitEnergy_zero,
    screenedPrimeClosure_eq_constantLine_iff_limitEnergy_zero,
    limitEnergy_finite_zero_product_remainder,
    finite_zero_product_gt_period5040,
    singleton_mellinCenteredProduct,
    one_sub_complex_norm_sq,
    legalMeanSection_single_zero_excess,
    riemannHypothesis_iff_unit_finite_zero_products]

-- 2026-11-21 | 4d199d2f8d39f37c426b9df6733548e10d3ec3b5 | Publish verified Pareto mean-section classification and unique minimum-norm theorem
-- Import interface: RiemannResearch.RH.EveryMeanSectionDecomposition
#recheck_categorical RiemannResearch.RH.MeanSectionStructure
  in RiemannResearch.RH.Pareto.PrimePowerSchur [
    every_mean_section_eq_screened_plus_mixed,
    screenedMeanSection_unique_minimizer]

-- 2026-11-21 | 3c9ae62606587b0fbb90ee7a55cb8cda9a262d97 | Export the RH category theory declarations and formalize CRT naturality and the split Pareto mean
-- Import interface: RiemannResearch.CategoryTheory.All
#recheck_categorical RiemannResearch.CategoryTheory.AtomCarryPresentation
  in RiemannResearch.CategoryTheory.AtomCarryPresentation [
    subsingleton_hom_of_injective]

#recheck_categorical RiemannResearch.RH.FiniteAtomCarryRefinement
  in RiemannResearch.RH.FiniteAtomCarryCRT [
    extendCoefficientsLinear,
    refineCoefficientsLinear,
    refineCoefficientsLinear_apply,
    stageSynthesis_refine]

#recheck_categorical RiemannResearch.RH.MixedConductorSplitExact
  in RiemannResearch.RH.Pareto.PrimePowerSchur [
    legalMixedInclusion,
    legalPacketMean_legalMixedInclusion,
    legalPacketMean_screenedMeanSection,
    legalMixedRetraction,
    legalMixedInclusion_legalMixedRetraction,
    legalMeanComplex,
    legalMeanSplitting,
    legalMixedInclusion_isSplitMono,
    legalPacketMean_isSplitEpi,
    legalMean_unique_mixed_lift,
    instHasZeroObjectTopModuleCatReal_riemannResearch,
    instHasBinaryBiproductsTopModuleCatReal_riemannResearch,
    legalMean_shortExact,
    legalMixedIsKernel,
    legalMeanIsCokernel,
    legalMixedBiprodIso,
    legalMixedQuotientIso,
    legalMixedQuotientIso_π]

#recheck_categorical RiemannResearch.RH.FiniteAtomCarryFunctor
  in RiemannResearch.RH.FiniteAtomCarryCRT [
    ConductorStage,
    ConductorStage.period,
    instPreorderConductorStage,
    stagePresentation,
    presentationFunctor,
    homToAtom,
    homToCarry,
    atomPresentationFunctor,
    carryPresentationFunctor,
    atomPresentationFunctor_map_apply,
    carryPresentationFunctor_map_apply,
    atomCarryRefinementIso,
    atomCarryRefinementIso_app]

-- 2026-11-21 | e2e8a5bc03fd5f9079fe19ac344abb9e31bcff25 | Construct the square-zero algebra of the screened Pareto mean
#recheck_categorical RiemannResearch.RH.MixedConductorSquareZero
  in RiemannResearch.RH.Pareto.PrimePowerSchur.LegalMeanAlgebra [
    mulWith,
    mean_mulWith,
    mulWith_assoc,
    mulWith_comm,
    mulWith_unit,
    mulWith_add,
    mulWith_smul,
    mulWith_zero,
    mulWith_unique,
    continuous_mulWith,
    screenedCommRing,
    mul_def,
    screenedAlgebra,
    algebraMap_apply,
    screenedTopologicalRing,
    meanHom,
    meanHom_apply,
    mixedIdeal,
    mem_mixedIdeal,
    mul_eq_zero_of_mem,
    mixedIdeal_sq,
    mixedIdeal_isMaximal,
    quotientField,
    quotientEquiv,
    quotientEquiv_mk,
    quotientEquiv_symm_apply,
    quotient_mk_mulWith,
    quotientHomeomorph,
    quotientEquiv_agrees_cokernel,
    retraction_inclusion,
    retraction_section,
    splitCoordinates,
    splitCoordinates_continuous,
    splitCoordinates_symm_continuous,
    changeUnit,
    changeUnit_apply,
    mean_changeUnit,
    changeUnit_unit,
    changeUnit_fixed,
    changeUnit_cancel,
    changeUnitEquiv,
    map_mulWith,
    changeUnit_mul,
    coe_screenedUnit,
    meanOne_pythagoras,
    eq_screenedUnit_of_norm_le,
    eq_screenedSection_of_norm_le,
    screenedUnit_natural,
    isometry_mul,
    packetSix,
    packetSix_square_test,
    exists_shear_moving_unit,
    unit_error_sq]

-- 2026-11-21 | b867e179ade428d2a8ed541d1c6dcead04edaa95 | Characterize the Pareto mean as a cokernel of contractions
#recheck_categorical RiemannResearch.RH.MixedConductorMetricCokernel
  in RiemannResearch.RH.Pareto.PrimePowerSchur [
    norm_screenedMeanSection_apply,
    screenedMeanSection_isometry_iff_one_mem,
    screenedMeanSection_adjoint_comp_self,
    screenedMeanSection_isometry_iff_adjoint,
    norm_legalPacketMean_le_one,
    norm_screenedMeanSection_comp_mean_le_one,
    norm_comp_legalPacketMean_mul,
    LegalMeanFactorizationBound,
    mixed_factorization,
    unique_scalar_factor,
    norm_descend_legalPacketMean,
    legalMeanFactorizationBound_iff,
    legalMean_contractive_cokernel_iff_isometry,
    algebraMap_isometry_iff_contractive_cokernel,
    legalMean_contractive_cokernel_iff_naturalApproximation,
    riemannHypothesis_of_legalMean_contractive_cokernel]

-- 2026-11-21 | 8d01b636e7c69d1768caf3d53f704836a42a2077 | Decompose the mixed Pareto ideal by prime support
#recheck_categorical RiemannResearch.RH.MixedConductorHilbertBasis
  in RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis [
    Index,
    packet,
    packet_independent,
    span_packets_closure,
    packet_span_orthogonal,
    mixed_complete,
    basis,
    basis_apply,
    packet_span_dense,
    basis_span_through,
    hasSum_modes,
    block,
    block_hasOrthogonalProjection,
    basis_mem_block,
    basis_mem_block_orthogonal,
    mem_block_iff,
    block_compl,
    packetBlock,
    packetBlock_hasOrthogonalProjection,
    gramSchmidt_eq_packet_residual,
    screenedComplement,
    screenedComplement_eq_orthogonal,
    six,
    basis_six,
    parity_six_coefficient_sq,
    projection_parseval,
    parity_saturation_iff_one_mem]

#recheck_categorical RiemannResearch.RH.MixedConductorBlockSplitting
  in RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis [
    projection_congr,
    projection_add,
    block_norm_sq,
    blockComplex,
    blockSplitting,
    instHasZeroObjectTopModuleCatReal_riemannResearch,
    instHasBinaryBiproductsTopModuleCatReal_riemannResearch,
    block_shortExact,
    blockBiprodIso,
    screenedComplement_hasOrthogonalProjection,
    packetBiprodIso,
    subspaceIdeal,
    subspaceIdeal_le,
    inclusion_injective,
    inclusion_mem_subspaceIdeal,
    subspaceIdealOrderIso,
    subspaceIdeal_isClosed_iff,
    complementary_subspaceIdeals]

#recheck_categorical RiemannResearch.RH.MixedConductorPrimeSupport
  in RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis [
    supportSpace,
    supportSpace_mono,
    supportSpace_one,
    supportCoordinate,
    supportSpace_le_coordinate_ker,
    supportCoordinate_residual,
    conductor_thirty_witness,
    exists_nat_support_card,
    supportSpace_strict,
    supportLayer,
    supportLayer_hasOrthogonalProjection,
    supportSpace_sup_layer,
    supportLayer_ne_bot,
    supportLayer_orthogonal,
    supportLayer_projection,
    supportSpace_dense,
    sum_supportLayer_projection,
    tendsto_sum_supportLayer_projection,
    sum_supportLayer_energy,
    tendsto_sum_supportLayer_energy,
    includeIn,
    layerComplex,
    layerSplitting,
    instHasZeroObjectTopModuleCatReal_riemannResearch,
    layer_shortExact,
    layerIsCokernel,
    instHasBinaryBiproductsTopModuleCatReal_riemannResearch,
    supportSpaceBiprodIso]

-- 2026-11-21 | dcdbbef767fd5f0f9cdb38616227fb78bcbb5d48 | Formalize the centered Pareto mean snake boundary and norm dichotomy
#recheck_categorical RiemannResearch.RH.CenteredMeanSnake
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    meanZero,
    meanZero_eq_orthogonal,
    mean_legal,
    mean_screened,
    meanZero_complete,
    center,
    center_apply,
    center_mem,
    center_eq_starProjection,
    center_fixes,
    centerLegal,
    mixedInclusion,
    mixedInMeanZero,
    mixedInMeanZero_closed,
    mixedInMeanZero_complete,
    BoundaryTarget,
    legal_row_exact,
    ambient_row_exact,
    ambient_mean_surjective,
    left_square,
    right_square,
    ambientMeanComplex,
    ambientMeanSplitting,
    instHasZeroObjectTopModuleCatReal_riemannResearch,
    ambientMean_shortExact,
    centeredDiagram,
    quotient_exact,
    scalar_kernel_exact,
    centerToKernel,
    snakeMap,
    defect,
    snakeMap_apply,
    legalConstants,
    center_eq_zero_iff,
    legalConstants_exact,
    constantMean,
    constantMean_injective,
    exact_constantMean_snakeMap,
    boundary,
    boundary_apply,
    boundary_toLinearMap,
    boundary_of_lift,
    exact_constantMean_boundary,
    defect_orthogonal,
    norm_sq_of_same_class,
    norm_defect_class,
    boundary_norm,
    boundary_norm_sq,
    boundary_norm_sq_eq_energy,
    boundary_eq_zero_iff_screened,
    boundary_eq_zero_iff_one_mem,
    boundary_range,
    boundary_injective_iff,
    legalConstants_eq_bot_of_nonmember,
    boundary_rank_one_of_nonmember,
    energy_eq_dist_sq,
    energy_le_legal_error,
    meanOne_norm_minimum,
    nonzero_branch,
    boundary_eq_zero_iff_naturalApproximation,
    riemannHypothesis_of_boundary_eq_zero,
    boundary_injective_iff_not_riemannHypothesis]

-- 2026-11-21 | 2e07ff3086cd2454fb458c2e648e4522fbcd1958 | Identify the centered Pareto mean quotients and the snake boundary in H/V
#recheck_categorical RiemannResearch.RH.CenteredMeanQuotients
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    projectedOne,
    inner_projectedOne,
    projectedOne_orthogonal_eq_mixed,
    InternalMeanQuotient,
    internalMeanQuotient_subsingleton,
    normalizedScreenedTwo_eq_projected_packet,
    mixedOrthogonal_starProjection_legal,
    legalScreening_ker_range,
    legal_mixed_screened_orthogonal_sum,
    one_eq_screened_add_orthogonal,
    meanZeroToLegalQuotient,
    meanZeroToLegalQuotient_ker,
    meanZeroRepresentative,
    mkQ_screenedTwo,
    meanZeroToLegalQuotient_representative,
    meanZeroToLegalQuotient_surjective,
    boundaryTargetEquivLegalQuotient,
    boundaryTargetEquivLegalQuotient_mk,
    boundaryTargetEquivLegalQuotient_symm_mk,
    boundaryTargetEquivLegalQuotient_boundary,
    boundary_one_eq_zero_iff_one_mem,
    boundaryTarget_subsingleton_iff_closedSpace_eq_top,
    boundaryTarget_subsingleton_iff_one_mem]

-- 2026-11-21 | 3604b67eef727aa573e3bdeaa6150dc794a95b01 | Characterize the ambient mean-zero space by vanishing of the Pareto snake boundary
#recheck_categorical RiemannResearch.RH.CenteredMeanQuotients
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    projectedOne_eq_scaled_section_one,
    screenedMeanSection_one_orthogonal_eq_mixed,
    mixedClosure_eq_closedSpace_inf_one_orthogonal,
    screenedTwo_sub_one_mem_orthogonals,
    screenedTwo_eq_one_of_one_orthogonal_le_mixed,
    one_orthogonal_le_mixedClosure_iff_one_mem,
    closedSpace_eq_top_iff_mixedClosure_eq_one_orthogonal,
    boundary_eq_zero_iff_mixedClosure_eq_one_orthogonal]

-- 2026-11-21 | 38077e604f2e6e45893435b815b32b11fe7be569 | Characterize equality of the screened and constant lines by the Pareto residual mean
#recheck_categorical RiemannResearch.RH.CenteredMeanQuotients
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    screenedLine_eq_projectedOne_line,
    limitResidual_mem_mixed_screened_orthogonals,
    limitResidual_mean_and_screened_norm,
    screenedLine_eq_one_line_iff_one_mem,
    screenedLine_eq_one_line_iff_residual_zero,
    screenedLine_eq_one_line_iff_residual_mean_zero]

-- 2026-11-21 | 1681cbb1fabd856d9c6867b018ce544cb7ce6aa6 | Reduce the ambient Pareto mean boundary to cofinal finite Möbius Gram bounds
#recheck_categorical RiemannResearch.RH.MixedParitySupportBounds
  in RiemannResearch.RH.Pareto.PrimePowerSchur.MixedMobiusTesting [
    parity_variance_eq_boundary_add_layers,
    support_error_floor,
    two_prime_error_floor,
    exists_squarefree_card,
    fixed_support_positive_floor,
    fresh_packet_combination,
    fresh_dilation_cost_floor]

-- 2026-11-21 | 5408c680531330991d8af3d327120285dd091c1c | Prove global Pareto Parseval and compute prime-support snake boundaries
#recheck_categorical RiemannResearch.RH.MixedConductorGlobalParseval
  in RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis [
    legalMixedRetraction_eq_projection,
    inner_mixed_screened,
    reassemble,
    legal_norm_sq_split,
    supportLayer_energy_remainder,
    supportCoordinate_tail_bound,
    exists_unit_missed_by_support_cutoff,
    legal_support_energy_remainder,
    tendsto_legal_support_reconstruction,
    tendsto_legal_support_energy,
    hasSum_supportLayer_energy,
    support_energy_eq_conductor_basis,
    legal_support_parseval,
    supportLayer_isHilbertSum,
    supportLayerEquiv,
    supportLayerEquiv_apply,
    LegalSupportSum,
    screenedScalarParametrization,
    norm_screenedScalarParametrization,
    legalSupportAnalysis,
    retract_synthesis,
    legalSupportEquiv,
    legalSupportEquiv_scalar,
    legalSupportEquiv_layer,
    hasSum_supportLayer_synthesis,
    legalSupportEquiv_symm_apply,
    parityMixedProjection,
    parityMixedProjection_norm_sq,
    parity_support_deficit,
    parity_support_saturation_iff_norm_one,
    norm_one_iff_forall_support_capture]

#recheck_categorical RiemannResearch.RH.MixedConductorSupportSnake
  in RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis [
    supportStageInclusion,
    supportStageRetraction,
    supportLayerQuotient,
    supportLayerSection,
    quotient_inclusion,
    layerRow_exact,
    quotient_section,
    retraction_inclusion,
    comparison_left_square,
    comparison_right_square,
    zero_right_exact,
    supportComparisonBoundary,
    supportComparisonBoundary_apply,
    supportComparisonBoundary_eq_zero_of_compatible,
    truncatedLayerBoundary_eq_zero,
    successiveLayerBoundary_eq_id,
    successiveLayerBoundary_ne_zero]

-- 2026-11-22 | aec81ef74004df423508cc5cef4e8497e1e48859 | Build the prime-support cokernel diagram from continuous quotient transitions
#recheck_categorical RiemannResearch.RH.PrimeSupportCokernel
  in RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis [
    ambientSupport,
    supportQuotientTransition,
    supportQuotientFunctor,
    supportQuotientCocone]

-- 2026-11-22 | 07d90fd1795e601809ffc5c2f0e265345115c4d7 | Compute the exact squared parity distance in the support cokernels and its limit
#recheck_categorical RiemannResearch.RH.PrimeSupportParityQuotient
  in RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis [
    parityQuotientClass,
    parityQuotientClass_norm_sq,
    tendsto_parityQuotientClass_norm_sq]

-- 2026-11-22 | e5c6e122cadd787310678dfeef87446a36883ec6 | Link finite mixed-packet Gram certificates and a uniform zero obstruction to RH
#recheck_categorical RiemannResearch.RH.PrimeSupportParityQuotient
  in RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis [
    boundary_eq_zero_iff_small_parity_quotients,
    riemannHypothesis_of_finite_parity_certificates,
    single_zero_le_parityQuotientClass]

-- 2026-11-22 | 7116291790271a32034368fb7b5c318e3338e568 | Descend the parity class through support quotients and bound its two-prime error
#recheck_categorical RiemannResearch.RH.PrimeSupportParityDescent
  in RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis [
    supportQuotient_hausdorff_desc,
    supportCocone_parity_eq_defect,
    norm_supportCocone_parity,
    parityQuotient_sq_add_captured,
    boundary_eq_zero_iff_frequent_support_contraction,
    riemannHypothesis_of_frequently_contracting_support_blocks,
    mixedWindow_le_ambientSupport,
    parityQuotient_le_window_deficit,
    twoPrime_parityQuotient_upper,
    twoPrime_parityQuotient_contracts]

-- 2026-11-22 | cd043dca560e1d1017fd033c851d060fd3dbe349 | Compute the exact two-prime Parseval energy and isolate the centered boundary
#recheck_categorical RiemannResearch.RH.MixedConductorPolarizedParseval
  in RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis [
    legal_inner_split_screened,
    legal_covariance_gap_eq_boundary,
    boundary_eq_zero_iff_legal_covariance,
    tendsto_polarized_layer_sum,
    one_mem_iff_tendsto_polarized_layer_sum,
    packet_inner_screened_eq_boundary,
    parity_pairing_sub_log_eq_boundary,
    boundary_eq_zero_iff_parity_pairing_le_log,
    riemannHypothesis_of_parity_pairing_le_log,
    two_three_packet_inner,
    two_three_projected_covariance_gap,
    riemannHypothesis_of_two_three_projected_covariance,
    boundary_eq_zero_iff_tendsto_two_three_cross,
    three_packet_norm_sq,
    balancedTwoThree,
    balancedTwoThree_val,
    balancedTwoThree_norm_sq,
    tendsto_balancedTwoThree_layer_energy,
    balancedTwoThree_mixed_inner,
    parity_projection_split_along_two_three]

-- 2026-11-22 | 406d339be396533508fb9b79c7938b9a86c4c518 | Identify the centered boundary with divergence of finite inverse Gram forms
#recheck_categorical RiemannResearch.RH.MixedConductorGramBoundary
  in RiemannResearch.RH.Pareto.PrimePowerSchur.PacketGramBoundary [
    meanVector,
    meanPencil,
    det_meanPencil,
    centered_det_pos,
    centeredInverseGramMass,
    centeredInverseGramMass_eq,
    centered_det_ratio_tendsto,
    centeredInverseGramMass_monotone,
    energy_nonzero_of_boundary_ne,
    centeredInverseGramMass_tendsto_of_ne,
    boundary_eq_zero_iff_centeredInverseGramMass_tendsto,
    riemannHypothesis_of_centeredInverseGramMass_tendsto]

-- 2026-11-22 | 3c1ebd9638f0ab2659fc5721e9ad08750e134f24 | Prove strict finite Gram bounds and zero-free disks for zeta
#recheck_categorical RiemannResearch.RH.MixedConductorGramZeroFree
  in RiemannResearch.RH.Pareto.PrimePowerSchur.PacketGramBoundary [
    normalizedScreenedTwo_not_mem_finiteSpace,
    packetUnitMeanLimit_eq_screened,
    packetMass_lt_limitMass,
    centeredInverseGramMass_eq_div,
    centeredInverseGramMass_nonneg,
    centeredInverseGramMass_mul_boundary_lt_one,
    single_zero_strict_gram_bound,
    one_sub_norm_sq_re_im,
    single_zero_outside_gram_disk,
    zeta_ne_zero_on_gram_rectangle]

-- 2026-11-22 | 66252a8c08dfe903b709446688359f5f56a38e41 | Compute mixed projection determinants and the exact log-two and log-three stages
#recheck_categorical RiemannResearch.RH.MixedConductorProjectedGram
  in RiemannResearch.RH.Pareto.PrimePowerSchur.PacketGramBoundary [
    mixedPacketGram,
    centeredPacketGram_apply,
    mixedPacketGram_eq_pencil,
    mixed_det_ratio,
    mixedPacketGram_det_pos,
    mixed_det_ratio_antitone,
    mixed_det_eq_centered_iff,
    mixed_det_ratio_tendsto_zero_of_boundary_ne,
    boundary_eq_zero_iff_cofinal_mixed_det_lower,
    centeredInverseGramMass_one,
    det_two_meanPencil,
    centeredInverseGramMass_two]

-- 2026-11-22 | e752554bf520ac1752b60eb1ba925218c4668f25 | Certify signed Gram tests and first-site overshoot, and index categorical declarations
#recheck_categorical RiemannResearch.RH.MixedConductorAbsoluteBoundary
  in RiemannResearch.RH.Pareto.PrimePowerSchur [
    abs_constant,
    exists_two_stage_abs_outside,
    abs_screened_residual_pairing,
    negative_mass_le_abs_legal_distance,
    screened_eq_one_iff_abs_pairing_nonpos,
    abs_screened_mem_iff_boundary_zero,
    boundary_zero_iff_projected_one_nonnegative,
    riemannHypothesis_of_abs_screened_mem]

#recheck_categorical RiemannResearch.RH.MixedConductorGramSites
  in RiemannResearch.RH.Pareto.PrimePowerSchur.PacketGramBoundary [
    siteVector,
    siteGram,
    siteVector_one,
    det_siteGram,
    projection_site_tendsto,
    boundary_eq_zero_iff_cofinal_site_det_sign,
    eventually_negative_site_det_of_boundary_ne,
    first_site_det_budget,
    boundary_eq_zero_iff_first_site_det_budget,
    riemannHypothesis_of_cofinal_first_site_det,
    first_site_det_as_one_solve,
    riemannHypothesis_of_cofinal_first_site_solve,
    projection_one_first_site,
    projection_two_first_site_gap,
    projection_two_first_site_gt_one,
    first_two_det_certificates,
    site_positive_of_residual_lt_weight,
    half_two_three_trial_error,
    two_stage_residual_lt_sixth,
    first_two_sites_det_positive,
    projection_first_site_not_monotone]

-- 2026-11-22 | b8007c6b5a0c1dcc791b1a7555eba652d2852823 | Relate the signed two-prime covariance deficit to finite Mellin zero interpolation
#recheck_categorical RiemannResearch.RH.MixedConductorPolarizedParseval
  in RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis [
    two_three_covariance_finite_zero_remainder,
    single_zero_le_two_three_covariance_gap]

-- 2026-11-22 | addec30c949356a63ec2105f0888e82b65d4d10c | Characterize the ambient Pareto mean kernel and its one-sided vectors
#recheck_categorical RiemannResearch.RH.MixedOrthogonalMean
  in RiemannResearch.RH.Pareto.PrimePowerSchur [
    mixedOrthogonalMean,
    mixedOrthogonalMean_surjective,
    mixedOrthogonalMeanQuotient,
    mixedPacketCoefficient,
    packet_pairing_eq_mixedPacketCoefficient,
    mixedOrthogonalMean_sub_packetCoefficient,
    mixedOrthogonalMean_ker,
    center_mem_mixedOrthogonal_kernel,
    mixedOrthogonal_split_at_one,
    mean_injOn_span_of_mean_one,
    mean_injOn_legal_mixedOrthogonal,
    mixedOrthogonalMean_injective_iff_span_one,
    mixedOrthogonal_eq_span_one_iff_one_mem,
    mixedOrthogonalMean_injective_iff_discrepancy_zero,
    mixedOrthogonal_inf_oneOrthogonal_eq_bot_iff_discrepancy_zero,
    riemannHypothesis_of_mixedOrthogonalMean_injective,
    mixedOrthogonal_eq_mean_smul_one_of_oneSidedBound,
    riemannHypothesis_of_mixedOrthogonal_meanZero_le_line]

-- 2026-11-22 | d0a5ec0d197d76c2eb08bd489a9c41c03503e998 | Identify the centered mixed kernel with the legal annihilator by a continuous linear equivalence
#recheck_categorical RiemannResearch.RH.MixedOrthogonalMean
  in RiemannResearch.RH.Pareto.PrimePowerSchur [
    ambientMixedMeanKernel,
    subtractPacketCoefficient,
    subtractPacketCoefficient_mem,
    legalOrthogonalEquivMeanZeroMixed,
    legalOrthogonalEquivMeanZeroMixed_apply,
    legalOrthogonalEquivMeanZeroMixed_symm_apply,
    legalOrthogonalEquivMeanZeroMixed_symm_norm_sq,
    ambientMixedMeanKernel_eq_bot_iff_legalOrthogonal_eq_bot]

-- 2026-11-22 | 8a76168130c2100138a4829447705a4d49a1e864 | Identify the domain of Pareto mean injectivity and separate squarefree mixed conductors
#recheck_categorical RiemannResearch.RH.MixedOrthogonalMean
  in RiemannResearch.RH.Pareto.PrimePowerSchur [
    meanKer_on_one_screenedTwo_span,
    discrepancy_mem_closedSpace_iff_zero,
    squarefreeMixedPacketClosure,
    squarefreeMixedPacketClosure_le_mixed_inf_four_ker,
    squarefreeMixed_two_twelve_independent,
    squarefreeMixedPacketClosure_lt_mixedClosure]

-- 2026-11-22 | 8258816dffd0196cb47403875136c77487fbf292 | Build squarefree CRT packet descent and the centered mean exact sequence
#recheck_categorical RiemannResearch.CategoryTheory.SquarefreeResidueCRT
  in RiemannResearch.SquarefreeResidueCRT [
    PrimeFamily,
    conductor,
    primeSupport,
    conductor_eq_prod,
    primeFactors_conductor,
    conductor_primeSupport,
    conductor_squarefree,
    conductor_dvd,
    Coordinates,
    pairwise,
    crtEquiv,
    crtEquiv_apply,
    squarefreeEquiv,
    restrictCoordinates,
    residueFunctor,
    coordinateFunctor,
    crtIso,
    primeFan,
    glue,
    glue_proj,
    primeFanIsLimit]

#recheck_categorical RiemannResearch.RH.CenteredMeanLongExact
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    CenterCokernel,
    toCenterCokernel,
    cokernelMean,
    constantClass,
    quotientBoundary,
    quotientBoundary_apply,
    quotientBoundary_mk,
    constantClass_injective,
    exact_constantClass_quotientBoundary,
    exact_quotientBoundary_toCenterCokernel,
    exact_toCenterCokernel_cokernelMean,
    cokernelMean_surjective,
    ZeroTerm,
    centeredLongSequence,
    pairExact,
    centeredLongSequence_exact,
    quotientBoundary_unit_residual]

#recheck_categorical RiemannResearch.RH.MixedConductorPrimeSupport
  in RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis [
    packet_mem_supportSpace,
    supportCoordinate_self]

#recheck_categorical RiemannResearch.RH.PrimeSupportAlgebraDescent
  in RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis [
    legalSupport,
    supportIdeal,
    supportIdeal_mono,
    supportIdeal_le_mixed,
    supportIdeal_sq,
    linear_factor_comp,
    factor_shortExact,
    supportAlgebraTower,
    supportAlgebraCocone,
    supportTransition_shortExact,
    supportTransition_kernel_mk_iff,
    supportAlgebra_hausdorff_desc,
    stageMeanBoundary,
    stageMeanBoundary_natural,
    stageMeanBoundary_mk,
    stageMeanBoundary_unit,
    boundaryToMixedQuotient,
    boundaryToMixedQuotient_injective,
    stageMeanBoundary_unit_eq_descended_parity,
    coordinateContrast,
    coordinateContrast_natCast,
    ramanujanSum_eq_crtContrast,
    squarefree_packet_prefix_crt,
    packet_mem_supportIdeal_iff,
    familyMixedIndex,
    squarefree_packet_descent,
    primePower_screened]

#recheck_categorical RiemannResearch.RH.CenteredMeanRHCriteria
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    ambientProduct,
    ambientMean_coe,
    inclusion_product_defect,
    legalRamanujan,
    legalRamanujan_mean,
    packetProductAgrees,
    packetProductAgrees_iff,
    two_three_product_iff_screened,
    stageUnit_zero_iff_boundary,
    categoricalMean_tfae,
    riemannHypothesis_of_stageUnit_zero,
    criterion_to_stageUnit_iff_naturalApproximation,
    stageUnit_zero_iff_riemannHypothesis,
    analyticRiemannHypothesis_tfae]

-- 2026-11-22 | 983c93a0c11e5024dd26d3771f191d56d52215d7 | Reconstruct the Pareto and zeta-two towers and the triangular squarefree density transfer
#recheck_categorical RiemannResearch.RH.ParetoAffineHeadTower
  in RiemannResearch.RH.Pareto.PrimePowerSchur.AffineHeadTower [
    kernel,
    mem_kernel,
    kernel_antitone,
    kernel_closed,
    instHasOrthogonalProjectionRealSubtypePreLpNatMemAddSubgroupThresholdHilbertKernel,
    row,
    row_mem,
    row_inner,
    row_ne_zero,
    direction,
    direction_mem,
    direction_eval,
    direction_orthogonal,
    directions_inner,
    subtract_next_mem,
    layer_eq_span,
    fiber,
    patch,
    patch_spec,
    mem_fiber_iff,
    feasible_norm_sq,
    stepEnergy,
    patch_norm_sq_step,
    patch_norm_sq,
    patch_error_sq,
    kernel_split,
    patch_eq_sum,
    patch_norm_sq_between,
    eq_zero_of_all_kernels,
    kernel_intersection,
    directions_dense,
    feasible_error_sq,
    eval_one,
    patch_eq_one_of_seed,
    stepEnergy_zero_of_seed,
    bounded_energy_iff,
    summable_stepEnergy_iff,
    riemannHypothesis_of_summable_steps,
    cofinal_energy_iff,
    energy_tendsto_atTop_of_seed_ne,
    patch_error_sublinear]

#recheck_categorical RiemannResearch.RH.ZetaTwoAffineHeadTower
  in RiemannResearch.RH.ZetaTwoAffineHeadTower [
    meanWeight,
    pareto_mean,
    meanWeight_value,
    meanWeight_norm_sq,
    kernel,
    kernel_closed,
    instHasOrthogonalProjectionRealSubtypePreLpNatMemAddSubgroupQHilbertKernel,
    anchor,
    fiber,
    mem_fiber_iff,
    patch,
    patch_mem,
    error_orthogonal,
    feasible_error_sq,
    nested_error_sq,
    coordinate_energy,
    error_le_anchor,
    error_sublinear,
    cofinal_error_iff,
    error_head,
    tail_weight_comparison,
    bounded_test_tail,
    bounded_test_error_sq,
    normalized_wavelet_bound,
    conductor_error_sq,
    tendsto_conductor,
    nonconstant_controls_error,
    cofinal_nonconstant_iff]

-- 2026-11-22 | 6f8673015600a62e0d94158362d3913d46d8dd16 | Correct the Pareto–von Mangoldt reduction and isolate the ambient projection criterion
#recheck_categorical RiemannResearch.RH.MixedOrthogonalMean
  in RiemannResearch.RH.Pareto.PrimePowerSchur [
    mean_not_injOn_legal_squarefreeMixedOrthogonal,
    mixedOrthogonalMean_injective_iff_full_capture_saturation]

-- 2026-11-22 | 82b612ebc3431b7bff3b1c9e9849bb05c9297b80 | Prove quantitative finite mixed fits and verify the Pareto–von Mangoldt RH reduction
#recheck_categorical RiemannResearch.RH.CenteredParityFiniteTrials
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CaptureGains [
    centeredParity_trial_error_sq,
    one_mem_iff_centeredParity_finite_trials,
    riemannHypothesis_of_centeredParity_finite_trials,
    eventually_centeredParity_finite_trials_of_conductor241]

-- 2026-11-22 | 1e7062893d1046cfed91f4522397f3a7cc9eb80a | Certify two-seed digamma error bounds and sharpen the Pareto projection estimate
#recheck_categorical RiemannResearch.RH.CenteredParityFiniteTrials
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CaptureGains [
    eventually_centeredParity_finite_trials_of_screened_error,
    eventually_centeredParity_finite_trials_of_covariance241]

-- 2026-11-23 | 76f0e93c9f389d5f4e42bf51072312e8f51811fc | Connect the ambient mean snake to finite Gram solves and certify the stage-four sign change
#recheck_categorical RiemannResearch.RH.CenteredMeanFiniteDescent
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    ambientQuotientMean,
    exact_boundaryToMixedQuotient_ambientQuotientMean,
    ambientQuotientSection,
    ambientQuotientMean_comp_section,
    stageBoundary_ambient_representative,
    stageBoundary_mk_eq_zero_iff,
    finiteWindow_deficit_eq_boundary_add_tail,
    finiteWindow_fifteen_deficit_lt,
    first_site_budget_solve,
    stageUnit_zero_iff_cofinal_gram_solve,
    riemannHypothesis_of_approximate_first_site_solves]

#recheck_categorical RiemannResearch.RH.SiteGramStrictStages
  in RiemannResearch.RH.Pareto.GramStageArithmetic [
    packetValue,
    packetValue_cast,
    massGrid,
    massInterval,
    massInterval_encloses_progression,
    weightInterval,
    weightInterval_contains,
    gramInterval,
    gramInterval_contains,
    meanInterval,
    meanInterval_contains,
    detInterval,
    detInterval_contains,
    sqrtTwoInterval,
    sqrtTwoInterval_contains,
    meanTable,
    gramTable,
    meanTable_encloses,
    gramTable_encloses,
    scoreInterval,
    scoreInterval_contains,
    stageFour_upper,
    stageThree_lower,
    first_site_stage_four_strict_failure,
    first_site_stage_three_strict_slack]

-- 2026-11-23 | b9f2aac3f1c346f46153e13d155f1a9288037243 | Formalize the mixed Pareto bimodule, quotient actions, and ambient snake geometry
#recheck_categorical RiemannResearch.RH.CenteredMeanAmbientGeometry
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    boundaryTargetContinuousEquivLegalQuotient,
    centerLegal_decomposition,
    centerLegal_range,
    defectLine_le_mixed_orthogonal,
    centerLegal_range_isClosed,
    cokernelMeanContinuous,
    cokernelMeanSection,
    cokernelMean_comp_section,
    commonMeanOrthogonal,
    defectLine_orthogonal_inf,
    defectLine_sup_common,
    residualLine_sup_common,
    constantLine_sup_common,
    toCenterCokernelContinuous,
    toCenterCokernel_defect_add,
    legalOrthogonalProjection_defect_add,
    transported_boundary_one_norm_sq,
    ambientMeanSection_graph]

#recheck_categorical RiemannResearch.RH.MixedConductorBimodule
  in RiemannResearch.RH.Pareto.PrimePowerSchur.LegalMeanAlgebra [
    mixedLeftModule,
    mixedRightModule,
    mixedLeft_smul,
    mixedRight_smul,
    mixedActionsCommute,
    mixedLeftContinuous,
    mixedRightContinuous,
    mixedRealTower,
    mixedRealRightTower,
    mixed_smul_norm,
    legalMixedInclusion_left,
    legalMixedInclusion_right,
    mulWith_mixed_actions,
    mixedIdealModuleEquiv,
    mixedQuotientLeftModule,
    mixedQuotientRightModule,
    mixedQuotientActionsCommute,
    continuous_mixedQuotientScalar,
    mixedQuotientLeftContinuous,
    mixedQuotientRightContinuous,
    mixedQuotient_actions,
    mixedIdeal_isTwoSided,
    inclusion_injective,
    mixedLeft_annihilator,
    mixedRight_annihilator,
    regularMean_shortExact,
    quotientLinearMap_mem_mixedIdeal,
    regularMean_no_linear_section]

#recheck_categorical RiemannResearch.RH.MixedConductorPrimeSupport
  in RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis [
    layerPacket,
    layerPacket_independent,
    supportLayer_infiniteDimensional]

#recheck_categorical RiemannResearch.RH.MixedConductorSupportSnake
  in RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis [
    layerGraphCoefficient,
    layerParts_add,
    layerSection_graph,
    layerSection_graph_properties,
    isometry_layerSection_iff]

#recheck_categorical RiemannResearch.RH.PrimeSupportAlgebraDescent
  in RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis [
    supportScalar,
    continuous_supportScalar,
    supportLeftModule,
    supportRightModule,
    supportActionsCommute,
    supportLeftContinuous,
    supportRightContinuous,
    supportActions_mk,
    supportActions_transition,
    supportActions_annihilator,
    supportSpace_stable_actions]

-- 2026-11-23 | f98bb5d0c40bb8b9d6ebd2232af13513c798e5ea | Rebuild the conductor limits, support colimits, and natural ambient snake tower
#recheck_categorical RiemannResearch.RH.ConductorTowerLimit
  in RiemannResearch.RH.ConductorTowerCompletions [
    conductorTowerDiagram,
    conductorTowerCone,
    cone_reduction,
    cone_compatible,
    conductorTowerLift,
    conductorTowerIsLimit,
    lcmConductorTowerIsLimit,
    primorialConductorTowerIsLimit]

#recheck_categorical RiemannResearch.RH.HausdorffSupportColimit
  in RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis [
    hausdorffTopModule,
    ambientSupport_isClosed,
    hausdorffSupportTower,
    hausdorffSupportCocone,
    hausdorffSupportIsColimit]

#recheck_categorical RiemannResearch.RH.PrimeSupportAlgebraDescent
  in RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis [
    idealTower,
    idealCocone]

#recheck_categorical RiemannResearch.RH.AlgebraicSupportColimit
  in RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis [
    algebraicSupportIdeal,
    supportIdeal_le_algebraic,
    algebraicSupportIdeal_le_mixed,
    idealCocone_rep,
    idealUnionDesc,
    idealUnionIsColimit,
    algebraicSupportCocone,
    algebraicSupportIsColimit,
    supportSeparation,
    supportSeparation_eq_colimit_desc,
    supportSeparation_shortExact,
    supportSeparation_kernel_mk_iff,
    algebraicSupportIdeal_closure,
    supportSeparation_continuous,
    supportSeparation_kernel_eq_closure_zero,
    exists_mixed_outside_support_stages,
    supportIdeal_iSup_lt_mixed,
    supportIdeal_comparison_not_injective,
    supportSeparation_ker_eq_mixed_image,
    supportAlgebraCocone_not_isColimit]

#recheck_categorical RiemannResearch.RH.CenteredMeanStageSnake
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.Stage [
    legalDen,
    zeroDen,
    ambientDen,
    mixedImage,
    Target,
    upperInclusion,
    upperMean,
    lowerInclusion,
    lowerMean,
    leftVertical,
    middleVertical,
    upper_exact,
    lower_exact,
    left_comm,
    right_comm,
    centerKernel,
    centerKernel_fixes,
    mixedRetraction_fixes,
    upperRetraction,
    lowerRetraction,
    upperSection,
    lowerSection,
    upperRow,
    lowerRow,
    upperSplitting,
    lowerSplitting,
    upper_shortExact,
    lower_shortExact,
    diagram,
    cokernel_exact,
    connecting,
    connecting_on_lift,
    targetEquiv,
    targetEquiv_connecting,
    connecting_one_eq_zero_iff,
    zeroTransition,
    targetTransition,
    connecting_natural,
    targetEquiv_transition,
    support_connecting,
    constant_iff_center_zero,
    constantToKernel,
    constantToKernel_bijective,
    kernelEquiv,
    StageCokernel,
    centerRange_eq,
    centerCokernelEquiv,
    kernelMean,
    kernelMean_injective,
    toCokernel,
    terminalMean,
    exact_kernelMean_connecting,
    exact_connecting_toCokernel,
    exact_toCokernel_terminalMean,
    terminalMean_surjective,
    StageZero,
    longSequence,
    exactPair,
    longSequence_exact,
    longSequence_comparison,
    support_connecting_algebra,
    quotientArrow,
    quotientArrow_id,
    quotientArrow_comp,
    upperTransition,
    lowerTransition,
    upperRowFunctor,
    lowerRowFunctor,
    splittings_natural,
    diagramTransformation,
    supportDiagramTransformation,
    supportDiagramTransformation_app,
    targetFunctor,
    connectingTransformation]

-- 2026-11-23 | b493682524b61303587dd1dddfb822364a38f9f3 | Prove strict mixed-window descent and separate the ternary mixed layer from centered parity
#recheck_categorical RiemannResearch.RH.MixedConductorStrictDescent
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    fixedTwoTrial_mem_finiteSpace,
    fixedTwoTrial_ne_screened,
    boundary_energy_lt_deficit,
    deficit_tendsto_boundary_energy,
    eventually_contracts_excess,
    exists_positive_relativeGain_from,
    dilated_mixed_packet_mem_window,
    dilated_packet_correlation_le_gain,
    exists_shifted_power_moment,
    fixedTwoTrial_exists_residue_moment,
    finite_mixed_test_pairing,
    boundary_eq_zero_of_block_correlation_shares,
    riemannHypothesis_of_dilated_packet_block_shares]

#recheck_categorical RiemannResearch.RH.TernaryMixedOrbitObstruction
  in RiemannResearch.RH.Pareto.PrimePowerSchur.TernaryOrbit [
    digit,
    digit_small,
    digit_zero,
    digit_one,
    digit_three,
    digit_five,
    digit_cases,
    digit_sq,
    digit_step,
    digitVector,
    digitVector_sequence,
    firstSite,
    firstSite_sequence,
    firstSite_pair,
    digitVector_split,
    digitVector_mean,
    digitVector_dilation_pair,
    centeredDigit,
    centeredDigit_dilation_pair,
    centeredDigit_norm_sq,
    parity_digit_lower,
    centeredParity_pair_gt,
    commute_three_pair,
    triple_packet,
    triple_packet_pair,
    ternary_mixed_layer_pair_zero,
    dilated_six_pair_zero,
    sixOrbit,
    sixOrbit_orthogonal,
    error_gt_of_centeredDigit_pair_zero,
    sixOrbit_error_gt,
    packet_ten_pair_le,
    packet_ten_not_mem_sixOrbit]

-- 2026-11-23 | 99dc7e2b1896d44e424d2728f1b4b7d54c158628 | Prove prime correlation divergence and cancellation in the mixed-conductor tower
#recheck_categorical RiemannResearch.RH.MixedPrimeCorrelationSeries
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    mixed_packet_mem_window,
    mixed_packet_pair_fitted,
    exists_mixed_packet_pair_ne_zero,
    normalized_mixed_pair_le_tail,
    moving_normalized_mixed_pair_tendsto_zero,
    packet_prime_mul_sub_dilation,
    finite_fit_dilated_pair_bound,
    mixed_mean_zero,
    fitted_prime_multiple_bound,
    prime_multiple_norm_le,
    fitted_prime_score_cubic_bound,
    fitted_prime_scores_summable,
    not_summable_prime_multiple_scores,
    fixed_fit_prime_shares_not_summable,
    updated_absolute_scores_summable,
    adjacent_dilation_block_gain,
    six_pair_ne_zero,
    six_orbit_divergence_and_error]

-- 2026-11-23 | 85c01ecd9d419ee70b4fb4139da8d042067ce52e | Identify the support separation kernel and preserve the ambient snake isometrically
#recheck_categorical RiemannResearch.RH.AlgebraicSupportColimit
  in RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis [
    algebraicSupportBoundary,
    algebraicSupportBoundary_stage,
    algebraicSupportBoundary_continuous,
    algebraicSupportBoundary_eq_zero_iff,
    supportSeparation_ker_lt_boundary_ker_iff]

#recheck_categorical RiemannResearch.RH.CenteredMeanStageSnake
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.Stage [
    targetIsometryEquiv,
    norm_connecting,
    targetTransition_eq_isometric_transport,
    mixedImage_supportUnion_eq_closure_zero]

-- 2026-11-23 | 4db8843a5836f94ba62c6a9fcfa1a2591aad998d | Compute the screened mean section from the digamma quotient ladder
#recheck_categorical RiemannResearch.RH.CenteredMeanDigammaSection
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection [
    packetGramEntry,
    packetGramEntry_eq,
    two_three_section_norm,
    jumpGram,
    jumpGram_eq,
    sectionCoordinate,
    sectionCoordinate_eq,
    sectionCoordinate_tendsto,
    reciprocal_jump_mass_tendsto,
    residualJumpAverage,
    periodic_error_eq,
    residualJumpAverage_eq,
    connecting_on_finite_section,
    stage_unit_digamma_identity,
    residualJumpAverage_tendsto,
    residualJumpAverage_eq_mass,
    stage_unit_vanishes_iff_jump_limit,
    representative,
    representative_mem,
    representative_norm_le,
    siteContrast,
    siteContrast_pair,
    residual_site_pair,
    site_quotient_polarization,
    site_between_trial_errors,
    first_site_profiles,
    first_site_interval]

-- 2026-11-23 | 04156c715ade235a52f7b765693695f63b4d2fb1 | Compute the inclusion and centered snakes for the two Pareto mean sequences
#recheck_categorical RiemannResearch.RH.CenteredMeanSnake
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    inclusion_left_square,
    inclusion_right_square,
    inclusionDiagram,
    inclusionConnecting,
    inclusionConnecting_eq_zero,
    meanSectionDifference,
    meanSectionDifference_coe,
    boundary_eq_quotient_meanSectionDifference]

#recheck_categorical RiemannResearch.RH.CenteredMeanQuotients
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    exact_inclusionConnecting_quotientEquiv,
    exact_inclusionQuotientEquiv_final]

-- 2026-11-23 | b5f3f9c4f50c9a110b8e875731a24ad95d41bae4 | Strengthen the centered snake first-site Gram criterion by a quadratic energy allowance
#recheck_categorical RiemannResearch.RH.CenteredMeanDyadicGram
  in RiemannResearch.RH.Pareto.CoefficientStabilization [
    firstSiteGramGap,
    firstSiteDyadicRemainder,
    firstSiteDyadicRemainder_norm_sq,
    finite_firstSiteGramGap_identity,
    limit_dyadic_pairing,
    limit_firstSiteGramGap_identity]

#recheck_categorical RiemannResearch.RH.CenteredMeanDyadicGram
  in RiemannResearch.RH.Pareto.PrimePowerSchur [
    parity_first_site,
    remainder_parity_pairing,
    limit_firstSiteGramGap_strict,
    firstSiteQuadraticAllowance,
    half_lt_firstSiteQuadraticAllowance,
    limit_firstSite_quadratic_strict]

#recheck_categorical RiemannResearch.RH.CenteredMeanDyadicGram
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    firstSiteGramCoordinates,
    firstSiteGramCoordinates_eq,
    firstSiteGramCoordinates_tendsto,
    stageUnit_zero_iff_cofinal_firstSite_test,
    stageUnit_zero_iff_cofinal_cubic_gram_bound,
    stageUnit_zero_iff_cofinal_quadratic_gram_solve,
    riemannHypothesis_of_cofinal_quadratic_gram_solve]

-- 2026-11-23 | ad17dd939b104a2ad6ac4cee2e74d34aa93b15f2 | Reduce the ambient snake to cofinal digamma prefixes and balanced cross bounds
#recheck_categorical RiemannResearch.RH.MixedConductorPolarizedParseval
  in RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis [
    subspace_two_three_cross_le_of_balanced_mem,
    riemannHypothesis_of_balanced_subspace_cross]

#recheck_categorical RiemannResearch.RH.CenteredMeanDigammaSection
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection [
    cofinalPrefixLowerBound,
    eventual_prefix_failure_of_screened_ne_one,
    cofinalPrefixLowerBound_iff_screened_eq_one,
    riemannHypothesis_of_cofinalPrefixLowerBound]

-- 2026-11-23 | 3f0c6f6056960b44526983dd3ff57513f8389987 | Bound actual first-site Gram solves uniformly beyond stage 480
#recheck_categorical RiemannResearch.RH.CenteredMeanGramUpperBound
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    firstSiteGramCoordinates_upper_of_doubleStage_le,
    quadratic_gram_solve_le_one_fortieth,
    cofinal_quadratic_gram_solve_of_one_fortieth_le]

-- 2026-11-24 | e8b3a783d45e319884bba37b80eb6ab98135daa8 | Retain exact two-prime deficits and rule out finite legal target certificates
#recheck_categorical RiemannResearch.RH.MixedConductorPolarizedParseval
  in RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis [
    subspace_two_three_cross_gap_exact,
    subspace_two_three_target_deficit_exact]

#recheck_categorical RiemannResearch.RH.MixedConductorGramZeroFree
  in RiemannResearch.RH.Pareto.PrimePowerSchur.PacketGramBoundary [
    two_mixed_projection_not_mem_subspace,
    finite_subspace_two_three_cross_lt_target]

-- 2026-11-24 | f5408378da369ed4642c3e4aadf973f01f605d8b | Relate the screened constant line to its first site and prime dilation adjoints
#recheck_categorical RiemannResearch.RH.ScreenedMeanDilationTests
  in RiemannResearch.RH.Pareto.PrimePowerSchur [
    inner_dilation_screenedTwo,
    adjoint_screenedTwo_sub_mem_orthogonal,
    adjoint_screenedTwo_norm_sq,
    screenedLine_eq_one_line_iff_two_three_adjoint_norms,
    screenedTwo_first_site_dilation_identity,
    screenedTwo_distance_le_first_site_deficit,
    screenedLine_eq_one_line_iff_first_site_norm]

-- 2026-11-24 | 14c80bf117c8d40d8ba6ae3a4848ae4df3785d6c | Compute the rank-one norm loss of the Pareto inclusion quotient
#recheck_categorical RiemannResearch.RH.CenteredMeanQuotientNorm
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    instHasOrthogonalProjectionRealSubtypePreLpNatMemAddSubgroupThresholdHilbertMinSubmoduleClosedSpaceOrthogonalMixedClosure,
    one_projection_geometry,
    energy_mul_one_add_defect,
    legalProjection_sub_mixedProjection,
    norm_mk_orthogonalProjection,
    defect_inner_common,
    quotient_norms_defect_add,
    exists_mixed_defect_common,
    quotient_mk_norm_loss,
    quotient_norm_loss_of_orthogonal,
    quotient_preserves_norm_iff,
    quotient_boundary_norm,
    quotient_inverse_bound,
    quotient_inverse_opNorm_of_defect_ne_zero,
    quotient_isometry_iff_defect_zero,
    defect_zero_iff_one_mem,
    quotient_isometry_iff_energy_zero,
    quotient_inverse_opNorm_of_defect_zero,
    stage_comparison_isometry_iff]

-- 2026-11-25 | c6df6d2947b0a3f46c5a34e0b5c09a7c6e7ede6d | Compute centered quotient losses, natural-dilation charge minima, and actual argument-variance criteria
#recheck_categorical RiemannResearch.RH.CenteredMeanQuotientNorm
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    centeredCoordinateClass,
    coordinate_quotient_norm_loss,
    hasSum_coordinate_quotient_norm_loss,
    boundary_zero_iff_coordinate_norms]

#recheck_categorical RiemannResearch.RH.CenteredMeanQuotientTail
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    coordinateLossTail,
    coordinateLossTail_eq,
    tailShift_residual_decomposition,
    residualTailEnergy_eq_coordinateLossTail,
    normalized_residualTailEnergy_le,
    boundary_zero_iff_frequently_bounded_coordinateLossTail,
    riemannHypothesis_of_frequently_bounded_coordinateLossTail,
    exists_riemannHypothesis_of_stretched_coordinateLossTail]

#recheck_categorical RiemannResearch.RH.CenteredMeanGramTail
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection [
    finiteSectionShell,
    finiteSectionShell_one_solve,
    finiteSectionShell_eq_pairing,
    finiteSectionShell_variance_partition,
    finiteSectionShell_tendsto,
    scaled_lossTail_le_of_cofinal_finiteSectionShell,
    boundary_zero_iff_cofinal_finiteSectionShell,
    exists_riemannHypothesis_of_cofinal_stretched_finiteSectionShell,
    finiteSectionTailCost,
    finiteSectionTailCost_eq,
    finiteSectionTailCost_tendsto,
    scaled_lossTail_le_of_cofinal_finiteSectionTailCost,
    boundary_zero_iff_cofinal_finiteSectionTailCost,
    exists_riemannHypothesis_of_cofinal_stretched_finiteSectionTailCost]

-- 2026-11-25 | 190a82ec60c50b4a252875bd331c4a7703835c2f | Prove the prime mean-square source, actual macroscopic gap law, and sharp RH criteria
#recheck_categorical RiemannResearch.RH.CenteredMeanPeriodicGramTail
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection [
    sectionSquare,
    sectionPeriodMean,
    sectionSquare_period,
    weighted_sectionSquare_coordinate,
    sectionPeriodMean_lower,
    finiteSectionTailCost_period_error,
    scaled_finiteSectionTailCost_tendsto_periodMean,
    later_tail_vector,
    later_finiteSectionTailCost_identity]

-- 2026-11-25 | 4d4b787b0b3f8b5347788940d51c4362b43edd6a | Prove mesoscopic pair counts, centered Mellin descent, parity Gram bounds and shifted zeta budgets
#recheck_categorical RiemannResearch.RH.CenteredMeanMellinDescent
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    legalQuotientMellin,
    boundaryMellin,
    boundaryMellin_mk,
    boundaryMellin_boundary,
    boundaryMellinRetraction,
    boundaryMellinRetraction_comp,
    boundarySplitMonoOfZetaZero,
    boundary_representative_mellin_power_lower,
    riemannHypothesis_of_boundary_head_subpower]

#recheck_categorical RiemannResearch.RH.CenteredMeanMovingGramTail
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection [
    finiteSectionTailDrift,
    finiteSectionTailDrift_eq,
    laterCost_le,
    finiteSectionTailDrift_tendsto_of_boundary_zero,
    sectionTailDamping,
    fixedSolve_stretched_finiteSectionTailCost_tendsto,
    CalibratedPhysicalSchedule,
    exists_calibrated_physicalSchedule,
    scaled_baseCost_le,
    exists_scale_boundary_zero_iff_cofinal_tailDrift]

#recheck_categorical RiemannResearch.RH.CenteredMeanQuotientNorm
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    boundary_surjective_iff_common_eq_bot,
    boundary_epi_iff_common_eq_bot]

#recheck_categorical RiemannResearch.RH.CenteredMeanDriftWindows
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection [
    finiteSectionDriftWindow,
    finiteSectionDriftWindow_partition,
    finiteSectionDriftWindow_omitted_tendsto_zero,
    exists_scale_boundary_zero_iff_cofinal_driftWindow,
    driftWindowExponent,
    riemannHypothesis_of_bounded_driftWindows]

#recheck_categorical RiemannResearch.RH.CenteredMeanDyadicGram
  in RiemannResearch.RH.Pareto.PrimePowerSchur [
    firstSiteDyadicRemainder_inner_double_legal,
    firstSiteParityProbe,
    firstSiteParityProbe_pair_and_norm,
    limit_firstSiteGram_parity_pencil,
    limit_firstSiteGram_projected_parity_bound,
    firstSiteParitySeparation,
    one_lt_firstSiteParitySeparation,
    limit_firstSite_coupled_separation,
    limit_firstSiteGramGap_coupled_strict,
    projectedParityGramWeight,
    projectedParityGramWeight_eq,
    limit_projected_parity_gram_strict,
    firstSiteRootDiscriminant,
    firstSiteRootDiscriminant_identity,
    limit_firstSite_lower_root_strict]

#recheck_categorical RiemannResearch.RH.CenteredMeanDyadicGram
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    stageUnit_zero_iff_cofinal_lower_root_gram_solve,
    stageUnit_zero_iff_cofinal_projected_parity_gram,
    limitEnergy_cube_le_of_frequently_cubic_gram_budget]

#recheck_categorical RiemannResearch.RH.CenteredMeanMellinCharacters
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    rightZero_ne_one,
    rightZero_ne_zero,
    normalizedBoundaryMellin,
    normalizedBoundaryMellin_boundary,
    testBoundaryDilations,
    testBoundaryDilations_normalized,
    normalizedBoundaryMellin_linearIndependent,
    boundaryCokernelMellinDifference,
    boundaryCokernelMellinDifference_ne_zero,
    riemannHypothesis_of_boundary_epi,
    boundary_epi_iff_riemannHypothesis]

#recheck_categorical RiemannResearch.RH.CenteredMeanProgressionGramTail
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection [
    progressionUpperMass,
    progressionUpperMass_bounds,
    hilbertTailShift_periodic_norm_sq,
    finiteSectionTailDriftUpper,
    finiteSectionTailDrift_eq_progressionSum,
    finiteSectionTailDriftUpper_bounds,
    firstPeriodTailDrift,
    progressionUpperMass_le_three_atoms,
    firstPeriodTailDrift_bounds,
    exists_scale_boundary_zero_iff_cofinal_firstPeriodTailDrift]

#recheck_categorical RiemannResearch.RH.CenteredMeanQuotientTail
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    exists_boundary_zero_of_stretched_coordinateLossTail]

#recheck_categorical RiemannResearch.RH.CenteredMeanGramUpperBound
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    firstSite_conductor241_polynomial_bound,
    quadratic_gram_solve_le_forty_nine_two_thousandths]

#recheck_categorical RiemannResearch.RH.DyadicParityGramRow
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    adjointParityGramRow,
    adjointParityGramRow_eq,
    finiteAdjointParityResidual,
    finiteAdjointParityResidual_eq,
    finiteAdjointParityResidual_tendsto,
    limitEnergy_le_six_mul_of_cofinal_adjoint_parity,
    stageUnit_zero_iff_cofinal_adjoint_parity_row,
    centeredAdjointParityResidual,
    centeredAdjointParityResidual_eq_one_solve,
    centeredAdjointParityResidual_tendsto,
    one_third_lt_centeredParityLowerCoefficient,
    centeredAdjointParity_limit_lower,
    centeredAdjointParity_energy_budget,
    stageUnit_zero_iff_cofinal_centered_adjoint_parity_row]

#recheck_categorical RiemannResearch.RH.MixedConductorL1Closure
  in RiemannResearch.RH.Pareto [
    adjacentContrast_mem_mixed,
    mixed_L1_approximation_iff_mean_zero,
    legal_L1_approximation,
    mixed_L1_distance_isGLB,
    finite_mixed_L1_approximation_exact_head]

#recheck_categorical RiemannResearch.RH.MixedConductorL1Closure
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    boundary_unit_exact_head_L1_representative,
    boundary_unit_head_energy_lower,
    boundary_zero_iff_bounded_representative_heads]

#recheck_categorical RiemannResearch.RH.CenteredMeanParityGramSix
  in RiemannResearch.RH.Pareto.PrimePowerSchur [
    projectedParityGramDefect,
    parityAdjointPacket_mixed_capture_lower,
    parityAdjointPacket_mixed_projection_ne_zero,
    parityAdjointPacket_mixed_capture_upper,
    parityAdjointPacket_six_captures_half_variance,
    projection_inner_mixed,
    firstSiteParityProbe_inner_double_mixed,
    limit_projectedParityGramDefect_mixed_identity,
    limit_projectedParityGramDefect_ge_mixed,
    limit_projectedParityGramDefect_ge_six,
    limit_projectedParityGramDefect_ge_mixed_projection,
    limit_projectedParityGramDefect_pos]

#recheck_categorical RiemannResearch.RH.CenteredMeanParityGramSix
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    stageUnit_zero_iff_cofinal_three_coordinate_parity_gram]

#recheck_categorical RiemannResearch.RH.DyadicParityGramCapacity
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    centeredParitySource,
    centeredParitySource_norm_sq,
    centeredParityGramRow,
    centeredParityGramRow_eq,
    centeredParityGramCapacity,
    projection_eq_of_eq_space,
    centeredParityGramCapacity_eq,
    centeredParityGram_error,
    centeredAdjointParityResidual_eq_pair,
    centeredParityGram_finite_remainder,
    limitEnergy_le_centeredParityGram_error,
    stageUnit_zero_iff_centeredParityGram_capacity,
    riemannHypothesis_of_centeredParityGram_capacity]

-- 2026-11-25 | 9a020add5bd47d00738b714351bb53c12789a26c | Quantify categorical Gram drift, two-stage parity and exact-head mean repair
#recheck_categorical RiemannResearch.RH.CenteredMeanMovingGramTail
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection [
    sectionTailDamping_tendsto]

#recheck_categorical RiemannResearch.RH.CenteredMeanQuotientTail
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    tailShift_one_norm_sq]

#recheck_categorical RiemannResearch.RH.DyadicParityTwoStageGram
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    parity_first_site_value,
    parity_mem_finite,
    endpointGramRemainder_inner_double_lower,
    endpointGramRemainder_inner_parity,
    finite_two_stage_parity_gram,
    two_stage_parity_pencil,
    finite_two_stage_projected_parity_gram,
    twoStageParityGramDefect,
    twoStageParityGramDefect_nonneg,
    twoStageParityGramDefect_tendsto,
    stageUnit_zero_iff_cofinal_two_stage_parity_gram,
    riemannHypothesis_of_cofinal_two_stage_parity_gram]

#recheck_categorical RiemannResearch.RH.LegalTailMeanCapacity
  in RiemannResearch.RH.Pareto [
    hilbertL1Norm_head_zero_sq_le]

#recheck_categorical RiemannResearch.RH.LegalTailMeanCapacity
  in RiemannResearch.RH.Pareto.PrimePowerSchur [
    legalHeadKernel,
    legalHeadKernel_complete,
    legalTailMeanCapacity,
    legalTailMeanCapacity_bounds,
    legalTailMeanCapacity_pos,
    legalTailMeanCapacity_normalized_bounds,
    legalTailMeanRepair,
    legalTailMeanRepair_energy,
    legalTailMeanRepair_isLeast,
    legalTailMeanRepair_energy_le,
    legalTailMeanRepair_energy_le_covariance241,
    finite_mixed_centered_head_screened_bound,
    finite_mixed_centered_heads_screened_stretched]

#recheck_categorical RiemannResearch.RH.CenteredMeanDriftWindows
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection [
    tail_norm_sq_eq_complement]

#recheck_categorical RiemannResearch.RH.CenteredMeanDriftCutoffs
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection [
    gramCutoffAmplification,
    gramCutoffAmplification_mono,
    legal_physical_tail_le,
    finiteSectionTailDrift_le_cutoffGain,
    finiteSectionTailCost_le_cutoffMass,
    scaled_bound,
    exists_schedule_uniform_finite_solve_drift]

-- 2026-11-25 | f9964c1a75e36b90576233e6f49e27684796e5dd | Certify 99 percent parity capture and a zero-free criterion from tail-mean capacity
#recheck_categorical RiemannResearch.RH.CenteredMeanDriftCutoffs
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection [
    finiteSectionTailDrift_scaled_le_cutoffGain,
    finiteSectionTailCost_scaled_le_cutoffMass]

#recheck_categorical RiemannResearch.RH.CenteredParityDilationCapacity
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    a,
    jump,
    jump_eq,
    jump_nonneg,
    a_le_half,
    a_mono,
    jump_block,
    centeredParityTransfer,
    centeredParityTransfer_mem,
    transfer_sub,
    transfer_succ,
    transfer_one_coordinate,
    source_coordinate,
    centeredParityTransfer_truncation,
    gain,
    gain_nonneg,
    gain_le,
    gain_sum_bound,
    centeredParityTransfer_norm_bound,
    centeredParityGram_error_le_transfer,
    truncation_le_reciprocal,
    centeredParity_residual_signed_bound,
    centeredParity_uniform_lower,
    centeredParity_limit_error_comparison,
    centeredParityGramCapacity_ninety_nine_percent]

#recheck_categorical RiemannResearch.RH.DyadicParityTwoStageGram
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    twoStageParityGramDefect_le_cubic]

#recheck_categorical RiemannResearch.RH.LegalTailMeanCapacityMellin
  in RiemannResearch.RH.Pareto [
    paretoTail_mellin]

#recheck_categorical RiemannResearch.RH.LegalTailMeanCapacityMellin
  in RiemannResearch.RH.Pareto.PrimePowerSchur [
    tail_mellin_weight_cancel,
    legalTailMeanCapacity_zero_gap,
    riemannHypothesis_of_legalTailMeanCapacity_saturation]

#recheck_categorical RiemannResearch.RH.CenteredMeanDyadicDrift
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection [
    dyadicDriftCutoff,
    dyadic_damping_le,
    dyadic_amplification_le,
    dyadic_damped_amplification_le,
    dyadic_finiteSectionTailDrift_le,
    dyadic_finiteSectionTailCost_le]

-- 2026-11-25 | 73056c5e375058d9f7b27cc1d56833231b4693a0 | Prove the signed zeta-argument PCC criterion, pair-count corrections and Gram cutoff barriers
#recheck_categorical RiemannResearch.RH.CenteredMeanLateSolveBarrier
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection [
    lateSolve_residualTail_identity,
    lateSolve_tail_le_weighted_costs,
    lateSolve_tail_le_three_costs,
    lateSolve_gain_product_lower,
    scaled_constant_tail_le_one,
    lateSolveExponent,
    eventually_one_le_stretched_scale,
    lateSolve_mass_loss_upper,
    lateSolve_cost_barrier,
    riemannHypothesis_of_bounded_lateSolve_cost]

#recheck_categorical RiemannResearch.RH.CenteredMeanBurnolStageBarrier
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection [
    logSquare_damping_tendsto_zero,
    burnol_lateSolve_drift_product_lower,
    burnol_lateSolve_barrier,
    burnol_polynomial_lateSolve_barrier,
    burnol_diagonal_lateSolve_barrier]

-- 2026-11-25 | 2928be2c0b97e62900d730d9f71aef4c63a44067 | Prove bilinear mixed-conductor rank one and exact defect form
#recheck_categorical RiemannResearch.RH.MixedConductorBilinear
  in RiemannResearch.RH.Pareto.PrimePowerSchur.Bilinear [
    directSumAssembly,
    directSumForm,
    directSumMean,
    mixedPairing,
    legalPairing,
    legalPairing_apply,
    mixedPairing_eq_zero,
    directSumMean_apply,
    directSumForm_apply,
    directSumForm_one,
    rawResidueAtom_inner_one_log,
    pairing_factorization_of_rigidity,
    legalPairing_eq_rankOne,
    legalPairing_one_seed,
    legalPairing_ne_zero,
    legalPairing_range,
    screening_factorization,
    legalPairing_right_radical,
    legalPairing_left_radical,
    meanProduct,
    screenedForm,
    defectForm,
    centeredScreening,
    meanProduct_apply,
    screenedForm_apply,
    defectForm_apply,
    centeredScreening_apply,
    mean_fullScreening,
    ambientMixedMeanKernel_complete,
    centeredScreening_mem,
    centeredScreening_eq_starProjection,
    defectForm_eq_inner,
    defectForm_self_eq_norm_sq,
    defectForm_nonneg,
    defectForm_symm,
    centeredScreening_legal,
    screenedForm_legal,
    defectForm_legal,
    defectForm_normalizedScreenedTwo,
    defectForm_vanishes_iff,
    legalPairing_eq_meanProduct_iff,
    riemannHypothesis_of_defectForm_vanishes]

-- 2026-11-25 | 633f6018d5b6f7388cf8d5685782a7c6e57d768b | Prove the squarefree Nyman–Beurling and centered categorical RH equivalences
#recheck_categorical RiemannResearch.RH.CenteredMeanSquarefreeConverse
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    riemannHypothesis_iff_squarefreeClosure,
    stageUnit_zero_iff_RH,
    riemannHypothesis_iff_naturalApproximation,
    boundary_epi_iff_RH]

-- 2026-11-25 | ab49c803c6b0ab751f1702659f5c693c7fa20a81 | Finish the two-seed RH and positive-gap ledger on the reconciled verified tree
#recheck_categorical RiemannResearch.RH.CenteredMeanTwoSeedConverse
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    positiveResidueDensityFromRH,
    riemannHypothesis_iff_twoSeedClosure,
    riemannHypothesis_iff_twoSeedDensity]

-- 2026-11-25 | 5655d6ff5d6cf38a5341288460928d2b609f1e60 | Identify the mixed bilinear rank-one coefficient by Fekete slopes and integrate the Archimedean heat term
#recheck_categorical RiemannResearch.RH.MixedConductorBilinear
  in RiemannResearch.RH.Pareto.PrimePowerSchur.Bilinear [
    pairing_eq_fekete_rate]

-- 2026-11-25 | 63d5223c954e570b02a34e321975e7c4ec410f09 | Prove legal tail capacity convergence, orthogonal dilation gains and a uniform conjugate-zero gap
#recheck_categorical RiemannResearch.RH.LegalTailMeanCapacity
  in RiemannResearch.RH.Pareto.PrimePowerSchur [
    tail_eq_mean_of_head_zero]

#recheck_categorical RiemannResearch.RH.LegalTailMeanCapacityConjugate
  in RiemannResearch.RH.Pareto [
    twoKernel_scaled_energy,
    scaled_pair_charge_le]

#recheck_categorical RiemannResearch.RH.LegalTailMeanCapacityConjugate
  in RiemannResearch.RH.Pareto.PrimePowerSchur [
    legalTailMeanCapacity_conjugate_zero_gap]

#recheck_categorical RiemannResearch.RH.LegalTailMeanCapacityDilation
  in RiemannResearch.RH.Pareto.PrimePowerSchur [
    normalizedLegalTailMeanCapacity,
    legalTailMeanVector,
    legalTailMeanVector_mem,
    legalTailMeanVector_pairing,
    legalHeadKernel_dilation,
    dilatedLegalTailMeanVector,
    legalTailMean_dilation_orthogonal,
    normalizedLegalTailMeanCapacity_gain,
    normalizedLegalTailMeanCapacity_mono_of_dvd,
    legalTailMean_gain_test,
    normalizedLegalTailMeanCapacity_two_lift_gain,
    factorial_cutoff_succ,
    normalizedLegalTailMeanCapacity_factorial_mono,
    normalizedLegalTailMeanCapacity_le_factorial,
    normalizedCapacity_bdd,
    normalizedLegalTailMeanCapacity_factorial_tendsto,
    legalHeadKernel_antitone,
    legalTailMeanCapacity_antitone,
    normalizedLegalTailMeanCapacity_rounding,
    normalizedLegalTailMeanCapacity_tendsto,
    normalizedLegalTailMeanCapacity_zero,
    normalizedLegalTailMeanCapacity_zero_mul_defect,
    normalizedLegalTailMeanCapacity_eq_one_iff_RH,
    normalizedLegalTailMeanCapacity_iSup_eq_one_iff_RH,
    riemannHypothesis_of_tailCapacity_relative_gain]

-- 2026-11-25 | aa07ba62c1a4b3940121cc81b8ebb0574009f04f | Identify the legal mean with pairing against the normalized projection
#recheck_categorical RiemannResearch.RH.MixedConductorBilinear
  in RiemannResearch.RH.Pareto.PrimePowerSchur.Bilinear [
    inner_screenedTwo_div_norm_sq,
    inner_limitProjection_eq_inner_one]

-- 2026-11-25 | 700a54c8f66176dd177fb16bde0824fd6cfb6dce | Complete Fekete rate laws and normalized screened prime-power declarations
#recheck_categorical RiemannResearch.RH.MixedConductorBilinear
  in RiemannResearch.RH.Pareto.PrimePowerSchur.Bilinear [
    pairing_eq_fekete_rate_at_base,
    mixedPacketCoefficient_eq_fekete_rate,
    fekete_screened_prime_pow,
    fekete_normalized_screened_prime_pow,
    fekete_normalized_screened_prime_pow_set,
    prime_pow_packet_pairing_eq_powerRate]

-- 2026-11-25 | f8eebcd596481080ebe2290d39fe26c82d7f4805 | Relate centered snake lifts and prime dilation pairings to the exact unit norm criterion
#recheck_categorical RiemannResearch.RH.CenteredMeanUnitNorm
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    stage_polarization_defect,
    screened_power_dilation_gram,
    screened_norm_sq_gram_cut,
    stage_lift_unit_norm_tfae,
    unit_norm_iff_finite_gram_halving]

-- 2026-11-25 | c76f5128f9b60dbee83219018a0ea402a7a73755 | Prove prime Gram repairs and the Laguerre variance obstruction for the centered unit lift
#recheck_categorical RiemannResearch.RH.MixedPrimeCorrelationSeries
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    prime_multiple_norm_lower]

#recheck_categorical RiemannResearch.RH.PrimeMultipleGramRepair
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake [
    packetRepairGain,
    packetRepair,
    packet_mem_stage,
    repair_norm,
    repair_mean,
    repair_fekete_pairing,
    packet_repair_refit_exact,
    finite_unit_detects_mixed,
    optimizer_detects_mixed,
    score_remainder_bound,
    prime_repair_harmonic_remainder,
    summable_prime_repair_remainder,
    optimizer_prime_repair_gain,
    later_excess_below_iff_boundary_lt,
    first_gram_excess_fiftyfold]

-- 2026-11-25 | b54b1b2ed59e4e1165976850e7c64d52b3b037de | Prove Pareto mixed-density projection limits and a consecutive-prime RH sign criterion
#recheck_categorical RiemannResearch.RH.MixedPacketDensityTests
  in RiemannResearch.RH.Pareto.PrimePowerSchur.MixedPacketDensity [
    riemannHypothesis_iff_union_eq_univ,
    eq_zero_iff_mixed_density_pairings,
    projected_mixed_dense,
    screened_eq_one_iff_mixed_density_pairings,
    semiprime_packet_sequence,
    semiprime_reciprocal_error_sq_le,
    packet_mem_mixed,
    smul_density,
    projected_density_eq,
    projected_error_sq_le,
    residual_pairing_identity,
    residual_energy_le_of_nonnegative_pairing,
    consecutivePacket,
    consecutivePacket_mem_mixed,
    consecutive_reciprocal_tendsto,
    projected_consecutive_tendsto,
    consecutive_projection_limits,
    residual_pairing_tendsto,
    rh_iff_residual_zero,
    riemannHypothesis_iff_consecutive_leakage_tendsto_zero,
    riemannHypothesis_iff_frequently_nonnegative_pairing]

-- 2026-11-25 | bd5bb15d1dff3a943fed45a162fa39c98984c400 | Formalize finite Pareto head sections, the centered snake, and the log-growth RH criterion
#recheck_categorical RiemannResearch.RH.PhysicalHeadMixedInterpolation
  in RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadMixedInterpolation [
    finiteMixedSpan,
    mem_finiteMixedSpan_iff,
    fresh_prime_packet_head,
    packet_head_in_mixed_range,
    legal_head_in_mixed_range,
    exists_mixed_head,
    exists_finite_window_mixed_head,
    exists_finite_window_head_preserving_mean,
    headBasis,
    headBasis_spec,
    mixedHeadRepair,
    mixedHeadRepair_apply,
    mixedHeadRepair_mem,
    mixedHeadRepair_restrict,
    exists_mixed_near_with_same_head,
    compactHead_eq_of_headRestriction_eq,
    exists_finite_window_near_with_same_head]

#recheck_categorical RiemannResearch.RH.PhysicalHeadSnakeSections
  in RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.PhysicalHeadSections [
    MatchesUnitHead,
    one_sequence_at_positive,
    matchesUnitHead_iff_sequence,
    headCompatible,
    mem_headCompatible_iff,
    stageMean,
    mem_stageMean_ker_iff,
    stageSection,
    stageRetraction,
    stageComplex,
    stageSplitting,
    instHasZeroObjectTopModuleCatReal_riemannResearch,
    stage_shortExact_of_unitHead,
    head_tail_boundary_pairing,
    head_tail_boundary_bound,
    boundary_eq_zero_iff_bounded_head_sections,
    stageSection_norm,
    unitMean_centered_norm_sq,
    defect_tail_norm_pos_of_unitHead,
    unitHead_section_cost_lower_bound,
    matchesUnitHead_mono,
    boundary_eq_zero_iff_cofinal_bounded_head_sections,
    stage_shortExact,
    iInf_headCompatible_eq_legalConstants,
    limit_mean_surjective_iff_boundary_zero]

#recheck_categorical RiemannResearch.RH.PhysicalHeadSectionGrowth
  in RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadSectionGrowth [
    kappa,
    kappa_isLeast,
    kappa_sq_eq_one_add_error,
    rhs_one_mem,
    kappa_eq_one_of_rh,
    rightZero_kappa_sq_lower,
    CofinalSubpower,
    cofinalSubpower_kappa_iff_rh,
    kappa_dichotomy,
    kappa_tendsto_atTop_of_not_rh,
    exists_finite_section_near_one,
    FiniteSectionSubpower,
    finiteSectionSubpower_iff_rh]

#recheck_categorical RiemannResearch.RH.PhysicalHeadFiniteMinimum
  in RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadFiniteMinimum [
    shiftedResidue,
    shiftedResidue_mem_window,
    shiftedResidue_head,
    mixedFloorColumn,
    mixedFloorColumn_mem_window,
    mixedFloorColumn_head,
    explicit_floor_mixed_interpolation,
    quadratic_window_mixed_head,
    finiteSectionNorms,
    exists_finite_section_near_minimum,
    kappa_isGLB_finiteSectionNorms,
    sInf_finiteSectionNorms]

#recheck_categorical RiemannResearch.RH.PhysicalHeadSectionLog
  in RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadSectionGrowth [
    one_le_norm_of_mem_fiber,
    CofinalLogSections,
    cofinalLogSections_iff_rh,
    parity_cofinalLogSections_iff_rh]

-- 2026-11-25 | 7ddc6074c075b9681e60b0239b1c77569b006173 | Formalize split physical-head algebras, the relative snake, and multiplicativity iff RH
#recheck_categorical RiemannResearch.RH.PhysicalHeadPacketSquare
  in RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadPacketSquare [
    packetDifference,
    packetDifference_sequence,
    packetDifference_zero_below,
    packetDifference_at_first_prime,
    packetDifference_mem_mixed,
    square_summable,
    packetSquare,
    packetSquare_sequence,
    packetSquare_mean,
    packetSquare_mean_pos,
    compactHead_zero_of_sequence,
    packetDifference_headCompatible,
    packetSquare_not_headCompatible,
    positive_stage_not_closed_under_square]

#recheck_categorical RiemannResearch.RH.PhysicalHeadStageAlgebra
  in RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadStageAlgebra [
    stageUnit,
    stageUnit_val,
    stageUnit_mean,
    stageProduct,
    stageProduct_val,
    mean_stageProduct,
    product_comm,
    product_right_smul,
    stageCommRing,
    mul_def,
    one_def,
    stageMean_mul,
    stageAlgebra,
    algebraMap_apply,
    algebraMap_eq_stageSection,
    augmentation,
    augmentation_apply,
    stageIdeal,
    mem_stageIdeal_iff,
    mul_eq_zero_of_mem,
    stageIdeal_sq,
    mixedCoordinate,
    mixedCoordinate_val,
    mixedCoordinate_unit,
    mixedCoordinate_kernel,
    coordinates]

#recheck_categorical RiemannResearch.RH.PhysicalHeadStageAlgebraComparison
  in RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadStageAlgebra [
    compactHead_nested,
    headCompatible_antitone,
    stageInclusion,
    stageInclusion_mean,
    stageInclusion_injective,
    displacement,
    displacement_mean,
    displacement_val,
    displacement_orthogonal_deeper,
    displacement_norm_sq,
    adjacent_displacement_norm_sq,
    inclusion_mul_defect,
    inclusion_unit_defect,
    transportLinear,
    transportLinear_apply,
    transportLinear_mean,
    transportLinear_unit,
    transportLinear_mul,
    stageAlgebraTransport,
    stageAlgebraTransport_apply,
    stageAlgebraTransport_injective,
    stageAlgebraTransport_on_kernel,
    stageInclusion_comp_apply,
    displacement_cocycle,
    stageAlgebraTransport_refl,
    stageAlgebraTransport_comp_apply,
    stageInclusion_multiplicative_iff,
    adjacent_stageInclusion_multiplicative_iff_rh]

#recheck_categorical RiemannResearch.RH.PhysicalHeadAlgebraSnake
  in RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadStageAlgebra [
    kernelInclusion,
    relativeCenter,
    relative_left_square,
    relative_right_square,
    deeperKernel,
    relative_cokernel_exact,
    relativeSnake,
    unitCarry,
    relativeSnake_one,
    relativeSnake_apply,
    relativeSnake_one_eq_unit_product_defect,
    kernel_vector_mem_affine_kernel,
    unitCarry_orthogonal,
    relativeSnake_one_norm_sq]

-- 2026-11-25 | 3323c2e457c8aa88b1671e73a209e9fc13565a50 | Identify the infinite physical-head snake in isometric layer coordinates
#recheck_categorical RiemannResearch.RH.PhysicalHeadLayerIsometry
  in RiemannResearch.RH.Pareto.PrimePowerSchur.AffineHeadTower [
    mixedHeadComplete,
    mixedHeadDirection,
    mixedHeadDirection_ne_zero,
    unitHeadDirection,
    unitHeadDirection_val,
    unitHeadDirection_orthonormal,
    unitHeadDirection_span_orthogonal,
    physicalHeadBasis,
    physicalHeadBasis_apply,
    headLayerIsometry,
    headLayerIsometry_apply,
    headLayer_hasSum,
    headLayer_parseval,
    headLayer_synthesis,
    headLayer_zero_iff_evaluation,
    mem_kernel_iff_headLayer_prefix_zero]

#recheck_categorical RiemannResearch.RH.PhysicalHeadProductSnake
  in RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadStageAlgebra [
    KernelSeq,
    StageSeq,
    kernelDiff,
    stageDiff,
    scalarDiff,
    constantScalar,
    constantScalar_exact,
    productInclusion,
    productMean,
    productRow_exact,
    product_left_square,
    product_right_square,
    productLift,
    productRetraction,
    productLift_right,
    productRetraction_left,
    KernelCokernel,
    unitCarries,
    productSnake,
    productSnake_one,
    productSnake_apply,
    productSnake_one_eq_zero_iff_coherent,
    coherentMean,
    stageKernel_exact,
    coherentMean_square,
    coherentMean_productSnake_exact,
    StageCokernel,
    cokernelInclusion,
    productSnake_cokernelInclusion_exact,
    scalarDiff_surjective,
    cokernelInclusion_surjective,
    cokernelInclusion_ker_eq_boundary_line,
    stageCokernelEquiv]

#recheck_categorical RiemannResearch.RH.PhysicalHeadInfiniteBoundary
  in RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadStageAlgebra [
    coherent_stage_values_constant,
    coherent_stage_value_eq_mean,
    coherentMean_injective,
    coherent_unit_value_eq_one,
    productSnake_one_eq_zero_iff_one_mem,
    productSnake_one_eq_zero_iff_centered_boundary,
    productSnake_one_eq_zero_iff_rh,
    adjacentSnakeEnergy,
    adjacentSnakeEnergy_eq_stepEnergy,
    partial_adjacentSnakeEnergy,
    productSnake_one_eq_zero_iff_summable_adjacent,
    finite_snake_norm_sq_tendsto_atTop_of_boundary_ne,
    finite_snake_norm_sq_sublinear]

#recheck_categorical RiemannResearch.RH.PhysicalHeadSequenceCokernel
  in RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadSequenceCokernel [
    readout,
    readout_injective,
    actualMixedSequences,
    SequenceQuotient,
    underlying,
    underlying_mem,
    underlying_vanishes,
    ofVanishing,
    partialKernelSum,
    partial_succ,
    partial_mem,
    kernelToMixed,
    kernelToMixed_mem,
    kernelOfMixed,
    kernelToMixed_ofMixed,
    kernelToMixed_injective,
    partialMixed,
    partialMixed_succ,
    decode,
    decode_apply,
    partial_stable,
    partial_diff,
    partialMixed_diff,
    decode_diff,
    decode_exact,
    interpolate,
    decode_surjective,
    quotientDecode,
    quotientDecode_ker,
    physicalCokernelEquiv,
    physicalCokernelEquiv_mk,
    ambientDecode,
    ambientDecode_ker,
    ambientToRange,
    ambientIntoCokernel,
    ambientIntoCokernel_injective,
    partial_unitCarries,
    decode_unitCarries,
    ambientIntoCokernel_boundary]

#recheck_categorical RiemannResearch.RH.PhysicalHeadBoundaryCoordinates
  in RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadBoundaryCoordinates [
    ScalarL2,
    signedCarry,
    signedCarry_eq_div_rowNorm,
    unitCarry_mixed,
    signedCarry_sq,
    layerValue,
    layerValue_unit,
    squareSummableSequences,
    mem_squareSummableSequences_iff,
    formalCoefficients,
    coefficient_stable,
    formalCoefficients_exact,
    diagonal,
    partial_diagonal,
    formalCoefficients_diagonal,
    quotientCoefficients,
    quotientCoefficients_ker,
    layerCokernelEquiv,
    layerCokernel_boundary,
    summable_signedCarry_iff_rh,
    exists_layer_lift_iff_rh,
    parity_capture_with_boundary,
    parity_capture_iff_summable_signedCarry,
    constant_layers_ne_zero,
    carryMeanSquare,
    carryMeanSquare_tendsto_zero,
    not_summable_one_sub_signedCarry,
    constant_layers_survive]

-- 2026-11-25 | df5c1bf8d28a736314a864c05d9c450372504515 | Compute the mixed parity projection by a scalar digamma Parseval recurrence
#recheck_categorical RiemannResearch.RH.MixedParityDigammaParseval
  in RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis.DigammaParseval [
    digammaWeight,
    digammaWeight_eq,
    digammaWeight_refinement,
    packetGramEntry_eq_weighted,
    modePair,
    orthogonalPacket,
    scale,
    scale_pos,
    basis_eq_scaled,
    scale_smul_basis,
    packet_expansion,
    diagonal_pair,
    cross_expansion,
    scale_sq,
    pivot_pos,
    modePair_recurrence,
    digammaRow,
    digammaRow_eq_modePair,
    basis_functional_recurrence,
    mixed_parity_coefficient,
    hasSum_parity_energy,
    parity_projection_norm,
    physical_head_coefficient,
    first_digamma_term,
    ten,
    mixed_lt_ten,
    before_six,
    before_ten,
    second_digamma_term,
    physical_head_energy_eq_digamma_series,
    parity_endpoint_iff_one_mem]

-- 2026-11-25 | 6439072cd92a8b0319ce9c262bada75e8080f057 | Identify the physical closure and reconstruction energy of canonical CRT carries
#recheck_categorical RiemannResearch.RH.CanonicalCarryClosure
  in RiemannResearch.RH.CanonicalCarryClosure [
    canonicalVector_pair_eq,
    rawClosure,
    asympWeight,
    rowWeight,
    rowWeight_tendsto,
    mul_escape_left,
    balanced_limit,
    primePower_mem_of_balanced_limits,
    modulus_is_power,
    full_atom_mem,
    rawClosure_le_full,
    carryClosure_eq_fullClosure_of_balanced_rows,
    common_auxiliary_primes,
    row_scalar,
    common_prime_balanced_rows,
    rawClosure_eq_fullClosure,
    pAtom_tendsto_zero,
    physical_rawCarry_closures,
    canonical_kernel_contains_full,
    pAtom_two_ne_zero,
    qResidue_two_ne_zero,
    no_continuous_carry_retraction,
    no_physical_prime_retraction,
    riemannHypothesis_iff_one_mem_canonicalCarryClosure,
    selectorGraph,
    selectorGraph_closure_eq_product,
    two_prime_carry_coordinate,
    physical_head_norm_sq_lower,
    two_prime_carry_norm_sq_lower,
    two_prime_row_norm_sq_lower,
    two_prime_oblique_amplification_sq]

#recheck_categorical RiemannResearch.RH.CanonicalCarryGram
  in RiemannResearch.RH.CanonicalCarryClosure [
    rawPVector,
    rawUnitObservation,
    rawUnitObservation_eq_log_row,
    rawUnitGramCost,
    rawUnitGramCost_eq_finiteOptimum,
    rawUnitGramCost_iSup,
    riemannHypothesis_iff_rawUnitGramCost_saturates,
    rawUnitGram_minimizers_tendsto]

-- 2026-11-25 | e684cf2b1d15c084044dff7d3e15cb406bac2ad6 | Reconstruct the mixed parity projection by infinite physical quotient descent
#recheck_categorical RiemannResearch.RH.MixedParityDigammaParseval
  in RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis.DigammaParseval [
    hasSum_parity_modes]

#recheck_categorical RiemannResearch.RH.MixedParityQuotientDescent
  in RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis.DigammaParseval [
    projectedParity,
    parityLayerCoefficient,
    parityLayerPrefix,
    physicalKernelInMixed,
    headLayer_eq_inner,
    inner_parityLayerPrefix,
    parityLayerPrefix_quotient,
    parityLayerPrefix_unique,
    hasSum_parityLayerProjection,
    parityLayerPrefix_tendsto,
    paritySiteRow,
    mixedSite,
    paritySiteRow_eq,
    parity_site_hasSum,
    physicalQuotientRestriction,
    parityLayerPrefix_compatible,
    parityLayerPrefix_site,
    parityLayerCoefficient_from_site,
    parityLayerCoefficient_eq_ambient,
    parityLayerPrefix_norm_sq,
    parityLayerPrefix_lift_cost,
    parityLayerPrefix_error,
    parityLayerPrefix_unique_minimum]

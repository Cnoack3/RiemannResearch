# Category theory and the Pareto boundary in Lean

The November reconstruction inventory below the reconstruction table covers 49 modules, 790 public named declarations, 86 private or local declarations, and 5 further anonymous instances. The first two sections contain the abstract categorical constructions and the Pareto diagrams. The third section includes their Hilbert-space, arithmetic, and other applications.

Each entry links to its declaration in this revision. Names are relative to the displayed namespace. The fields of structures and classes appear beside their declarations. Imported mathlib declarations and automatically generated recursors are outside the index.

The underlying Hilbert quotient tower and its algebra quotients have separate Hausdorff descent theorems. The complete mean snake sequence, its pullback to each stage, and the squarefree residue product are indexed here. [Hilbert tower](RH/PrimeSupportParityDescent.lean) · [Algebra tower](RH/PrimeSupportAlgebraDescent.lean) · [Exact sequence](RH/CenteredMeanLongExact.lean) · [Arithmetic criteria](RH/CenteredMeanRHCriteria.lean). The [Gram boundary research note](THEOREM_CATALOG_PARETO_BOUNDARY_GRAM_20261121.md) records the exact arithmetic tests and their outstanding hypotheses.

## November 24 additions to the centered boundary declarations

The quotient declarations and boundary representatives use `RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake`. The Gram-tail declarations use its `DigammaSection` namespace. The full set is available through [CategoryTheory.All](CategoryTheory/All.lean).

| Module | Selected declarations | Mathematical content |
| --- | --- | --- |
| [CenteredMeanQuotientNorm](RH/CenteredMeanQuotientNorm.lean) | [`centeredCoordinateClass`](RH/CenteredMeanQuotientNorm.lean#L332), [`coordinate_quotient_norm_loss`](RH/CenteredMeanQuotientNorm.lean#L337), [`hasSum_coordinate_quotient_norm_loss`](RH/CenteredMeanQuotientNorm.lean#L354), [`boundary_zero_iff_coordinate_norms`](RH/CenteredMeanQuotientNorm.lean#L369) | The exact coordinate norm losses sum to the limiting energy. |
| [CenteredMeanQuotientTail](RH/CenteredMeanQuotientTail.lean) | [`coordinateLossTail`](RH/CenteredMeanQuotientTail.lean#L30), [`residualTailEnergy_eq_coordinateLossTail`](RH/CenteredMeanQuotientTail.lean#L61), [`boundary_zero_iff_frequently_bounded_coordinateLossTail`](RH/CenteredMeanQuotientTail.lean#L102), [`exists_riemannHypothesis_of_stretched_coordinateLossTail`](RH/CenteredMeanQuotientTail.lean#L161) | The physical residual tail gives a necessary and sufficient cofinal test for a zero boundary. |
| [CenteredMeanGramTail](RH/CenteredMeanGramTail.lean) | [`finiteSectionShell_one_solve`](RH/CenteredMeanGramTail.lean#L34), [`finiteSectionShell_variance_partition`](RH/CenteredMeanGramTail.lean#L67), [`finiteSectionTailCost`](RH/CenteredMeanGramTail.lean#L142), [`finiteSectionTailCost_tendsto`](RH/CenteredMeanGramTail.lean#L155), [`boundary_zero_iff_cofinal_finiteSectionTailCost`](RH/CenteredMeanGramTail.lean#L175) | At each physical cutoff the finite Gram tail tends to the limiting tail. The cofinal test requires a common bound. |
| [CenteredMeanPeriodicGramTail](RH/CenteredMeanPeriodicGramTail.lean) | [`sectionPeriodMean`](RH/CenteredMeanPeriodicGramTail.lean#L27), [`sectionPeriodMean_lower`](RH/CenteredMeanPeriodicGramTail.lean#L49), [`finiteSectionTailCost_period_error`](RH/CenteredMeanPeriodicGramTail.lean#L62), [`scaled_finiteSectionTailCost_tendsto_periodMean`](RH/CenteredMeanPeriodicGramTail.lean#L106), [`later_finiteSectionTailCost_identity`](RH/CenteredMeanPeriodicGramTail.lean#L132) | At fixed Gram cutoff the scaled physical tail converges to a strictly positive period mean. Moving to a later Gram solve has an exact signed cost. |
| [CenteredMeanMovingGramTail](RH/CenteredMeanMovingGramTail.lean) | [`finiteSectionTailDrift_eq`](RH/CenteredMeanMovingGramTail.lean#L30), [`fixedSolve_stretched_finiteSectionTailCost_tendsto`](RH/CenteredMeanMovingGramTail.lean#L84), [`exists_calibrated_physicalSchedule`](RH/CenteredMeanMovingGramTail.lean#L105), [`exists_scale_boundary_zero_iff_cofinal_tailDrift`](RH/CenteredMeanMovingGramTail.lean#L137) | The scaled drift from a base Gram solve to cofinally late updated solves tests the centered boundary. |
| [CenteredMeanProgressionGramTail](RH/CenteredMeanProgressionGramTail.lean) | [`finiteSectionTailDrift_eq_progressionSum`](RH/CenteredMeanProgressionGramTail.lean#L67), [`firstPeriodTailDrift_bounds`](RH/CenteredMeanProgressionGramTail.lean#L118), [`exists_scale_boundary_zero_iff_cofinal_firstPeriodTailDrift`](RH/CenteredMeanProgressionGramTail.lean#L138) | In the cofinal test a single shifted period controls the complete positive tail within a factor of three. |
| [CenteredMeanDriftWindows](RH/CenteredMeanDriftWindows.lean) | [`finiteSectionDriftWindow_partition`](RH/CenteredMeanDriftWindows.lean#L30), [`finiteSectionDriftWindow_omitted_tendsto_zero`](RH/CenteredMeanDriftWindows.lean#L50), [`exists_scale_boundary_zero_iff_cofinal_driftWindow`](RH/CenteredMeanDriftWindows.lean#L73), [`riemannHypothesis_of_bounded_driftWindows`](RH/CenteredMeanDriftWindows.lean#L113) | At a fixed base solve, any sequence of window lengths tending to infinity exhausts the later-solve drift. |
| [MixedConductorL1Closure](RH/MixedConductorL1Closure.lean) | [`boundary_unit_exact_head_L1_representative`](RH/MixedConductorL1Closure.lean#L222), [`boundary_unit_head_energy_lower`](RH/MixedConductorL1Closure.lean#L241), [`boundary_zero_iff_bounded_representative_heads`](RH/MixedConductorL1Closure.lean#L262) | The unit class has representatives with arbitrarily long zero heads. A uniform bound on their Hilbert norms characterizes boundary vanishing. |
| [CenteredMeanMellinDescent](RH/CenteredMeanMellinDescent.lean) | [`boundaryMellin_boundary`](RH/CenteredMeanMellinDescent.lean#L37), [`boundarySplitMonoOfZetaZero`](RH/CenteredMeanMellinDescent.lean#L64), [`boundary_representative_mellin_power_lower`](RH/CenteredMeanMellinDescent.lean#L74), [`riemannHypothesis_of_boundary_head_subpower`](RH/CenteredMeanMellinDescent.lean#L84) | At a right zero the boundary arrow has an explicit left inverse, and its representatives obey a quantitative power lower bound. |
| [CenteredMeanMellinCharacters](RH/CenteredMeanMellinCharacters.lean) | [`normalizedBoundaryMellin_linearIndependent`](RH/CenteredMeanMellinCharacters.lean#L66), [`boundaryCokernelMellinDifference_ne_zero`](RH/CenteredMeanMellinCharacters.lean#L82), [`riemannHypothesis_of_boundary_epi`](RH/CenteredMeanMellinCharacters.lean#L96), [`boundary_epi_iff_riemannHypothesis`](RH/CenteredMeanMellinCharacters.lean#L110) | Distinct right zeros yield independent normalized evaluations. The epimorphism implies RH. The converse takes the Báez-Duarte implication. |
| [CenteredMeanDriftCutoffs](RH/CenteredMeanDriftCutoffs.lean) | [`finiteSectionTailDrift_le_cutoffGain`](RH/CenteredMeanDriftCutoffs.lean#L42), [`finiteSectionTailCost_le_cutoffMass`](RH/CenteredMeanDriftCutoffs.lean#L60), [`exists_schedule_uniform_finite_solve_drift`](RH/CenteredMeanDriftCutoffs.lean#L114) | The gain in reciprocal packet mass bounds the physical drift throughout any prescribed finite range of solves. |
| [DyadicParityTwoStageGram](RH/DyadicParityTwoStageGram.lean) | [`finite_two_stage_projected_parity_gram`](RH/DyadicParityTwoStageGram.lean#L155), [`twoStageParityGramDefect_tendsto`](RH/DyadicParityTwoStageGram.lean#L245), [`stageUnit_zero_iff_cofinal_two_stage_parity_gram`](RH/DyadicParityTwoStageGram.lean#L272), [`riemannHypothesis_of_cofinal_two_stage_parity_gram`](RH/DyadicParityTwoStageGram.lean#L292) | Vanishing of the stage unit is equivalent to arbitrarily small determinants at cofinal finite stages. |
| [LegalTailMeanCapacity](RH/LegalTailMeanCapacity.lean) | [`legalTailMeanCapacity_normalized_bounds`](RH/LegalTailMeanCapacity.lean#L125), [`legalTailMeanRepair_isLeast`](RH/LegalTailMeanCapacity.lean#L153), [`legalTailMeanRepair_energy_le_covariance241`](RH/LegalTailMeanCapacity.lean#L208) | The optimal mean correction preserves the fitted head and costs at most 1009/1000 of the unrestricted squared error. |
| [CenteredParityDilationCapacity](RH/CenteredParityDilationCapacity.lean) | [`centeredParity_uniform_lower`](RH/CenteredParityDilationCapacity.lean#L278), [`centeredParity_limit_error_comparison`](RH/CenteredParityDilationCapacity.lean#L307), [`centeredParityGramCapacity_ninety_nine_percent`](RH/CenteredParityDilationCapacity.lean#L338) | Every cutoff from 61,695 captures at least 99 percent of the centered parity source energy. |
| [CenteredMeanDyadicDrift](RH/CenteredMeanDyadicDrift.lean) | [`dyadicDriftCutoff`](RH/CenteredMeanDyadicDrift.lean#L21), [`dyadic_finiteSectionTailDrift_le`](RH/CenteredMeanDyadicDrift.lean#L99), [`dyadic_finiteSectionTailCost_le`](RH/CenteredMeanDyadicDrift.lean#L112) | The damped cost of all solves through a dyadic cutoff is bounded by the actual reciprocal packet-mass gain. |
| [LegalTailMeanCapacityMellin](RH/LegalTailMeanCapacityMellin.lean) | [`legalTailMeanCapacity_zero_gap`](RH/LegalTailMeanCapacityMellin.lean#L50), [`riemannHypothesis_of_legalTailMeanCapacity_saturation`](RH/LegalTailMeanCapacityMellin.lean#L98) | Every right zero forces a uniform deficit from full head-tail mean capacity. |

## Reconstructing the November 20 category theory

The historical reference is [the November 20 Pacific revision](https://github.com/Cnoack3/RiemannResearch/commit/3c9ae62606587b0fbb90ee7a55cb8cda9a262d97). Its ten imported modules are preserved. The [centered ambient snake](https://github.com/Cnoack3/RiemannResearch/commit/dcdbbef767fd5f0f9cdb38616227fb78bcbb5d48) and the [successive-layer snakes](https://github.com/Cnoack3/RiemannResearch/commit/5408c680531330991d8af3d327120285dd091c1c) entered the repository on November 21 Pacific. Import `RiemannResearch.CategoryTheory.All` for the entire construction.

| Part of the construction | Maps and verified properties | Lean source |
|---|---|---|
| Finite CRT and atom/carry presentations | Local matching, overlap equalizers, categorical CRT, squarefree product coordinates and naturality under conductor refinement | [Finite-family CRT](CategoryTheory/FiniteFamilyCRT.lean), [squarefree residues](CategoryTheory/SquarefreeResidueCRT.lean), [atom/carry refinement](RH/FiniteAtomCarryFunctor.lean) |
| Inverse conductor towers | Reduction from later to earlier residues. The ring of compatible families satisfies `conductorTowerIsLimit`. The cofinal LCM tower gives the product of the p-adic integer rings. The primorial tower gives the product of their residue fields. The restriction map loses prime-power information. | [Categorical limit](RH/ConductorTowerLimit.lean), [ring identifications and topology](RH/ConductorTowerCompletions.lean), [profinite CRT](NumberTheory/ProfiniteCRTUniversal.lean) |
| Completion, carry and affine head constraints | Completion by finite coordinate images, norm-convergent recursive carry expansions, nested affine head fibres and their reconstruction-energy criterion | [Finite images](Analysis/FiniteCoordinateCompletion.lean), [infinite carries](RH/QInfiniteSquarefreeCarry.lean), [affine heads](RH/ParetoAffineHeadTower.lean), [reconstruction energy](RH/ConductorReconstructionEnergy.lean) |
| Screened algebra and mixed bimodule | Square-zero ideal, commuting continuous left and right actions, annihilator, quotient algebra and section changes. The real-linear mean has a section. The regular-module quotient has no module-linear section. | [Multiplication](RH/MixedConductorSquareZero.lean), [module actions](RH/MixedConductorBimodule.lean) |
| Support layers | Strict filtration, orthogonal layer projections and Parseval. For the two layer diagrams, truncation induces zero and inclusion induces the identity. | [Filtration](RH/MixedConductorPrimeSupport.lean), [polarized Parseval](RH/MixedConductorPolarizedParseval.lean), [layer snakes](RH/MixedConductorSupportSnake.lean) |
| Forward quotient towers | Ordinary real-algebra colimit by the union of ideals, canonical surjection to the closed-ideal quotient, nonzero kernel equal to the closure of zero. The ambient Hilbert quotient is a colimit in Hausdorff topological modules. | [Algebraic colimit](RH/AlgebraicSupportColimit.lean), [Hausdorff colimit](RH/HausdorffSupportColimit.lean), [algebra descent](RH/PrimeSupportAlgebraDescent.lean) |
| Mean snakes | Both split rows, the zero connecting map for ordinary inclusion, the defect class for centering, full exact sequence, quotienting both rows by any mixed submodule, naturality of both rows, their splittings and their connecting maps, and comparison of all interior arrows | [Original diagram](RH/CenteredMeanSnake.lean), [ambient sequence](RH/CenteredMeanLongExact.lean), [stage sequences](RH/CenteredMeanStageSnake.lean) |
| Finite arithmetic and infinite descent | Finite Gram solves, strict signed tests and the condition for arbitrarily late contractions of the quotient norm. Vanishing at infinite depth is the remaining arithmetic obligation. | [Finite solves](RH/CenteredMeanFiniteDescent.lean), [certified signs](RH/SiteGramStrictStages.lean), [contraction criterion](RH/PrimeSupportParityDescent.lean) |

## Abstract category theory and CRT


### All

[Lean source](CategoryTheory/All.lean)

Import interface.

### AtomCarryPresentation

[Lean source](CategoryTheory/AtomCarryPresentation.lean)


Namespace `RiemannResearch.CategoryTheory.AtomCarryPresentation`

- structure [Presentation](CategoryTheory/AtomCarryPresentation.lean#L34)
  - [Presentation.Coeff](CategoryTheory/AtomCarryPresentation.lean#L35)
  - [Presentation.addCommGroup](CategoryTheory/AtomCarryPresentation.lean#L36)
  - [Presentation.moduleStruct](CategoryTheory/AtomCarryPresentation.lean#L37)
  - [Presentation.finite](CategoryTheory/AtomCarryPresentation.lean#L38)
  - [Presentation.synthesis](CategoryTheory/AtomCarryPresentation.lean#L39)
- structure [PresentationHom](CategoryTheory/AtomCarryPresentation.lean#L47)
  - [PresentationHom.map](CategoryTheory/AtomCarryPresentation.lean#L48)
  - [PresentationHom.preserves](CategoryTheory/AtomCarryPresentation.lean#L49)
- [instance : Category (Presentation.{u, v, w} R H)](CategoryTheory/AtomCarryPresentation.lean#L51)
- theorem [subsingleton_hom_of_injective](CategoryTheory/AtomCarryPresentation.lean#L64)
- def [ofSynthesis](CategoryTheory/AtomCarryPresentation.lean#L79)
- def [coordinateIso](CategoryTheory/AtomCarryPresentation.lean#L84)
- def [crtEquiv](CategoryTheory/AtomCarryPresentation.lean#L107)
- theorem [crtEquiv_apply](CategoryTheory/AtomCarryPresentation.lean#L116)
- theorem [crtEquiv_involutive](CategoryTheory/AtomCarryPresentation.lean#L120)
- def [carrySynthesis](CategoryTheory/AtomCarryPresentation.lean#L124)
- theorem [carrySynthesis_apply](CategoryTheory/AtomCarryPresentation.lean#L128)
- theorem [crt_synthesis](CategoryTheory/AtomCarryPresentation.lean#L133)
- def [crtIso](CategoryTheory/AtomCarryPresentation.lean#L144)
- theorem [crt_range](CategoryTheory/AtomCarryPresentation.lean#L169)
- theorem [crt_injective](CategoryTheory/AtomCarryPresentation.lean#L184)
- theorem [crt_disjoint](CategoryTheory/AtomCarryPresentation.lean#L192)
- def [coefficientSynthesis](CategoryTheory/AtomCarryPresentation.lean#L210)
- theorem [family_carrySynthesis](CategoryTheory/AtomCarryPresentation.lean#L217)
- theorem [family_coprod_injective](CategoryTheory/AtomCarryPresentation.lean#L230)
- theorem [family_crt_span](CategoryTheory/AtomCarryPresentation.lean#L246)
- theorem [family_crt_disjoint](CategoryTheory/AtomCarryPresentation.lean#L259)

### FiniteFamilyCRT

[Lean source](CategoryTheory/FiniteFamilyCRT.lean)


Namespace `Setoid`

- def [crtComp](CategoryTheory/FiniteFamilyCRT.lean#L24)
- def [CRTCompatible](CategoryTheory/FiniteFamilyCRT.lean#L28)
- def [HasFiniteCRT](CategoryTheory/FiniteFamilyCRT.lean#L32)
- def [CRTGluing](CategoryTheory/FiniteFamilyCRT.lean#L37)
- theorem [hasFiniteCRT_of_crtGluing](CategoryTheory/FiniteFamilyCRT.lean#L42)
- theorem [crtGluing_of_hasFiniteCRT](CategoryTheory/FiniteFamilyCRT.lean#L72)
- theorem [hasFiniteCRT_iff_crtGluing](CategoryTheory/FiniteFamilyCRT.lean#L106)
- theorem [crtCompatible_of_solution](CategoryTheory/FiniteFamilyCRT.lean#L111)
- theorem [solution_iff_common_relation](CategoryTheory/FiniteFamilyCRT.lean#L118)
- def [crtKernel](CategoryTheory/FiniteFamilyCRT.lean#L128)
- def [CRTMatching](CategoryTheory/FiniteFamilyCRT.lean#L143)
- def [crtAllKernel](CategoryTheory/FiniteFamilyCRT.lean#L148)
- def [crtQuotientMap](CategoryTheory/FiniteFamilyCRT.lean#L155)
- theorem [crtQuotientMap_injective](CategoryTheory/FiniteFamilyCRT.lean#L164)
- theorem [crtQuotientMap_surjective](CategoryTheory/FiniteFamilyCRT.lean#L176)
- noncomputable def [crtQuotientEquiv](CategoryTheory/FiniteFamilyCRT.lean#L195)
- theorem [existsUnique_solution](CategoryTheory/FiniteFamilyCRT.lean#L203)
- def [CRTPermutes](CategoryTheory/FiniteFamilyCRT.lean#L222)
- def [crtCompositeSetoid](CategoryTheory/FiniteFamilyCRT.lean#L226)
- theorem [crtCompositeSetoid_eq_sup](CategoryTheory/FiniteFamilyCRT.lean#L241)
- theorem [crtComp_iff_sup](CategoryTheory/FiniteFamilyCRT.lean#L255)
- theorem [crtGluing_of_distributive_permutable](CategoryTheory/FiniteFamilyCRT.lean#L262)
- def [crtOverlapLeft](CategoryTheory/FiniteFamilyCRT.lean#L287)
- def [crtOverlapRight](CategoryTheory/FiniteFamilyCRT.lean#L292)
- theorem [crt_overlap_eq_iff_pair](CategoryTheory/FiniteFamilyCRT.lean#L297)
- def [CRTOverlapMatching](CategoryTheory/FiniteFamilyCRT.lean#L316)
- def [crtMatchingEquivOverlap](CategoryTheory/FiniteFamilyCRT.lean#L321)
- noncomputable def [crtQuotientOverlapEquiv](CategoryTheory/FiniteFamilyCRT.lean#L329)
- theorem [crt_extend_solution](CategoryTheory/FiniteFamilyCRT.lean#L342)

### FunctorCRT

[Lean source](CategoryTheory/FunctorCRT.lean)


Namespace `CategoryTheory.InternalEquivalencePresentation`

- noncomputable def [mapRelation](CategoryTheory/FunctorCRT.lean#L25)
- theorem [holds_map](CategoryTheory/FunctorCRT.lean#L73)
- theorem [localSolution_map_internal](CategoryTheory/FunctorCRT.lean#L84)
- theorem [localComp_map_internal](CategoryTheory/FunctorCRT.lean#L96)

### LocalFamilyCRT

[Lean source](CategoryTheory/LocalFamilyCRT.lean)


Namespace `CategoryTheory`

- structure [RegularCoverCalculus](CategoryTheory/LocalFamilyCRT.lean#L32)
  - [RegularCoverCalculus.comp](CategoryTheory/LocalFamilyCRT.lean#L33)
  - [RegularCoverCalculus.pullback](CategoryTheory/LocalFamilyCRT.lean#L35)
- structure [GeneralizedEquivalence](CategoryTheory/LocalFamilyCRT.lean#L41)
  - [GeneralizedEquivalence.rel](CategoryTheory/LocalFamilyCRT.lean#L42)
  - [GeneralizedEquivalence.precomp](CategoryTheory/LocalFamilyCRT.lean#L43)

Namespace `CategoryTheory.GeneralizedEquivalence`

- def [LocalComp](CategoryTheory/LocalFamilyCRT.lean#L51)
- def [LocalSolution](CategoryTheory/LocalFamilyCRT.lean#L56)
- def [LocalCompatible](CategoryTheory/LocalFamilyCRT.lean#L61)
- def [HasLocalFiniteCRT](CategoryTheory/LocalFamilyCRT.lean#L65)
- def [LocalGluing](CategoryTheory/LocalFamilyCRT.lean#L70)
- theorem [localComp_self](CategoryTheory/LocalFamilyCRT.lean#L76)
- theorem [localComp_swap](CategoryTheory/LocalFamilyCRT.lean#L80)
- theorem [localComp_precomp](CategoryTheory/LocalFamilyCRT.lean#L85)
- theorem [localComp_left_trans](CategoryTheory/LocalFamilyCRT.lean#L97)
- theorem [hasLocalFiniteCRT_of_localGluing](CategoryTheory/LocalFamilyCRT.lean#L105)
- theorem [localGluing_of_hasLocalFiniteCRT](CategoryTheory/LocalFamilyCRT.lean#L139)
- theorem [hasLocalFiniteCRT_iff_localGluing](CategoryTheory/LocalFamilyCRT.lean#L171)
- def [kernel](CategoryTheory/LocalFamilyCRT.lean#L177)

Namespace `CategoryTheory`

- structure [InternalEquivalencePresentation](CategoryTheory/LocalFamilyCRT.lean#L193)
  - [InternalEquivalencePresentation.object](CategoryTheory/LocalFamilyCRT.lean#L194)
  - [InternalEquivalencePresentation.left](CategoryTheory/LocalFamilyCRT.lean#L195)
  - [InternalEquivalencePresentation.right](CategoryTheory/LocalFamilyCRT.lean#L196)
  - [InternalEquivalencePresentation.joint_monic](CategoryTheory/LocalFamilyCRT.lean#L197)
  - [InternalEquivalencePresentation.diagonal](CategoryTheory/LocalFamilyCRT.lean#L199)
  - [InternalEquivalencePresentation.diagonal_left](CategoryTheory/LocalFamilyCRT.lean#L200)
  - [InternalEquivalencePresentation.diagonal_right](CategoryTheory/LocalFamilyCRT.lean#L201)
  - [InternalEquivalencePresentation.swap](CategoryTheory/LocalFamilyCRT.lean#L202)
  - [InternalEquivalencePresentation.swap_left](CategoryTheory/LocalFamilyCRT.lean#L203)
  - [InternalEquivalencePresentation.swap_right](CategoryTheory/LocalFamilyCRT.lean#L204)
  - [InternalEquivalencePresentation.trans](CategoryTheory/LocalFamilyCRT.lean#L205)
  - [InternalEquivalencePresentation.trans_left](CategoryTheory/LocalFamilyCRT.lean#L206)
  - [InternalEquivalencePresentation.trans_right](CategoryTheory/LocalFamilyCRT.lean#L207)

Namespace `CategoryTheory.InternalEquivalencePresentation`

- def [Holds](CategoryTheory/LocalFamilyCRT.lean#L214)
- def [toGeneralized](CategoryTheory/LocalFamilyCRT.lean#L217)
- theorem [finite_crt_iff_gluing](CategoryTheory/LocalFamilyCRT.lean#L245)

Namespace `CategoryTheory`

- theorem [equal_of_kernelPair](CategoryTheory/LocalFamilyCRT.lean#L259)
- theorem [isRegularEpi_of_cover_factor](CategoryTheory/LocalFamilyCRT.lean#L268)

Namespace `CategoryTheory.GeneralizedEquivalence`

- theorem [localSolution_map](CategoryTheory/LocalFamilyCRT.lean#L311)
- theorem [localComp_map](CategoryTheory/LocalFamilyCRT.lean#L324)
- theorem [local_extend_solution](CategoryTheory/LocalFamilyCRT.lean#L346)

### OverlapEqualizerCRT

[Lean source](CategoryTheory/OverlapEqualizerCRT.lean)


Namespace `CategoryTheory.GeneralizedEquivalence`

- noncomputable def [overlapProductLeft](CategoryTheory/OverlapEqualizerCRT.lean#L31)
- noncomputable def [overlapProductRight](CategoryTheory/OverlapEqualizerCRT.lean#L36)
- theorem [exists_overlap_equalizer_quotient](CategoryTheory/OverlapEqualizerCRT.lean#L43)

### QuotientMatchingCRT

[Lean source](CategoryTheory/QuotientMatchingCRT.lean)


Namespace `CategoryTheory.GeneralizedEquivalence`

- def [QuotientPair](CategoryTheory/QuotientMatchingCRT.lean#L28)
- theorem [finite_local_lifts](CategoryTheory/QuotientMatchingCRT.lean#L34)
- theorem [quotientPair_kernel](CategoryTheory/QuotientMatchingCRT.lean#L59)
- theorem [quotient_crt_local_lift](CategoryTheory/QuotientMatchingCRT.lean#L78)
- theorem [quotient_matching_isRegularEpi](CategoryTheory/QuotientMatchingCRT.lean#L103)
- theorem [quotient_matching_kernel](CategoryTheory/QuotientMatchingCRT.lean#L120)
- theorem [quotient_matching_isIso](CategoryTheory/QuotientMatchingCRT.lean#L137)
- theorem [quotient_image_matching_universal](CategoryTheory/QuotientMatchingCRT.lean#L157)
- theorem [quotient_image_pairwise](CategoryTheory/QuotientMatchingCRT.lean#L187)
- theorem [quotient_matching_pullback](CategoryTheory/QuotientMatchingCRT.lean#L199)

### RegularCategoryCRT

[Lean source](CategoryTheory/RegularCategoryCRT.lean)


Namespace `CategoryTheory`

- structure [RegularImageFactorization](CategoryTheory/RegularCategoryCRT.lean#L27)
  - [RegularImageFactorization.object](CategoryTheory/RegularCategoryCRT.lean#L28)
  - [RegularImageFactorization.epi](CategoryTheory/RegularCategoryCRT.lean#L29)
  - [RegularImageFactorization.mono](CategoryTheory/RegularCategoryCRT.lean#L30)
  - [RegularImageFactorization.fac](CategoryTheory/RegularCategoryCRT.lean#L31)
  - [RegularImageFactorization.epi_regular](CategoryTheory/RegularCategoryCRT.lean#L32)
  - [RegularImageFactorization.mono_monic](CategoryTheory/RegularCategoryCRT.lean#L33)
- class [HasRegularImageFactorizations](CategoryTheory/RegularCategoryCRT.lean#L36)
  - [HasRegularImageFactorizations.exists_factorization](CategoryTheory/RegularCategoryCRT.lean#L37)

Namespace `CategoryTheory.GeneralizedEquivalence`

- theorem [exists_matching_quotient](CategoryTheory/RegularCategoryCRT.lean#L47)

Namespace `CategoryTheory`

- theorem [isIso_mono_of_regularEpi_factor](CategoryTheory/RegularCategoryCRT.lean#L92)
- theorem [regularEpi_comp_of_regularImages](CategoryTheory/RegularCategoryCRT.lean#L110)
- class [RegularCategoryStructure](CategoryTheory/RegularCategoryCRT.lean#L144)
  - [RegularCategoryStructure.regularEpi_pullback](CategoryTheory/RegularCategoryCRT.lean#L146)
- theorem [regularCoverCalculusOfRegular](CategoryTheory/RegularCategoryCRT.lean#L150)

Namespace `CategoryTheory.InternalEquivalencePresentation`

- theorem [finite_crt_iff_gluing_of_regular](CategoryTheory/RegularCategoryCRT.lean#L164)

Namespace `CategoryTheory.GeneralizedEquivalence`

- theorem [exists_matching_quotient_of_regular](CategoryTheory/RegularCategoryCRT.lean#L178)

### SquarefreeResidueCRT

CRT as a natural isomorphism of diagrams of commutative rings and a product universal property. [Lean source](CategoryTheory/SquarefreeResidueCRT.lean)

Namespace `RiemannResearch.SquarefreeResidueCRT`

- abbrev [PrimeFamily](CategoryTheory/SquarefreeResidueCRT.lean#L22)
- def [conductor](CategoryTheory/SquarefreeResidueCRT.lean#L24)
- def [primeSupport](CategoryTheory/SquarefreeResidueCRT.lean#L26)
- theorem [conductor_eq_prod](CategoryTheory/SquarefreeResidueCRT.lean#L29)
- theorem [primeFactors_conductor](CategoryTheory/SquarefreeResidueCRT.lean#L32)
- theorem [conductor_primeSupport](CategoryTheory/SquarefreeResidueCRT.lean#L36)
- theorem [conductor_squarefree](CategoryTheory/SquarefreeResidueCRT.lean#L39)
- theorem [conductor_dvd](CategoryTheory/SquarefreeResidueCRT.lean#L55)
- abbrev [Coordinates](CategoryTheory/SquarefreeResidueCRT.lean#L60)
- private theorem [pairwise](CategoryTheory/SquarefreeResidueCRT.lean#L62)
- def [crtEquiv](CategoryTheory/SquarefreeResidueCRT.lean#L67)
- theorem [crtEquiv_apply](CategoryTheory/SquarefreeResidueCRT.lean#L70)
- def [squarefreeEquiv](CategoryTheory/SquarefreeResidueCRT.lean#L75)
- def [restrictCoordinates](CategoryTheory/SquarefreeResidueCRT.lean#L79)
- def [residueFunctor](CategoryTheory/SquarefreeResidueCRT.lean#L87)
- def [coordinateFunctor](CategoryTheory/SquarefreeResidueCRT.lean#L93)
- def [crtIso](CategoryTheory/SquarefreeResidueCRT.lean#L100)
- def [primeFan](CategoryTheory/SquarefreeResidueCRT.lean#L106)
- private def [glue](CategoryTheory/SquarefreeResidueCRT.lean#L110)
- private theorem [glue_proj](CategoryTheory/SquarefreeResidueCRT.lean#L114)
- def [primeFanIsLimit](CategoryTheory/SquarefreeResidueCRT.lean#L121)

## Pareto sequences, functors, quotients, and connecting maps


### CenteredMeanQuotients

[Lean source](RH/CenteredMeanQuotients.lean)


Namespace `RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake`

- def [projectedOne](RH/CenteredMeanQuotients.lean#L36)
- theorem [inner_projectedOne](RH/CenteredMeanQuotients.lean#L38)
- theorem [projectedOne_orthogonal_eq_mixed](RH/CenteredMeanQuotients.lean#L46)
- theorem [projectedOne_eq_scaled_section_one](RH/CenteredMeanQuotients.lean#L56)
- theorem [screenedMeanSection_one_orthogonal_eq_mixed](RH/CenteredMeanQuotients.lean#L63)
- abbrev [InternalMeanQuotient](RH/CenteredMeanQuotients.lean#L73)
- theorem [internalMeanQuotient_subsingleton](RH/CenteredMeanQuotients.lean#L77)
- theorem [normalizedScreenedTwo_eq_projected_packet](RH/CenteredMeanQuotients.lean#L86)
- theorem [mixedOrthogonal_starProjection_legal](RH/CenteredMeanQuotients.lean#L94)
- theorem [legalScreening_ker_range](RH/CenteredMeanQuotients.lean#L101)
- theorem [legal_mixed_screened_orthogonal_sum](RH/CenteredMeanQuotients.lean#L126)
- theorem [one_eq_screened_add_orthogonal](RH/CenteredMeanQuotients.lean#L135)
- theorem [screenedLine_eq_projectedOne_line](RH/CenteredMeanQuotients.lean#L143)
- theorem [limitResidual_mem_mixed_screened_orthogonals](RH/CenteredMeanQuotients.lean#L154)
- theorem [limitResidual_mean_and_screened_norm](RH/CenteredMeanQuotients.lean#L161)
- theorem [screenedLine_eq_one_line_iff_one_mem](RH/CenteredMeanQuotients.lean#L169)
- theorem [screenedLine_eq_one_line_iff_residual_zero](RH/CenteredMeanQuotients.lean#L181)
- theorem [screenedLine_eq_one_line_iff_residual_mean_zero](RH/CenteredMeanQuotients.lean#L188)
- def [meanZeroToLegalQuotient](RH/CenteredMeanQuotients.lean#L194)
- theorem [meanZeroToLegalQuotient_ker](RH/CenteredMeanQuotients.lean#L197)
- def [meanZeroRepresentative](RH/CenteredMeanQuotients.lean#L207)
- private theorem [mkQ_screenedTwo](RH/CenteredMeanQuotients.lean#L214)
- theorem [meanZeroToLegalQuotient_representative](RH/CenteredMeanQuotients.lean#L218)
- theorem [meanZeroToLegalQuotient_surjective](RH/CenteredMeanQuotients.lean#L223)
- def [boundaryTargetEquivLegalQuotient](RH/CenteredMeanQuotients.lean#L229)
- theorem [boundaryTargetEquivLegalQuotient_mk](RH/CenteredMeanQuotients.lean#L233)
- theorem [boundaryTargetEquivLegalQuotient_symm_mk](RH/CenteredMeanQuotients.lean#L237)
- theorem [boundaryTargetEquivLegalQuotient_boundary](RH/CenteredMeanQuotients.lean#L245)
- theorem [boundary_one_eq_zero_iff_one_mem](RH/CenteredMeanQuotients.lean#L252)
- theorem [boundaryTarget_subsingleton_iff_closedSpace_eq_top](RH/CenteredMeanQuotients.lean#L261)
- theorem [boundaryTarget_subsingleton_iff_one_mem](RH/CenteredMeanQuotients.lean#L269)
- theorem [mixedClosure_eq_closedSpace_inf_one_orthogonal](RH/CenteredMeanQuotients.lean#L275)
- theorem [screenedTwo_sub_one_mem_orthogonals](RH/CenteredMeanQuotients.lean#L283)
- theorem [screenedTwo_eq_one_of_one_orthogonal_le_mixed](RH/CenteredMeanQuotients.lean#L294)
- theorem [one_orthogonal_le_mixedClosure_iff_one_mem](RH/CenteredMeanQuotients.lean#L302)
- theorem [closedSpace_eq_top_iff_mixedClosure_eq_one_orthogonal](RH/CenteredMeanQuotients.lean#L312)
- theorem [boundary_eq_zero_iff_mixedClosure_eq_one_orthogonal](RH/CenteredMeanQuotients.lean#L322)
- theorem [exact_inclusionConnecting_quotientEquiv](RH/CenteredMeanQuotients.lean#L329)
- theorem [exact_inclusionQuotientEquiv_final](RH/CenteredMeanQuotients.lean#L339)

### CenteredMeanSnake

[Lean source](RH/CenteredMeanSnake.lean)


Namespace `RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake`

- abbrev [meanZero](RH/CenteredMeanSnake.lean#L36)
- theorem [meanZero_eq_orthogonal](RH/CenteredMeanSnake.lean#L38)
- private theorem [mean_legal](RH/CenteredMeanSnake.lean#L44)
- private theorem [mean_screened](RH/CenteredMeanSnake.lean#L49)
- instance [meanZero_complete](RH/CenteredMeanSnake.lean#L52)
- def [center](RH/CenteredMeanSnake.lean#L56)
- theorem [center_apply](RH/CenteredMeanSnake.lean#L59)
- theorem [center_mem](RH/CenteredMeanSnake.lean#L62)
- theorem [center_eq_starProjection](RH/CenteredMeanSnake.lean#L66)
- private theorem [center_fixes](RH/CenteredMeanSnake.lean#L75)
- def [centerLegal](RH/CenteredMeanSnake.lean#L79)
- def [mixedInclusion](RH/CenteredMeanSnake.lean#L82)
- def [mixedInMeanZero](RH/CenteredMeanSnake.lean#L88)
- instance [mixedInMeanZero_closed](RH/CenteredMeanSnake.lean#L90)
- instance [mixedInMeanZero_complete](RH/CenteredMeanSnake.lean#L94)
- abbrev [BoundaryTarget](RH/CenteredMeanSnake.lean#L97)
- theorem [legal_row_exact](RH/CenteredMeanSnake.lean#L99)
- theorem [ambient_row_exact](RH/CenteredMeanSnake.lean#L110)
- theorem [ambient_mean_surjective](RH/CenteredMeanSnake.lean#L113)
- theorem [left_square](RH/CenteredMeanSnake.lean#L117)
- theorem [right_square](RH/CenteredMeanSnake.lean#L124)
- def [ambientMeanComplex](RH/CenteredMeanSnake.lean#L136)
- def [ambientMeanSplitting](RH/CenteredMeanSnake.lean#L144)
- local [instance : HasZeroObject (TopModuleCat.{0} ℝ)](RH/CenteredMeanSnake.lean#L165)
- theorem [ambientMean_shortExact](RH/CenteredMeanSnake.lean#L168)
- def [centeredDiagram](RH/CenteredMeanSnake.lean#L171)
- private theorem [quotient_exact](RH/CenteredMeanSnake.lean#L186)
- private theorem [scalar_kernel_exact](RH/CenteredMeanSnake.lean#L196)
- private def [centerToKernel](RH/CenteredMeanSnake.lean#L200)
- def [snakeMap](RH/CenteredMeanSnake.lean#L203)
- def [defect](RH/CenteredMeanSnake.lean#L212)
- theorem [snakeMap_apply](RH/CenteredMeanSnake.lean#L216)
- abbrev [legalConstants](RH/CenteredMeanSnake.lean#L225)
- private theorem [center_eq_zero_iff](RH/CenteredMeanSnake.lean#L228)
- private theorem [legalConstants_exact](RH/CenteredMeanSnake.lean#L237)
- def [constantMean](RH/CenteredMeanSnake.lean#L245)
- theorem [constantMean_injective](RH/CenteredMeanSnake.lean#L247)
- theorem [exact_constantMean_snakeMap](RH/CenteredMeanSnake.lean#L259)
- def [boundary](RH/CenteredMeanSnake.lean#L266)
- theorem [boundary_apply](RH/CenteredMeanSnake.lean#L269)
- theorem [boundary_toLinearMap](RH/CenteredMeanSnake.lean#L271)
- theorem [boundary_of_lift](RH/CenteredMeanSnake.lean#L277)
- theorem [exact_constantMean_boundary](RH/CenteredMeanSnake.lean#L287)
- theorem [defect_orthogonal](RH/CenteredMeanSnake.lean#L292)
- theorem [norm_sq_of_same_class](RH/CenteredMeanSnake.lean#L300)
- theorem [norm_defect_class](RH/CenteredMeanSnake.lean#L312)
- theorem [boundary_norm](RH/CenteredMeanSnake.lean#L323)
- theorem [boundary_norm_sq](RH/CenteredMeanSnake.lean#L326)
- theorem [boundary_norm_sq_eq_energy](RH/CenteredMeanSnake.lean#L331)
- theorem [boundary_eq_zero_iff_screened](RH/CenteredMeanSnake.lean#L336)
- theorem [boundary_eq_zero_iff_one_mem](RH/CenteredMeanSnake.lean#L341)
- theorem [boundary_range](RH/CenteredMeanSnake.lean#L344)
- theorem [boundary_injective_iff](RH/CenteredMeanSnake.lean#L351)
- theorem [legalConstants_eq_bot_of_nonmember](RH/CenteredMeanSnake.lean#L369)
- theorem [boundary_rank_one_of_nonmember](RH/CenteredMeanSnake.lean#L378)
- theorem [energy_eq_dist_sq](RH/CenteredMeanSnake.lean#L383)
- theorem [energy_le_legal_error](RH/CenteredMeanSnake.lean#L388)
- theorem [meanOne_norm_minimum](RH/CenteredMeanSnake.lean#L396)
- theorem [nonzero_branch](RH/CenteredMeanSnake.lean#L408)
- theorem [boundary_eq_zero_iff_naturalApproximation](RH/CenteredMeanSnake.lean#L418)
- theorem [riemannHypothesis_of_boundary_eq_zero](RH/CenteredMeanSnake.lean#L422)
- theorem [boundary_injective_iff_not_riemannHypothesis](RH/CenteredMeanSnake.lean#L426)
- private theorem [inclusion_left_square](RH/CenteredMeanSnake.lean#L435)
- private theorem [inclusion_right_square](RH/CenteredMeanSnake.lean#L440)
- def [inclusionDiagram](RH/CenteredMeanSnake.lean#L447)
- def [inclusionConnecting](RH/CenteredMeanSnake.lean#L461)
- theorem [inclusionConnecting_eq_zero](RH/CenteredMeanSnake.lean#L471)
- def [meanSectionDifference](RH/CenteredMeanSnake.lean#L478)
- theorem [meanSectionDifference_coe](RH/CenteredMeanSnake.lean#L481)
- theorem [boundary_eq_quotient_meanSectionDifference](RH/CenteredMeanSnake.lean#L488)

### FiniteAtomCarryCRT

[Lean source](RH/FiniteAtomCarryCRT.lean)


Namespace `RiemannResearch.RH.FiniteAtomCarryCRT`

- def [primeConductors](RH/FiniteAtomCarryCRT.lean#L23)
- theorem [mem_primeConductors_iff](RH/FiniteAtomCarryCRT.lean#L27)
- def [mixedConductors](RH/FiniteAtomCarryCRT.lean#L52)
- abbrev [PrimeIndex](RH/FiniteAtomCarryCRT.lean#L55)
- abbrev [MixedIndex](RH/FiniteAtomCarryCRT.lean#L56)
- def [primeAtom](RH/FiniteAtomCarryCRT.lean#L58)
- def [mixedAtom](RH/FiniteAtomCarryCRT.lean#L59)
- def [carryVector](RH/FiniteAtomCarryCRT.lean#L60)
- def [atomSpan](RH/FiniteAtomCarryCRT.lean#L62)
- theorem [combined_atoms_independent](RH/FiniteAtomCarryCRT.lean#L65)
- theorem [mixed_card_ge_two](RH/FiniteAtomCarryCRT.lean#L98)
- def [factorIndex](RH/FiniteAtomCarryCRT.lean#L109)
- def [rowCoefficients](RH/FiniteAtomCarryCRT.lean#L123)
- theorem [row_synthesis](RH/FiniteAtomCarryCRT.lean#L127)
- theorem [carry_eq_row_sub_atom](RH/FiniteAtomCarryCRT.lean#L153)
- theorem [atomSpan_eq_partition](RH/FiniteAtomCarryCRT.lean#L164)
- theorem [atomSpan_eq_prime_sup_carry](RH/FiniteAtomCarryCRT.lean#L192)
- theorem [prime_carry_disjoint](RH/FiniteAtomCarryCRT.lean#L204)
- def [presentationIso](RH/FiniteAtomCarryCRT.lean#L216)

### FiniteAtomCarryFunctor

[Lean source](RH/FiniteAtomCarryFunctor.lean)


Namespace `RiemannResearch.RH.FiniteAtomCarryCRT`

- structure [ConductorStage](RH/FiniteAtomCarryFunctor.lean#L21)
  - [ConductorStage.period](RH/FiniteAtomCarryFunctor.lean#L22)
- [instance : Preorder ConductorStage](RH/FiniteAtomCarryFunctor.lean#L24)
- private abbrev [stagePresentation](RH/FiniteAtomCarryFunctor.lean#L29)
- private def [presentationFunctor](RH/FiniteAtomCarryFunctor.lean#L34)
- private theorem [homToAtom](RH/FiniteAtomCarryFunctor.lean#L49)
- private theorem [homToCarry](RH/FiniteAtomCarryFunctor.lean#L53)
- def [atomPresentationFunctor](RH/FiniteAtomCarryFunctor.lean#L58)
- def [carryPresentationFunctor](RH/FiniteAtomCarryFunctor.lean#L62)
- theorem [atomPresentationFunctor_map_apply](RH/FiniteAtomCarryFunctor.lean#L65)
- theorem [carryPresentationFunctor_map_apply](RH/FiniteAtomCarryFunctor.lean#L69)
- def [atomCarryRefinementIso](RH/FiniteAtomCarryFunctor.lean#L74)
- theorem [atomCarryRefinementIso_app](RH/FiniteAtomCarryFunctor.lean#L78)

### MeanSectionStructure

[Lean source](RH/MeanSectionStructure.lean)


Namespace `RiemannResearch.RH.Pareto.PrimePowerSchur`

- theorem [every_mean_section_eq_screened_plus_mixed](RH/MeanSectionStructure.lean#L11)
- theorem [screenedMeanSection_unique_minimizer](RH/MeanSectionStructure.lean#L45)

### MixedConductorBlockSplitting

[Lean source](RH/MixedConductorBlockSplitting.lean)


Namespace `RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis`

- private theorem [projection_congr](RH/MixedConductorBlockSplitting.lean#L28)
- theorem [projection_add](RH/MixedConductorBlockSplitting.lean#L35)
- theorem [block_norm_sq](RH/MixedConductorBlockSplitting.lean#L41)
- def [blockComplex](RH/MixedConductorBlockSplitting.lean#L47)
- def [blockSplitting](RH/MixedConductorBlockSplitting.lean#L59)
- local [instance : HasZeroObject (TopModuleCat.{0} ℝ)](RH/MixedConductorBlockSplitting.lean#L76)
- local [instance : HasBinaryBiproducts (TopModuleCat.{0} ℝ)](RH/MixedConductorBlockSplitting.lean#L79)
- theorem [block_shortExact](RH/MixedConductorBlockSplitting.lean#L82)
- def [blockBiprodIso](RH/MixedConductorBlockSplitting.lean#L87)
- instance [screenedComplement_hasOrthogonalProjection](RH/MixedConductorBlockSplitting.lean#L91)
- def [packetBiprodIso](RH/MixedConductorBlockSplitting.lean#L97)
- def [subspaceIdeal](RH/MixedConductorBlockSplitting.lean#L105)
- theorem [subspaceIdeal_le](RH/MixedConductorBlockSplitting.lean#L114)
- private theorem [inclusion_injective](RH/MixedConductorBlockSplitting.lean#L119)
- theorem [inclusion_mem_subspaceIdeal](RH/MixedConductorBlockSplitting.lean#L123)
- def [subspaceIdealOrderIso](RH/MixedConductorBlockSplitting.lean#L133)
- theorem [subspaceIdeal_isClosed_iff](RH/MixedConductorBlockSplitting.lean#L159)
- theorem [complementary_subspaceIdeals](RH/MixedConductorBlockSplitting.lean#L189)

### MixedConductorPrimeSupport

[Lean source](RH/MixedConductorPrimeSupport.lean)


Namespace `RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis`

- abbrev [supportSpace](RH/MixedConductorPrimeSupport.lean#L33)
- theorem [supportSpace_mono](RH/MixedConductorPrimeSupport.lean#L36)
- theorem [packet_mem_supportSpace](RH/MixedConductorPrimeSupport.lean#L44)
- theorem [supportSpace_one](RH/MixedConductorPrimeSupport.lean#L48)
- def [supportCoordinate](RH/MixedConductorPrimeSupport.lean#L60)
- theorem [supportCoordinate_self](RH/MixedConductorPrimeSupport.lean#L64)
- theorem [supportSpace_le_coordinate_ker](RH/MixedConductorPrimeSupport.lean#L74)
- theorem [supportCoordinate_residual](RH/MixedConductorPrimeSupport.lean#L90)
- theorem [conductor_thirty_witness](RH/MixedConductorPrimeSupport.lean#L98)
- private theorem [exists_nat_support_card](RH/MixedConductorPrimeSupport.lean#L110)
- theorem [supportSpace_strict](RH/MixedConductorPrimeSupport.lean#L123)
- abbrev [supportLayer](RH/MixedConductorPrimeSupport.lean#L143)
- instance [supportLayer_hasOrthogonalProjection](RH/MixedConductorPrimeSupport.lean#L146)
- theorem [supportSpace_sup_layer](RH/MixedConductorPrimeSupport.lean#L149)
- theorem [supportLayer_ne_bot](RH/MixedConductorPrimeSupport.lean#L153)
- theorem [supportLayer_orthogonal](RH/MixedConductorPrimeSupport.lean#L159)
- theorem [supportLayer_projection](RH/MixedConductorPrimeSupport.lean#L163)
- theorem [supportSpace_dense](RH/MixedConductorPrimeSupport.lean#L168)
- theorem [sum_supportLayer_projection](RH/MixedConductorPrimeSupport.lean#L176)
- theorem [tendsto_sum_supportLayer_projection](RH/MixedConductorPrimeSupport.lean#L190)
- theorem [sum_supportLayer_energy](RH/MixedConductorPrimeSupport.lean#L198)
- theorem [tendsto_sum_supportLayer_energy](RH/MixedConductorPrimeSupport.lean#L218)
- private def [includeIn](RH/MixedConductorPrimeSupport.lean#L224)
- def [layerComplex](RH/MixedConductorPrimeSupport.lean#L228)
- def [layerSplitting](RH/MixedConductorPrimeSupport.lean#L241)
- local [instance : HasZeroObject (TopModuleCat.{0} ℝ)](RH/MixedConductorPrimeSupport.lean#L259)
- theorem [layer_shortExact](RH/MixedConductorPrimeSupport.lean#L262)
- def [layerIsCokernel](RH/MixedConductorPrimeSupport.lean#L265)
- local [instance : HasBinaryBiproducts (TopModuleCat.{0} ℝ)](RH/MixedConductorPrimeSupport.lean#L269)
- def [supportSpaceBiprodIso](RH/MixedConductorPrimeSupport.lean#L272)

### MixedConductorSplitExact

[Lean source](RH/MixedConductorSplitExact.lean)


Namespace `RiemannResearch.RH.Pareto.PrimePowerSchur`

- def [legalMixedInclusion](RH/MixedConductorSplitExact.lean#L23)
- theorem [legalPacketMean_legalMixedInclusion](RH/MixedConductorSplitExact.lean#L26)
- theorem [legalPacketMean_screenedMeanSection](RH/MixedConductorSplitExact.lean#L30)
- def [legalMixedRetraction](RH/MixedConductorSplitExact.lean#L35)
- theorem [legalMixedInclusion_legalMixedRetraction](RH/MixedConductorSplitExact.lean#L44)
- def [legalMeanComplex](RH/MixedConductorSplitExact.lean#L49)
- def [legalMeanSplitting](RH/MixedConductorSplitExact.lean#L57)
- instance [legalMixedInclusion_isSplitMono](RH/MixedConductorSplitExact.lean#L80)
- instance [legalPacketMean_isSplitEpi](RH/MixedConductorSplitExact.lean#L83)
- theorem [legalMean_unique_mixed_lift](RH/MixedConductorSplitExact.lean#L87)
- local [instance : HasZeroObject (TopModuleCat.{0} ℝ)](RH/MixedConductorSplitExact.lean#L102)
- local [instance : HasBinaryBiproducts (TopModuleCat.{0} ℝ)](RH/MixedConductorSplitExact.lean#L105)
- theorem [legalMean_shortExact](RH/MixedConductorSplitExact.lean#L109)
- def [legalMixedIsKernel](RH/MixedConductorSplitExact.lean#L113)
- def [legalMeanIsCokernel](RH/MixedConductorSplitExact.lean#L117)
- def [legalMixedBiprodIso](RH/MixedConductorSplitExact.lean#L121)
- def [legalMixedQuotientIso](RH/MixedConductorSplitExact.lean#L126)
- theorem [legalMixedQuotientIso_π](RH/MixedConductorSplitExact.lean#L130)

### MixedConductorSupportSnake

[Lean source](RH/MixedConductorSupportSnake.lean)


Namespace `RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis`

- abbrev [supportStageInclusion](RH/MixedConductorSupportSnake.lean#L20)
- abbrev [supportStageRetraction](RH/MixedConductorSupportSnake.lean#L24)
- abbrev [supportLayerQuotient](RH/MixedConductorSupportSnake.lean#L28)
- abbrev [supportLayerSection](RH/MixedConductorSupportSnake.lean#L32)
- private theorem [quotient_inclusion](RH/MixedConductorSupportSnake.lean#L35)
- private theorem [layerRow_exact](RH/MixedConductorSupportSnake.lean#L43)
- private theorem [quotient_section](RH/MixedConductorSupportSnake.lean#L56)
- private theorem [retraction_inclusion](RH/MixedConductorSupportSnake.lean#L60)
- private theorem [comparison_left_square](RH/MixedConductorSupportSnake.lean#L64)
- private theorem [comparison_right_square](RH/MixedConductorSupportSnake.lean#L73)
- private theorem [zero_right_exact](RH/MixedConductorSupportSnake.lean#L81)
- def [supportComparisonBoundary](RH/MixedConductorSupportSnake.lean#L89)
- theorem [supportComparisonBoundary_apply](RH/MixedConductorSupportSnake.lean#L102)
- theorem [supportComparisonBoundary_eq_zero_of_compatible](RH/MixedConductorSupportSnake.lean#L111)
- theorem [truncatedLayerBoundary_eq_zero](RH/MixedConductorSupportSnake.lean#L120)
- theorem [successiveLayerBoundary_eq_id](RH/MixedConductorSupportSnake.lean#L129)
- theorem [successiveLayerBoundary_ne_zero](RH/MixedConductorSupportSnake.lean#L135)

### PrimeSupportCokernel

[Lean source](RH/PrimeSupportCokernel.lean)


Namespace `RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis`

- abbrev [ambientSupport](RH/PrimeSupportCokernel.lean#L26)
- def [supportQuotientTransition](RH/PrimeSupportCokernel.lean#L35)
- def [supportQuotientFunctor](RH/PrimeSupportCokernel.lean#L40)
- def [supportQuotientCocone](RH/PrimeSupportCokernel.lean#L58)

### PrimeSupportParityDescent

[Lean source](RH/PrimeSupportParityDescent.lean)


Namespace `RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis`

- theorem [supportQuotient_hausdorff_desc](RH/PrimeSupportParityDescent.lean#L27)
- theorem [supportCocone_parity_eq_defect](RH/PrimeSupportParityDescent.lean#L57)
- theorem [norm_supportCocone_parity](RH/PrimeSupportParityDescent.lean#L73)
- theorem [parityQuotient_sq_add_captured](RH/PrimeSupportParityDescent.lean#L87)
- theorem [boundary_eq_zero_iff_frequent_support_contraction](RH/PrimeSupportParityDescent.lean#L97)
- theorem [riemannHypothesis_of_frequently_contracting_support_blocks](RH/PrimeSupportParityDescent.lean#L129)
- theorem [mixedWindow_le_ambientSupport](RH/PrimeSupportParityDescent.lean#L136)
- theorem [parityQuotient_le_window_deficit](RH/PrimeSupportParityDescent.lean#L148)
- theorem [twoPrime_parityQuotient_upper](RH/PrimeSupportParityDescent.lean#L176)
- theorem [twoPrime_parityQuotient_contracts](RH/PrimeSupportParityDescent.lean#L188)

### PrimeSupportParityQuotient

[Lean source](RH/PrimeSupportParityQuotient.lean)


Namespace `RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis`

- def [parityQuotientClass](RH/PrimeSupportParityQuotient.lean#L43)
- theorem [parityQuotientClass_norm_sq](RH/PrimeSupportParityQuotient.lean#L47)
- theorem [tendsto_parityQuotientClass_norm_sq](RH/PrimeSupportParityQuotient.lean#L97)
- theorem [boundary_eq_zero_iff_small_parity_quotients](RH/PrimeSupportParityQuotient.lean#L107)
- theorem [riemannHypothesis_of_finite_parity_certificates](RH/PrimeSupportParityQuotient.lean#L123)
- theorem [single_zero_le_parityQuotientClass](RH/PrimeSupportParityQuotient.lean#L155)

### CenteredMeanLongExact

Exactness at every term of the centered mean sequence, including its two endpoints. [Lean source](RH/CenteredMeanLongExact.lean)

Namespace `RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake`

- abbrev [CenterCokernel](RH/CenteredMeanLongExact.lean#L36)
- def [toCenterCokernel](RH/CenteredMeanLongExact.lean#L39)
- def [cokernelMean](RH/CenteredMeanLongExact.lean#L48)
- def [constantClass](RH/CenteredMeanLongExact.lean#L54)
- def [quotientBoundary](RH/CenteredMeanLongExact.lean#L58)
- theorem [quotientBoundary_apply](RH/CenteredMeanLongExact.lean#L61)
- theorem [quotientBoundary_mk](RH/CenteredMeanLongExact.lean#L66)
- theorem [constantClass_injective](RH/CenteredMeanLongExact.lean#L71)
- theorem [exact_constantClass_quotientBoundary](RH/CenteredMeanLongExact.lean#L74)
- theorem [exact_quotientBoundary_toCenterCokernel](RH/CenteredMeanLongExact.lean#L83)
- theorem [exact_toCenterCokernel_cokernelMean](RH/CenteredMeanLongExact.lean#L97)
- theorem [cokernelMean_surjective](RH/CenteredMeanLongExact.lean#L107)
- private abbrev [ZeroTerm](RH/CenteredMeanLongExact.lean#L113)
- def [centeredLongSequence](RH/CenteredMeanLongExact.lean#L116)
- private theorem [pairExact](RH/CenteredMeanLongExact.lean#L122)
- theorem [centeredLongSequence_exact](RH/CenteredMeanLongExact.lean#L129)
- theorem [quotientBoundary_unit_residual](RH/CenteredMeanLongExact.lean#L143)

### PrimeSupportAlgebraDescent

The stage ideals, short exact transitions, Hausdorff descent, and packet detection. [Lean source](RH/PrimeSupportAlgebraDescent.lean)

Namespace `RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis`

- private abbrev [legalSupport](RH/PrimeSupportAlgebraDescent.lean#L34)
- def [supportIdeal](RH/PrimeSupportAlgebraDescent.lean#L39)
- theorem [supportIdeal_mono](RH/PrimeSupportAlgebraDescent.lean#L50)
- theorem [supportIdeal_le_mixed](RH/PrimeSupportAlgebraDescent.lean#L54)
- theorem [supportIdeal_sq](RH/PrimeSupportAlgebraDescent.lean#L58)
- private def [idealTower](RH/PrimeSupportAlgebraDescent.lean#L66)
- private def [idealCocone](RH/PrimeSupportAlgebraDescent.lean#L80)
- private theorem [linear_factor_comp](RH/PrimeSupportAlgebraDescent.lean#L92)
- private theorem [factor_shortExact](RH/PrimeSupportAlgebraDescent.lean#L102)
- def [supportAlgebraTower](RH/PrimeSupportAlgebraDescent.lean#L112)
- def [supportAlgebraCocone](RH/PrimeSupportAlgebraDescent.lean#L115)
- theorem [supportTransition_shortExact](RH/PrimeSupportAlgebraDescent.lean#L119)
- theorem [supportTransition_kernel_mk_iff](RH/PrimeSupportAlgebraDescent.lean#L124)
- theorem [supportAlgebra_hausdorff_desc](RH/PrimeSupportAlgebraDescent.lean#L131)
- def [stageMeanBoundary](RH/PrimeSupportAlgebraDescent.lean#L163)
- theorem [stageMeanBoundary_natural](RH/PrimeSupportAlgebraDescent.lean#L166)
- theorem [stageMeanBoundary_mk](RH/PrimeSupportAlgebraDescent.lean#L172)
- theorem [stageMeanBoundary_unit](RH/PrimeSupportAlgebraDescent.lean#L176)
- def [boundaryToMixedQuotient](RH/PrimeSupportAlgebraDescent.lean#L182)
- theorem [boundaryToMixedQuotient_injective](RH/PrimeSupportAlgebraDescent.lean#L186)
- theorem [stageMeanBoundary_unit_eq_descended_parity](RH/PrimeSupportAlgebraDescent.lean#L196)
- def [coordinateContrast](RH/PrimeSupportAlgebraDescent.lean#L205)
- theorem [coordinateContrast_natCast](RH/PrimeSupportAlgebraDescent.lean#L208)
- theorem [ramanujanSum_eq_crtContrast](RH/PrimeSupportAlgebraDescent.lean#L218)
- theorem [squarefree_packet_prefix_crt](RH/PrimeSupportAlgebraDescent.lean#L226)
- theorem [packet_mem_supportIdeal_iff](RH/PrimeSupportAlgebraDescent.lean#L233)
- def [familyMixedIndex](RH/PrimeSupportAlgebraDescent.lean#L249)
- theorem [squarefree_packet_descent](RH/PrimeSupportAlgebraDescent.lean#L262)
- theorem [primePower_screened](RH/PrimeSupportAlgebraDescent.lean#L272)

### CenteredMeanRHCriteria

The two-prime product test, the equivalent Pareto conditions, and six analytic RH equivalences. [Lean source](RH/CenteredMeanRHCriteria.lean)

Namespace `RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake`

- def [ambientProduct](RH/CenteredMeanRHCriteria.lean#L43)
- private theorem [ambientMean_coe](RH/CenteredMeanRHCriteria.lean#L47)
- theorem [inclusion_product_defect](RH/CenteredMeanRHCriteria.lean#L54)
- def [legalRamanujan](RH/CenteredMeanRHCriteria.lean#L65)
- theorem [legalRamanujan_mean](RH/CenteredMeanRHCriteria.lean#L68)
- def [packetProductAgrees](RH/CenteredMeanRHCriteria.lean#L74)
- theorem [packetProductAgrees_iff](RH/CenteredMeanRHCriteria.lean#L80)
- theorem [two_three_product_iff_screened](RH/CenteredMeanRHCriteria.lean#L90)
- theorem [stageUnit_zero_iff_boundary](RH/CenteredMeanRHCriteria.lean#L97)
- theorem [categoricalMean_tfae](RH/CenteredMeanRHCriteria.lean#L104)
- theorem [riemannHypothesis_of_stageUnit_zero](RH/CenteredMeanRHCriteria.lean#L135)
- theorem [criterion_to_stageUnit_iff_naturalApproximation](RH/CenteredMeanRHCriteria.lean#L140)
- theorem [stageUnit_zero_iff_riemannHypothesis](RH/CenteredMeanRHCriteria.lean#L147)
- theorem [analyticRiemannHypothesis_tfae](RH/CenteredMeanRHCriteria.lean#L160)

## Applications and companion modules


### CompactMatchingQuotient

[Lean source](Analysis/CompactMatchingQuotient.lean)


Namespace `CompactConstraintEnergy`

- def [quotientHomeomorph](Analysis/CompactMatchingQuotient.lean#L27)
- theorem [quotientHomeomorph_mk](Analysis/CompactMatchingQuotient.lean#L48)
- abbrev [MatchingSpace](Analysis/CompactMatchingQuotient.lean#L59)
- def [commonKernel](Analysis/CompactMatchingQuotient.lean#L63)
- theorem [commonKernel_iff](Analysis/CompactMatchingQuotient.lean#L66)
- def [toMatching](Analysis/CompactMatchingQuotient.lean#L72)
- theorem [continuous_toMatching](Analysis/CompactMatchingQuotient.lean#L77)
- def [matchingQuotientHomeomorph](Analysis/CompactMatchingQuotient.lean#L85)
- theorem [matchingQuotientHomeomorph_mk](Analysis/CompactMatchingQuotient.lean#L101)

### FiniteCoordinateCompletion

[Lean source](Analysis/FiniteCoordinateCompletion.lean)


Namespace `FiniteCoordinate`

- def [Compatible](Analysis/FiniteCoordinateCompletion.lean#L21)
- abbrev [Completion](Analysis/FiniteCoordinateCompletion.lean#L24)
- def [toCompletion](Analysis/FiniteCoordinateCompletion.lean#L26)
- abbrev [Image](Analysis/FiniteCoordinateCompletion.lean#L30)
- def [Coherent](Analysis/FiniteCoordinateCompletion.lean#L34)
- abbrev [ImageLimit](Analysis/FiniteCoordinateCompletion.lean#L38)
- def [toImageLimit](Analysis/FiniteCoordinateCompletion.lean#L40)
- def [fromImageLimit](Analysis/FiniteCoordinateCompletion.lean#L46)
- def [completionEquivImageLimit](Analysis/FiniteCoordinateCompletion.lean#L57)
- def [completionHomeomorphImageLimit](Analysis/FiniteCoordinateCompletion.lean#L73)
- def [PairwiseCompatible](Analysis/FiniteCoordinateCompletion.lean#L93)
- def [HasFiniteCRT](Analysis/FiniteCoordinateCompletion.lean#L98)
- theorem [compatible_iff_pairwise](Analysis/FiniteCoordinateCompletion.lean#L103)
- def [completionHomeomorphMatching](Analysis/FiniteCoordinateCompletion.lean#L113)
- theorem [compatible_operation](Analysis/FiniteCoordinateCompletion.lean#L119)
- def [completionOperation](Analysis/FiniteCoordinateCompletion.lean#L134)
- theorem [toCompletion_operation](Analysis/FiniteCoordinateCompletion.lean#L141)
- theorem [continuous_completionOperation](Analysis/FiniteCoordinateCompletion.lean#L149)
- theorem [compatible_iff_mem_closure](Analysis/FiniteCoordinateCompletion.lean#L162)
- theorem [isClosed_compatible](Analysis/FiniteCoordinateCompletion.lean#L188)
- instance [completionCompactSpace](Analysis/FiniteCoordinateCompletion.lean#L196)
- theorem [toCompletion_denseRange](Analysis/FiniteCoordinateCompletion.lean#L201)

### CRTReconstructionObstructions

[Lean source](LinearAlgebra/CRTReconstructionObstructions.lean)


Namespace `CRTReconstruction`

- def [leftPartition](LinearAlgebra/CRTReconstructionObstructions.lean#L20)
- def [rightPartition](LinearAlgebra/CRTReconstructionObstructions.lean#L21)
- theorem [join_compatible_not_pair_solvable](LinearAlgebra/CRTReconstructionObstructions.lean#L23)
- theorem [three_linear_constraints_obstruction](LinearAlgebra/CRTReconstructionObstructions.lean#L41)
- def [firstKernel](LinearAlgebra/CRTReconstructionObstructions.lean#L55)
- def [secondKernel](LinearAlgebra/CRTReconstructionObstructions.lean#L56)
- def [sumKernel](LinearAlgebra/CRTReconstructionObstructions.lean#L57)
- theorem [kernel_meet_eq_bot](LinearAlgebra/CRTReconstructionObstructions.lean#L60)
- theorem [kernel_binary_sums_top](LinearAlgebra/CRTReconstructionObstructions.lean#L66)
- theorem [kernel_distributivity_failure](LinearAlgebra/CRTReconstructionObstructions.lean#L85)
- noncomputable def [nearSingularEquiv](LinearAlgebra/CRTReconstructionObstructions.lean#L94)
- theorem [nearSingular_target_inverse](LinearAlgebra/CRTReconstructionObstructions.lean#L121)
- def [euclideanEnergy](LinearAlgebra/CRTReconstructionObstructions.lean#L125)
- theorem [nearSingular_target_energy](LinearAlgebra/CRTReconstructionObstructions.lean#L127)
- theorem [isomorphism_reconstruction_cost_unbounded](LinearAlgebra/CRTReconstructionObstructions.lean#L132)
- theorem [finite_unit_data_energy](LinearAlgebra/CRTReconstructionObstructions.lean#L142)
- theorem [infinite_unit_data_not_square_summable](LinearAlgebra/CRTReconstructionObstructions.lean#L157)
- theorem [finite_unit_data_minimal_energy](LinearAlgebra/CRTReconstructionObstructions.lean#L164)

### EquivalenceRelationCRT

[Lean source](Logic/EquivalenceRelationCRT.lean)


Namespace `RiemannResearch.Logic.FamilyCRT`

- def [PairwiseCompatible](Logic/EquivalenceRelationCRT.lean#L23)
- def [HereditaryCRT](Logic/EquivalenceRelationCRT.lean#L27)
- def [MeetComposition](Logic/EquivalenceRelationCRT.lean#L32)
- theorem [hereditaryCRT_of_meetComposition](Logic/EquivalenceRelationCRT.lean#L37)
- theorem [meetComposition_of_hereditaryCRT](Logic/EquivalenceRelationCRT.lean#L66)
- theorem [hereditaryCRT_iff_meetComposition](Logic/EquivalenceRelationCRT.lean#L105)
- theorem [meet_composition_iff](Logic/EquivalenceRelationCRT.lean#L109)
- theorem [solution_iff_intersection](Logic/EquivalenceRelationCRT.lean#L119)
- def [kernelFamily](Logic/EquivalenceRelationCRT.lean#L126)
- theorem [exists_joint_of_pairwise](Logic/EquivalenceRelationCRT.lean#L130)

### GeneralizedCRTDescentTargets

[Lean source](NumberTheory/GeneralizedCRTDescentTargets.lean)


Namespace `RiemannResearch.NumberTheory.GeneralizedCRT`

- def [IsTopologicalRingCRT](NumberTheory/GeneralizedCRTDescentTargets.lean#L21)
- def [IsEffectiveDescent](NumberTheory/GeneralizedCRTDescentTargets.lean#L31)

### ProfiniteCRT

[Lean source](NumberTheory/ProfiniteCRT.lean)


Namespace `RiemannResearch.NumberTheory.GeneralizedCRT`

- local [instance (p : Nat.Primes) : Fact p.val.Prime](NumberTheory/ProfiniteCRT.lean#L25)
- def [primePowerModulus](NumberTheory/ProfiniteCRT.lean#L28)
- private theorem [primePowers_cofinal](NumberTheory/ProfiniteCRT.lean#L31)
- def [padicProjection](NumberTheory/ProfiniteCRT.lean#L54)
- theorem [padicProjection_toZModPow](NumberTheory/ProfiniteCRT.lean#L62)
- private theorem [continuous_padicProjection](NumberTheory/ProfiniteCRT.lean#L66)
- private def [toPadicProduct](NumberTheory/ProfiniteCRT.lean#L85)
- private theorem [toPadicProduct_injective](NumberTheory/ProfiniteCRT.lean#L92)
- private theorem [toPadicProduct_surjective](NumberTheory/ProfiniteCRT.lean#L100)
- def [profinitePadicEquiv](NumberTheory/ProfiniteCRT.lean#L139)
- theorem [profinitePadicEquiv_apply](NumberTheory/ProfiniteCRT.lean#L142)
- theorem [isTopologicalRingCRT_profinitePadicEquiv](NumberTheory/ProfiniteCRT.lean#L146)
- theorem [tendsto_iff_padicProjection](NumberTheory/ProfiniteCRT.lean#L155)

### ProfiniteCRTUniversal

[Lean source](NumberTheory/ProfiniteCRTUniversal.lean)


Namespace `RiemannResearch.NumberTheory.GeneralizedCRT`

- def [compatibleLift](NumberTheory/ProfiniteCRTUniversal.lean#L18)
- theorem [reduce_compatibleLift](NumberTheory/ProfiniteCRTUniversal.lean#L28)
- theorem [compatibleLift_unique](NumberTheory/ProfiniteCRTUniversal.lean#L33)
- theorem [continuous_compatibleLift](NumberTheory/ProfiniteCRTUniversal.lean#L44)
- theorem [existsUnique_continuous_lift](NumberTheory/ProfiniteCRTUniversal.lean#L50)
- theorem [compatibleLift_comp](NumberTheory/ProfiniteCRTUniversal.lean#L63)
- local [instance (p : Nat.Primes) : Fact p.val.Prime](NumberTheory/ProfiniteCRTUniversal.lean#L71)
- noncomputable def [padicFamilyLift](NumberTheory/ProfiniteCRTUniversal.lean#L74)
- theorem [padicProjection_familyLift](NumberTheory/ProfiniteCRTUniversal.lean#L83)
- theorem [padicFamilyLift_unique](NumberTheory/ProfiniteCRTUniversal.lean#L89)
- theorem [continuous_padicFamilyLift](NumberTheory/ProfiniteCRTUniversal.lean#L98)

### ProfiniteGeneralizedCRT

[Lean source](NumberTheory/ProfiniteGeneralizedCRT.lean)


Namespace `RiemannResearch.NumberTheory.GeneralizedCRT`

- abbrev [PositiveModulus](NumberTheory/ProfiniteGeneralizedCRT.lean#L21)
- [instance (n : PositiveModulus) : NeZero n.val](NumberTheory/ProfiniteGeneralizedCRT.lean#L23)
- def [profiniteRing](NumberTheory/ProfiniteGeneralizedCRT.lean#L26)
- abbrev [ProfiniteInt](NumberTheory/ProfiniteGeneralizedCRT.lean#L45)
- def [reduce](NumberTheory/ProfiniteGeneralizedCRT.lean#L48)
- theorem [reduce_compatible](NumberTheory/ProfiniteGeneralizedCRT.lean#L55)
- theorem [continuous_reduce](NumberTheory/ProfiniteGeneralizedCRT.lean#L59)
- private theorem [isClosed_profiniteRing](NumberTheory/ProfiniteGeneralizedCRT.lean#L62)
- [instance : CompactSpace ProfiniteInt](NumberTheory/ProfiniteGeneralizedCRT.lean#L71)
- theorem [exists_profiniteInt_iff_pairwise](NumberTheory/ProfiniteGeneralizedCRT.lean#L76)
- theorem [profiniteInt_ext_of_lcm_cofinal](NumberTheory/ProfiniteGeneralizedCRT.lean#L108)
- theorem [existsUnique_profiniteInt_iff_pairwise_of_lcm_cofinal](NumberTheory/ProfiniteGeneralizedCRT.lean#L145)
- theorem [tendsto_iff_eventually_reduce_eq](NumberTheory/ProfiniteGeneralizedCRT.lean#L160)

### EveryMeanSectionDecomposition

[Lean source](RH/EveryMeanSectionDecomposition.lean)

Import interface.

### FiniteAtomCarryRefinement

[Lean source](RH/FiniteAtomCarryRefinement.lean)


Namespace `RiemannResearch.RH.FiniteAtomCarryCRT`

- private theorem [refineDivisor](RH/FiniteAtomCarryRefinement.lean#L25)
- def [primeEmbedding](RH/FiniteAtomCarryRefinement.lean#L29)
- def [mixedEmbedding](RH/FiniteAtomCarryRefinement.lean#L34)
- def [extendCoefficients](RH/FiniteAtomCarryRefinement.lean#L40)
- private theorem [extend_at](RH/FiniteAtomCarryRefinement.lean#L43)
- private theorem [extend_outside](RH/FiniteAtomCarryRefinement.lean#L48)
- private theorem [sum_extend_mul](RH/FiniteAtomCarryRefinement.lean#L54)
- theorem [rowCoefficients_refine](RH/FiniteAtomCarryRefinement.lean#L64)
- theorem [rowCoefficients_refine_outside](RH/FiniteAtomCarryRefinement.lean#L74)
- abbrev [StageCoefficients](RH/FiniteAtomCarryRefinement.lean#L84)
- def [refineCoefficients](RH/FiniteAtomCarryRefinement.lean#L86)
- private def [extendCoefficientsLinear](RH/FiniteAtomCarryRefinement.lean#L90)
- def [refineCoefficientsLinear](RH/FiniteAtomCarryRefinement.lean#L107)
- theorem [refineCoefficientsLinear_apply](RH/FiniteAtomCarryRefinement.lean#L112)
- theorem [stageSynthesis_refine](RH/FiniteAtomCarryRefinement.lean#L116)
- theorem [refineCoefficients_injective](RH/FiniteAtomCarryRefinement.lean#L130)
- theorem [crtEquiv_refine](RH/FiniteAtomCarryRefinement.lean#L142)
- def [pullResidue](RH/FiniteAtomCarryRefinement.lean#L167)
- private theorem [reduction_val](RH/FiniteAtomCarryRefinement.lean#L170)
- private theorem [fraction_reduction](RH/FiniteAtomCarryRefinement.lean#L176)
- private theorem [carry_reduction](RH/FiniteAtomCarryRefinement.lean#L181)
- def [residueAtomSynthesis](RH/FiniteAtomCarryRefinement.lean#L190)
- def [residueCarrySynthesis](RH/FiniteAtomCarryRefinement.lean#L193)
- theorem [residueAtomSynthesis_refine](RH/FiniteAtomCarryRefinement.lean#L196)
- theorem [residueCarrySynthesis_refine](RH/FiniteAtomCarryRefinement.lean#L206)
- theorem [packetSynthesis_refine](RH/FiniteAtomCarryRefinement.lean#L226)
- theorem [packetCoordinates_refine](RH/FiniteAtomCarryRefinement.lean#L243)
- theorem [canonicalCarry_packetCoordinates_refine](RH/FiniteAtomCarryRefinement.lean#L257)
- theorem [word_packetCoordinates_refine](RH/FiniteAtomCarryRefinement.lean#L271)

### MixedConductorAbsoluteBoundary

[Lean source](RH/MixedConductorAbsoluteBoundary.lean)


Namespace `RiemannResearch.RH.Pareto.PrimePowerSchur`

- private theorem [abs_constant](RH/MixedConductorAbsoluteBoundary.lean#L21)
- theorem [exists_two_stage_abs_outside](RH/MixedConductorAbsoluteBoundary.lean#L28)
- theorem [abs_screened_residual_pairing](RH/MixedConductorAbsoluteBoundary.lean#L50)
- theorem [negative_mass_le_abs_legal_distance](RH/MixedConductorAbsoluteBoundary.lean#L60)
- theorem [screened_eq_one_iff_abs_pairing_nonpos](RH/MixedConductorAbsoluteBoundary.lean#L69)
- theorem [abs_screened_mem_iff_boundary_zero](RH/MixedConductorAbsoluteBoundary.lean#L95)
- theorem [boundary_zero_iff_projected_one_nonnegative](RH/MixedConductorAbsoluteBoundary.lean#L108)
- theorem [riemannHypothesis_of_abs_screened_mem](RH/MixedConductorAbsoluteBoundary.lean#L125)

### MixedConductorContractiveSection

[Lean source](RH/MixedConductorContractiveSection.lean)


Namespace `RiemannResearch.RH.Pareto.PrimePowerSchur`

- instance [legalClosedSpace_completeSpace](RH/MixedConductorContractiveSection.lean#L20)
- private theorem [meanSection_norm_at_one](RH/MixedConductorContractiveSection.lean#L24)
- private theorem [meanSection_mean_one](RH/MixedConductorContractiveSection.lean#L34)
- theorem [legalMeanSection_norm_sq](RH/MixedConductorContractiveSection.lean#L40)
- theorem [screenedPrimeClosure_eq_constantLine_iff_contractive_section](RH/MixedConductorContractiveSection.lean#L57)
- theorem [legalPacketMean_adjoint_eq_scaled_section](RH/MixedConductorContractiveSection.lean#L87)
- theorem [legalPacketMean_comp_adjoint](RH/MixedConductorContractiveSection.lean#L101)
- theorem [screenedPrimeClosure_eq_constantLine_iff_coisometry](RH/MixedConductorContractiveSection.lean#L113)
- theorem [exists_legalMeanSection_norm_sq_dilation](RH/MixedConductorContractiveSection.lean#L133)

### MixedConductorGlobalParseval

[Lean source](RH/MixedConductorGlobalParseval.lean)


Namespace `RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis`

- theorem [legalMixedRetraction_eq_projection](RH/MixedConductorGlobalParseval.lean#L32)
- theorem [inner_mixed_screened](RH/MixedConductorGlobalParseval.lean#L42)
- private theorem [reassemble](RH/MixedConductorGlobalParseval.lean#L49)
- theorem [legal_norm_sq_split](RH/MixedConductorGlobalParseval.lean#L54)
- theorem [supportLayer_energy_remainder](RH/MixedConductorGlobalParseval.lean#L69)
- theorem [supportCoordinate_tail_bound](RH/MixedConductorGlobalParseval.lean#L76)
- theorem [exists_unit_missed_by_support_cutoff](RH/MixedConductorGlobalParseval.lean#L85)
- theorem [legal_support_energy_remainder](RH/MixedConductorGlobalParseval.lean#L94)
- theorem [tendsto_legal_support_reconstruction](RH/MixedConductorGlobalParseval.lean#L100)
- theorem [tendsto_legal_support_energy](RH/MixedConductorGlobalParseval.lean#L110)
- theorem [hasSum_supportLayer_energy](RH/MixedConductorGlobalParseval.lean#L118)
- theorem [support_energy_eq_conductor_basis](RH/MixedConductorGlobalParseval.lean#L124)
- theorem [legal_support_parseval](RH/MixedConductorGlobalParseval.lean#L130)
- theorem [supportLayer_isHilbertSum](RH/MixedConductorGlobalParseval.lean#L136)
- def [supportLayerEquiv](RH/MixedConductorGlobalParseval.lean#L153)
- theorem [supportLayerEquiv_apply](RH/MixedConductorGlobalParseval.lean#L157)
- abbrev [LegalSupportSum](RH/MixedConductorGlobalParseval.lean#L170)
- def [screenedScalarParametrization](RH/MixedConductorGlobalParseval.lean#L173)
- theorem [norm_screenedScalarParametrization](RH/MixedConductorGlobalParseval.lean#L190)
- private def [legalSupportAnalysis](RH/MixedConductorGlobalParseval.lean#L195)
- private theorem [retract_synthesis](RH/MixedConductorGlobalParseval.lean#L207)
- def [legalSupportEquiv](RH/MixedConductorGlobalParseval.lean#L218)
- theorem [legalSupportEquiv_scalar](RH/MixedConductorGlobalParseval.lean#L238)
- theorem [legalSupportEquiv_layer](RH/MixedConductorGlobalParseval.lean#L242)
- theorem [hasSum_supportLayer_synthesis](RH/MixedConductorGlobalParseval.lean#L247)
- theorem [legalSupportEquiv_symm_apply](RH/MixedConductorGlobalParseval.lean#L252)
- def [parityMixedProjection](RH/MixedConductorGlobalParseval.lean#L265)
- private theorem [parityMixedProjection_norm_sq](RH/MixedConductorGlobalParseval.lean#L268)
- theorem [parity_support_deficit](RH/MixedConductorGlobalParseval.lean#L276)
- theorem [parity_support_saturation_iff_norm_one](RH/MixedConductorGlobalParseval.lean#L287)
- theorem [norm_one_iff_forall_support_capture](RH/MixedConductorGlobalParseval.lean#L301)

### MixedConductorGramBoundary

[Lean source](RH/MixedConductorGramBoundary.lean)


Namespace `RiemannResearch.RH.Pareto.PrimePowerSchur.PacketGramBoundary`

- def [meanVector](RH/MixedConductorGramBoundary.lean#L29)
- def [meanPencil](RH/MixedConductorGramBoundary.lean#L32)
- theorem [det_meanPencil](RH/MixedConductorGramBoundary.lean#L36)
- theorem [centered_det_pos](RH/MixedConductorGramBoundary.lean#L50)
- def [centeredInverseGramMass](RH/MixedConductorGramBoundary.lean#L55)
- theorem [centeredInverseGramMass_eq](RH/MixedConductorGramBoundary.lean#L59)
- theorem [centered_det_ratio_tendsto](RH/MixedConductorGramBoundary.lean#L75)
- theorem [centeredInverseGramMass_monotone](RH/MixedConductorGramBoundary.lean#L84)
- private theorem [energy_nonzero_of_boundary_ne](RH/MixedConductorGramBoundary.lean#L91)
- theorem [centeredInverseGramMass_tendsto_of_ne](RH/MixedConductorGramBoundary.lean#L97)
- theorem [boundary_eq_zero_iff_centeredInverseGramMass_tendsto](RH/MixedConductorGramBoundary.lean#L109)
- theorem [riemannHypothesis_of_centeredInverseGramMass_tendsto](RH/MixedConductorGramBoundary.lean#L141)

### MixedConductorGramSites

[Lean source](RH/MixedConductorGramSites.lean)


Namespace `RiemannResearch.RH.Pareto.PrimePowerSchur.PacketGramBoundary`

- def [siteVector](RH/MixedConductorGramSites.lean#L25)
- def [siteGram](RH/MixedConductorGramSites.lean#L28)
- theorem [siteVector_one](RH/MixedConductorGramSites.lean#L31)
- theorem [det_siteGram](RH/MixedConductorGramSites.lean#L36)
- private theorem [projection_site_tendsto](RH/MixedConductorGramSites.lean#L48)
- theorem [boundary_eq_zero_iff_cofinal_site_det_sign](RH/MixedConductorGramSites.lean#L56)
- theorem [eventually_negative_site_det_of_boundary_ne](RH/MixedConductorGramSites.lean#L82)
- private theorem [first_site_det_budget](RH/MixedConductorGramSites.lean#L100)
- theorem [boundary_eq_zero_iff_first_site_det_budget](RH/MixedConductorGramSites.lean#L113)
- theorem [riemannHypothesis_of_cofinal_first_site_det](RH/MixedConductorGramSites.lean#L124)
- theorem [first_site_det_as_one_solve](RH/MixedConductorGramSites.lean#L136)
- theorem [riemannHypothesis_of_cofinal_first_site_solve](RH/MixedConductorGramSites.lean#L144)
- theorem [projection_one_first_site](RH/MixedConductorGramSites.lean#L160)
- theorem [projection_two_first_site_gap](RH/MixedConductorGramSites.lean#L175)
- theorem [projection_two_first_site_gt_one](RH/MixedConductorGramSites.lean#L208)
- theorem [first_two_det_certificates](RH/MixedConductorGramSites.lean#L227)
- theorem [site_positive_of_residual_lt_weight](RH/MixedConductorGramSites.lean#L241)
- theorem [half_two_three_trial_error](RH/MixedConductorGramSites.lean#L263)
- theorem [two_stage_residual_lt_sixth](RH/MixedConductorGramSites.lean#L279)
- theorem [first_two_sites_det_positive](RH/MixedConductorGramSites.lean#L304)
- theorem [projection_first_site_not_monotone](RH/MixedConductorGramSites.lean#L314)

### MixedConductorGramZeroFree

[Lean source](RH/MixedConductorGramZeroFree.lean)


Namespace `RiemannResearch.RH.Pareto.PrimePowerSchur.PacketGramBoundary`

- theorem [normalizedScreenedTwo_not_mem_finiteSpace](RH/MixedConductorGramZeroFree.lean#L25)
- theorem [packetUnitMeanLimit_eq_screened](RH/MixedConductorGramZeroFree.lean#L33)
- theorem [packetMass_lt_limitMass](RH/MixedConductorGramZeroFree.lean#L39)
- theorem [centeredInverseGramMass_eq_div](RH/MixedConductorGramZeroFree.lean#L58)
- theorem [centeredInverseGramMass_nonneg](RH/MixedConductorGramZeroFree.lean#L64)
- theorem [centeredInverseGramMass_mul_boundary_lt_one](RH/MixedConductorGramZeroFree.lean#L69)
- theorem [single_zero_strict_gram_bound](RH/MixedConductorGramZeroFree.lean#L77)
- private theorem [one_sub_norm_sq_re_im](RH/MixedConductorGramZeroFree.lean#L92)
- theorem [single_zero_outside_gram_disk](RH/MixedConductorGramZeroFree.lean#L98)
- theorem [zeta_ne_zero_on_gram_rectangle](RH/MixedConductorGramZeroFree.lean#L107)

### MixedConductorHilbertBasis

[Lean source](RH/MixedConductorHilbertBasis.lean)


Namespace `RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis`

- abbrev [Index](RH/MixedConductorHilbertBasis.lean#L39)
- def [packet](RH/MixedConductorHilbertBasis.lean#L42)
- theorem [packet_independent](RH/MixedConductorHilbertBasis.lean#L45)
- theorem [span_packets_closure](RH/MixedConductorHilbertBasis.lean#L62)
- private theorem [packet_span_orthogonal](RH/MixedConductorHilbertBasis.lean#L80)
- private instance [mixed_complete](RH/MixedConductorHilbertBasis.lean#L99)
- def [basis](RH/MixedConductorHilbertBasis.lean#L103)
- theorem [basis_apply](RH/MixedConductorHilbertBasis.lean#L107)
- theorem [packet_span_dense](RH/MixedConductorHilbertBasis.lean#L111)
- theorem [basis_span_through](RH/MixedConductorHilbertBasis.lean#L118)
- theorem [hasSum_modes](RH/MixedConductorHilbertBasis.lean#L124)
- def [block](RH/MixedConductorHilbertBasis.lean#L129)
- instance [block_hasOrthogonalProjection](RH/MixedConductorHilbertBasis.lean#L132)
- theorem [basis_mem_block](RH/MixedConductorHilbertBasis.lean#L136)
- private theorem [basis_mem_block_orthogonal](RH/MixedConductorHilbertBasis.lean#L139)
- theorem [mem_block_iff](RH/MixedConductorHilbertBasis.lean#L152)
- theorem [block_compl](RH/MixedConductorHilbertBasis.lean#L170)
- def [packetBlock](RH/MixedConductorHilbertBasis.lean#L184)
- instance [packetBlock_hasOrthogonalProjection](RH/MixedConductorHilbertBasis.lean#L187)
- theorem [gramSchmidt_eq_packet_residual](RH/MixedConductorHilbertBasis.lean#L194)
- def [screenedComplement](RH/MixedConductorHilbertBasis.lean#L227)
- theorem [screenedComplement_eq_orthogonal](RH/MixedConductorHilbertBasis.lean#L233)
- def [six](RH/MixedConductorHilbertBasis.lean#L268)
- theorem [basis_six](RH/MixedConductorHilbertBasis.lean#L271)
- theorem [parity_six_coefficient_sq](RH/MixedConductorHilbertBasis.lean#L291)
- theorem [projection_parseval](RH/MixedConductorHilbertBasis.lean#L302)
- theorem [parity_saturation_iff_one_mem](RH/MixedConductorHilbertBasis.lean#L321)

### MixedConductorMetricCokernel

[Lean source](RH/MixedConductorMetricCokernel.lean)


Namespace `RiemannResearch.RH.Pareto.PrimePowerSchur`

- theorem [norm_screenedMeanSection_apply](RH/MixedConductorMetricCokernel.lean#L32)
- theorem [screenedMeanSection_isometry_iff_one_mem](RH/MixedConductorMetricCokernel.lean#L38)
- theorem [screenedMeanSection_adjoint_comp_self](RH/MixedConductorMetricCokernel.lean#L52)
- theorem [screenedMeanSection_isometry_iff_adjoint](RH/MixedConductorMetricCokernel.lean#L69)
- theorem [norm_legalPacketMean_le_one](RH/MixedConductorMetricCokernel.lean#L82)
- theorem [norm_screenedMeanSection_comp_mean_le_one](RH/MixedConductorMetricCokernel.lean#L93)
- theorem [norm_comp_legalPacketMean_mul](RH/MixedConductorMetricCokernel.lean#L102)
- def [LegalMeanFactorizationBound](RH/MixedConductorMetricCokernel.lean#L132)
- private theorem [mixed_factorization](RH/MixedConductorMetricCokernel.lean#L137)
- private theorem [unique_scalar_factor](RH/MixedConductorMetricCokernel.lean#L147)
- theorem [norm_descend_legalPacketMean](RH/MixedConductorMetricCokernel.lean#L159)
- theorem [legalMeanFactorizationBound_iff](RH/MixedConductorMetricCokernel.lean#L168)
- theorem [legalMean_contractive_cokernel_iff_isometry](RH/MixedConductorMetricCokernel.lean#L199)
- theorem [algebraMap_isometry_iff_contractive_cokernel](RH/MixedConductorMetricCokernel.lean#L208)
- theorem [legalMean_contractive_cokernel_iff_naturalApproximation](RH/MixedConductorMetricCokernel.lean#L216)
- theorem [riemannHypothesis_of_legalMean_contractive_cokernel](RH/MixedConductorMetricCokernel.lean#L223)

### MixedConductorMetricLifting

[Lean source](RH/MixedConductorMetricLifting.lean)


Namespace `RiemannResearch.RH.Pareto.PrimePowerSchur`

- theorem [legalPacketMean_fiber_bound](RH/MixedConductorMetricLifting.lean#L27)
- theorem [legalPacketMean_unitBall_image](RH/MixedConductorMetricLifting.lean#L38)
- theorem [normalized_legalPacketMean_isometric_section](RH/MixedConductorMetricLifting.lean#L55)
- theorem [norm_screenedMeanSection](RH/MixedConductorMetricLifting.lean#L80)
- theorem [exists_legalMeanSection_norm_le_iff](RH/MixedConductorMetricLifting.lean#L89)
- theorem [exists_contractive_legalMeanSection_iff_unitBall_lifts_one](RH/MixedConductorMetricLifting.lean#L105)
- theorem [exists_contractive_legalMeanSection_iff_limitEnergy_zero](RH/MixedConductorMetricLifting.lean#L112)
- theorem [screenedPrimeClosure_eq_constantLine_iff_limitEnergy_zero](RH/MixedConductorMetricLifting.lean#L118)
- theorem [exists_legalMeanSection_period5040](RH/MixedConductorMetricLifting.lean#L125)
- theorem [riemannHypothesis_of_legalMeanSection](RH/MixedConductorMetricLifting.lean#L133)
- theorem [exists_contractive_legalMeanSection_iff_riemannHypothesis](RH/MixedConductorMetricLifting.lean#L144)
- theorem [limitEnergy_finite_zero_product_remainder](RH/MixedConductorMetricLifting.lean#L159)
- theorem [legalMeanSection_finite_zero_product](RH/MixedConductorMetricLifting.lean#L185)
- theorem [finite_zero_product_gt_period5040](RH/MixedConductorMetricLifting.lean#L208)
- private theorem [singleton_mellinCenteredProduct](RH/MixedConductorMetricLifting.lean#L218)
- private theorem [one_sub_complex_norm_sq](RH/MixedConductorMetricLifting.lean#L222)
- theorem [legalMeanSection_single_zero_excess](RH/MixedConductorMetricLifting.lean#L230)
- theorem [riemannHypothesis_iff_unit_finite_zero_products](RH/MixedConductorMetricLifting.lean#L244)

### MixedConductorPolarizedParseval

[Lean source](RH/MixedConductorPolarizedParseval.lean)


Namespace `RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis`

- theorem [legal_inner_split_screened](RH/MixedConductorPolarizedParseval.lean#L30)
- theorem [legal_covariance_gap_eq_boundary](RH/MixedConductorPolarizedParseval.lean#L40)
- theorem [boundary_eq_zero_iff_legal_covariance](RH/MixedConductorPolarizedParseval.lean#L48)
- theorem [tendsto_polarized_layer_sum](RH/MixedConductorPolarizedParseval.lean#L64)
- theorem [one_mem_iff_tendsto_polarized_layer_sum](RH/MixedConductorPolarizedParseval.lean#L77)
- theorem [packet_inner_screened_eq_boundary](RH/MixedConductorPolarizedParseval.lean#L92)
- theorem [parity_pairing_sub_log_eq_boundary](RH/MixedConductorPolarizedParseval.lean#L103)
- theorem [boundary_eq_zero_iff_parity_pairing_le_log](RH/MixedConductorPolarizedParseval.lean#L111)
- theorem [riemannHypothesis_of_parity_pairing_le_log](RH/MixedConductorPolarizedParseval.lean#L126)
- theorem [two_three_packet_inner](RH/MixedConductorPolarizedParseval.lean#L133)
- theorem [two_three_projected_covariance_gap](RH/MixedConductorPolarizedParseval.lean#L153)
- theorem [riemannHypothesis_of_two_three_projected_covariance](RH/MixedConductorPolarizedParseval.lean#L174)
- theorem [boundary_eq_zero_iff_tendsto_two_three_cross](RH/MixedConductorPolarizedParseval.lean#L185)
- theorem [three_packet_norm_sq](RH/MixedConductorPolarizedParseval.lean#L211)
- def [balancedTwoThree](RH/MixedConductorPolarizedParseval.lean#L224)
- theorem [balancedTwoThree_val](RH/MixedConductorPolarizedParseval.lean#L228)
- theorem [balancedTwoThree_norm_sq](RH/MixedConductorPolarizedParseval.lean#L249)
- theorem [tendsto_balancedTwoThree_layer_energy](RH/MixedConductorPolarizedParseval.lean#L260)
- theorem [balancedTwoThree_mixed_inner](RH/MixedConductorPolarizedParseval.lean#L266)
- theorem [parity_projection_split_along_two_three](RH/MixedConductorPolarizedParseval.lean#L287)

### MixedConductorProjectedGram

[Lean source](RH/MixedConductorProjectedGram.lean)


Namespace `RiemannResearch.RH.Pareto.PrimePowerSchur.PacketGramBoundary`

- def [mixedPacketGram](RH/MixedConductorProjectedGram.lean#L21)
- theorem [centeredPacketGram_apply](RH/MixedConductorProjectedGram.lean#L26)
- theorem [mixedPacketGram_eq_pencil](RH/MixedConductorProjectedGram.lean#L40)
- theorem [mixed_det_ratio](RH/MixedConductorProjectedGram.lean#L59)
- theorem [mixedPacketGram_det_pos](RH/MixedConductorProjectedGram.lean#L68)
- theorem [mixed_det_ratio_antitone](RH/MixedConductorProjectedGram.lean#L75)
- theorem [mixed_det_eq_centered_iff](RH/MixedConductorProjectedGram.lean#L83)
- theorem [mixed_det_ratio_tendsto_zero_of_boundary_ne](RH/MixedConductorProjectedGram.lean#L104)
- theorem [boundary_eq_zero_iff_cofinal_mixed_det_lower](RH/MixedConductorProjectedGram.lean#L112)
- theorem [centeredInverseGramMass_one](RH/MixedConductorProjectedGram.lean#L127)
- theorem [det_two_meanPencil](RH/MixedConductorProjectedGram.lean#L146)
- theorem [centeredInverseGramMass_two](RH/MixedConductorProjectedGram.lean#L171)

### MixedConductorRankOne

[Lean source](RH/MixedConductorRankOne.lean)


Namespace `RiemannResearch.RH.Pareto.PrimePowerSchur`

- theorem [residuePairing_eq_log](RH/MixedConductorRankOne.lean#L34)
- private theorem [packet_pairing_eq_of_residue_log](RH/MixedConductorRankOne.lean#L52)
- def [normalizedScreenedTwo](RH/MixedConductorRankOne.lean#L79)
- theorem [normalizedScreenedTwo_mean](RH/MixedConductorRankOne.lean#L82)
- theorem [normalizedScreenedTwo_mem_screenedPrimeClosure](RH/MixedConductorRankOne.lean#L88)
- theorem [fullScreening_packet_eq_mangoldt_smul](RH/MixedConductorRankOne.lean#L93)
- theorem [screenedPrimeClosure_eq_span_two](RH/MixedConductorRankOne.lean#L117)
- theorem [one_mem_closedSpace_iff_normalizedScreenedTwo](RH/MixedConductorRankOne.lean#L134)
- theorem [riemannHypothesis_of_normalizedScreenedTwo](RH/MixedConductorRankOne.lean#L150)
- theorem [fullScreening_eq_mean_smul](RH/MixedConductorRankOne.lean#L158)
- theorem [mem_mixedClosure_iff_mem_closedSpace_and_mean_zero](RH/MixedConductorRankOne.lean#L170)
- theorem [hilbertDilation_sub_self_mem_mixedClosure](RH/MixedConductorRankOne.lean#L184)
- theorem [fullScreening_hilbertDilation_eq](RH/MixedConductorRankOne.lean#L191)
- theorem [screenedPrimeClosure_eq_inf_orthogonal](RH/MixedConductorRankOne.lean#L197)
- theorem [mixed_sup_screenedPrimeClosure](RH/MixedConductorRankOne.lean#L213)
- theorem [mixed_inf_screenedPrimeClosure](RH/MixedConductorRankOne.lean#L218)
- theorem [screenedPrimeSpan_eq_span_two](RH/MixedConductorRankOne.lean#L223)
- def [legalPacketMean](RH/MixedConductorRankOne.lean#L235)
- def [screenedMeanSection](RH/MixedConductorRankOne.lean#L242)
- theorem [legalPacketMean_comp_screenedMeanSection](RH/MixedConductorRankOne.lean#L250)
- theorem [legalPacketMean_ker](RH/MixedConductorRankOne.lean#L257)
- theorem [mixed_orthogonal_eq_screened_sup_legal_orthogonal](RH/MixedConductorRankOne.lean#L264)
- theorem [mixed_orthogonal_eq_target_sup_legal_orthogonal](RH/MixedConductorRankOne.lean#L275)
- theorem [screened_sup_ambient_orthogonal_ne_mixed_orthogonal](RH/MixedConductorRankOne.lean#L304)
- theorem [mixed_orthogonal_span_one_iff_residual_spans](RH/MixedConductorRankOne.lean#L321)
- theorem [limitProjection_inner_one](RH/MixedConductorRankOne.lean#L370)
- theorem [limitProjection_eq_scaled_screenedTwo](RH/MixedConductorRankOne.lean#L377)
- [instance : screenedPrimeClosure.HasOrthogonalProjection](RH/MixedConductorRankOne.lean#L391)
- theorem [mixed_starProjection_screenedTwo](RH/MixedConductorRankOne.lean#L395)
- theorem [mixedOrthogonal_starProjection_one](RH/MixedConductorRankOne.lean#L402)
- theorem [screenedPrimeClosure_starProjection_one](RH/MixedConductorRankOne.lean#L406)
- theorem [mixedOrthogonal_starProjection_closedSpace](RH/MixedConductorRankOne.lean#L418)
- theorem [mixedOrthogonal_limitProjection_eq_one_iff](RH/MixedConductorRankOne.lean#L432)
- theorem [normalizedScreenedTwo_energy_product](RH/MixedConductorRankOne.lean#L439)
- theorem [one_sub_limitEnergy_pos](RH/MixedConductorRankOne.lean#L448)
- theorem [normalizedScreenedTwo_error_sq_eq_limitEnergy](RH/MixedConductorRankOne.lean#L456)
- theorem [normalizedScreenedTwo_eq_limitProjection_iff](RH/MixedConductorRankOne.lean#L463)
- def [fixedTwoTrial](RH/MixedConductorRankOne.lean#L479)
- theorem [fixedTwoTrial_tendsto](RH/MixedConductorRankOne.lean#L482)
- theorem [fixedTwoTrial_tendsto_one_iff](RH/MixedConductorRankOne.lean#L486)
- theorem [ramanujanPacketHilbert_two_norm_sq](RH/MixedConductorRankOne.lean#L491)
- private theorem [fixedTwo_error_eq_capture](RH/MixedConductorRankOne.lean#L504)
- theorem [fixedTwoTrial_error_eq_capture](RH/MixedConductorRankOne.lean#L535)
- theorem [full_capture_saturation_iff](RH/MixedConductorRankOne.lean#L542)
- theorem [fixed_capture_tendsto_saturation_iff](RH/MixedConductorRankOne.lean#L560)
- theorem [fixed_capture_tendsto_saturation_iff_naturalApproximation](RH/MixedConductorRankOne.lean#L571)
- theorem [riemannHypothesis_of_fixed_capture_saturation](RH/MixedConductorRankOne.lean#L577)

Namespace `RiemannResearch.RH.Pareto.PsiNormalizedRamanujan`

- theorem [fullScreening_centeredInput](RH/MixedConductorRankOne.lean#L589)
- theorem [fullCovarianceMass_eq_fixed_error](RH/MixedConductorRankOne.lean#L604)
- theorem [fullCovarianceMass_normalized_tendsto_fixed_error](RH/MixedConductorRankOne.lean#L609)
- theorem [fullCovarianceMass_subquadratic_iff_one_mem](RH/MixedConductorRankOne.lean#L623)
- theorem [riemannHypothesis_of_fullCovarianceMass_subquadratic](RH/MixedConductorRankOne.lean#L636)
- theorem [covarianceMass_eq_fixed_error_add_diagonal_tail](RH/MixedConductorRankOne.lean#L643)

### MixedConductorSquareZero

[Lean source](RH/MixedConductorSquareZero.lean)


Namespace `RiemannResearch.RH.Pareto.PrimePowerSchur.LegalMeanAlgebra`

- def [mulWith](RH/MixedConductorSquareZero.lean#L31)
- theorem [mean_mulWith](RH/MixedConductorSquareZero.lean#L35)
- theorem [mulWith_assoc](RH/MixedConductorSquareZero.lean#L40)
- theorem [mulWith_comm](RH/MixedConductorSquareZero.lean#L45)
- theorem [mulWith_unit](RH/MixedConductorSquareZero.lean#L49)
- theorem [mulWith_add](RH/MixedConductorSquareZero.lean#L52)
- theorem [mulWith_smul](RH/MixedConductorSquareZero.lean#L57)
- theorem [mulWith_zero](RH/MixedConductorSquareZero.lean#L62)
- theorem [mulWith_unique](RH/MixedConductorSquareZero.lean#L66)
- theorem [continuous_mulWith](RH/MixedConductorSquareZero.lean#L79)
- scoped instance [screenedCommRing](RH/MixedConductorSquareZero.lean#L87)
- theorem [mul_def](RH/MixedConductorSquareZero.lean#L102)
- scoped instance [screenedAlgebra](RH/MixedConductorSquareZero.lean#L105)
- theorem [algebraMap_apply](RH/MixedConductorSquareZero.lean#L110)
- scoped instance [screenedTopologicalRing](RH/MixedConductorSquareZero.lean#L115)
- def [meanHom](RH/MixedConductorSquareZero.lean#L119)
- theorem [meanHom_apply](RH/MixedConductorSquareZero.lean#L123)
- def [mixedIdeal](RH/MixedConductorSquareZero.lean#L126)
- theorem [mem_mixedIdeal](RH/MixedConductorSquareZero.lean#L128)
- theorem [mul_eq_zero_of_mem](RH/MixedConductorSquareZero.lean#L134)
- theorem [mixedIdeal_sq](RH/MixedConductorSquareZero.lean#L140)
- instance [mixedIdeal_isMaximal](RH/MixedConductorSquareZero.lean#L144)
- noncomputable abbrev [quotientField](RH/MixedConductorSquareZero.lean#L149)
- def [quotientEquiv](RH/MixedConductorSquareZero.lean#L153)
- theorem [quotientEquiv_mk](RH/MixedConductorSquareZero.lean#L157)
- theorem [quotientEquiv_symm_apply](RH/MixedConductorSquareZero.lean#L160)
- theorem [quotient_mk_mulWith](RH/MixedConductorSquareZero.lean#L164)
- def [quotientHomeomorph](RH/MixedConductorSquareZero.lean#L171)
- theorem [quotientEquiv_agrees_cokernel](RH/MixedConductorSquareZero.lean#L180)
- private theorem [retraction_inclusion](RH/MixedConductorSquareZero.lean#L185)
- private theorem [retraction_section](RH/MixedConductorSquareZero.lean#L189)
- def [splitCoordinates](RH/MixedConductorSquareZero.lean#L195)
- theorem [splitCoordinates_continuous](RH/MixedConductorSquareZero.lean#L219)
- theorem [splitCoordinates_symm_continuous](RH/MixedConductorSquareZero.lean#L224)
- def [changeUnit](RH/MixedConductorSquareZero.lean#L230)
- theorem [changeUnit_apply](RH/MixedConductorSquareZero.lean#L233)
- theorem [mean_changeUnit](RH/MixedConductorSquareZero.lean#L236)
- theorem [changeUnit_unit](RH/MixedConductorSquareZero.lean#L241)
- theorem [changeUnit_fixed](RH/MixedConductorSquareZero.lean#L244)
- theorem [changeUnit_cancel](RH/MixedConductorSquareZero.lean#L249)
- def [changeUnitEquiv](RH/MixedConductorSquareZero.lean#L255)
- theorem [map_mulWith](RH/MixedConductorSquareZero.lean#L265)
- theorem [changeUnit_mul](RH/MixedConductorSquareZero.lean#L273)
- private theorem [coe_screenedUnit](RH/MixedConductorSquareZero.lean#L280)
- theorem [meanOne_pythagoras](RH/MixedConductorSquareZero.lean#L284)
- theorem [eq_screenedUnit_of_norm_le](RH/MixedConductorSquareZero.lean#L302)
- theorem [eq_screenedSection_of_norm_le](RH/MixedConductorSquareZero.lean#L311)
- theorem [screenedUnit_natural](RH/MixedConductorSquareZero.lean#L331)
- theorem [isometry_mul](RH/MixedConductorSquareZero.lean#L345)
- def [packetSix](RH/MixedConductorSquareZero.lean#L353)
- theorem [packetSix_square_test](RH/MixedConductorSquareZero.lean#L358)
- theorem [exists_shear_moving_unit](RH/MixedConductorSquareZero.lean#L370)
- theorem [unit_error_sq](RH/MixedConductorSquareZero.lean#L385)

### MixedParitySupportBounds

[Lean source](RH/MixedParitySupportBounds.lean)


Namespace `RiemannResearch.RH.Pareto.PrimePowerSchur.MixedMobiusTesting`

- theorem [parity_variance_eq_boundary_add_layers](RH/MixedParitySupportBounds.lean#L35)
- theorem [support_error_floor](RH/MixedParitySupportBounds.lean#L52)
- theorem [two_prime_error_floor](RH/MixedParitySupportBounds.lean#L89)
- private theorem [exists_squarefree_card](RH/MixedParitySupportBounds.lean#L106)
- theorem [fixed_support_positive_floor](RH/MixedParitySupportBounds.lean#L122)
- theorem [fresh_packet_combination](RH/MixedParitySupportBounds.lean#L149)
- theorem [fresh_dilation_cost_floor](RH/MixedParitySupportBounds.lean#L171)

### UniversalAtomCarryPresentation

[Lean source](RH/UniversalAtomCarryPresentation.lean)


Namespace `RiemannResearch.RH.UniversalAtomCarry`

- abbrev [Atom](RH/UniversalAtomCarryPresentation.lean#L22)
- def [atom](RH/UniversalAtomCarryPresentation.lean#L25)
- def [atomSpan](RH/UniversalAtomCarryPresentation.lean#L27)
- structure [Certificate](RH/UniversalAtomCarryPresentation.lean#L30)
  - [Certificate.arity](RH/UniversalAtomCarryPresentation.lean#L31)
  - [Certificate.input](RH/UniversalAtomCarryPresentation.lean#L32)
  - [Certificate.input_gt_one](RH/UniversalAtomCarryPresentation.lean#L33)
  - [Certificate.coeff](RH/UniversalAtomCarryPresentation.lean#L34)
  - [Certificate.output](RH/UniversalAtomCarryPresentation.lean#L35)
  - [Certificate.output_gt_one](RH/UniversalAtomCarryPresentation.lean#L36)
  - [Certificate.charge](RH/UniversalAtomCarryPresentation.lean#L37)
  - [Certificate.reciprocal](RH/UniversalAtomCarryPresentation.lean#L38)
- def [Certificate.carry](RH/UniversalAtomCarryPresentation.lean#L41)
- theorem [Certificate.carry_eq](RH/UniversalAtomCarryPresentation.lean#L44)
- abbrev [Label](RH/UniversalAtomCarryPresentation.lean#L53)
- abbrev [Word](RH/UniversalAtomCarryPresentation.lean#L54)
- def [atomSymbol](RH/UniversalAtomCarryPresentation.lean#L56)
- def [carrySymbol](RH/UniversalAtomCarryPresentation.lean#L58)
- def [Certificate.expression](RH/UniversalAtomCarryPresentation.lean#L61)
- def [atomSynthesis](RH/UniversalAtomCarryPresentation.lean#L65)
- def [includeAtoms](RH/UniversalAtomCarryPresentation.lean#L68)
- def [eliminate](RH/UniversalAtomCarryPresentation.lean#L71)
- def [synthesis](RH/UniversalAtomCarryPresentation.lean#L74)
- theorem [eliminate_atomSymbol](RH/UniversalAtomCarryPresentation.lean#L76)
- theorem [eliminate_carrySymbol](RH/UniversalAtomCarryPresentation.lean#L80)
- theorem [eliminate_includeAtoms](RH/UniversalAtomCarryPresentation.lean#L84)
- theorem [synthesis_atomSymbol](RH/UniversalAtomCarryPresentation.lean#L92)
- theorem [synthesis_carrySymbol](RH/UniversalAtomCarryPresentation.lean#L95)
- theorem [synthesis_eq_realized](RH/UniversalAtomCarryPresentation.lean#L103)
- theorem [atom_linearIndependent](RH/UniversalAtomCarryPresentation.lean#L115)
- def [relation](RH/UniversalAtomCarryPresentation.lean#L122)
- theorem [relation_eq](RH/UniversalAtomCarryPresentation.lean#L124)
- def [relations](RH/UniversalAtomCarryPresentation.lean#L132)
- private def [residual](RH/UniversalAtomCarryPresentation.lean#L134)
- private theorem [residual_mem](RH/UniversalAtomCarryPresentation.lean#L136)
- theorem [relations_eq_ker](RH/UniversalAtomCarryPresentation.lean#L155)
- theorem [range_synthesis](RH/UniversalAtomCarryPresentation.lean#L168)
- def [quotientEquivAtomSpan](RH/UniversalAtomCarryPresentation.lean#L178)
- theorem [quotientEquivAtomSpan_mk](RH/UniversalAtomCarryPresentation.lean#L182)

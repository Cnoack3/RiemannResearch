# Conditional iid / Cesàro: Lean continuation coverage

Date: 2026-09-17. Continuation of `ConditionalMeanFormalization20260917.md`.

This report maps the 28 new modules listed below and the modified `Analysis/MellinStepSeries.lean` to the mathematical completion and proof appendices. It replaces the earlier list of missing extensions with the more precise status below. It does not certify every sentence of the mathematical manuscripts as a Lean theorem.

**All 28 new modules have passed development checking**, together with the modified MellinStepSeries module, as recorded by the coordinating verifier below. The functional repairs and actual randomized arithmetic consumers passed their final development batch. Representative theorem axioms contain only the standard foundational dependencies listed below. The separate publication receipt records the saved-project validation and publication gate. Successful ephemeral checks alone do not certify that gate.

## Verification and revision record

| Item | Coordinator evidence and final publication status |
|---|---|
| Baseline revision | `7b03d5f` |
| Core development batch | `job_J31RyhMvuPkQHotYu8K9AJ3d1Mw5_yGl`, SHA-256 `c3884acb09fdef28499d3c107fcbf1c472a8d0ad367cd24f1bf9a053081dc26e`, successful. |
| Finite-matrix development batch | `job_K1iIEGgBPVw44aZ44p4MDl9dlJ00AKJh`, SHA-256 `7437e5151d9bd26589bbb0fdad589146a8e8a19f8de611522d9bf67ab3fbeba6`, successful. |
| Operator / Hilbert identification job | `job_h5-3WKRVOvTrVTSL2jtrysHPqv-UPbES`, SHA-256 `2d2e6872660b87e9ac249bda2de4697ff394dd0233b152bd392aa918b4eb9480`, exit 0 . Covers six Cesàro operator modules, dependency slice and `ConditionalIIDHilbertIdentification`. |
| Complete modified `MellinStepSeries.lean` | `job_yBZGV0QIV9pIx1c-uP0x143pwbp9a0hl`, SHA-256 `bd7c8adaeda92117c8c9bbfc606c6df20b6b5172297bee4bc94b30df81c0933f`, successful full-file check . |
| Bundled Mellin / randomized arithmetic consumer batch | `job__hvaRrDghL_TCmFaaC8nNzS7sF-9GiL0`, SHA-256 `a62020d9432f2307cb854703d83dc21e01e40438434773c7ddfe8bc32172299a`, successful (19.483 seconds). |
| Arithmetic axiom-audit batch | `job_2IsWVQUbYncN7Tt0bwGI57lZNr4eymKe`, SHA-256 `800e831322f940424cc01ec8e3819e682475ecc3effbccee0ace68f67ade2439`, successful. Audits the normalized tail inverse, residue Gram positivity, canonical Mobius energy bound, and actual RH subpolynomial criterion: only `propext`, `Classical.choice`, `Quot.sound`. |
| Representative `#print axioms` results | `conditionalComplexMellinFunctional_norm`, `conditionalMellinFunctional_cesaroOperator`, `cesaroOperator_range_not_closed`, and `legal_randomized_conditionalMean_decomposition`: only `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx` or custom axiom in these audited endpoints. |
| Saved-project validation | All 28 new modules are exported from `RiemannResearch.lean`; the modified existing module is included. The checkpoint must validate the affected saved import graph before publication. Consult the publication receipt for its result. |
| Final revision and publication | The revision is the published commit containing this report; its full hash and confirmed publication result are recorded in the accompanying publication receipt. |

No unchecked candidate is made verified by inclusion in the manifest. No statement below supplies a missing proof of `PositiveResidueDensityFromRH` or the actual uniform/subpolynomial arithmetic bound.

## Models and hypotheses

The pre-existing probability space is the actual countable latent mixture of infinite iid uniform paths. Its `coordinates_iCondIndepFun` concludes Mathlib conditional independence, and its `probability` has an actual probability-measure instance. New probability statements use this same measure.

`ThresholdHilbert` is a real `lp` space with exponent two. Its source decoding `hilbertSequence` realizes weights w_n=1/[n(n+1)]. The new target decoding `conditionalSequence` realizes q_t=2/[(t+1)(t+2)]. Although the two bundled Hilbert types use the same unweighted coordinate carrier, the decodings and intended norms differ. `cesaroOperator` includes the required sqrt(q) output scaling. The complex target is separately constructed as `lp (fun _ : ℕ => ℂ) 2`.

Physical indices are positive integers; Lean row and coordinate indices often use a zero-based predecessor. `diagonalSampleSize F j` consequently uses j+1. Residue generators in older sources are the raw integer residues `n mod d`; the normalized modules prove the conversion to g_d(n)=(n mod d)/d. The finite minima therefore have the manuscript's normalization, rather than relying on a silent coefficient rescaling.

## Manifest: exact new endpoints

Paths below are relative to `RiemannResearch/`. Namespace abbreviations are C=`Analysis.Cesaro`, P=`RH.Pareto`, CI=`Probability.ConditionalIID`, FCM=`LinearAlgebra.FiniteConstrainedMatrix`, and CFM=`RH.Pareto.ConditionalFiniteMinimum`.

| Module | Representative endpoint and exact scope |
|---|---|
| `RH/ConditionalMeanMinimumCriteria.lean` | P.`subpolynomial_conditionalHeadMinimum_iff_actual_heads` selects one genuine near-minimizer family for every exponent. P.`riemannHypothesis_of_subpolynomial_conditionalHeadMinimum` and `riemannHypothesis_of_cofinal_bounded_conditionalHeadMinimum` conclude actual Mathlib RH from explicit growth premises. Cofinal eventual boundedness equals global boundedness. |
| `RH/ConditionalMeanTailObstruction.lean` | P.`exact_head_tail_dual_obstruction` and `conditionalHeadMinimum_ge_head_add_dual` retain the signed tail and compulsory head mass. The divided inequality assumes positive dual tail; `dualTail_pos_eventually_of_zero` proves that condition eventually under a hypothetical zero. |
| `RH/CanonicalMobiusConditionalHead.lean` | P.`canonicalMobiusHead_mem_class`, `mobiusReciprocalSum_abs_le_one`, `canonicalMobiusHead_energy_le`, and `conditionalHeadMinimum_lt_two_mul`: actual legal Möbius heads and the unconditional O(N) bound, including E_N≤N(2N+1)/(N+2)<2N for N>0. |
| `RH/ConditionalMeanTailNonattainment.lean` | P.`legalSeedSpan_eq_zero_of_cesaro_tail` proves tail injectivity using periodicity. `conditionalMeanSquare_gt_head_mass` proves every positive exact legal head has energy strictly greater than Q_N=N/(N+2); `head_mass_not_mem_conditionalHeadEnergies` gives nonattainment. |
| `RH/FiniteResidueHeadSurjectivity.lean` | P.`exists_finite_residue_head`, `exists_finite_residue_cesaro_head`, and `finiteResidue_cesaro_head_surjective`: arbitrary finite ordinary or mean heads can be realized by the actual bounded dictionary. |
| `RH/ConditionalResidueGram.lean` | P.`conditionalResidueTailMatrix_posDef`, `conditionalResidueGramMatrix_posDef`, and the quadratic identities: the actual signed arithmetic matrices, with summable entries, are positive definite. |
| `RH/ConditionalResidueHeadMatrix.lean` | P.`conditionalResidueHeadMatrix_surjective` and `conditionalResidueGramMatrix_eq_weighted_head_add_tail`: actual full row rank for D≥N+1 and G=Aᵀdiag(q)A+T. |
| `RH/ConditionalFiniteMatrixMinimum.lean` | CFM.`fullValue_isLeast`, `tailValue_isLeast`, `fullValue_eq_inverseMatrix`, `fullValue_eq_head_add_tailValue`, and `fullValue_gt_head_mass`: attained finite-dictionary minima, inverse formulas, and strict finite tail cost. `conditionalHeadMinimum_le_fullValue` compares each finite minimum with the full legal infimum. |
| `Analysis/MellinCesaroHilbert.lean` | C.`hilbert_terminal_pairing_tendsto_zero`, `hilbert_second_pairing_summable`, and `cesaro_mellin_pairing_hilbert`: boundary decay, absolute second-series convergence, and exact pairing for every real H vector when Re(s)>1/2, with no bounded-sequence premise. |
| `Analysis/MellinNormalizedResidue.lean` | P.`normalizedResidueHilbert_sequence`, `residueFraction_first_hasSum_zeta`, `residueFraction_second_pairing_zeta`, and their `_one` counterparts: exact normalized first series on Re(s)>0; second series on Re(s)>1/2; removable value (log d)/d. `one_le_conditionalMellinDualSquare` gives D_s≥1. Conductor-valued statements expose `[NeZero d]`, derivable from the existing d>0 premise. |
| `Analysis/CesaroPosteriorKernel.lean` | C.`posteriorTail_hasSum`, `posteriorTail_bayes`, `adjointTail_summable`, `adjointSequence_recover`, and `rowTransition_detailed_balance`: normalized numerical posterior, all-J adjoint tails, inverse-tail identity, and reversibility. |
| `Analysis/CesaroWeightedContraction.lean` | C.`cesaro_weighted_energy_le`, `cesaroOperator`, `cesaroOperator_apply`, and `cesaroOperator_injective`: actual bundled real continuous linear contraction with the physical Cesàro coordinates. |
| `Analysis/CesaroDenseRange.lean` | C.`cesaroOperator_range_closure` and `cesaroOperator_range_not_closed`: dense, nonclosed range. An explicit alternating target is proved outside the range. |
| `Analysis/CesaroHilbertAdjoint.lean` | C.`cesaroOperator_adjoint_coordinate`, `cesaroOperator_adjoint_injective`, `cesaroOperator_norm`, and `cesaroOperator_adjoint_one`: actual adjoint formula, injectivity, norm(C)=1, and preservation of the decoded constants. |
| `Analysis/CesaroKernelOperator.lean` | C.`rowTransition_hasSum`, `rowTransition_stationary`, `cesaroMarkovOperator_positive`, `cesaroMarkovOperator_hasSum`, and `cesaroOperator_signed_kernel_pairing`: stochastic reversible C*C, its all-H coordinate series, and signed iterated kernel pairing. |
| `Analysis/CesaroKernelClosedForm.lean` | C.`rowKernel_closed_form`: K(m)=Σ_{k≥0}(m+k)⁻²−3/(2m)+1/[2(m+1)], for m>0, after proving the relevant series and endpoint limits. |
| `Probability/ConditionalIIDExchangeability.lean` | CI.`probability_map_permuteRows` and `permuteRows_measurePreserving`: full joint-measure invariance under every permutation of the infinite row index set, keeping the latent endpoint. |
| `Probability/ConditionalIIDStrongLaw.lean` | CI.`runningMaximum_eventually_eq_endpoint` and `observationAverage_strongLaw_simultaneous`: almost-sure eventual endpoint recovery and a single full-measure event on which the mean converges for every real arithmetic observable. The pathwise statement has no global moment premise. |
| `Probability/ConditionalIIDDivisibility.lean` | CI.`conditional_divisibility_event` and `conditional_joint_divisibility_event`: exact floor and same-row lcm conditional probabilities in the constructed measure. |
| `Probability/ConditionalIIDSampleRates.lean` | CI.`diagonal_average_error_le`, `diagonalSampleSize_tendsto`, and `diagonal_average_error_tendsto`: deterministic r_j=max(j+1,ceil((j+1)v_j)) gives error≤bias+1/(j+1). The L² hypotheses remain explicit. The reverse convergence implication permits every positive deterministic schedule. |
| `LinearAlgebra/FiniteConstrainedMatrixMinimum.lean` | FCM.`minimumCoefficients_constraint`, `minimumCoefficients_completion`, `inverseCompressed_isLeast`, and `minimumCoefficients_unique`: actual constrained minimizer, signed completion, attained minimum and uniqueness, under positive definiteness and surjective constraints. |
| `LinearAlgebra/FiniteConstrainedMatrixInverse.lean` | FCM.`minimumCoefficients_eq_inverse_matrix` and `inverseMatrix_isLeast`: literal matrix-inverse formulas, with invertibility discharged by the preceding hypotheses. |
| `RH/ConditionalResidueNormalization.lean` | CFM.`synthesis_toRaw`, `normalized_constrained_energy_set_eq`, and `normalized_fullValue_isLeast`: invertible coefficient change identifies the raw and normalized arithmetic feasible energy sets. |
| `RH/ConditionalNormalizedMatrixMinimum.lean` | CFM.`normalizedTailMatrix_posDef`, `fullValue_eq_normalized_inverseMatrix`, and `fullValue_eq_head_add_normalized_tail_inverse`: the manuscript's actual normalized inverse-Gram and inverse-tail formulas. |
| `Probability/ConditionalIIDHilbertIdentification.lean` | CI.`hilbertSequence_coordinate_memLp_two` proves every actual H vector has the required observation L² property. `hilbertSequence_average_error_convex_combination` and `hilbertSequence_average_square_norm_identity` give the exact full/smoothed weighted error and norm formulas. |
| `Analysis/ConditionalMellinFunctional.lean` | C.`conditionalComplexMellinFunctional` is an actual complex-linear continuous map on complex J; `_norm` gives norm exactly sqrt(D_s). `conditionalMellinFunctional` is its real-linear restriction, with `_norm_le`, `_cesaroOperator`, and `_one`. Complex image identities are stated for embedded real Cesàro vectors. |
| `Probability/RandomizedCorrectionPythagoras.lean` | `Probability.RandomizedCorrection.expected_quadratic_loss_decomposition`, `mean_coefficients_preserve_constraint`, and `smoothed_finite_coefficient_loss_decomposition`: exact expected-loss decomposition, mean feasibility, and continuous-operator version for genuinely square-integrable finite random coefficients. No coefficient independence is assumed. |
| `RH/RandomizedCesaroCorrection.lean` | P.`legal_randomized_full_energy_decomposition`, `legal_randomized_conditionalMean_decomposition`, and `legal_mean_conditional_energy_le_randomized`: the same identities instantiated with actual legal arithmetic vectors and the constructed Cesàro operator. |

One existing module is also modified: `Analysis/MellinStepSeries.lean` adds `stepMellin_integrable_of_bounded`, `hasSum_first_mellin_pairing_of_integrable`, and `hasSum_first_mellin_pairing_of_bounded`. The bounded case reaches the full positive half-plane through countable step-integral additivity. The original all-H `hasSum_first_mellin_pairing` name and signature are preserved. This change must be included in saved-project verification even though it is not one of the 28 new manifest entries.

## What the new RH criteria actually say

The full legal infimum is a genuine real infimum over a nonempty, bounded-below energy set. The earlier `ConditionalMeanHeadMinimum` module supplies finite interpolation, near-minimizers, monotonicity, Q_N≤E_N, and the exact-head error bound 8/(N+2) when witness energy is at most one. The continuation supplies the canonical Möbius O(N) upper bound, stronger tail obstructions, cofinal equivalences, and actual finite normalized matrix minima.

The conclusions `RiemannHypothesis` are Mathlib's proposition. The subpolynomial criterion still takes `SubpolynomialConditionalHeadMinimum Y` and cofinality of Y as hypotheses. The bounded criterion still takes a bound on the actual energies. There is no unconditional proof of either premise and no unconditional proof of RH.

The existing `PositiveResidueDensityFromRH` is exactly a proposition naming the missing classical implication:

```lean
def PositiveResidueDensityFromRH : Prop :=
  RiemannHypothesis → hilbertLegalClosure {n : ℕ | 0 < n} = ⊤
```

It is not an axiom or a proved provider. No module in this continuation discharges it. The weighted Nyman–Beurling theorem cited in `ClassicalDensityBoundary.md` is a recognized external mathematical input, still requiring a Lean formalization. Its mathematical truth must not be confused with a checked theorem in this project.

Separate from that classical formalization obligation, the research assertion remains the existence of a uniform, or cofinal subpolynomial, bound for the actual legal constrained energies / signed correction remainder. Positive definiteness, finite attainment, coefficient randomization, and E_N<2N do not prove that bound.

## Original handoff: remaining distinctions

The original handoff explicitly permits reporting the missing RH-to-NB converse and keeping the Mertens specialization separate. Those are preserved as boundaries above; they are not silently supplied by the sufficient criteria.

| Original statement | Exact coverage distinction |
|---|---|
| Theorem 2.3, finite permutations and latent recovery (recovery optional after the core in §10A) | Invariance is proved for every infinite permutation, which includes the required finite permutations. Almost-sure eventual running-maximum recovery is proved. The displayed finite-r conditional formula P(max<t\|T=t)=(1−1/t)^r is not yet a separate declaration. No quantitative recovery probability is claimed. |
| Theorem 4.2, posterior and row kernel (posterior/adjoint optional in §10C) | The numerical posterior has actual nonnegativity, mass-one and Bayes identities. The operator's actual adjoint and signed iterated kernel identity are proved. A standalone Mathlib `condDistrib` identification of T given K=n is not packaged. Joint product-index absolute summability is stronger than the displayed iterated-series endpoint and is not claimed here. |
| Lemma 5.1, total dual bound | Pointwise coefficient estimates, actual dual summability, the D_s functional bound and quantitative dual-tail bound are available. The literal total bound D_s≤3|s(s+1)|²ζ(2Re(s)) is not yet an assembled declaration. |
| §5, scalar fields | A genuine complex-linear Lambda on complex J and its exact norm are constructed. The source Cesàro operator and all-H Mellin bridge use real H, with the complex Lambda evaluated on embedded real images. The literal arbitrary-complex-source extension needs separate complexification of C and the first Mellin pairing. This limitation does not affect the stated real legal-witness RH criteria. |
| §8, optional Mertens consequences | Earlier finite head/window and floor/counting repair lower bounds are retained. The continuation adds no prime-reciprocal asymptotic provider and makes no new verification claim for the full sieve-growth specialization. |

The existing signed two-replica identities remain real-valued and retain off-diagonal terms. The actual-H observation theorem now discharges their moment premise for every real H vector. Complex sesquilinear replica identities are outside these endpoints.

## Later completion and appendix refinements

These are additional mathematical claims in the later completion/proof appendices. They should not be used to enlarge the list of original handoff requirements retroactively, but should remain visible when assessing whether the *entire later markdown* is machine formalized.

| Later refinement | Remaining assembly |
|---|---|
| Completion (10.4), constrained minimum in W=closure(C(V)) | Finite interpolation, the actual C operator and the earlier generic `FiniteConstraintClosure.closure_exact_constraints` are available. The concrete continuous head operator/right inverse, its application to W and the projection-minimum identification are not assembled. The generic theorem explicitly assumes its right inverse. |
| Completion (10.6), RH⇔bounded E_N⇔E_N=Q_N | The bounded/subpolynomial⇒RH directions are supplied. The reverse still requires the classical density provider and the concrete constrained-closure deduction above. |
| Completion (11.5), E_N=inf_D E_{N,D}=lim_D E_{N,D} | Each finite minimum is constructed, and `conditionalHeadMinimum_le_fullValue` gives one inequality. Cofinal finite-dictionary exhaustion, monotonicity in D and the full infimum/limit identification are not packaged. |
| Completion (11.6), explicit correction-basis Schur formula | Actual normalized inverse-Gram and inverse-tail minimum formulas are supplied. Choosing a basis of ker A and specializing the signed correction formula Q_N+c₀ᵀTc₀−hᵀ(NᵀTN)⁻¹h, including the zero-dimensional case, remain separate endpoints. The uniform remainder bound (11.7) remains an unproved research assertion. |
| Arithmetic appendix, witness-period-dependent strict energy gap | Strict positive tail energy and nonattainment are formalized. The additional explicit numerical lower gap depending on the witness's particular period is not assembled. No uniform gap over all legal periods is asserted. |
| Probability appendix, recovery rates and more general reindexings | The exact unconditional recovery-error mixture, cutoff/exponential estimate, invariance under injective non-surjective reindexing, and completed-sigma-algebra recovery statement are stronger than the present declarations. |
| Completion (5.3), (5.6), full complex first functional | The extra first-dual zeta bound, exact cubic prefix constant and bundled complex source functional are not assembled. The all-real-H proof instead uses the sufficient bound |S_N|≤‖f‖(N+1)sqrt(N), proving the required boundary decay. |
| Completion (10.7), combined RH-conditional sample-rate witness | The established 8/(N+2) bound for energy≤1 and generic deterministic sample rate are available. The sharper square-root tail bound and a single RH-conditional witness theorem with rate 1/N+8/(N+2) need separate assembly and, for witness existence, the reverse provider. |

The norm equality sqrt(D_s) is claimed for the complex-linear functional. Its real restriction has only the stated upper bound; no unsupported real operator-norm equality is asserted.

## Mathematical source trail

The separate proof notes used here are `CofinalMinimumProof.md`, `MobiusHeadProof.md`, `AllHilbertMellinProof.md`, `BoundedPositiveMellinProof.md`, `NormalizedResidueMellinProof.md`, `CesaroOperatorProof.md`, `ConditionalIIDExtensionsProof.md`, `ArithmeticVariationalProof.md`, `ConditionalMellinFunctionalProof.md`, `RandomCoefficientPythagorasProof.md`, and `ClassicalDensityBoundary.md`. All these source notes are collected in `Conditional_IID_Cesaro_Proof_Companion_2026-09-17.md`. The companion preserves earlier wording and planning remarks; where implementation changed, the active source and the exact scopes in this report control. In particular, the normalized Mellin vector is now constructed directly from `(1/d) • digitHilbert d 1`, with its physical normalized sequence proved.

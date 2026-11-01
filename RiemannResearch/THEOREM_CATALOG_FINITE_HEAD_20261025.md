# Finite-head convergence: theorem catalog supplement

See also [CRT Gram minimizers, 28 October 2026](THEOREM_CATALOG_CRT_GRAM_20261028.md)
for exact-head norm optimization, complete-Q objective comparison, and the open uniform bound.

25 October 2026. Source: the user's finite-head projection convergence request.

## Established statements

The convergence results in this section are unconditional. The hypothesis in the general
Hilbert results is supplied by the existing strong projection convergence
theorems in the two application results. No RH or constant-target membership
hypothesis occurs.

- `Analysis/FiniteCoordinateConvergence.lean`:
  `Analysis.finite_abs_sub_eventually` and
  `Analysis.finite_max_abs_sub_tendsto` upgrade pointwise real convergence
  to uniform convergence over a fixed finite set.
- `RH/FiniteHeadHilbertConvergence.lean`:
  `ZetaTwoHilbert.qSequence_head_max_tendsto`,
  `ZetaTwoHilbert.qSequence_uniform_on_head`,
  `Pareto.hilbertSequence_tendsto_of_tendsto`,
  `Pareto.hilbertSequence_head_max_tendsto`, and
  `Pareto.hilbertSequence_uniform_on_head` apply this to the actual physical
  Q and Pareto coordinates.
- `RH/FiniteHeadProjectionConvergence.lean`, namespace
  `RiemannResearch.RH.FiniteHeadProjectionConvergence`:
  `q_optimizer_head_max_tendsto`, `q_optimizer_uniform_on_head`,
  `pareto_projection_head_max_tendsto`, and
  `pareto_projection_uniform_on_head` specialize to the standard projections.

The maximum statements use `Finset.Icc 1 H` and require `1 ≤ H`.
The epsilon statements permit every natural H, including the empty head H = 0.
The Q stages are squarefree; the standard Pareto stages use all conductors.
The limiting projections depend on the measure. These results assert neither
uniform convergence over all positive integers nor convergence to the constant 1.

## Prime-increment continuation, 26 October 2026

### Established statements

- `Analysis/PrimeIncrementEnvelope.lean`: the three declarations
  `prime_mul_log_envelope_step`, `sub_one_abs_le_of_prime_increments`,
  and `abs_le_polylog_of_prime_increments` telescope a local prime
  increment bound into a physical polylogarithmic envelope.
- `Analysis/ProjectionAveragingDefect.lean`: `commutator_witness`,
  `commutator_witness_energy`, `defect_pairing`, `defect_energy_bound`,
  `defect_zero_iff_target_mem`, `commutator_zero_iff_target_mem`, and
  `parity_defect_energy_bound` retain the exact signed projection identities.
  The parity specialization explicitly assumes its averaging identities.
- `RH/QSquarefreePrimeIncrement.lean`:
  `residual_zero_of_correction_prime_increments`,
  `residual_zero_iff_correction_prime_increments`,
  `residual_zero_of_frequently_moving_prime_increments`, and
  `residual_zero_iff_frequently_moving_prime_increments` give exact
  prime-edge tests for actual residual vanishing. Each edge may use its
  own cofinal set of stages.
- In the same namespace, `exists_large_prime_increment_of_residual_ne_zero`
  and `eventually_large_moving_prime_increment_of_residual_ne_zero`
  prove the alternative: a nonzero residual forces every proposed
  logarithmic allowance to fail at one fixed prime edge, eventually at
  all sufficiently late moving stages.

### Conditional research reduction

`riemannHypothesis_of_frequently_moving_prime_increments` concludes
Mathlib's RiemannHypothesis from the frequent-edge bound.

- **Open:** a provider for common L>=0 and integer m>=0 on the actual
  canonical moving corrections. With L>0 fixed, the criterion is
  equivalent to residual vanishing; that does not establish its premise.
- **Open:** formal realization of the actual prime-two averaging operator
  if the separate abstract averaging specialization is used.

Three new modules passed targeted server verification; inspected principal
declarations use only propext, Classical.choice, and Quot.sound.
See `RH/PrimeIncrementResearch20261026.md` for statements and verification.
`RH/LegalSubspaceProjectionObstruction.md` and
`RH/SingleConductorProjectionBound.md` were separate **paper proofs** at that checkpoint;
the formalization status was advanced in the continuation below.
The first rules out uniform stability over arbitrary legal subspaces
containing g_2, while the second controls a single added conductor for each
fixed prior legal space. Neither supplies a stage-uniform canonical bound.

## Formal projection continuation, 27 October 2026

### Established statements

- `Analysis/PrimeIncrementEnvelope.lean` adds sparse prime-parent telescoping:
  one chosen descending prime edge per integer suffices.
- `Analysis/OrthogonalPairCorrection.lean`, `SingleDirectionProjection.lean`,
  and `SingleDirectionResponseDifference.lean` prove exact signed projection,
  residual, coefficient, and response-difference identities before estimates.
- `Analysis/ConductorLogEnvelope.lean` supplies physical-log scalar bounds and
  shifted fixed-log-power domination by square roots.
- `RH/QBoundedSubspaceEvaluation.lean`, `QBoundedResidueProjection.lean`,
  `QConductorEstimates.lean`, and `QConductorDecay.lean` provide complete-Q
  evaluation/mean/norm estimates and actual normalized-conductor decay.
- `RH/QSingleConductorPrerequisites.lean`, `QSingleConductorProjection.lean`,
  and `QSingleConductorUniform.lean`: `stage_uniform_response_physical_bound`
  and `stage_uniform_response_weighted_energy_bound` hold uniformly in the
  added conductor and all inputs, with constants depending on the fixed stage.
- `RH/QSingleConductorOperatorDecay.lean`:
  `stage_response_extension_operator_norm_tendsto_zero` proves convergence
  to the response operator of the fixed base stage, not necessarily to zero.
- `RH/QReciprocalQuarterContraction.lean` proves the exact reciprocal
  quarter-contraction and its compressed orthogonal-residual bound.
- `RH/QLegalMixedConductor.lean`, `QLegalMixedConductorMoments.lean`,
  `QLegalMixedConductorAsymptotics.lean`, `QLegalMixedConductorReciprocal.lean`,
  and `QLegalMixedConductorPhysical.lean` provide the actual two-dimensional
  legal family, exact coefficient, unconditional eventual positivity,
  bounded physical remainder, and sharp ordinary norms.
- `RH/ResidueMidpointIncrement.lean` and `QLegalMixedConductorIncrement.lean`:
  `exists_prime_actualCorrection_exceeds_polylog` rules out every fixed
  polylogarithmic prime-two allowance over this noncanonical family.
- `RH/QLegalMixedConductorWeightedEnergy.lean`:
  `correctionWeightedEnergy_tendsto_atTop` proves complete summable weighted
  energy divergence; prime witnesses can be arbitrarily large.
- `RH/QLegalMixedConductorTransferObstruction.lean`:
  `exists_prime_weighted_transfer_failure` and
  `no_uniform_actual_weighted_transfer` discharge all actual-family providers.
  Raw weighted energy is at most 1/1024 while correction energy diverges.

### Conditional research reduction and open obligations

`RH/QSquarefreePrimeIncrement.lean` adds
`residual_zero_iff_frequently_moving_prime_parent_increments` for fixed m and
L>0, and `riemannHypothesis_of_frequently_moving_prime_parent_increments`.
The latter concludes the literal Mathlib RH proposition.

- **Open:** a common-L,m sparse prime-parent increment provider for the
  actual canonical moving corrections. The fixed-space theorem allows
  stage-dependent constants and does not discharge this obligation.
- **Open:** the actual countable prime-resampling kernel, reversibility,
  exit-rate/exhaustion providers, and spectral-gap-one Poincaré theorem.
  The deterministic weighted-energy counterexample does not by itself
  formalize the paper's Dirichlet-form conclusions. The limiting criterion
  additionally requires the extended L¹ Poincaré statement.

See `RH/FormalResearch20261027.md` for exact quantifiers, theorem roles,
proof improvements, and the remaining mathematical boundary. The written
real-exponent weighted-energy extensions are not independently certified.

## CRT coprime approximation, 28 October 2026

### Established statements

Module `RH/QCRTCoprimeApproximation.lean`, namespace
`RiemannResearch.RH.QCRTCoprimeApproximation`:

- `coprimeApprox_mem_divisorStage`, `coprimeApprox_legal`,
  `coprimeApprox_sequence`, `coprimeApprox_mod`, and
  `coprimeApprox_count_mod` construct the legal reduced-residue count.
- `sieveCount_one_head`, `coprimeApprox_exact_head`,
  `approximant_legal`, `approximant_exact_head`, and
  `approximant_pointwise` give an explicit squarefree primorial family,
  exactly one on expanding initial intervals, hence pointwise convergent.
- `rawApproximant_legal`, `sieveSlope_primorial_one`,
  `rawApproximant_head`, `rawApproximant_pointwise`, and
  `rawApproximant_eq_moebius` identify the raw signed Mobius construction.
- `rawApproximant_norm_lower`, `rawApproximant_norm_sq_tendsto_atTop`,
  and `rawApproximant_norm_tendsto_atTop` certify its divergent complete
  Q energy, despite its pointwise limit one.
- `coprimeApprox_norm_sq` retains the exact signed correction energy.

### Open goal and nonformalized calculation

No new conditional RH theorem is introduced. The open goal remains a
different legal approximating family with uniformly bounded full energy.
The corrected reduced-residue count also has divergent energy by the
separate mathematical argument in `RH/CRTLegalApproximants20261028.md`;
that reflection/plateau proof is not Lean-certified in this change.
Raw-family divergence and the corrected-family norm identity are checked.


## Minimum-energy exact-head continuation, 28 October 2026

### Established statements

- `RH/QResidueHeadSpace.lean` adds the projection adjustment
  `exactHeadAdjustment`, preservation of every prescribed head,
  the full Pythagorean remainder, the exact removed energy,
  attained minimum, uniqueness, and seed independence. These hold for
  all natural head lengths, including zero.
- `Analysis/FiniteHilbertGramMatrix.lean` identifies the actual inverse
  matrix coefficients and gives the exact residual Schur value.
- `LinearAlgebra/FiniteAffineGramMinimum.lean` proves the literal
  kernel-basis inverse formula, full signed completion, attained minimum,
  and uniqueness for arbitrary feasible constraints. The head rows may
  be dependent; empty correction index types are permitted.
- `LinearAlgebra/FinitePenroseMinimum.lean` proves the displayed
  Moore–Penrose formula from two defining Penrose identities, with full
  remainder and uniqueness. A canonical pseudoinverse is not constructed.
- `RH/QCRTMinimumEnergy.lean` constructs the actual minimum-energy
  primorial CRT family and proves squarefree legality, expanding exact
  heads, pointwise convergence to one, unique stagewise minimality,
  and the full-Q inverse-Gram value. Its arithmetic feasibility and
  compensated-basis hypotheses are discharged.

The combined check `job_6WDnuf1bbVMSqqSk5zDR9f07H6zZkwoB` passed.
Inspected principal declarations use only propext, Classical.choice,
and Quot.sound. See `RH/MinimumEnergyExactHead20261028.md`.

### Open analytic estimate

A common bound on these complete minimum energies, even along a
cofinal subsequence, remains open. No uniform bound or RH conclusion
is supplied by the finite-dimensional minimization.


## Squarefree prefix response analysis, 30 October 2026

### Paper results; no new Lean declarations

- `RH/SquarefreePrefixResponseResearch20261030.md` derives the exact
  multiplicative-range Abel formula, the full squarefree inverse-Gram and
  divisor-prefix expansions, and the signed update when a conductor enters.
- It proves a weighted prefix-energy bound for the actual residual, retaining
  the projection loss square, and a logarithmic bound for all sites beyond
  `floor (n / (6 + log n))` in the centered correction.
- `RH/SquarefreePrefixResponseDiagnostics20261030.md` gives complete-period
  float64 calculations through stage 240 and standalone reproduction code.
  All range contributions at the largest sampled response at stage 240 have
  the same sign; no universal cross-range sign cancellation is established.

### Open arithmetic provider

A uniform polylogarithmic bound for the remaining signed short-head response,
its weighted prefix energy, or the displayed partial normal-equation errors
is not proved. The existing conditional polylogarithmic RH implication is
unchanged. This concerns ordinary canonical projections, not the distinct
constrained primorial minimum-energy family. The new analysis is on paper;
no Lean verification or rigorous numerical enclosure is claimed.

## Squarefree short-head formalization and refinements, 31 October 2026

### Established finite identities and inequalities

- `Analysis/FiniteDivisorCoercivity.lean` and `RH/MobiusHeadCoercivity.lean`
  prove finite signed Mobius recovery and the coefficient energy bound with
  factor `(2 - 1/H)^2 * L_H^2`, strictly below the earlier `4 * L_H^2`.
  The slope square includes all high-conductor coefficients.
- `Analysis/FiniteGramCoercivity.lean`, `RH/QHeadGramCoercivity.lean`,
  `RH/QDivisorHeadCoercivity.lean`, and `RH/QSquarefreeSchurCoercivity.lean`
  give an unconditional inverse bound for the complete-Q, full-head-null
  Schur family. A legal anchor exists when `1 <= H` and `2*H <= N+1`.
- `Analysis/RankOneCoefficientCoercivity.lean` and `RH/QFullGramRankOne.lean`
  retain the leading-slope square to subtract `(sum b)^2/(card+1)` from
  the full normalized inverse-Gram upper bound, with exact deficit identities.
- `Analysis/CenteredProjectionResponse.lean` and
  `RH/QSquarefreeShortHeadResponse.lean` give exact source variance,
  complementary signed response, the joint ellipse, partial normal equations,
  and two-stage kernel/optimizer energy gaps for the actual canonical residual.
- `RH/QSquarefreeSchurRepresentation.lean` proves the actual head-space span
  and literal signed response `y^T S^-1 q`, with original source moments.
  No omitted composite conductor, truncated Q Gram, or span hypothesis remains.
- `Analysis/DyadicBlockSummability.lean` and `RH/QPolylogBlockEnergy.lean`
  transfer physical dyadic mean squares to complete weighted summable energy.
- `Analysis/WeightedYoungConstant.lean` and
  `RH/QSquarefreeShortHeadYoung.lean` optimize the actual-block comparison
  constant to `(sqrt C + 2*sqrt zetaTwo)^2` for `C>0`, retaining the loss square.

### Conditional research reductions

- `RH/QSquarefreeShortHeadCriterion.lean` weakens uniform stagewise bounds
  to frequently occurring bounds, with separate unbounded stage sets at
  each fixed physical site.
- `RH/QSquarefreeDyadicMeanSquare.lean` and
  `RH/QSquarefreeShortHeadBlocks.lean` prove RH from a common logarithmic
  mean-square envelope on each dyadic short-head block. The unbounded stage
  sets may differ between blocks.

**Open:** the common arithmetic signed-source bound, including the weaker
frequent dyadic mean-square envelope. The unconditional inverse-Gram bound
does not establish it. The finite-cutoff constant improves, but no new
asymptotic exponent or unconditional RH conclusion is obtained.

See `RH/SquarefreeShortHeadLean20261031.md` for precise formulas, formal
scope, and the exploratory stage-240/site-221 checks. Those numerical values
remain uncertified; the eight lower-range contributions all remain negative.

## Conditional-iid Cesàro continuation, 1 November 2026

The source-level continuation is documented in
[ConditionalIIDCesaroResearch20261101.md](RH/ConditionalIIDCesaroResearch20261101.md).
Its new modules are `Analysis/LowerLogGrowth.lean`,
`RH/ConditionalMeanNormalization.lean`,
`RH/ConditionalMeanLowerGrowth.lean`, and
`RH/SquarefreeMobiusCesaroHeads.lean`.

The unconditional results are exact Cesàro energy scaling, the
extended-liminf/cofinal-smallness equivalence, squarefree Möbius head
feasibility, literal finite squarefree support, prefix exhaustion, and
preservation of exact heads under deterministic finite signed averaging.

The RH endpoints are **conditional research reductions**. They require a
cofinal legal exact-head family whose complete normalized Cesàro energy
has zero lower logarithmic growth exponent. Only nonzero head values are
required; no lower bound away from zero is imposed.

**Open:** a checked arithmetic provider of this lower-growth condition for
the actual explicit family or a deterministic repair average. The localized
dyadic estimate also remains Open in this continuation. No new RH-to-density
converse is asserted. All four new modules passed the saved-module import and
principal axiom audit recorded in the report (exit code 0; standard foundations
only). The final checkpoint receipt certifies publication of the saved project.

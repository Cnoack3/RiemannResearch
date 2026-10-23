# Theorem catalog

### Independent squarefree-head compression and reduced complete Gram (2026-10-22)

Established finite and actual-Q statements:
- `RH/QSquarefreeHeadCompression.lean` proves exact physical-head rank
  `card {n in [1,M] : Squarefree n}`, for a legal squarefree dictionary
  containing every low squarefree conductor and one conductor above M.
- `observations_iff_head` proves complete equivalence of the independent
  value observations F(1), F(s)-F(1) and all physical-head constraints for
  radical-compatible vectors. `interpolate_observations` supplies every
  compressed source; `projected_observations_independent` discharges rank.
- `exists_physical_reconstruction` provides the entire physical head from
  compressed coordinates, preserving nonsquarefree-site probability weights.
- `RH/QSquarefreeReducedGram.lean` proves complete A G^{-1} A^T entries,
  the exact constrained completion and infinite-tail identity, retains the
  signed arbitrary-correction cross term, and transports the full head metric.
- `Analysis/FiniteFeasibleGramRepair.normal_repair_le_of_probe_comparison`
  proves E <= delta*(K-1) from a comparison in the actual normal-solution
  direction only; `normal_repair_target_rayleigh` gives its unconditional
  nonzero-repair Rayleigh-quotient specialization.
- `RH/QSquarefreeHeadCompressionExamples.lean` proves the rational determinant
  1/5, exact heads through sites 4 and 6, and actual four-site rank 3.

Conditional research reduction:
- `RH/QSquarefreeReducedGram.closure_capacity_rh_of_uniform_reduced_cost`
  reuses the bounded-exact-head consumer to obtain squarefree closure,
  capacity divergence, and RH from uniformly bounded reduced repair costs.

Open arithmetic provider: `sup_M r_M^T W_M^{-1} r_M < infinity` for a
specified legal dictionary schedule. A uniform bound on the target-direction
`delta_M*(K_M-1)` also suffices. No such estimate or RH is asserted.
Compression preserves the exact constrained minimum; it does not lower it.
Exact-rational interval calculations and floating-point eigenvalue examples
in the memorandum are explicitly separated from Lean theorem claims.
Research detail: `RH/QSquarefreeHeadCompressionResearch20261022.md`.

### Continuous prime-polynomial high moments (2026-10-22)

Established analytic statements:
- `Analysis/PrimeMomentDiagonal.lean` proves the prime-tuple fiber bound `k!`,
  the coefficient square-sum bound, and exact grouped polynomial expansion.
- `Analysis/DirichletMeanSquare.lean` retains the complete signed Gram identity
  and both endpoint Hilbert forms. The proved Montgomery–Vaughan provider
  gives weighted error `26 * sum (norm(a)^2 / delta)` and integer-log error
  `52 * N * sum norm(a)^2`, with no assumed mean-value theorem.
- `Analysis/PrimeDirichletHighMoment.lean` proves the ordinary interval bound
  `integral |P|^(2*k) <= (B-A+52*X^k) * k! * (sum |a|^2)^k`, including
  arbitrary complex coefficients, and the exact signed companion identity.
  If `52*X^k <= B-A`, the factor is at most `2*(B-A)`.
- `Analysis/HighMomentTransfer.lean` proves integral transfer for integrable
  powers, permitting functions with jumps, and the coarse all-k assembly
  `T * (9*C*k*(L+k))^k` from explicitly supplied component estimates.

Conditional research reductions and open providers:
- Open: the actual continued-argument interface and Selberg prime
  approximation, including the actual unconditional zero-density provider.
- Open: the prime-variance asymptotic and large-k estimate needed for the
  exact uniform Tsang theorem. `TsangHighMomentAsymptotic` states the target
  as a proposition only; no declaration asserts it for the actual zeta S.
- The prime-polynomial theorem has no RH or zeta-specific hypotheses.

Candidate job `job_b1mERBtaZPfFm_jSPqCcmKiK7p0do4eR` verified all four
developments. Standalone module build and five central axiom audits passed
in `job_RRcFxliqlBKvrMMeo2zTbO61l10bm7AN`, using only ordinary foundations.
Research detail: `RH/AnalyticHighMomentResearch20261022.md`.

### Microscopic consecutive-gap transfers and collision criteria (2026-10-22)

Established finite statements:
- `Analysis/FiniteGapVariance.lean` proves exact shortfall/stop-loss duality,
  the finite weighted Cantelli bound, an integer-count quadratic refinement,
  and arbitrary central-moment bounds for the empty-window probability.
- It proves the complete second-factorial-moment identity, retaining the
  nonnegative higher-occupancy remainder, and large/small consecutive-gap
  frequency transfers with the geometric void identity explicit.
- `Analysis/ActualConsecutiveGapCriterion.lean` proves that positivity of
  every genuine interior actual-zero gap is equivalent to criticality and
  simplicity at that cutoff, including empty/singleton cutoffs.
  The artificial final gap to T is excluded. The equivalent zero-gap count
  and cofinal criterion are also established.

Conditional research reductions and open providers:
- Open in Lean: the finite count-law/geometric assembly for circular windows.
  Existing truncated actual-gap volume identities remain available.
- Open in Lean: Tsang/Fujii analytic high-moment providers. The memo derives
  an unconditional exponential limiting upper tail from cited Tsang moments
  in ordinary mathematics; it is not a fully formalized zeta theorem.
- Open mathematically: the precise fixed-microscopic sine-kernel variance,
  the full consecutive-gap law, and the prior uniform arithmetic repair bound.
- The adjacent-gap positivity criterion is not a provider of its own
  hypothesis; it includes simplicity and is stronger than RH alone.

Combined candidate verified by job `job_IpGcQZW2IkOT9za93zjDg6Xr8LIymrzy`
(exit 0, verified=true). Seven central axiom audits used ordinary foundations.
Research detail: `RH/MicroscopicConsecutiveGapResearch20261022.md`.


### Feasible complete-Gram head repair and weighted physical frames (2026-10-22)

Established finite and actual-Q statements:
- `Analysis/FiniteFeasibleGramRepair.lean` proves arbitrary-source normal
  solvability from feasibility, exact HEAD/REPAIR completions without row
  independence, and bounded normal solvability iff the directional inequality.
  It also proves frame-to-energy bounds and the complementary signed
  covariance estimate `(y^T r)^2 <= delta * y^T(D-W)y`.
- `Analysis/FiniteSampledRepairStability.lean` proves the exact sampled
  repair decomposition: the complete constrained optimum plus one
  nonnegative screened sampling-error square. The removed sampling-error
  square is retained in an exact companion identity.
- `RH/QSquarefreeHeadRank.lean` derives the physical four-row relation and
  proves projected head rows dependent for every legal dictionary when M>=4.
  Constant heads remain compatible; full row rank is unnecessary.
- `RH/QSquarefreeHeadFrame.lean` proves head probability mass <=1 and
  candidate norm squared <=1/c from feasibility and the stated weighted
  lower frame estimate.

Conditional research reductions:
- `RH/QSquarefreeHeadRepair.closure_capacity_rh_of_uniform_directional_repairs`
  derives feasibility, complete bounded residuals, squarefree closure,
  capacity divergence, and RH from a uniform actual-Q directional bound.
- `RH/QSquarefreeHeadFrame.closure_capacity_rh_of_uniform_head_frame`
  gives the same conclusions from a positive uniform physical frame constant
  and explicit finite head feasibility.

Open arithmetic obligations:
- Uniform target-direction repair bound for actual legal dictionary families.
- Alternatively, a uniform lower weighted frame bound for a prescribed
  feasible dictionary family.
- A quantitative zero-statistic-to-physical-head map, with its means,
  complete signed covariance, and correct P/Q change of law.

The reductions do not prove these providers or RH. Core and extension
candidates passed jobs `job_J3EsWCrx8r5PV3GerVTGR1GCZBWxSRP9` and
`job_R9o_ZtxHDeOgoLZd_AIl8BaRiT2YwzMQ`, both exit 0, verified=true.
Eight central axiom audits used only ordinary foundations. Final publication
is subject to the containing server checkpoint.
Research detail: `RH/QSquarefreeHeadRepairResearch20261022.md`.


### Explicit horizontal second-moment logarithmic rate (2026-10-22)

Established finite identities and transfers:
- Analysis/FiniteStrictTailSecondMoment.lean proves the exact second-moment
  layer cake, the truncated exponential integral with its endpoint retained,
  and the finite estimate sum x_i^2 <= 2 M/a^2 from an exponential strict tail.
- Analysis/ActualZeroHorizontalMomentRate.lean specializes the identity and
  tail transfer to every actual positive-height zeta-zero occurrence,
  retaining analytic multiplicity. Any eventual E(T)/T <= K/log T implies
  SublinearHorizontalEnergy.

Conditional research reduction:
- SelbergDensityBound T C a, with T>1, C>=0 and a>0, gives
  0 <= E(T)/T <= 4 C/(a^2 log T); a=1/4 gives 64 C/log T.
- UniformSelbergDensity a gives E(T)/T = O(1/log T).
- Open formalization obligation: a checked analytic provider for the classical
  unconditional Selberg density theorem. These deductions introduce no RH
  premise or project-local axiom and do not assert that provider.

### Contractive complete-Q CRT carry screening (2026-10-22)

Established Hilbert and actual Q finite-synthesis results:

- `Analysis/ContractionScreening.lean` proves the exact contraction-screening
  identity with both nonnegative remainders retained, the relative screened
  energy bound, and control of total energy by retained projection energy.
- `RH/QCarryContraction.lean` proves the finite zero-charge identity
  h = (T_p - I) f for the actual complete Q residue vectors. Using the
  existing sharp squared floor-dilation contraction 1/p, it gives
  ||(I-P)C||^2 <= ||h||^2/p and
  ||h||^2 <= p/(p-1) ||L-PC||^2 for every exact carry decomposition L-C,
  provided the source f and the lower part L belong to the screening space.
- The actual complete-Q exact identity retains the projection square and the
  full nonnegative quotient-block defect. No independence assumption is used.

The uniform retained-energy provider for growing exact heads remains
**Open**. Its RH application is a **conditional research reduction**:
the bound would give uniformly bounded legal exact-head vectors, then
constant closure and RH. No unconditional RH conclusion is claimed.

The coherent candidate passed job `job_TbqRqhx3JJsy8lm0cQhO97h-RqgIHp3l`,
exit 0, verified=true, reported execution 7.246 seconds. Eight central axiom
audits used only ordinary foundations. Final module validation and publication
are gated by the server checkpoint. Details:
`RH/QCarryContractionResearch20261022.md`.


### Zero-displacement and finite Mellin Gram certificates (2026-10-21)

Established by targeted server verification, subject to the containing
commit's final publication checkpoint:

- `RH/ParetoMellinFiniteGram.lean`: actual finite continuous Mellin kernel
  integrability, exact signed Cauchy Gram energy, the complete squared
  integral remainder, and normal-equation / inverse-Gram lower certificates.
- `RH/QZeroGramObstruction.lean`: sharper actual Q single-zero floor,
  reflected displacement throughout the open critical strip, finite-height
  zero-free rectangle certificates, and actual optimizer / limiting floors.
- The actual finite zero-Gram inverse formula explicitly assumes nonzero
  Gram determinant. A stronger exact Q energy identity and its variational
  bound require no nonsingularity or distinctness and retain the full
  positive law-change correction.

Job `job_7_KqBemftXQhWCvxQGqLiZ6UMYKWAnDt` passed, exit 0,
verified=true, reported execution 14.531 seconds. Seven central axiom
audits showed only ordinary foundations. No RH or density premise occurs.

Distinct-node nonsingularity, the Cauchy determinant product and infinite
zero-product comparison, and the Burnol asymptotic rate remain unformalized.
Capacity saturation remains an unresolved arithmetic target. Exact scope
and source references: `RH/QZeroGramResearch20261021.md`.

### Sharper zero contributions and actual prime-coordinate Gram certificates (2026-10-22)

Established finite and Hilbert-space results:

- `Analysis/ActualZeroCoshMass.lean` now propagates the sharp strip coefficient
  through every actual finite cutoff: ||S-L|| <= 4(cosh(|u|/2)-1) E(T).
- `RH/RamanujanZeroSignal.lean` sharpens the existing horizontal signal weight
  to 4 pi (sqrt(q)-1)^2 for q >= 1, proves improvement of the full inverse-Gram
  budget, and retains individual exponential-tail frequency denominators.
- `Analysis/FiniteGramSignalStability.lean` proves the exact radial
  least-squares remainder, screening linearity and contraction, and the literal
  screened matrix K = A - (A b)(A b)^T/kappa with an entrywise certificate.
- `RH/RamanujanZeroSignal.lean` retains the signed Landau/density interaction
  after screening, allows arbitrary radial correction before bounding the
  density residual, and gives prime normalization from a nonzero pairing.
- `RH/ZetaTwoParetoTransfer.lean` now includes the exact convergent
  Radon--Nikodym norm correction, before its use in new prime-coordinate bounds.
- `RH/QPrimeParetoGram.lean` uses the existing proved Q independence and
  orthonormal prime modes to obtain actual Pareto Gram bounds zetaTwo/2 I <= G <=
  zetaTwo I, retaining the complete correction and projection residual.
- `RH/PrimePacketIncrementIndependence.lean` proves mutual independence of
  actual prime-packet increments under Q by the exact affine divisibility identity.
- `RH/RamanujanPrimeCoordinates.lean` connects these modes to actual packet
  synthesis and unit-target error, with all residuals retained; it proves the
  quadratic-form lower certificate H >= zetaTwo/2 C^T C.

Open domain-specific obligations remain separate:

- Actual classical density/sublinear-energy provider: still unformalized.
- Squarefree packet capacity saturation: still an unresolved mathematical target.
- Vanishing nonradial actual zero defect or a growing-family effective budget:
  not supplied merely by the new finite screening theorem.
- Rank/smallest-singular-value estimates for the prime observation matrix C:
  needed before inferring packet inverse conditioning from the auxiliary modes.
- No independence of zero ordinates or integrated packets is asserted.

Targeted job `job_IftM-8dWigpEFiUvcWkCzVs6Hd9kEWrg` succeeded, exit 0,
verified=true, reported execution 15.057 seconds. Ten central axiom audits
showed only ordinary foundations; substantive local hypotheses remain in
their types. The containing commit's checkpoint certifies final publication.
See `RH/RamanujanZeroPrimeGramResearch20261022.md` for exact formulas,
declaration names, proof interpretation, and the remaining obligations.

### Ramanujan zero signals, relaxed density, and inverse-Gram stability (2026-10-21)

Established finite and Hilbert-space results:

- `Analysis/SignalNormalizationStability.lean`: exact normalization,
  orthogonal vector identity and Gram-determinant remainder.
- `Analysis/FiniteGramSignalStability.lean`: the literal actual inverse
  matrix realizes the dual norm and pairing. Its full signed screened
  rank-one formula gives the exact normalized error, projective convergence
  criterion, complete target error, and anisotropic metric certificates.
- `RH/RamanujanZeroSignal.lean`: exact weighted-Q/P packet mean and Gram
  entries, finite packet independence, sparse squarefree prime signal,
  signed Landau/density energy decomposition, and actual inverse-Gram
  density budgets. Finite screened-error certificates give exact prime
  normalization and complete unit-target error bounds without RH or density.

Conditional research reductions:

- `Analysis/ActualZeroSublinearEnergy.lean` proves that one shrinking strip
  suffices: delta(T)^2 log T -> 0 and its actual inclusive right-half count
  divided by T -> 0 imply E(T)/T -> 0. Actual Riemann--von Mangoldt supplies
  the total-count upper bound. The moving-strip analytic count provider is Open.
- `UniformLogLossDensity a b`, for every a > 0 and every fixed real b,
  implies that weaker sublinear horizontal moment. A loglog/log window
  absorbs every fixed log loss; the analytic density provider remains Open.
- General exponential profiles have the explicit finite-band budget
  M(T)/(T decay(T)^2), including their actual inverse-Gram coordinate cost.
- `sampledSignal_tendsto`, `sampled_inverseNorm_error_tendsto`,
  `coefficients_tendsto`, and `exists_strictMono_zero_cutoffs` now take
  `SublinearHorizontalEnergy`; UniformSelbergDensity (1/4) is no longer
  required in those theorem types. A checked transfer from every positive
  UniformSelbergDensity exponent remains available; its classical provider is Open.
- The growing-family target consumer requires capacity saturation and
  vanishing screened ratios. It requires no uniform bound on inverse Gram
  operators and no radial-error convergence.

Open arithmetic obligation: prove saturation of complete squarefree packet
capacities, kappa_D -> 1. Neither density relaxation nor prime normalization
supplies this assertion. Effective growing cutoffs require the actual Gram
budgets or sharper signed screening. The weighted-Q/P Gram must be retained.

Targeted server job `job_uf5iCmx68d_G_97lUaLH3vpOpDfI5k5D` passed,
exit 0, verified=true, reported execution 16.249 seconds. Six central new
declarations had only ordinary foundations in their axiom lists; domain
premises remain visible in their types. The containing commit's successful
checkpoint validates publication. See
`RH/RamanujanDensityRelaxationResearch20261021.md` for the proof chain,
source references, exact Gram identities, and Open obligations.

### Factorial cutoffs, anchored targets, and sampled gains (2026-10-21)

Established identities and obstructions, subject to the containing commit's checkpoint:

- `NumberTheory/PrimeFactorialBlockJumps.lean`: exact actual factorial-valuation
  jumps, complete signed compensated jumps, and prime pairing to floor quotients.
- `RH/QFactorialCutoffObstruction.lean`: the actual D=3, p=2 cutoff has
  incompatible jumps at 6 and 36 after every real linear compensation.
  Its complete error against the constant-enlarged squarefree legal closure
  equals `1/(2582 ζ(2))` plus an explicit norm square.
- `RH/QPrimeAnchoredTarget.lean`: a continuous three-site charge extracts
  constants from the full squarefree dictionary restricted to p-divisible
  conductors. Exact heads through p+1 force the constant to be zero.
- `Analysis/FiniteSampledGain.lean` and `Analysis/SampledScreenedGain.lean`:
  exact signed source identities, fully sampled squared error budgets, and
  certified lower bounds for actual one-direction and nested projection gains.
  True screening annihilates old-approximant displacement in the source.
- `Analysis/ActualZeroFixedStripConcentration.lean`: finite head/tail and
  Markov estimates; fixed-strip concentration is equivalent to vanishing
  normalized horizontal energy, including empty cutoffs and multiplicities.

Conditional research reductions:

- `riemannHypothesis_of_bounded_anchored_exact_heads` gives RH from a uniform
  complete-Q energy budget for actual anchored exact-head approximants.
- `tendsto_normalized_ordinate_of_fixedStrip` transfers separately provided
  fixed-strip concentration and normalized Landau cancellation to actual phases.

Open: the anchored arithmetic energy budget (or sufficient cumulative legal
gains), the actual fixed-strip density provider, and the null-boundary passage
to half-open phase bins. None is supplied by the conditional reductions.
See `RH/MobiusSamplingContinuationResearch20261021.md`.

### Zero-phase sampling and floor-logarithm/valuation inversion (2026-10-21)

Established finite and Hilbert-space identities:

- `Analysis/FiniteCellSampling.lean`: exact regrouping and importance-weighted
  sample limits for a finite cell partition, plus relabeling invariance.
- `Analysis/FiniteWeightedSampling.lean`: exact signed form/energy differences,
  relative energy comparison, signed source error, quadratic optimizer
  displacement and true residual bounds, and sampled-minimum comparison.
- `Analysis/FiniteSamplingDiagonal.lean`: a strictly increasing diagonal with
  prescribed positive errors, conditional on each fixed finite stage converging.
- `Analysis/PrimePhaseCRTCells.lean`: literal fractional-log prime phases,
  floor bins, unique CRT coding, and the correct positive representative;
  physical zero residue is represented by L. Frequency inputs remain explicit.
- `RH/QZeroPhaseSampling.lean` and `RH/QPrimePhaseSampling.lean`: complete
  periodic Q inner products, norm comparisons, and exact CRT-phase sampling.
  The weights retain every arithmetic-progression tail. Physical agreement is
  required only at positive coordinates, avoiding an auxiliary-zero mismatch.
- `NumberTheory/PrimeLogValuationMobius.lean`: the actual `Nat.log` jump is the
  positive-power indicator; its divisor sum is `Nat.factorization`; actual
  Moebius inversion and cumulative summation recover `Nat.log` exactly.
- `RH/PrimeValuationClosureObstruction.lean`: any actual Q representative of
  the prime valuation is outside `closureWithConstants`, because its jumps at
  p and p² are 1 and 2. This does not exclude the floor-logarithm target.

Conditional research reduction:

- `RH/QZeroPhaseSamplingRH.lean`:
  `riemannHypothesis_of_weighted_sampled_error` derives Mathlib RH from
  genuine squarefree-legal approximants, bounded periodic residual realizations,
  cell-frequency relative errors at most one half, and sampled errors tending
  to zero. The simpler norm-square closure criterion is also supplied.

Open obligations: (1) an actual multiplicity-preserving zeta-zero analytic
provider for the joint bin frequencies; (2) an independent arithmetic estimate
forcing the complete legal approximation errors to zero. Classical fixed-stage
zero equidistribution is known; its provider chain is not completed here.
Finite inversion alone does not give a bounded closure-preserving transform.

See `RH/QZeroPhaseSamplingResearch20261021.md` and
`RH/PrimeLogValuationResearch20261021.md` for proofs, precise hypotheses,
verification evidence, and a coordinated RH agenda. Publication is certified
only by the containing commit's successful Lean-server checkpoint.

### Three-stage interpolation and prime-jump energy obstruction (2026-10-21)

- `Analysis/ThreeStageSieveAlgebra.lean`: exact 3x3 determinant, Cramer solution
  and uniqueness, singular compatibility, both alternating sign patterns,
  variation identity, and full Gram and target-error identities.
- `Analysis/PrimePowerEulerDecay.lean` and `RH/QPrimePowerSieveUniform.lean`:
  arbitrary-real-power Euler decay; actual fixed-prime probes and monotonicity.
- `RH/QSievePrimeJump.lean`: exact semiprime jumps of arbitrary finite
  zero-drift sieve rows and complete-Q bounds on cumulative coefficients.
- `Analysis/VanishingProbeCost.lean`: scalar norm-divergence consumer.
- `RH/QThreeStageSieveEnergy.lean`: actual three-stage probe/energy bounds;
  `threeStage_prime_cutoffs_norm_tendsto_atTop` rules out bounded complete
  norm for cofinal increasing prime-cutoff rows matching any fixed nonzero
  Euler signature. Bertrand discharges the short-prime witnesses. No sign,
  variation, determinant-gap, RH, or assumed energy hypothesis is used.

The coherent candidate passed server job `job_glGMgJ9jle0g9AD2X0YuRw3pTIXboR3d`,
exit 0, verified=true. Saved-source audit and publication remain checkpoint-gated.
See `RH/ThreeStageSieveResearch20261021.md` for exact hypotheses and evidence.

The extension to arbitrary row lengths and the continuous separator of the
entire fixed-p raw-sieve span plus constants are ordinary proved arguments
recorded in the note; their infinite-series Lean assembly remains Open.
Full squarefree-divisor target closure and RH remain Open.

### Five actual squarefree legal directions (2026-10-21)

- `RH/QResidueThreeMoments.lean`: exact conductor-three even/parity moments
  and complete-Q second moment, with full weighted reindexing.
- `RH/QSquarefreeLegalBasis.lean`: nonzero innovations at conductors 3,5,6;
  `legalFrame_orthonormal`, legal closure membership, exact energy and
  least-squares gap, and nonzero finite residuals for both logarithmic targets.
- `RH/QPrimePowerLegalCoefficients.lean`: complete target moments, exact
  `residueMoment_head_tail`, coefficients at all three new directions,
  `qTarget_five_direction_energy`, and strictly positive remaining energy.

These statements have no RH or assumed target-closure hypothesis. Publication
is subject to the server checkpoint. Numerical evaluations and informal
AP-series/explicit coordinate bounds are distinguished from Lean declarations
in `RH/LegalBasisContinuationResearch20261021.md`.

Continuation (2026-10-22): `RH/QSquarefreeCompleteBasis.lean` supplies the
complete legal basis, with zeros removed from the exhaustive Gram–Schmidt
dictionary. `legalVector_closed_span` identifies its closed span with
`closureWithConstants`, and `legalHilbertBasis` bundles the complete basis.
`legalProjection_hasSum` proves unconditional reconstruction of the legal
projection. `legalBasis_energy_exact` and `legalBasis_error_exact` retain
the full orthogonal legal residual and every signed coefficient discrepancy.
`mem_closureWithConstants_iff_parseval` proves the exact saturation equivalence.
The first vectors are qOne and positive parityUnit; the F2 parity coefficient
remains 1/sqrt(3), with captured energy 1/3. No independence of the input
dictionary or target-membership hypothesis is assumed for the construction.

Open: Parseval saturation for F2 and F3, hence their actual legal membership.
Higher Meixner completeness is a separate open task.

### Arbitrary signed sieve rows and one-sign-change obstruction (2026-10-20)

New unconditional declarations, subject to this change's final server checkpoint:

- `Analysis/SignedBalancedRows.lean`: exact determinant/mass transport,
  positive-negative-part probe bounds, and impossibility of reversed slopes.
- `RH/QPrimePowerSignedObstruction.lean`: exact finite-row Mellin identity,
  uniform Euler decay, arbitrary-row bounded-TV quantitative complete-Q error
  lower bound, and divergence of the complete norm for cofinal families.
- `RH/QPrimePowerOneSignObstruction.lean`: actual equal-slope Euler rigidity,
  uniform determinant bound including plateaux, and the same quantitative
  obstruction for negative-before-positive rows with no TV bound. The reverse
  one-sign orientation is algebraically impossible.

The exact squared-error constant is
(2sigma-1)/(4 zeta(2) sigma^2 (p^sigma-1)^2), multiplying H^(2sigma-1).
All finite row lengths and growing support sizes are covered. The existing
exact head, complete signed Gram energy, and Mellin-tail results are reused.
No RH or unresolved arithmetic provider is assumed.

Saved-source/axiom audit: job_76IUGeg_G8JQSttSmSc0gDDtB_DbezCN,
exit 0, verified=true; nine inspected declarations use standard foundations.
Final integrated publication is separately checkpoint-gated.
See `RH/SignedSieveRowsObstructionResearch20261020.md` for assumptions,
proof identities, excluded families, and the remaining alternating-row agenda.

Update (2026-10-21): cofinal three-stage rows matching a fixed nonzero signature
are excluded by the prime-jump energy theorem above. The broader arbitrary-row
obstruction has an ordinary proof awaiting its infinite-series Lean assembly.
Open: broader squarefree-divisor constructions, full target closure, and RH.

### Orthonormal parity coordinates and logarithmic rigidity (2026-10-20 UTC)

- `RH/QParityBasis.lean`: `parityFrame_orthonormal` gives the constant and
  centered parity unit vectors; `parityApproximation_energy_exact` retains the
  complete residual in the two-coordinate Pythagorean identity.
- `RH/QPrimePowerParityBasis.lean`: both coordinates and their approximation
  belong to `closureWithConstants`; `qTarget_two_inner_parityUnit` is exactly
  `1 / sqrt 3`, and `qTarget_two_parity_energy_exact` captures energy `1/3`
  with the full remaining norm square.
- `RH/QPrimePowerTransformRigidity.lean`: power-invariant jumps force any
  physical sequence `phi (Nat.log p n)` in the enlarged closure to be affine
  in `Nat.log p n`. A geometric transform in that closure has base one.
- `RH/FinitePrimeCentered.lean`: exact centered finite Boolean-product Gram
  identities, isolated-success coefficients, and `unitMonomial_gram` equal
  to the identity matrix when all parameters lie strictly between zero and one.
  This finite law is not asserted here to be the actual integer Zipf law.
- `RH/QFinitePrimeBasis.lean` (2026-10-21 UTC): `booleanLift_inner` transfers
  every finite distinct-prime Boolean observable's Gram form to actual QHilbert,
  using the existing actual configuration law. `primeUnitVector_orthonormal`
  and `primeUnitVector_energy_exact` establish actual orthonormal centered
  products and the complete finite expansion with its residual norm square.
  No legality or completeness of the full valuation basis is asserted.
- `RH/QPrimePowerHilbertFrame.lean` (2026-10-21 UTC):
  `divisorWavelet_prime_pow_succ` identifies adjacent scaled divisibility tails;
  `primePowerFrame_orthonormal` reuses the established ambient divisor basis
  for all powers of one prime, including the constant mode.
- `RH/QPrimePowerWaveletCoefficients.lean` (2026-10-21 UTC):
  `qTarget_inner_primePowerDivisor` computes the full dilation moment;
  `qTarget_inner_primePowerFrame_succ` gives exactly
  `1 / (p^k * sqrt (p^2 - 1))` for the floor-log target's mode k+1.
  `qTarget_primePower_energy_exact` and `qTarget_primePower_error_exact`
  retain the full residual and every signed trial-coefficient discrepancy.
  This is an ambient wavelet expansion, not a legal-membership provider.
- `RH/QPrimePowerMixedWavelet.lean` (2026-10-21 UTC):
  `divisorWavelet_primePower_mul` gives the exact coprime factorization
  into adjacent p-power tails, with every signed Moebius coefficient.
- `RH/QPrimePowerMixedCoefficients.lean` (2026-10-21 UTC):
  `qTarget_scaled_primePower_divisor` computes the exact dilation moment.
  `qTarget_inner_mixed_divisorWavelet` and its normalized version vanish
  for prime p and nontrivial p-coprime cofactor.
  `qTarget_mixed_modes_error_exact` retains the complete norm-square
  residual and signed coefficients. Legal closure preservation is not asserted.
  Saved-source/axiom check `job_BkDWoFzxSF1ltu_DvyDoKvPsQrHn_huG`:
  exit 0, standard foundations only. Final publication is checkpoint-gated.
- `RH/QPrimePowerInfiniteProjection.lean` (2026-10-21, Pacific time):
  `primePower_nonconstant_summable` and `primePowerProjection_tendsto`
  construct the norm-convergent sum of all nonconstant same-prime modes.
  `primePowerProjection_norm_sq` sums the captured energy exactly to
  p^2/(p^2-1)^2, giving 4/9 and 9/64 for bases two and three.
  `qTarget_primePower_centered_energy_exact` retains the mean and full residual;
  `qTarget_primePower_series_error_exact` handles arbitrary convergent signed
  trial series without discarding either residual.
  `primePowerProjectionUnit_norm_sq` and
  `qTarget_inner_primePowerProjectionUnit` give a unit direction with target
  coefficient p/(p^2-1), specifically 2/3 and 3/8.
  Its physical valuation identification is established in the following module.
  Saved-source audit `job_X7L7Pa-gdRGA1ipw_C70373N-JKbpJT4` passed;
  six inspected declarations use standard foundations only.
- `RH/QPrimePowerValuationProjection.lean` (2026-10-21, Pacific time):
  `primePower_projection_partial_sequence` proves coordinate stabilization;
  `primePowerProjection_sequence` identifies P_p with v_p-1/(p^2-1), and
  `primePowerProjectionUnit_sequence` identifies U_p with ((p^2-1)v_p-1)/p.
  `primeValuationVector_sequence` constructs the actual valuation representative.
  Both centered and normalized projections are proved outside
  `closureWithConstants`, using the existing prime-valuation obstruction.
  This does not decide membership of the floor-logarithm target.
  Audit `job_Le-uksdxS3DuX7sdeqv8fBrU3_jxoPyz` passed with standard foundations.

- `RH/QPrimePowerCofactorResidual.lean` (2026-10-22, Pacific time):
  `primeCofactorResidual_sequence` identifies the full residual with the centered
  floor logarithm of n/p^(v_p(n)); `primeCofactorTarget_mean` computes its mean.
  `primeCofactorResidual_sequence_mul_power` proves invariance under p-powers.
  `primeCofactorResidual_norm_sq_series` retains the complete weighted series.
  `primeCofactorResidual_energy_lower_bound` gives 1/(zeta(2)*(1+(p+1)^2));
  `qTarget_primePower_captured_energy_lt` proves strict residual positivity.
  This is not a distance-to-legal-closure bound or a target membership provider.
  Audit job_N4o66XJr8nz6ncuK5mBkF_FW4tgnS-PP passed; standard foundations only.

- `RH/QPrimePowerCofactorExpansion.lean` (2026-10-22, Pacific time):
  `primeCofactorResidual_inner_basis` proves exact coefficient support at
  nonconstant p-coprime conductors in the complete ambient divisor basis.
  `primeCofactorResidual_hasSum_coprime` reconstructs the full residual;
  `primeCofactorResidual_parseval_coprime` retains its complete coefficient energy.
  `qTarget_eq_mean_projection_coprime_tsum` and `qTarget_coprime_energy_exact`
  assemble the full target expansion and exact energy, with no vanished residual.
  `qTarget_coprime_expansion_error_exact` retains all signed discrepancies,
  including every conductor outside the target's cofactor support.
  Remaining coefficient evaluation, higher Meixner completeness, and legal
  closure membership remain open; no legal-preservation claim is made.
  Audit job_DNkLbnBu24d0gJ_Hm4zVpcN_5yEK5Otx passed; standard foundations only.

- `RH/QDivisorDilationCoefficients.lean` (2026-10-22, Pacific time):
  `normalizedDivisorWavelet_inner_dilation` gives the exact signed dilation
  formula for any Q-Hilbert vector; `normalizedDivisorWavelet_residue_coefficient`
  supplies legal atom columns. `divisorBasis_error_finite_exact` retains signed
  discrepancies and the complete orthogonal remainder.

- `RH/QPrimePowerCoprimeCoefficients.lean` (2026-10-22, Pacific time):
  `qTarget_inner_basis_moebius` and `qTarget_inner_primePower_mean_difference`
  give exact arithmetic coefficients. Dilated means are summable, with exact
  head-tail identities. `qTarget_inner_primePower_bounds` gives adjacent-integer
  bounds. Explicit conductors 2, 3, 4, 5, 9 are checked.
  `primeCofactorResidual_two_energy_ge_eighth` and
  `primeCofactorResidual_three_energy_ge_twentyFourth` give 1/8 and 1/24,
  improving ambient residual bounds; these are not legal distance bounds.

- `RH/QPrimePowerThresholdSeries.lean` (2026-10-22, Pacific time):
  `dilatedTargetMean_threshold_series` exchanges the actual Zipf threshold
  sums using proved double summability. Exact integer ceilings have no rounding.
  `qTarget_basis_threshold_error_exact` retains every signed Moebius tail.
  `qTarget_primePower_threshold_hasSum` expresses each prime-power conductor
  coefficient as a convergent series of finite nonnegative interval sums.
  `qTarget_primePower_threshold_head_tail` retains the complete level tail;
  `qTarget_primePower_threshold_tendsto` certifies convergence of finite heads.
  The quantitative tail bound is now supplied by QPrimePowerThresholdTail.
  F_p remains Nat.log p n; no membership provider is supplied.

- `RH/QPrimePowerThresholdTail.lean` (2026-10-22, Pacific time):
  `dilatedTargetMean_threshold_error_bounds` proves the explicit bound
  tau = [d/((p-1)p^K) + d^2/((p^2-1)p^(2K))]/zeta(2).
  `qTarget_basis_threshold_error_interval` retains separate signed
  Moebius contributions to the lower and upper errors, using the exact
  remainder identity from QPrimePowerThresholdSeries.
  `qTarget_primePower_threshold_error_bounds` certifies finite interval
  coefficient heads with an error between zero and tau/sqrt(J_2).
  Finite-precision rounding certification, higher Meixner completeness,
  and actual legal Parseval saturation remain open.

- `RH/QDivisorModeLegality.lean` (2026-10-22, Pacific time):
  `residue_three_single_mode_defect` gives 9 E_Q[g_3]/8 > 0.
  `ambient_single_mode_not_legal_preserving` exhibits legal g_3 whose ambient
  single-mode projection lies outside closureWithConstants.
  Saved-source audit job_KKzufSXky1fZEHuoYg_hE31wTjIgZjzv passed:
  16 inspected declarations use only standard foundations.
  RH/FpCoprimeCoefficientsResearch20261022.md records exact arithmetic series,
  exploratory numerical Gram comparisons, reproduction code, and open tasks.

Open: higher Meixner orthogonality and completeness for the full valuation basis,
Parseval saturation for the legal squarefree basis, and membership of the full
F_2 and F_3 targets in `closureWithConstants`. The existing two-target RH
criterion remains a conditional research reduction; these additions do not
supply either target-membership provider.
See `RH/FpOrthonormalBasisResearch20261020.md` for the informal full-basis
construction and the remaining obligations.

### Unconditional signed ratio, complete metric refinement, and target caps (2026-10-20 UTC)

New unconditional results, accepted through this change's final server checkpoint:

- `NumberTheory/PrimorialPolynomialLower.lean`: the elementary cubic primorial
  lower bound from three Bertrand intervals, with no prime number theorem.
- `RH/QRationalSignedTailRatio.lean`:
  `rationalSignedTail_div_minimum_tendsto_unconditional` proves S/R -> -1 at
  every exhaustive cutoff, including repeated periods, without assuming D>0.
  The explicit normalized-boundary bound is 1280/[3 floor((n+3)/8)] for n>=21.
- `RH/QRationalAbsorptionError.lean`: the least signed absorption error is
  A_theta=(1-theta)R-B; A_theta/R -> 1-theta. Errors o(R), and any fixed
  multiple of the explicit endpoint B, cannot yield cofinal absorption for theta<1.
- `RH/PrimePowerTargetCap.lean`: exact Pareto capped-target error
  (p+1)/[p^K(p-1)^2], complete-Q error bounds and convergence, and nonlegality
  of every positive cap from its unequal jumps at p and p^(K+1).
- `RH/QResiduePowerRefinement.lean`: exact residue refinement for every
  reciprocal power of order s+2.
- `RH/QRationalQuarticRefinement.lean`: complete quartic-tail control yields
  Gap_(kL)(f) <= [20/(3k)]Gap_L(f), uniformly over all periodic coefficients.
- `RH/QRationalStageGain.lean`: the exact stage identity now gives the actual
  refund factor 1-20/(3k), retaining the full displacement square. Existing
  stage and cumulative-budget thresholds improve from 120/240 to 7/14.

Open: constant membership in the complete-Q squarefree closure, an independent
upper bound R_n -> 0, and RH. Neither the unconditional signed ratio nor the
surrogate-metric contraction supplies this missing upper bound.
See `RH/QSignedRatioAndTargetCapsResearch20261020.md`.

### Recovered actual signed and screened rational gains (2026-10-21)

Established finite and complete-Q identities, subject to the final successful
server checkpoint for this change:

- `RH/QRationalStageCorrelation.lean`: actual signed correlation equals the
  correlation with optimizer displacement; exact one-direction square completion,
  its lower certificate, divisor instantiation, and the quartic refund bound.
- `RH/QRationalReoptimization.lean`: actual old-space projection in the later
  rational metric; exact displacement = metric drift + genuine legal gain;
  actual screened directions and their target-charge certificates.
  `rationalScreened_residue_energy_pos` proves positive screened energy for every
  e>=2 dividing the later period but not the old period, using the site L_n.
  `rationalLegalGain_ge_new_divisor_charge` therefore has no assumed positive
  denominator.
- `RH/QRationalDisplacementComparison.lean`: complete-Q comparison with factors
  1 and 5/3, and exact Q projection-gain comparison retaining signed mismatch.
- `Analysis/GainBudgetConsumer.lean`: finite terminal gain estimate
  `(1 + sum c_j) R_N <= R_0 + sum epsilon_j`, and summable-error zero-limit consumer.

Conditional research reduction:
`RH/QRationalGainProvider.lean` specializes the consumer to actual rational
minima on cofinal chains with period ratios >=14 and concludes squarefree
constant closure from its explicit arithmetic provider.

Open: prove `hprovider` for actual gains, with divergent cumulative c_j and
summable nonnegative errors. The positive screened denominator does not supply
a lower bound for the signed numerator. Constant closure and RH remain open.
See `RH/QRationalScreenedGainResearch20261021.md`.

### Rational tail fluctuations and absorption obstruction (2026-10-20 UTC)

Established finite declarations after this change's successful server checkpoint:

- `Analysis/FiniteClassDirichlet.lean`: weighted Cauchy--Schwarz, exact pairwise
  centered variance, class Poincare/negative-mass bounds, and dual square completion.
- `RH/QRationalTailPoincare.lean`: actual pairwise tail and all gcd-class bounds,
  including `rational_negative_mass_path_budget`.
- `RH/QRationalTailDuality.lean`: actual residual admissibility, exact dual gap,
  sharp Cauchy--Schwarz, attained objective, and `rational_tail_bound_iff_dual_bound`.
- `RH/QRationalCoprimeLower.lean`: actual coprime three-site and polynomial
  lower bounds, `rationalSignedTail_near_negative_minimum`, and
  `seventh_primorial_signed_absorption_fails`: S_510510 < -(1999/2000) R_510510.

No unresolved normal-equation or closure provider is assumed in these results.
The original research memo derived S/R -> -1 along distinct primorials using the
finite bound and Bertrand's postulate. The continuation listed above now proves
it in Lean for every cutoff. It rules out error-free fixed-factor absorption;
it does not rule out absolute error decay, squarefree closure, or RH.

Open: an arithmetic upper bound R_(L_n)->0, equivalently a vanishing upper bound
for every constrained dual objective. A valid signed absorption error may tend
to zero but cannot be o(R) along valid cofinal stages. Completed exact minimizer
experiments cover L=2,6,30,210; cheap three-site certificates stop at the seventh
primorial 510510. No logarithmic-head computations were duplicated.
See `RH/QRationalTailFluctuationResearch20261020.md` and
`RH/QRationalTailExactChecks20261020.md`.

### Simultaneous coprime-pair energy certificates (2026-10-21 UTC)

New finite results for the actual complete-divisor rational minimizer:

- `Analysis/CoprimePairEnergy.lean`: exact pair and shared-coordinate square
  completions, the finite-sum energy gap, and strict improvement over every
  selected single pair when a second positive pair is present.
- `RH/QRationalCoprimePairs.lean`: `rational_coprime_pairs_gap` retains all
  unused-site, shared-coordinate, and pair-mean squares. With
  A=sum w_(q-1)w_q/(w_(q-1)+w_q), it gives
  R >= b+w_1 A/(w_1+A) for any disjoint family of coprime pairs.
- `rationalSignedTail_coprime_pairs_ratio_bound` retains the full endpoint
  in the denominator. `seventh_primorial_twenty_pair_absorption_fails` proves
  S_510510 < -(9999/10000)R_510510 with no hypotheses or optimizer solve.

The general application assumes only finite site ranges, coprimality, and
pair disjointness. The concrete theorem discharges them by exact computation.
Open: an independent upper estimate forcing the primorial minimum to zero.
These lower certificates and upper bounds on S do not establish constant
squarefree closure or RH. See `RH/QRationalCoprimePairResearch20261021.md`
for the exact identity, verification provenance, and reproducible Fraction checks.

### Uniform complete-Q two-stage obstruction (2026-10-20 UTC)

New unconditional declarations in `RH/QPrimePowerTwoStageObstruction.lean`:
`sieveTwoStageVector_mellin_uniform`,
`sieveTwoStageVector_quantitative_lower`, and
`sieveTwoStageVector_norm_tendsto_atTop`.
They cover every prime p, 1/2<sigma<1, and every sufficiently large first
integer cutoff, uniformly over all nondegenerate later cutoffs, including
arbitrarily close slopes. The exact positive squared-error constant is
(2sigma-1)/(4 zeta(2) sigma^2 (p^sigma-1)^2).

Providers: `Analysis/PrimePowerEulerDecay.lean` (elementary actual Euler
decay), `RH/QPrimePowerSieveMellin.lean` and
`RH/QPrimePowerSievePrimeStep.lean` (actual finite arithmetic),
`RH/PrimeSieveSecantLimits.lean` and `RH/QPrimePowerSieveUniform.lean`
(uniformity with unchanged stages), `RH/QPrimePowerSieveTwoStage.lean`
(all-prime actual synthesis), `RH/ParetoMellinTail.lean`,
`RH/QMellinTail.lean`, and `RH/PrimePowerTargetMellinLower.lean`.
Separately, `Analysis/ReducedResiduePowerSum.lean` proves the requested
fixed-positive-modulus reduced-residue asymptotic.

Final source/import/axiom audit: job_3vRdgkwYETp-cBXwh7lK3XpJAWryflzA,
verified=true, exit 0; standard foundations only.
Final publication is separately checkpoint-gated.
See `RH/TwoStageSieveFormalizationResearch20261020.md` for exact scope.
Squarefree target closure, general signed energy providers, and RH remain Open.

### Moving prime-power sieve secants (2026-10-20 UTC)

Finite results in `RH/PrimeSieveSecantAlgebra.lean`: exact three-stage
positive secant subdivision, unit coefficient sum, finite adjacent-intercept
bound, and exact scalar Euler-step cancellation. Actual complete-Q vector
linear-probe specialization is in `RH/QPrimePowerTwoStage.lean`.
Coherent job `job_plyXN2GIWDtP2oM300djFafThEoz1jwr` succeeded with
verified=true, exit 0; inspected axioms were standard foundations only.
Final staged/integrated publication is gated by the server checkpoint.

The all-moving-two-stage Mellin obstruction and polynomial complete-Q
error lower bound are now formalized in the completion listed above.
Both prime-power target closure memberships and RH remain Open.
See `RH/TwoStageSieveObstructionResearch20261020.md` for derivations,
assumptions, circularity audit, and the next actual signed-budget obligation.

### Two-prime Mellin criterion with real constants (2026-10-20 UTC)

Conditional research reduction:
`PrimePowerTarget.riemannHypothesis_of_two_targets_mem_closureWithConstants`
in `RH/PrimePowerTwoTargetCriterion.lean` proves
F_2,F_3 in closure(H + R*1) imply literal Mathlib RiemannHypothesis.
Open providers: both displayed complete-Q closure memberships.
No target membership or RH is asserted unconditionally.

The continuous imaginary Mellin annihilator, power reality and conjugation
rigidity are proved, reusing the existing Q targets, square-summability,
exact Mellin transforms, and two-three complex-power injectivity.
`RH/RealZetaNonvanishing.lean` proves positive-real zeta nonvanishing away
from the pole using the positive normalized-residue first-difference series.

Separate signed investigation in `RH/QPrimePowerSignedSieve.lean` proves
actual finite signed primorial legality, exact head mass/drift accounting,
balanced target heads, the full signed complete-Q Gram energy, and the
necessity of a negative weight. Open: a uniform complete-Q bound as the
head grows. The bounded-total-variation signed-averaging obstruction in
the memorandum is ordinary mathematics, not a new Lean declaration.

Criterion import/axiom job `job_ZtiduMFytOiXGO3pUEfgIRraXHMF4N98` and
coherent signed-sieve job `job_JVh7lckC1sH3Q3a1EWRBSWidRscovVff` succeeded.
Final integrated publication remains gated by the server checkpoint.
See `RH/TwoPrimeMellinCriterionResearch20261020.md`.


### Parity, dilation separation, and exact-head target equivalences (2026-10-20 UTC)

Established after this change's successful server checkpoint:

- `RH/QEvenClosure.lean`: parity/constant membership equivalence for any
  submodule containing g_2, exact screened-vector equality, complete
  squared errors, and actual stage/limiting specializations.
- `RH/QSquarefreeDilationObstruction.lean`: the full square-jump witness
  annihilates C=closure(H+R*1); its exact signed energy decomposition gives
  a squared-error lower bound 1/(30*zetaTwo) for both D1 and Dg_2 against C.
  D(C) is not contained in C and D(H) is not contained in H.
  F_2 itself passes the four-site test.
- `RH/QExactHeadAverages.lean`: arbitrary Q closure vectors admit
  arbitrarily close finite-head repairs. Closure membership is equivalent
  to existence of uniformly full-energy-bounded algebraic exact heads.
- `RH/QPrimePowerHeadClosure.lean`: specializes that genuine equivalence
  to every F_p (p>1), with or without a real constant, using all squarefree
  conductors. Supports may depend on the requested head.
- `Analysis/SignedBalancedRows.lean` and the actual sieve specialization:
  exact endpoint-slack identity, sharp total-variation lower bound
  (a+b)/(a-b), endpoint attainment, and a relative-slope constraint
  under a variation cap. No Hilbert norm bound is inferred from TV.

Conditional research reduction:
`PrimePowerTarget.riemannHypothesis_of_bounded_two_finite_exact_heads`.
Open providers: uniform complete-Q energy budgets for both F_2 and F_3
in the algebraic squarefree span plus constants.
No membership or RH assertion is supplied unconditionally.

The previous handoff's coalescing two-stage possibility is already excluded
by newer main's `sieveTwoStageVector_norm_tendsto_atTop`; this continuation
does not re-prove it. Arbitrary multi-stage bounded-variation norm divergence
and the proposed sign-ordered decomposition remain separate unformalized
follow-ups in `RH/QParityHeadContinuationResearch20261020.md`.

### Actual rational coefficients and cofinal squarefree closure dependencies (2026-10-20 UTC)

Established after this change's successful server checkpoint:

- `RH/QRationalCoefficientLimit.lean`: continuous extraction from the full
  divisor synthesis, eventual identification of the actual selected rational
  coefficients at each squarefree m>=2, and unconditional convergence to the
  existing complete-Q projection coefficient lambda_m. Simultaneous convergence
  to -mu(m) is equivalent to qOne in the squarefree closed span.
- `RH/QRationalTailDirichlet.lean`: actual residual-tail first differences,
  positive site weights, exact weighted difference energy E_L-5/(3L^2),
  equality with the initial centered tail for a normal solution, an individual
  difference bound, and specialization to the selected rational minimizer.
- `Analysis/FiniteWeightedTailCharge.lean` adds
  `cofinal_absorption_iff_zero_limit`, using an explicitly supplied energy
  limit and exact signed identity.
- `RH/QRationalSignedTailClosure.lean`: complete signed identity retaining
  the Q projection error, optimizer displacement, and rational-weight gap;
  an explicit full-Q optimizer error bound under a finite signed budget;
  and equivalence between cofinal fixed-factor signed absorption and closure.

Conditional research reduction: `closure_of_cofinal_signed_budget`.
Open providers: a fixed theta<1, errors epsilon_n->0, and cofinally valid
S_(L_n)>=-theta E_(L_n)-epsilon_n for the actual rational minimizers.
The equivalence theorem does not establish this arithmetic input.
The alternative identification lambda_m=-mu(m) remains Open.

Targeted job `job_YvilkfIZOAr6G2fp5uYHveRqsPeJe7sm` succeeded with exit 0;
five principal axiom inspections used only propext, Classical.choice, Quot.sound.
The final checkpoint determines integrated publication verification.
Exact Wolfram checks stop at the seventh primorial 510510: all divisor
incidence/charge identities at seven levels, 543105 full-period Mobius
synthesis cases, and 543102 canonical CRT-carry cases, with no failures.
These are finite algebra checks, not optimizer solves or limit estimates.
See `RH/QSquarefreeClosureDependencies20261020.md` and
`RH/WolframSeventhPrimorialChecks20261020.md`.


### Complete-Q metric refinement and actual logarithmic targets (2026-10-20 UTC)

Established results after this change's successful server checkpoint:

- `RH/QRationalPeriodRefinement.lean`: a retained positive midpoint defect
  gives a two-sided complete rational-weight gap and the coefficient-independent
  estimate `Gap_(kL)(f) <= (120/k) Gap_L(f)` for every L-periodic vector.
  Ratios at least 240 halve this gap.
- `RH/QRationalStageGain.lean`: actual rational normal-equation minima satisfy
  an exact cross-stage identity retaining signed metric refunds and the full
  later-metric optimizer displacement. A telescoping finite budget controls
  half the old gap plus this displacement at ratios at least 240.
  This displacement is not the complete-Q projection gain.
- `RH/QParityLegalGain.lean`: exact legal capture of the parity projection in
  nested spaces; new projection gain is `(1-4D_V)^2 (D_V-D_W)`.
  The explicitly computed component already in the old space is not new gain.
- `RH/QPrimePowerTwoStage.lean`: actual legal two-stage logarithmic-head
  interpolation, complete signed norm and correction identities, feasibility
  of every finite logarithmic head, and norm divergence with the first cutoff
  fixed.
- `RH/QPrimePowerConstrainedHead.lean` and the generic extension in
  `RH/QResidueHeadSpace.lean`: actual full-divisor-dictionary constrained
  optimizers, exact inverse-Gram energy, Pythagorean minimality for every
  feasible vector, and exact fixed-head energy decrease under nested periods.
- `RH/PrimePowerHilbertTarget.lean`: construction of the actual target
  `F_p(n)=Nat.log p n` by a Hilbert-space contraction for p>1, with Pareto
  mean `1/(p-1)` and exact norm square `(p+1)/(p-1)^2`.
- `RH/PrimePowerTargetMellin.lean`: actual Q target, norm comparison, and
  normalized Mellin transform `s M_s(F_p)=1/(p^s-1)` for Re(s)>1/2.
  Membership of this target in the squarefree Q closure implies RH.
- `RH/QExactHeadAverages.lean` and
  `RH/QPrimePowerInterpolationClosure.lean`: bounded actual legal target
  heads imply closure membership. Both flexible periods and an internally
  feasible selected logarithmic-head optimizer family have conditional RH
  consumers. The uniform complete-Q energy bound remains an explicit,
  unproved hypothesis.
- `RH/QPrimePowerTargetJumps.lean`: squarefree-divisor and positive-power
  jump constraints for the actual logarithmic target. These are necessary
  relations, not a sufficiency criterion for closure.
- `RH/QPrimePowerSieveEnergy.lean`: complete target energy sharpens the raw
  sieve lower bound to
  `||A_H||_Q^2 >= a_H^2 H/(2 zeta(2)) - 6/zeta(2)`, with the exact signed
  finite-head identity retained before the bound.
- `Analysis/FinitePrimeProductBounds.lean` and
  `RH/ZetaTwoParetoTransfer.lean`: supporting positivity and generic
  squarefree-closure-to-Pareto-closure transfer.

**Open:** `1 in H`, vanishing of the projection defect D, a uniform bound
for the actual moving-head constrained minima, and the signed absorption
estimate. None of the new conditional consumers proves these hypotheses.
The earlier published logarithmic-target status is superseded only for
target construction, its norm and Mellin transform; closure membership
remains open.

Exact finite symbolic checks covered 41 logarithmic-head coordinates through
the seventh primorial 510510. They neither compute all seven rational minima
nor establish an infinite energy bound. See
`RH/QLogarithmicTargetsAndMetricRefinement20261020.md` for formulas,
verification scope, provenance, and the remaining analytic obligations.


### Squarefree cylinders, rational variational limits, and exact obstructions (2026-10-20 UTC)

Established results after this change's successful server checkpoint:

- `NumberTheory/SquarefreePowerCongruence.lean`: positive powers identify
  equal gcd classes modulo a squarefree modulus; positive-periodic,
  power-invariant functions therefore have gcd-class values.
- `RH/PeriodicDivisorJumps.lean`: exact finite Mobius reconstruction and
  integration of gcd-class jumps, retaining the slope before periodicity
  eliminates it.
- `RH/QSquarefreePeriodicJump.lean`: the actual complete-Q squarefree legal
  closure preserves equal-squarefree-divisor jump relations and positive-power
  jump invariance.
- `RH/QSquarefreeCylinder.lean`: for squarefree L>0, every physically
  L-periodic member F of the legal closure has the exact decomposition
  F=F(L)*qOne+v with v in the full divisor stage V_L. A zero endpoint puts F
  already in V_L; a nonzero endpoint forces qOne into the legal closure.
  Conversely, the gcd-jump representation isolates this constant-membership
  obligation exactly.
- `RH/QRationalWeightComparison.lean`: exact midpoint telescoping retains
  the positive defect and endpoint remainder. The complete residue weights
  satisfy zeta(2)*w <= u <= (5/3)*zeta(2)*w. The rational objective equals
  the complete-Q objective plus its nonnegative finite weight gap. For each
  fixed competitor with residual bounded by B, that gap is at most 2*B^2/L.
- `RH/QRationalMinimumLimit.lean`: actual divisor normal-equation solutions
  define attained rational minima R_n at the primorial periods L_n. The
  finite synthesis range is exactly the Q primorial stage. If p_n is the
  finite Q optimizer and f_n the selected rational optimizer, the full
  decomposition is
  R_n=zeta(2)*E_n+zeta(2)*||f_n-p_n||^2+gap_n.
  Put K=the closed squarefree legal span, P=projection_K(qOne), and
  D=||qOne-P||^2. The actual minima satisfy R_n -> zeta(2)*D, unconditionally.
  The proof fixes an earlier legal Q competitor before increasing the period;
  it assumes no bound on the moving optimizer's coefficients. The condition
  R_n -> 0 is equivalent to qOne in K.
- `RH/QRationalMinimizerConvergence.lean`: the rational weight gap at the
  actual moving minimizer tends to zero, ||f_n-p_n||^2 tends to zero, and
  f_n -> P in the complete Q norm. The actual Q errors tend to D. Convergence
  f_n -> qOne is equivalent to qOne in K; neither conclusion assumes it.
- `RH/QRationalSignedTailLimit.lean`: for every positive L, the selected
  rational minimizer satisfies the exact signed identity
  R_L+S_L=5*phi(L)/(3*L^2). The endpoint tends to zero on the primorial chain,
  so S_n -> -zeta(2)*D. Every finite R_n is positive, and the exact ratio
  identity S_n/R_n+1=(5*phi(L_n)/(3*L_n^2))/R_n retains the boundary term.
  Under the explicit hypothesis D>0, S_n/R_n -> -1. Signed-tail convergence
  to zero is equivalent to qOne in K.
- `RH/QModThreeConditionalObstruction.lean`: the literal complete-Q
  conditional image C_3 g_2 has a four-site defect J>=1/3. Its squared
  distance from every legal closure element is at least 1/(270*zeta(2));
  the exact witness decomposition retains the orthogonal norm-square
  remainder. The input g_2 is legal and its actual conditional image is not.
- `RH/QPrimorialSixConditionalObstruction.lean`: at the actual
  primorial period six, the complete-Q conditional image C_6 g_5 has signed
  four-site defect J<=-1/40. Four fiber terms are evaluated exactly and the
  entire remaining tail is retained before its certified rational bound.
  Its squared distance from every legal closure element is at least
  1/(48000*zeta(2)), with the full orthogonal remainder in the exact identity.
  The input g_5 is legal and its actual conditional image is not. Thus the
  failure of general conditional-expectation preservation occurs at an
  actual primorial stage, independently of RH.
- `RH/QParityProjectionDefect.lean`: for a projection space V containing
  g_2, the actual parity projection of r=qOne-projection_V(qOne) is exactly
  4*||r||^2 times the even indicator. The optimizer's exact parity leakage is
  ||r||^2*(1-4*||r||^2). Containing g_3 gives the strict bound ||r||^2<1/4.
  For the actual infinite legal optimizer P, physical two-periodicity is
  therefore equivalent to qOne in K. This is an exact iff, not an established
  periodicity provider.

- `RH/QSixAtomTrialBound.lean`: the legal trial g_2+g_3+g_6 has exact
  complete-Q error w_6(5)+1/36 <= 61/900. Thus D<=61/900 and the actual
  limiting optimizer satisfies (164/225)*D <= ||P-C_2 P||^2 <= D.
- `Analysis/PrimeProductDyadicGrowth.lean`: the existing elementary finite
  prime-product cube bound yields (4/225)*4^m <= a_(64^m)^2*64^m. An
  exponential term absorbs the retained quadratic finite-head error.
- `Analysis/PrimeProductHeadGrowth.lean`: monotonicity extends this rate
  to every positive cutoff: a_H^2*H >= 4^(Nat.log 64 H)/900. Consequently
  a_H^2*H/(2Z)-(Nat.log 2 H)^2 tends to infinity for each fixed Z>0.
- `RH/QPrimePowerSieve.lean`: actual divisor-incidence coefficients select
  the gcd-p class and define a legal finite residue synthesis A_(p,L).
  Its physical sequence is exactly count{m<=n:gcd(m,L)=p}-a_(p,L)*n,
  with exact slope phi(L/p)/L. Under concrete prime coverage, the count
  equals Nat.log p n in the finite head and the full Q norm satisfies
  ||A_(p,L)||^2 >= a_(p,L)^2*H/(2*zeta(2))-(Nat.log p H)^2.
- `RH/QPrimePowerPrimorial.lean`: all coverage and slope obligations are
  discharged for the actual gcd-two primorial synthesis A_H. It belongs
  to the squarefree span, converges at each physical coordinate to
  Nat.log 2 n, and its complete Q norm tends to infinity as H tends to
  infinity through ALL natural cutoffs. These are unconditional results.
  Existing `FinitePrimeProductBounds` is reused; this family differs from
  the earlier first-coordinate family in `PrimeSievePointEnergy`.

Conditional research reduction:

- `QParityProjectionDefect.riemannHypothesis_of_limiting_optimizer_two_periodic`
  applies the existing Q-to-Pareto/RH transfer. Its substantive obligation is
  Open: physical two-periodicity of the actual limiting optimizer. The proved
  iff shows that this premise already entails the original constant-membership
  conclusion; the parity calculation does not discharge it.

Open: prove D=0, equivalently qOne in K. The rational-minimum, rational-optimizer,
weight-gap, and signed-tail limits above are now formal results, but their
existence does not force the limiting defect to vanish. Signed coprime-tail
absorption with a fixed coefficient below one, or sufficient divergent
normalized prime-plus-carry gains, still needs an actual checked provider.
The C_3 and C_6 counterexamples rule out general preservation of legality by
residue conditional expectations as such a provider. The concrete pointwise sieve family cannot supply a norm-bounded
approximation. The broader prime-power target membership, Mellin reduction,
and positive-averaging discussion in its note are ordinary arguments, not
new formal provider theorems. No unconditional RH theorem is claimed.

See `RH/QCylinderContinuationResearch20261020.md` and
`RH/PrimePowerTargetsResearch20261020.md`.

### All gcd-class rational tail charges (2026-10-20 UTC)

Established finite results:
- `NumberTheory/DivisorIncidence.lean`: concrete divisor-Mobius left inverse
  and specialization of the generic finite incidence extractor to gcd labels;
  positive gcd-class cardinalities phi(L/e); endpoint class C_L={L}.
- `RH/QRationalGcdTail.lean`: actual divisor normal equations imply every
  gcd-class charge 5*phi(L/e)/(3*L^2), common literal average 5/(3*L^2),
  zero centered class sums, exact classwise and full-period square
  decompositions, and endpoint tail. `exists_all_class_minimum` assembles
  these for an attained global minimum with no unresolved normal equations.
- `Analysis/FiniteSignedVariance.lean`: finite signed variance budgets.
  The actual coprime specialization proves 4*N*(N+phi(L)*c_L)<=phi(L)*V,
  retaining all signs and the full centered-square sum V.

Open: an actual asymptotic upper bound strong enough to control N-P,
the signed absorption estimate, and rational-to-complete-Q limiting assembly.
No unconditional RH theorem follows from finite centering.
See `RH/QRationalGcdTailResearch20261020.md`.

### Actual CRT gain and parity-conditional closure (2026-10-20 UTC)

Established:
- `Analysis/ScreenedBlockGain.lean`: actual nested projection score/trace
  inequality and its positive-denominator consequence, with no independence
  or inverse Gram assumptions. Reuses the existing Pythagorean identity.
- `RH/QCRTCarryGain.lean`: literal floor-carry full-divisor block scores
  bounded by actual complete-Q stage gains; exact separation of prime and
  carry increments; `prime_gain_add_score_div_le_total_gain` retains both.
  Empty blocks are covered by the division-free statements.
- `RH/QParityConditionalTarget.lean`: complete parity conditional image
  of legal `g_6`; positive constant coefficient; exact screen/energy scaling;
  its membership in the squarefree closed span iff `qOne` membership;
  preservation of that closure by the fiber-mean parity map iff the same
  constant membership. Finite-stage error identity included.

Conditional research reduction:
- `riemannHypothesis_of_paritySix_mem_closure` consumes the unresolved
  membership of that one conditional image. This hypothesis remains Open.
- Actual divergence of combined prime-plus-carry normalized scores remains
  Open. No unconditional RH theorem or new RH-to-closure provider is claimed.

`RH/QCRTProfiniteResearch20261020.md` records the theorem scope, exact rational
Wolfram checks, complete-Q high-precision checks, and ordinary (not Lean)
proofs of quantitative full-cylinder approximation and Haar/Q density growth.

### CRT carry blocks and actual rational-weight minima (2026-10-19)

Established finite results:
- `RH/QRationalCoprimeMinimum.lean`: `exists_signed_minimum` constructs an
  attained minimum for every positive period, with no normal-equation
  hypothesis. `divisorFit_completion` retains the exact weighted square
  remainder for every competing divisor fit. Coefficients are real;
  rationality is not asserted by this formalization.
- `RH/QRationalCoprimeLegality.lean` and `RH/QRationalCoprimeTail.lean`:
  actual Mobius/centered-prefix synthesis, endpoint and fitted-vector
  normal equations, and E+S=5*totient(L)/(3*L^2), with every signed tail
  and the zero residue retained. All divisors participate.
- `RH/QCarryScreenedBlock.lean` and `Analysis/FiniteGramBlockTrace.lean`:
  actual Q screening and representative invariance, complete new-prime
  block span, exact inverse-Gram gain, and aggregate-score/trace bounds.
- `Analysis/ConditionalGainGeometry.lean`: exact conditional energy split,
  I^2 <= D*J, J <= I, and zero gain if conditioning lands in the old legal
  space, under the displayed projection hypotheses.
- `Analysis/FiniteWeightedTailCharge.lean` and
  `Analysis/FiniteIncidenceTailCharge.lean`: finite signed Fubini,
  absorption algebra, generic incidence inversion, exact Jordan charge,
  and centered square decomposition.
- `RH/QBoundedCollapseRate.lean`: complete-Q cutoff/rate estimates from
  explicit global-amplitude and physical-head-slope bounds.

Open research obligations: actual asymptotic signed absorption or cumulative
relative-gain divergence; rational-to-Q comparison/convergence assembly;
full Haar optimizer and product-bound specialization; concrete Q-cylinder
specialization; screened dictionary independence assembly. The former concrete
all-gcd Mobius and class-cardinality gap is discharged by
`NumberTheory/DivisorIncidence.lean` and `RH/QRationalGcdTail.lean`, including
an attained-minimum assembly; see the 20 October all-class entry above.
No unconditional RH theorem is asserted. The Python and Wolfram checks are
finite arithmetic evidence, not asymptotic estimates or Lean certificates.
See `RH/CRTCarryVerificationResearch20261019.md` and its exact experiments.

### Squarefree LCM block balance and sublinear affine energy (2026-10-19)

Established:
- `RH/QSquarefreeHeadSchedule.lean`: feasible natural primorial head chain,
  nearby divisor anchors H<r<=2H, and the missing-prime obstruction.
- `RH/QSquarefreeBlockBalance.lean`: actual inverse-Gram head costs evaluated
  in the exact cost-minus-gain telescope, the signed weighted-defect bound,
  and equivalence of a uniform energy bound with the exact signed budget.
- `RH/QPeriodicBlockComparison.lean`: exact first-period refinement and
  compensating complete-tail decrease for the same residual, two-sided
  complete-energy bounds, and the signed tail mixed term for changed profiles.
- `RH/QSquarefreeAffineEnergy.lean`: complete quantitative comparison with
  canonical exact heads; unconditional actual constrained energy E_H=o(H)
  and signed cumulative cost minus gain o(H). Reuses the checked PNT-based
  cancellation and the October 19 complete-Q conductor estimate.

Conditional research reductions: `rh_of_signed_budget`,
`rh_of_weighted_defect_budget`, `rh_of_weighted_partial_sums`, and
`rh_of_cofinal_signed_budget`. Open: provide the displayed uniform signed
budget, at least along cofinal endpoints. Sublinear energy does not give it.
The fixed primorial diagonal is not proved equivalent to RH in both directions.
Exact rational complete-tail certificates cover twelve finite heads; these
host computations are distinct from Lean kernel checks of the general results.
See `RH/QPrimorialBlockBalanceResearch20261019.md`.

### Balazard triangular dual refinement (2026-10-19)

Established:
- `Analysis/EscapingRieszDirections.lean`: normalized weak escape
  now allows convergent fixed generator pairings, extending eventual equality.
- `RH/QTriangularTargetDirection.lean`: directionCapacity_atom_bound
  retains the exact complete-Q one-atom capacity lower estimate.
- `RH/QSquarefreeTriangularEscape.lean`: the actual squarefree prefix
  dictionaries discharge retention; along escaping squarefree stage indices,
  gain tends to zero and the complete scalar-fit error tends to one.
- `RH/QTriangularCoefficientProbe.lean`: exact adjacent second
  differences recover native-Q coefficient functionals and legal biorthogonality.
- `RH/QTriangularDualDensity.lean`: the complete triangular dual
  dictionary is ambient-Q dense and its finite projections converge.
  Dual density does not assert legal membership or prove RH.
- `RH/QTriangularRayleigh.lean`: exact legal scalar fit from G^{-1}v;
  its complete target error is 1-B^2/A, the scalar optimization retains
  A(a-B/A)^2, and comparison with the actual target projection retains
  the full squared-norm gap. No asymptotic Rayleigh provider is assumed.
- `Analysis/FiniteKernelEnergy.lean`: exact finite variance identity.
- `Analysis/TriangularOverlapKernel.lean`: actual nonnegative
  reciprocal overlap matrix with exact row and column masses.
- `Analysis/QuotientFiberRamps.lean`: finite integer quotient
  regrouping and its exact real ramp representation.
- `RH/MobiusTriangularEnergy.lean`:
  `triangularChargeRiesz_energy_identity` retains the complete variance;
  `triangularChargeRiesz_norm_sq_le` bounds the actual norm by e_N;
  `triangularChargeRiesz_tendsto_zero` proves unconditional strong
  convergence. Bounded moving tests, and the more general vanishing
  e_N times squared test-norm condition, are covered.
- `RH/QTriangularCharge.lean`: actual Q coefficient pairing,
  sharp zeta(2) squared-norm comparison, arbitrary moving squarefree
  optimizer/residual stages, exact legal finite-sum evaluation, and
  `coefficient_direction_sq_le` for the direction 1-1/d.
- `RH/QTriangularInverseGram.lean`: `inverseGram_direction_le` proves
  the actual bound v^T G^{-1} v <= zeta(2) N^2 e_N for every finite
  distinct dictionary with 2 <= d <= N, where v_d = 1-1/d.

- `RH/QTriangularRieszEnergy.lean`: actual Q Riesz coordinates and
  pairing, exact metric-change remainder W_N, full zeta(2)e_N energy
  identity with V_N and W_N, unconditional strong Q convergence, and
  the sharp moving-test inequality retaining both remainders.
- `RH/QTriangularInverseGram.lean`: `inverseGram_energy_identity`
  retains the orthogonal projection remainder as well as V_N and W_N;
  `inverseGram_direction_le_exact` sharpens the finite bound to
  v^T G^{-1}v <= zeta(2)N^2(e_N-V_N-W_N).
  `target_charge_residual_certificate` is a lower target-error certificate,
  and `direction_target_gram_cauchy` bounds the mixed inverse-Gram pairing.
  Escaping target means tend to zero while v_d tends to one, ruling out a
  fixed nonzero scalar identification along escaping conductors.

The native-Q Riesz and inverse-Gram norm-decomposition obligations are
discharged.
- `RH/QTriangularTargetMean.lean`: exact target charge tau_N, finite
  Abel evaluation, exact e_N=tau_N^2+variance, and unconditional tau_N->0.
- `Analysis/EscapingRieszDirections.lean`: norm escape from vanishing
  tests and weak zero of normalized representers with fixed generator pairings.
- `RH/QTriangularTargetDirection.lean`: normalized Rayleigh gain tends
  to zero for retained dictionaries with an escaping conductor.
- `RH/QPrimorialChargeDirection.lean`: actual squarefree primorial divisor
  dictionaries discharge all retention and escape hypotheses.
  `primorial_rayleighGain_tendsto_zero` and
  `primorial_rayleighFit_error_tendsto_one` rule out the single-direction
  gain->1 route. The full legal approximation problem remains open.
- `RH/QTriangularRayleigh.lean`: the norm and error identities now also
  cover zero capacity, without a nonvanishing hypothesis.
See `RH/QTriangularDirectionEscapeResearch20261019.md`.

RH research Open: bounded complete energy of legal exact-head candidates,
or another argument forcing the optimal residual energy to zero.
Uniform triangular cancellation is automatic for bounded ambient tests
and does not discharge this obligation.

### Damped Möbius signed P/Q discrepancy (2026-10-19)

Established:
- `RH/QMetricApproximateHeads.lean`: exact correction head/tail split,
  the full Pareto-tail upper bound, and harmonic/logarithmic control
  for approximate physical heads.
- `RH/DampedMobiusMetricDiscrepancy.lean`:
  `q_residual_head_identity` retains the finite reciprocal charge;
  `q_residual_head_abs_le_envelope` proves the sharper endpoint bound
  B=max(|A|,|A-epsilon log H|).
  `q_residual_discrepancy_le_signed_head_tail` proves
  D <= B^2 log(H+1)+(E_P-E_head)/(H+1) for actual damped squarefree
  vectors, without RH. The exact complete discrepancy is retained.

Conditional research reduction:
`q_residual_norm_ratio_tendsto_one` gives zeta(2) E_Q/E_P -> 1
when H grows, E_P>0, and B^2 log(H+1)/E_P -> 0.
Open: supply that relative-head budget for the intended diagonal in Lean.
Open: prove unconditional complete approximation-error decay sufficient
for RH. A small discrepancy or asymptotic ratio does not supply decay.
The second-order Chebyshev discrepancy remains an ordinary RH-conditional
argument, not a checked theorem here.
See `RH/DampedMobiusMetricDiscrepancyResearch20261019.md`.


### Q conductor coefficient mass and scaled signed carries (2026-10-19)

Established:
- `RH/QConductorCoefficientMass.lean`: exact complete-Q conductor
  head/tail split; `qResidue_norm_sq_le_two_div` proves
  ||g_d||_Q^2 <= 2/(zeta(2)d). `qResidue_sum_norm_le_mass` and
  `qResidue_sum_mass_lower` give the finite signed-combination bound and
  necessary mass (1-epsilon)sqrt(zeta(2)D/2), without squarefree assumptions.
- `RH/QCarryCoefficientEnergy.lean`: upper bound for unscaled step
  carries, normalized-carry two-sided energy bounds, squarefree legality,
  pointwise and weak zero limits, and the error-minus-energy limit one.
  Scaled packets with both conductors escaping have uniformly bounded
  complete Q energy and coefficient mass of order sqrt(D); the existing
  general conductor-escape theorem proves their zero weak limit.

Open: a growing squarefree legal exact-head family with uniformly bounded
physical Q energy has not been constructed. The new packets accommodate
coefficient growth but do not approach one. Exact conditional and Fourier
identities retain signed cancellations; the required arithmetic estimate
on the selected combined profiles remains Open.
See `RH/QCoefficientMassCarryResearch20261019.md`.


### RH next-head costs and complete periodic tails (2026-10-19)

Established:
- `RH/QSquarefreeHeadStep.lean`: exact physical one-site observation,
  positive actual inverse-Gram capacity, correction completion with its norm
  remainder, and exact finite-stage cost `minimumError_single_head_cost`.
  `minimumError_single_head_near_anchor_bound` bounds that actual cost by
  4 delta_n^2 / (zeta(2)(n-1)) for n<r<=2n. The full inverse Gram form retains
  every old zero-head conductor and its signed interactions.
- `RH/NormalizedResidueExactHeadCharges.lean`:
  `residueFraction_exact_head_next_coefficient` identifies delta_n=c_n+mu(n).
  The head-step module specializes its cost bound to actual optimizer
  coefficients.
- `RH/QPeriodicTailEnergy.lean`: exact first-period plus complete-tail
  decomposition, two-sided bounds by the unweighted period energy over L^2,
  and `periodicTailEnergy_tendsto_zero_iff`.
- `RH/QResidueConditional.lean`: `carry_square_atom` and
  `carry_norm_sq_lower` give the linear-in-p lower bound for a fixed-d
  individual unscaled step carry; combinations retain signed mixed terms.
- `Analysis/FiniteGramCapacity.lean`: scalar constrained completion for an
  arbitrary prescribed value and the energy of its scaled minimum vector.

Conditional research reduction / Open: the bounded-affine-minima RH
consumer still needs an actual uniformly bounded squarefree legal family.
Neither a uniform signed cost/gain balance nor a sufficient coefficient-
defect budget along growing feasible stages has been proved. These local
bounds do not close RH. See `RH/QHeadStepTailResearch20261019.md`.

### Squarefree profinite Q targets: finite arithmetic and open estimates (2026-10-19)

Established:
- `RH/QResidueConditional.lean`: complete progression-weight consistency,
  positive normalized alpha weights, old-modulus conditional means for every
  new divisor conductor and integer step carry, exact signed conditional Gram
  decomposition, multiples scaling, and the zero-fiber leakage floor.
- `RH/QPrimeCRTCarries.lean`: constructed canonical prime CRT coefficients,
  their bounds and modular certificate, exact integer floor carries, literal
  legal Q representatives, and their complete finite conditional formula.
- `NumberTheory/ResidueRelationLattice.lean`: actual kernel, quotient/index L,
  and existence/uniqueness of integral coordinates in the full-period basis.
- `RH/QUniformNormalizedAverages.lean`: exact uniform common-period error
  and its 1/M bound; physical identification of the same Q averages; uniform
  error tending to zero and complete-Q error tending to one.
- `RH/QFourierKernel.lean`: absolutely convergent linear-first Fourier Gram,
  finite DFT legal-residue Gram formula, entrywise bound, and exact complete
  frequency-block cancellation.
- `RH/QSquarefreeAffineHead.lean`: exact head costs and period gains with
  their joint telescope; a nonsquarefree next head site changes neither the
  feasible constraints nor the optimizer or its complete Q minimum.

Conditional research reductions and Open obligations:
the existing bounded-exact-head RH consumer still requires a uniform
complete-Q bound on an actual legal family. The new cost/gain telescope
does not provide that bound. Legal Schur exhaustion and growing legal-block
estimates remain Open. The complete Fourier block includes its constant
frequency and is not asserted to be a legal approximation. The source's
prime-coordinate lattice-basis conversion and optional inverse-limit
formalization are not supplied here.

See `RH/QProfiniteTargetsResearch20261019.md` for exact scope, provenance,
declaration names, and the distinction between finite uniform and Q geometry.

### Balazard--de Roton signed critical-line error (2026-10-19)

Established: `RH/ParetoBoundedMellin.lean` supplies bounded-vector Mellin
integrability and finite linearity on Re(s)>0, including the critical line.
`RH/BalazardDeRotonCriticalEnergy.lean` proves the actual finite damped
Möbius residual formula with its reciprocal charge, the complete
critical-line norm identity `critical_energy`, and
`criticalApproximation_iff_hardy`. The signed identity `signed_energy`
retains the mixed integral, and `factor_two_exact_gap` retains the entire
nonnegative remainder. Component L2 assumptions are explicit in both.

Conditional research reductions:
`riemannHypothesis_of_criticalApproximation`,
`qSquarefreeClosure_of_criticalApproximation`, and
`riemannHypothesis_of_signed_budget` consume an arbitrarily small complete
boundary-energy budget. Open: a provider proving that budget, or the signed
version with its component L2 conditions, without RH. The paper's
RH-conditional analytic estimates are not formalized or assumed as axioms.
See `RH/BalazardDeRotonResearch20261019.md` for the paper audit,
normalization, exact formulas, source corrections, and research agenda.

### Complete Q Mellin witness and strict B-factor improvement (2026-10-18)

Established: `Analysis/ReciprocalCellAbel.lean` proves the exact finite and
infinite Abel identities, shifted boundaries, and complete remainder
identities. `RH/WeightedPowerCellMass.lean` discharges summability and the
vanishing boundary for actual power cells, proves their exact B(beta)/(2 beta-1)
sum, identifies B(beta)=sum n^(-2 beta)/(n+1), and proves 1/2 < B(beta) < 1.

Established: `RH/QMellinCellEnergy.lean` proves the actual Q/P cell-energy
identity, complete positive correction, sharp B-factor upper envelope,
and equality with the entire nonnegative cell remainder retained.
`RH/QMellinWitness.lean` represents the signed functional by a convergent
series on actual QHilbert, proves its weighted norm bound and positive
energy, and proves the resulting finite legal-error lower bounds at a
hypothetical zeta zero Re(s)>1/2, s != 1. These are zero-obstruction
theorems, with the zero hypothesis explicit; no analytic provider is assumed.
The B-factor lower constant strictly exceeds the old global-transfer
constant. Finite prefixes of actual cell slack give further certified bounds.

Open: the complete unconditional legal-error upper estimate needed for RH.
The real Q-to-complex functional is bounded; equality with its real operator
norm is not claimed. The closed-span extension and the appendix's additional
elementary bound B(beta)<=(2 beta+1)/(4 beta) are not new Lean theorems here.
Research record: `RH/QMellinWitnessResearch20261018.md`.

### Burnol exact finite rates and Q cutoff transfer (2026-10-18)

Established unconditionally: `Analysis/FiniteTwoMomentEnergy.lean` proves
exact two-moment energy decomposition, its lower bound and attainment.
`RH/BurnolDoubleRootModel.lean` proves the real coefficient-space
double-root identity and the attained cubic target minimum
12/[L(L+1)(L+2)], preserving the complete nonnegative remainder.
The polynomial divisibility and circle-Parseval bridge remains an ordinary
proof in the research record, not a specialized Lean theorem.

Conditional research reduction: `RH/BurnolParetoTransfer.lean` now handles
arbitrary finite legal candidates; `RH/BurnolQCutoffTransfer.lean` transfers
the continuous cutoff lower envelope to actual Q error while retaining the
exact metric correction. The maximal conductor is unchanged, including
for squarefree subsets. Open: a Lean provider of Burnol's analytic envelope.

Ordinary proofs, not Lean-verified here: general target-jet rates, exact
repeated-root factorial formula, fixed-zero-family second-order bound,
and additional elementary Q-envelope and tail refinements. The central
Q Mellin B-factor witness bound is now established in the entry above.
Open: the unconditional complete legal error upper estimate needed for RH.
No RH proof is claimed.
Research record: `RH/BurnolRatesResearch20261018.md` and its two appendices.

### Baez-Duarte 2002 audit and Bombieri smoothing (2026-10-18)

Established, unconditional: `RH/BombieriSmoothing.lean` proves the exact
arbitrary-damping linear-cutoff head identity, squarefree coefficient
support, signed finite-head Q energy, and variance-plus-square formulas.
It retains the damping defect, mixed term, and moment square.
`divisorMoment_three` and `divisorMoment_ninetyFive` certify -2 and 67;
the divisor moment has no fixed sign. `seed_two_eq_zero` shows why smoothing
cannot be assumed to improve every finite cutoff.

`RH/BaezDuarteCellEnergy.lean` proves 0 <= m(n) <= 1/2 for the actual
reciprocal-cell first moment, its integral identification, the exact
nonnegative polynomial remainder, and the infinite weighted factor-5/4
energy comparison under ordinary moment and summability hypotheses.

Open formal integration: the complete reciprocal partition and variance
identity connecting that model to `naturalError`. The full factor-5/4
continuous-to-Pareto transfer has an ordinary proof in the research record,
but is not yet claimed as a specialized Lean theorem.
Open analytic obligation: finite canonical damped energy for arbitrarily
small positive damping, or a complete smoothing error bound including the
infinite tail. Neither follows from these finite identities.

Historical RH-dependent rate improvements are documented with their original
hypotheses; they are not asserted as newly formalized analytic providers.
Research record: `RH/BaezDuarte2002Research20261018.md`.

### Bagchi audit and exact Q dilation energy (2026-10-18)

Established, unconditional: `RH/QFloorDilationEnergy.lean` retains exact
finite and infinite quotient-block energy and its nonnegative remainder.
`floorDilation_norm_sq_le_sharp` improves the previous 2/m Q bound to 1/m.
`floorDilation_pareto_defect_le` and its half-bound quantify recovery of
the Pareto quadratic form with complete infinite tails and O(1/m) error.
`floorDilation_normalized_energy_tendsto` proves the resulting limit.
`floorDilation_relative_energy_tendsto` shows that dilation preserves the
limiting relative error against the simultaneously dilated constant.

The source is Bagchi (2006), Theorem 7, for the dilation strategy; the Q
estimates are an elementary extension, with no novelty claim. The audit
also records the squarefree target/totality distinction and the needed
almost-everywhere and critical-line qualifications in the analytic proof.
The existing Burnol finite-energy criterion is identified, not duplicated.

Open: RH-to-squarefree-closure analytic providers and an unconditional
arithmetic estimate forcing vanishing constant-approximation error.
No RH conclusion follows from these dilation identities alone.
Research record: `RH/BagchiDilationEnergyResearch20261018.md`.

### Full-Pareto overshoot and signed innovation criteria (2026-10-18)

Established: `RH/ThresholdHilbertL1.lean` proves the complete negative mass is
1-Lipschitz, including its L1 difference bound. `RH/ParetoProjectionOvershoot.lean`
retains the exact residual-mean/overshoot identities, gives the finite
first-coordinate lower bound and limiting two-sided bounds, and proves
vanishing overshoot and residual L1 excess equivalent to zero limiting defect
and constant closure. The first nonempty finite stage has zero overshoot
and positive error, so only the limiting criterion is asserted.

`Analysis/ProjectionPairingVariation.lean` proves finite and infinite
two-gap pairing budgets and absolute summability for nested projections.
`RH/ParetoSignedInnovations.lean` retains each signed Schur summand, proves
absolute summability and its complete tail budget, and identifies the total
as minus the limiting first residual coordinate. Its vanishing is equivalent
to zero limiting residual.

Conditional research reductions: complete overshoot upper bounds with
coefficient below 1-sqrt(2)/2; ordinary residual or parity-optimizer first
coordinate upper bounds with coefficient below 2-sqrt(2); or a vanishing
signed innovation endpoint. Open: providers of these arithmetic estimates.
The optimizer dyadic specialization uses n -> 2*n+3 because n denotes M-3.
These reductions imply the project's RiemannHypothesis statement when their
explicit hypotheses are supplied. The classical RH-to-closure converse is
not newly formalized here. The floating-point Gram table remains exploratory.
Research record: `RH/ParetoOvershootSignedInnovationsResearch20261018.md`.

### Explicit period-210 strict budget and signed improvement (2026-10-18)

Established, unconditional: `RH/QPeriod210Certificate.lean` kernel-checks all
15 rational coefficients, squarefree legality, period 210, the exact maximum,
first value, rational derivative energy, normalization brackets, and complete
infinite primitive tail. `candidate_strict_certificate` proves
J_(1/10)(F)<3715960194137/38587500000000<1/10 in the actual Q-Hilbert space.
`stage_four_strict_budget` transfers this to the actual stage minimizer.

`RH/QPeriod210AffineCorrection.lean` retains the signed primitive cross term
and proves J_(1/10)(F+(1/3)g_11)<469/5000. The corrected trial is squarefree
legal at period 2310. Support modules `RH/QDifferenceGram.lean` and
`RH/QFiniteEnergyBounds.lean` provide complete derivative Gram identities
and rigorous square/mixed finite-head plus infinite-tail bounds.

Open: a cofinal legal family at lambda_N>0 tending to zero with
b_N²>q_N(J_(lambda_N)(u_N)-lambda_N), or the exact rational-step variant
b_N²-(q_N t_N-b_N)²>q_N(J_(lambda_N)(u_N)-lambda_N).
These are finite positive-penalty results, not a proof of RH.
Research record: `RH/QPeriod210CertificateResearch20261018.md`.

### Complete-Q exact-head energy audit (2026-10-18)

- `Analysis/InverseSquareTailCertificates.lean`: exact rational upper/lower
  step identities, finite telescoping bounds, summability, complete infinite
  inverse-square tail enclosures, and positive scaling. These certify the
  analytic remainder used by the exact-arithmetic Q-Gram calculator.
- `RH/QExactHeadEnergyCertificates.lean`: `exactHead_one`,
  `two_residue_error_sq`, `exactHead_one_error_sq` identify the actual H=1
  canonical trial and its complete error 1/4. `exactHead_residual_floor_tail`
  retains the signed Mobius tail and prime-anchor term at every tail site.
  `exactHead_error_window_budget` gives a quantified complete-Q budget with
  ordinary and reciprocal Mobius cancellation bounds explicit in its type.
- Accompanying calculation bundle: reproducible integer/rational numerical
  certificates for H=1 through 64 at selected stages. These numerical
  intervals are not individual Lean-verified numerical declarations.
- Research record: `RH/QExactHeadEnergyAuditResearch20261018.md`. The
  unconditional logarithmic rate improvement is derived mathematically
  from classical cancellation; the quantitative provider is not newly
  connected in Lean. Bounded/subpolynomial complete energy remains Open.
  The halted five-iteration sparse power-cost program remains closed.

### Strict finite primorial regularization certificates (2026-10-18)

Established: `Analysis/PrimitiveRegularization.lean` adds exact scalar-target
and signed line completions, strict-budget transfer through closure, and the
finite signed correlation certificate. `RH/QPrimorialRegularization.lean`
constructs the actual finite-stage normal solutions, retains every complete
regularized displacement square in stage comparisons, and proves strong
fixed-positive-penalty convergence to the closed-space normal solution.
Its `squarefree_constant_mem_iff_strict_primorial_budget` proves that squarefree
constant closure is equivalent to cofinal finite-stage values strictly below
the penalty, for any positive penalty sequence tending to zero.

Conditional research reductions: `riemannHypothesis_of_strict_primorial_budget`
and `riemannHypothesis_of_primorial_ray_certificates`. Open: a provider of the
strict complete-energy budgets or the signed certificates
b²>(a-lambda)(||Delta v||²+lambda||v||²). RH-to-squarefree-closure is an
external Bagchi Remark 8 input, not newly formalized. Project source passed
server job `job_P_eLBEpaKz8ssfTu89mTobUdIdHLDMKx`; all six selected axiom
reports contain only standard foundations. Final publication uses the checkpoint. Research record:
`RH/QPrimorialRegularizationResearch20261018.md`.

### Lattice cumulant coordinates and complete correction budgets (2026-10-18)

Established: `Analysis/SquarefreeCumulantCoordinates.lean` proves the exact
three-prime triangular composition and inverse laws, convolution exp/log
polynomial inverses, synthesized-range invariance, and legal synthesis.
`Analysis/PrimitiveRegularization.lean` adds the exact affine correction
identity q*J(u+t*v)=q*J(u)-b^2+(q*t-b)^2 and its strict-budget consumer,
including the signed primitive cross term in b.

`RH/QLatticeRegularization.lean` transfers the squarefree closure criterion
through arbitrary surjective finite-stage coordinates, proves three-prime
physical range/closure and objective invariance, and checks a four-site
counterexample to representing g2*g3 by g2,g3,g6. The counterexample concerns
that finite span, not the full closed squarefree space.

Conditional research reduction: `strict_value_of_correction_certificate`.
Open: complete signed certificates at vanishing penalties, general finite
Boolean convolution formalization, and an appropriate infinite-transform
norm bound. The period-210 rational full-tail certificate is now formalized in
`RH/QPeriod210Certificate.lean`, and its signed prime-eleven improvement is
formalized in `RH/QPeriod210AffineCorrection.lean` (see the entry above).
The general cover-matrix exponential and weighted coefficient
Banach-algebra arguments are paper results, not new Lean declarations.
Research record and reproducible Wolfram code:
`RH/QLatticeRegularizationResearch20261018.md`,
`RH/QLatticeFinitePatterns20261018.md`.

### Unit-signal all-conductor optimizer limit (2026-10-18)

`Analysis/UnitSignalProjection.lean` constructs the normalized optimizer from
Mathlib's orthogonal projection and gives its exact Pythagorean remainder,
uniqueness, defect formula, nested-stage difference, and norm convergence.
`RH/ZetaTwoParitySignal.lean` supplies the complete inverse-square multiples
mass, actual parity vectors, quarter target energy, and positive conductor-3
pairing. `RH/ZetaTwoUnitSignal.lean` instantiates the model on the actual
all-conductor stages (conductors 2 through n+3) and closed residue span.
`allConductorOptimizer_tendsto` gives unconditional norm convergence;
`allConductorLimit_error` identifies the limiting error as delta/(1-4*delta).
These statements do not assume or prove that delta vanishes.

Established continuation: `RH/QFloorDyadicEnergy.lean` reuses the existing
floor dilation and proves its exact complete even/odd energy decomposition
and the sharper squared-norm bound 1/2. `RH/ZetaTwoUnitSignalDilation.lean`
connects the unrestricted legal closure and finite cutoff doubling, proves
the signed head identity and complete two-scale slack decomposition, and
establishes `allConductorLimit_polynomial_detector` without additional
arithmetic hypotheses. The first-coordinate inverse-Gram formulas identify
the actual signed coefficient functional in the remaining scalar allowance.

Conditional research reduction: `Analysis/UnitSignalTwoScale.lean` gives
additive and quarter-allowance estimates from an explicit squared two-scale
hypothesis and a limit-zero criterion from an explicit polynomial detector.
The new actual finite and cofinal-subsequence consumers retain the scalar
lower allowance as a hypothesis. Open: its arithmetic provider. The limiting
quarter allowance is equivalent to zero error and constant closure, so it
remains a substantive RH-strength obligation. Uniform strict contraction at every
dyadic stage is obstructed by an external logarithmic lower bound; that
paper argument is recorded but is not formalized by these modules.

The four separate modules passed server job `job_gz3QFNBGiQj80LxZBDsVlHlig5_Dd4HE`
(exit 0); eight selected axiom reports used only `propext`,
`Classical.choice`, and `Quot.sound`. Final publication is gated by server
validation of the integrated source and exports.
[Scope, exact identities, and open obligations](RH/UnitSignalLimit20261013.md).
[Actual detector and inverse-Gram obligation](RH/UnitSignalDilationResearch20261018.md).
Provenance: supplied unit-signal manuscript, Sections 1--6; no novelty claim.

### Signed inverse-square tails and composite-gain location (2026-10-18)

- `Analysis/InverseSquareAbelTail.lean`:
  `InverseSquareAbelTail.centered_identity`,
  `centered_error_bound`, `periodic_centered_error_bound`,
  `finite_signed_error_bound` retain the exact signed mean and bound
  the complete centered tail by `B/(K+1)^2`. The two mass bounds and
  `weighted_sum_neg` give explicit complete-series sign certificates.
- `RH/QMeanTailEnergyCertificate.lean`:
  `QMeanTailEnergyCertificate.energy_difference_centered_tail` applies
  the estimate to actual Q-Hilbert norms with the prefix and full tail retained.
- `RH/QCompositeGainProfile.lean`:
  `QCompositeGainProfile.profile_period_mean` gives
  `-(10*t+31*t^2)/5400`;
  `positive_profile_translation_negative` proves strict negativity of
  every positive-step translated profile for `K>=110`;
  `quarter_translation_negative` gives `K>=63`.
  `profile_signedEnergy`, `profile_energy_series` connect the original
  profile to the actual legal B_4,B_5 Q line.
  `trial_gain_lower_refined`, `optimized_gain_lower_refined` improve the
  complete-Q finite saving to `1/(3100*zetaTwo)`.
  These translations are not asserted legal growing canonical heads.
  No below-one SPC exponent or infinite annihilator provider is obtained.
- Research record: `RH/QSignedTailScalingResearch20261018.md`.
  Separately authorized continuation; the original five-pass program stays closed.

### Quantitative reflected trials and escaping-support obstruction (2026-10-18)

Established: RH/QDivisibilityHilbertMoments.lean proves the full divisor
progression moment, divisor mass and norm d^(-2), exact lcm overlap, and
orthogonality of residue atoms to divisible progressions.

Established: RH/QReflectedFiniteStage.lean proves the exact shifted
reflected error with its signed mixed term; on the own-period divisor stage
the full error improves by exactly d^(-2), and the shifted trial stays in
that stage. Its binaryTrial is squarefree legal and has complete squared
error 1/4 + d^(-2) - 2/lcm(2,d)^2. It also proves the exact two-site
completed square and the complete-error lower bound
(c_2 - 1)^2/(8*zeta(2)); packets using only conductors at least three
therefore have error at least 1/(8*zeta(2)) for every d >= 3.
All these declarations passed a complete-module server check; the final
checkpoint is the separate publication gate.

External certificates, not Lean proofs: rational trials in divisor stages
6, 30, 210, 2310 have complete squared errors below
0.026990, 0.024290, 0.016848, 0.013550, respectively.
The research record preserves exact coefficients, integer-only checks,
and outward bounds on the entire periodic tails. Its general-H
escaping-support limit, Gram/projection corollaries, sharp distance
estimate, and primorial-sieve divergence arguments are mathematical
derivations, not newly formalized declarations.

Open: complete signed screened-packet gains sufficient for reflected
distance decay, or subpolynomial complete energy for the exhaustive
exact-head affine minima. Ambient convergence gives no legality.
The singleton approximation route remains excluded. No RH proof is claimed.
Research record: RH/QReflectedFiniteStageResearch20261017.md.

### Certified complete-Q composite-anchor gain (2026-10-17)

- `RH/QSignedEnergyCertificate.lean`:
  `QSignedEnergyCertificate.signedEnergy_summable`,
  `energy_difference_series`, `energy_difference_prefix_tail`,
  `energy_difference_lower`: signed full-Q differences with an exact
  prefix/tail split and a one-sided complete-tail certificate.
- `RH/QCompositeSixGain.lean`:
  `QCompositeSixGain.trial_gain_lower`, `gain_lower` certify a gain at
  least `1/(10000*zetaTwo)` from B_4 toward the legal composite-anchor
  B_5; `trial_legal`, `trial_exact`, `line_legal`, `line_exact`
  retain squarefree legality and the exact head through coordinate 4.
  `denominator_pos` and `line_completion` use the actual Q source
  and complete denominator. `physicalGain_prefix` and
  `physicalGain_lower` supply kernel-checked signed arithmetic.
  Finite provider only; no SPC exponent below one or infinite annihilator claim.

### Exhaustive squarefree canonical exact heads and prime-only incompleteness (2026-10-17)

Established: RH/SquarefreeCanonicalCoordinates.lean proves
coefficient_canonical_nonsquarefree, coefficient_squarefree_zero,
canonical_expansion_squarefree_mask, exists_finiteSpace_of_squarefree, and
exists_squarefree_canonical_affine_expansion in Pareto.CoefficientStabilization.
Nonsquarefree anchors in the full triangular expansion have zero coefficients
for squarefree-legal vectors, by the finite reciprocal-sum nonvanishing theorem.
The generic coefficient_normalizedResidue helper is in its owning
RH/MobiusCoefficientStabilization.lean module.

Established: RH/QSquarefreeCanonicalExhaustion.lean proves exists_affine_expansion:
every finite legal Q exact-head vector with H>=1 is a finite signed affine
combination of squarefree canonical anchors beyond H, with the full vector
unchanged. It also proves six_not_prime_expansion: the legal anchor-6 canonical
head is absent from every finite prime-anchor canonical linear family.

These are unconditional algebraic results. Prime-only incompleteness is not a
cost lower bound, and full squarefree exhaustion is not an upper energy bound.
Open: any SPC(a) provider for 0<a<1 and the infinite annihilator provider.
Research record: RH/QSparsePowerCostResearch20261017.md, historical iteration 4/5.
The fifth and final pass subsequently certified a finite complete-Q
composite-anchor gain (see the entry above). The five-pass program is complete
and halted; RH/QSparsePowerCostIterationState.json records its durable status.
Neither an exponent below one nor the infinite annihilator provider was obtained.

### Complete Q screened variance and finite common-quotient region (2026-10-17)

Established: RH/QCanonicalSchurVariance.lean proves
schur_quotient_variance_full_energy, schur_quotient_variance_le, and
schur_gain_le_inverse_quotient_variance in RH.QCanonicalWindowCapacity.
The exact complete Q Schur energy retains defect-squared profile variance,
the mean square, and the entire infinite complement. A positive cell variance
caps the signed source-squared/Schur gain by its reciprocal. This is an upper
gain obstruction, not an upper energy or lower gain certificate. Contiguous
windows are not asserted squarefree legal; the legal two-anchor case is included.

Established: Analysis.FiniteWeightedVariance.affine_energy gives generic
scalar-affine completion including zero slope. NumberTheory/CommonFloorQuotient.lean
proves common_floor_quotient_bound: equal floor quotients at 0<a<b force
n*(b-a)<a*b, so common-quotient simplification leaves an infinite complement.

Open: a complete mixed-quotient arithmetic estimate supplying any SPC(a),
0<a<1, and the full infinite squarefree annihilator implication.
Research: RH/QSparsePowerCostResearch20261017.md, historical iteration 3/5.
Cumulative anchor charges and signed mixed Mertens quotient correlations were
proposed at this stage; the bounded program subsequently completed all five
passes and is halted, as recorded in RH/QSparsePowerCostIterationState.json.

### Canonical squarefree Q correlations and an affine-cost obstruction (2026-10-17)

Established: RH/QExactHeadCorrelations.lean proves the complete Q bounded-test
tail inequality, actual canonical residual Gram entries tending to zero
for each fixed row, a quantitative mixed-entry estimate, and the full signed
mixture energy identity with squarefree legality and exact-head support.
No growing-matrix uniform bound is inferred from the fixed-row limit.

Established: Analysis/OrthogonalAffineCostObstruction.lean gives the
geometric diagonal model G_ii=4^(i+1), assigned heads 16^(i+1), exact finite
reciprocal-energy sum, and affine cost at least 3 for all signed weights
of total one, despite sublinear diagonal/head cost and zero cross entries.
This refutes a generic averaging shortcut, not the squarefree RH assertion.

Open: a quantitative signed growing-block Gram or screened-gain estimate
providing any SPC(a) with 0<a<1. See RH/QSparsePowerCostResearch20261017.md.
This was published iteration 2/5. RH/QSparsePowerCostIterationState.json now
records all five completed publications and the halted program status.

### Sparse squarefree power costs: unconditional exponent-one baseline (2026-10-17)

Established: RH/QSquarefreeSublinearHeads.lean proves canonical exact-head
squarefree legality when the anchor is squarefree, complete Q primitive and
residual energy o(H), and arbitrarily cheap cofinal linear-cost heads with
prime anchors. RH/QSquarefreeSparsePowerCost.lean defines SparsePowerCost(a)
and proves it unconditionally for every a>=1.

Conditional research reductions: zero_free_of_sparsePowerCost excludes
Re(s)>1/2, s!=1, with 2*Re(s)-1>=a from SparsePowerCost(a).
riemannHypothesis_of_sparsePowerCost_tendsto_zero proves actual Mathlib RH
from a sequence of available cost exponents tending to zero.
Open: an arithmetic provider for any exponent a in (0,1), and for a sequence
of exponents tending to zero. The o(H) baseline is not such a provider.
Research record: RH/QSparsePowerCostResearch20261017.md, historical iteration 1/5.
RH/QSparsePowerCostIterationState.json now records all five completed
publications and the halted program status.

### Squarefree Q infinite duality and sparse power costs (2026-10-17)

Established: RH/QSquarefreeDualClosure.lean proves squarefree closure iff
every full-Q squarefree annihilator has mean zero, with literal weighted
series, a normalized separator if closure fails, and the complete bound
1 <= norm(h)^2 * norm(qOne-F)^2 for every finite legal F.
It proves unconditionally that finite-support annihilators have mean zero
and any normalized separator has a nonzero coordinate beyond each cutoff.

Established: RH/QExactHeadSubpolynomial.lean now permits arbitrarily sparse
power-cost comparisons with different legal exact heads for each exponent,
constant, and cutoff. No uniform error bound or fixed family is required.

Conditional research reductions: riemannHypothesis_of_annihilator_mean_zero
and riemannHypothesis_of_arbitrarily_small_power_cost retain their complete
infinite dual uniqueness or power-cost provider explicitly.
Open: both arithmetic providers and the requested squarefree constant closure.
The literature RH-to-squarefree-density implication is not newly formalized.
Research record: RH/QSquarefreeNoUniformBoundResearch20261017.md.

### Squarefree Pareto/Q coefficient and gain conversion (2026-10-17)

Established: Analysis/CoordinateProjectionCriterion.lean characterizes target
membership through retained continuous coordinates when omitted coordinates
vanish on the dictionary and target, and the complete coordinates separate
the ambient Hilbert space.

Established: RH/SquarefreeMobiusProjection.lean applies this criterion to
actual squarefree Pareto and Q projections. It proves unconditional fixed
coefficient stabilization, the equivalent squarefree Mobius-target and
closure conditions, P/Q equivalence of those conditions, genuine finite
inverse-covariance coefficient recovery, and the inverse-capacity criterion.
Omitted nonsquarefree coordinates vanish throughout the legal closure;
nonsquarefree atoms are outside that closure. The exact limiting residual
correction and quantitative stabilization retain the full defect.

Established: RH/QSquarefreeRelativeGain.lean gives complete additive and
product identities, zero gains at masked-out nonsquarefree stages, and the
equivalence between squarefree Q closure and nonsummability of actual gains.
All 29 public theorem axiom reports list only the ordinary Mathlib foundations.

Conditional research reductions: the RH consumers retain simultaneous
squarefree Mobius-limit or relative-gain nonsummability hypotheses explicitly.
Open: actual target identification/capacity divergence/gain nonsummability.
The classical RH-to-squarefree-density direction is not newly formalized.

Research record: RH/SquarefreeParetoQTransferResearch20261017.md.

### Infinite CRT Q limits and subpolynomial exact-head energy (2026-10-17)

Established: RH/QConductorLimits.lean proves dominated convergence in the
complete atomic Q norm, residue and divisibility atoms tending to zero as
their conductors escape, and reflected residue vectors tending to one.
RH/QConductorEscape.lean retains the exact linear-head energy and proves
weak convergence to zero for uniformly norm-bounded finite combinations
whose entire conductor support escapes; coefficient signs and support sizes
are unrestricted.

Established: RH/QSquarefreeJumpApplications.lean gives exact singleton and
g_3-squared error decompositions with full norm-square remainders, the lower
bounds 1/(30*zeta(2)) and 2/(1215*zeta(2)), and nonmembership results.
Each reflected squarefree atom with d >= 3 has defect one and is outside
the legal closure. Their legal distances tend to zero if and only if the
constant belongs to the squarefree Q closure; no distance decay is supplied.

Established: RH/QExactHeadSubpolynomial.lean transfers the existing
localized Mellin zero-power obstruction to the complete Q error, with
constant (2*Re(s)-1)/(zeta(2)*norm(s)^2) and cutoff 1 <= k < n.

Conditional research reductions:
riemannHypothesis_of_cofinal_exact_head_subpolynomial and
riemannHypothesis_of_subpolynomial_affine_minima derive actual Mathlib RH
from cofinal exact legal heads and log(1+E)/log(n) tending to zero.
Open: the subpolynomial complete Q-energy provider, including its
specialization to the exhaustive affine minima. Independent squarefree
periods and all signed Gram terms remain available. No RH-to-squarefree-
density implication is newly formalized.
Research record: RH/QInfiniteCRTContinuationResearch20261017.md.

### Unconditional squarefree exact-head linear Q-error (2026-10-17)

Established: RH/QSquarefreeLinearBenchmark.lean reuses the squarefree
legality and exact physical Q/P identification in QSquarefreeSublinearHeads.
The complete Pareto bound and full norm transfer give
||F_N||_Q^2 < 8*N/zeta(2) and
||1-F_N||_Q^2 <= 2 + 16*N/zeta(2).

For every positive requested head H, exists_exactHead_linear_error uses
Bertrand's postulate to choose H <= N < 2H with N+1 prime. The trial equals
one through H and has complete error at most 2 + 32*H/zeta(2).
No RH or unproved energy hypothesis occurs in these benchmark declarations.
All infinite physical tails are retained. The existing asymptotic o(N)
result remains available; this benchmark gives an explicit all-head bound.

Open: a bounded or subpolynomial complete-energy provider. The linear
benchmark does not discharge the RH reduction's subpolynomial premise.
Research record: RH/QSquarefreeLinearBenchmarkResearch20261017.md.

### Complete physical Q primitive-penalty regularization (2026-10-17)

Established: Analysis/PrimitiveRegularization.lean proves the exact objective
completion, signed two-penalty and zero-penalty cross identities, energy difference,
energy and derivative-error monotonicity, exact-target identity, and Galerkin
Pythagoras. Lax--Milgram gives unconditional existence and uniqueness of a
normal solution and minimizer for a bounded Hilbert-space map and positive
penalty.

Established: RH/QPhysicalDifference.lean constructs the actual physical
unilateral shift as a Q contraction and the bounded injective difference
operator with boundary F(0)=0. RH/QPrimitiveEnergyClosure.lean proves
bounded-difference closure, an O(penalty) complete-energy closure consumer,
unconditional existence of the unique squarefree regularized minimizer,
and squarefree constant closure if and only if the canonical normal family
has a uniform critical objective budget along positive penalties tending
to zero.

Conditional research reduction:
riemannHypothesis_of_regularized_legal_budget yields actual Mathlib RH.
Open: its uniform complete primitive-energy budget. No arithmetic O(penalty)
provider or new RH-to-squarefree-density implication is formalized here.
The original Markdown appendix required syntax and namespace repairs before
checking. The divisor-coordinate finite optimizer and its divergent period
mean are additional paper derivations, not claims certified by these modules.


### All-order squarefree cumulants and physical projective realization (2026-10-17)

Established: NumberTheory/SquarefreeCumulantTower.lean constructs iterated
square-zero algebras with actual Boolean-subset convolution, coefficient
equivalence, augmentation nilpotence, all-order inverse log/exp transforms,
additive/multiplicative identities, and the existing two-prime specialization.
NumberTheory/SquarefreeCumulantLimit.lean proves compatible arbitrary-mask
restrictions, constructs the inverse-limit ring with universal property and
levelwise inverse transforms, and gives finite approximations with eventual
exact agreement at every fixed projection.

Established: RH/QSquarefreeFormalSynthesis.lean gives legal synthesis by
literal residues, complete atomic-Q norm and signed Gram error/difference
identities, separate exact boundedness and strong-realization tests, and
equality of finite cumulant and moment synthesis ranges. Strong and weak
physical limits remain in the existing closed legal span. A compatible
singleton family with moment c_p=p has F_n(1)=n and norm squared at least
n^2/zeta(2), proving that formal completion does not imply physical bounds.
Continuous finite-site Mobius functionals recover the legal coefficients,
separate all Q vectors, and characterize the target one by -mu(m).

Conditional research reduction:
riemannHypothesis_of_bounded_cumulant_heads uses the existing exact-head
averaging bridge. Open: its growing exact heads and one uniform complete
signed Q-error budget. No unconditional RH claim is made. Partition-sum
formulas, a quotient-polynomial equivalence, and a separate topological-ring
instance are not newly formalized.
Research record: RH/QSquarefreeCumulantCompletionResearch20261017.md.

### Exhaustive squarefree exact-head affine minimum (2026-10-17)

Established: RH/NormalizedResidueExactHeadCharges.lean characterizes a
finite zero head by zero reciprocal slope and vanishing low coefficients.
RH/QResidueHeadSpace.lean identifies the entire finite zero-head subspace
with the span of all compensated high-conductor directions, proves their
independence, and constructs the actual affine Gram optimizer with exact
complete-error formula, Pythagorean remainder, and uniqueness.

Established: RH/QSquarefreeAffineHead.lean proves the exact Mobius baseline
head and finite divisor-stage membership, the exhaustive affine feasible
set, and forced period support for nonzero low Mobius coefficients.
Its actual minimum has a complete norm-square remainder. Period
enlargement gains exactly the squared optimizer displacement, and both
the minimum and optimizer are independent of the normalization anchor.
Large composite conductors and refitting of old coefficients are retained.

Conditional research reduction:
riemannHypothesis_of_bounded_affine_minima derives Mathlib RH from the
actual squarefree optimizers with growing exact heads.
Open: one uniform bound on these complete optimized Q errors.
The RH-to-density direction and subpolynomial zero-witness consumer are
not newly formalized here. The all-order log/exp algebra is now supplied by
SquarefreeCumulantTower and SquarefreeCumulantLimit above.
Research record: RH/QSquarefreeAffineHeadResearch20261017.md.

### Squarefree convolution cumulants and legal physical packets (2026-10-16)

Established: NumberTheory/SquarefreeCumulantPair.lean proves inverse
normalized two-prime convolution log/exp coordinates, logarithmic
additivity, exponential multiplicativity, product associativity and
commutativity, and the exact reciprocal-slope balance and defect formulas.

Established: RH/QSquarefreeLatticePackets.lean proves divisor-stage
transport by actual Q floor dilations, squarefree legality under explicit
coprime support hypotheses, compensated zero-head directions and their
reciprocal-zero synthesis, and the actual two-prime cumulant packet.
Its complete error identity retains all signed correlations and mixed
terms. Its composite-cumulant completion gives the exact optimum and
nonnegative excess square, with the nonzero direction stated explicitly.

Open: a cofinal uniform or subpolynomial bound for the complete exact-head
error. The all-order nilpotent algebra and projective completion are now
formalized in SquarefreeCumulantTower and SquarefreeCumulantLimit above.
The exhaustive affine characterization and complete minimum are now
formalized in QResidueHeadSpace and QSquarefreeAffineHead above.
The original packet research record is
RH/QSquarefreeLatticePacketsResearch20261016.md.

### Exact von Mangoldt–LCM arithmetic (2026-10-16)

Established: NumberTheory/VonMangoldtLCM.lean reuses Mathlib's actual
Nat.lcmUpto, Nat.factorization_lcmUpto, and
Chebyshev.psi_eq_log_lcmUpto. It counts the LCM's p-adic exponent by the
positive prime powers p^k <= N, proves the exact log increment Lambda(n),
the multiplication-by-p identity at p^k, and the equivalence between
unchanged running LCM and a non-prime-power index.

The complete signed finite identity is
  psi(N) = log(lcm(1,...,N))
         = -sum_(1<=d<=N) mu(d)*log(d)*floor(N/d).
The natural quotient is formed before casting to the reals. Its proof
uses the exact arithmetic-function convolution summation identity.
Exponentiation recovers the actual positive integer LCM.

No RH assumption is used. The pointwise damping derivative, its signed
Taylor remainder, the global Hilbert estimate, and the RH-to-Hardy
approximation provider remain separate obligations.
Research record: NumberTheory/VonMangoldtLCMResearch20261016.md.

### Mobius prime-packet arithmetic and complete screened trials (2026-10-17)

Established finite results: RH/QMobiusPrimePacketArithmetic.lean proves
coprime inclusion-exclusion with every integer quotient, identifies the
actual totient density, and proves h_(L,p)(k)=k*phi(L)/(p*L)-A_L(floor(k/p))
for all positive L,p. It also proves the short head, full p*L period, and
h_(6,5)(7)=-8/15.

Established finite results: RH/QCovarianceTrial.lean retains the signed
source t^T delta, every mixed entry of t^T R t, and the exact equality
Gamma=alpha^2/E+||v_star-(alpha/E)*w_t||^2. Positive energy and the trial
lower bound follow for independent complete families and nonzero t.

Established finite results: RH/QMobiusPrimePacket.lean supplies actual
squarefree primorial packet weights mu(d), including d=1, literal legal
membership, the physical coprime-count formula, the pairing with the actual
primorialOptimizer residual, positive screened energy, and
moebius_trial_lower_bound for the existing actual packetGain.

Conditional research reduction: moebius_gain_lower_of_bounds consumes the
explicit finite estimates a^2<=alpha^2, E<=e, 0<e. It supplies no uniform
arithmetic provider. Open: sufficiently strong next-prime source and
screened-energy estimates. Open: divergence of accumulated actual gains;
the existing capacity telescope retains its initial capacity. No RH
conclusion is claimed. External interval experiments are not Lean certificates.

Research record: RH/QMobiusPrimePacketResearch20261017.md.

### Complete-tail constrained Q minimum and conductor-gap arithmetic (2026-10-16)

Established: Analysis/FiniteGramRankOne.lean proves actual Gram inverse
rank-one updates for arbitrary nonnegative head cost, simultaneous source
updates, mismatch and penalty identities, and unchanged constrained
coefficients. RH/QTailGram.lean constructs the complete physical tail with
original Q weights and proves positive definiteness by periodicity and
residue independence.

Established: RH/QTailConstrainedMinimum.lean identifies the actual tail
optimizer coefficientwise with the existing complete-Q optimizer, proves
C_full=C_tail/(1+(H/zeta(2))*C_tail), its reciprocal identity, the actual
matrix inverse action, and the exact tail formula and completion for
the original minimumError. The smaller full mismatch is accompanied
by an exact increase in the unconstrained residual.

Established: RH/QTailConductorGap.lean proves the complete inverse-capacity
gap identity and C_tail<=zeta(2)/(J-H) when all free conductors exceed J>H.
For squarefree free families, a nonsquarefree H+1 forces C_tail<=zeta(2).
It also proves the forced signed floor residual before the first wrap,
its exact Mertens-increment form on H<n<=2H+1, and the complete minimum's
arithmetic block plus full physical tail remainder.

Open: a uniform bound on the actual complete minimum along growing heads.
These exact identities and finite numerical probes do not supply it.
Research record: RH/QTailConstrainedResearch20261016.md.

### LCM squarefree constrained Q minimum and normalization capacity (2026-10-16)

Established: Analysis/FiniteGramScalarConstraint.lean proves the actual scalar
constrained inverse-Gram optimizer, its exact energy, unique coefficients,
and full nonnegative squared-norm remainder. RH/QLargeConductorCapacity.lean
proves the exact identity C=(H/zeta(2))*C^2+Tail_Q(U), its inverse-capacity
identity, and C<=zeta(2)/H for independent conductors above a positive head.
A bounded normalization penalty, or bounded complete constrained energy,
forces H*mismatch^2<=zeta(2)*B. This is the large-conductor normalization
capacity, distinct from the centered target capacity in QSquarefreeCapacity.

Established: RH/QSquarefreeConstrainedMinimum.lean constructs the actual
signed Mobius seed, proves squarefree legality and its exact linear head,
and assembles the exact squarefree optimizer and constrained energy formula.

Conditional research reduction: riemannHypothesis_of_bounded_minimumError
derives Mathlib RH from a uniform bound for these actual optimized errors
along finite nonempty distinct squarefree families above growing heads.
Open: the uniform minimumError bound. No RH-to-density bridge, LCM/radical
arithmetic, or refined repeated-period harmonic comparison is proved here.
Research record: RH/QLCMConstrainedMinimumResearch20261016.md.

### Q-squarefree primorial cofinality and capacity (2026-10-16)

Established: RH/QSquarefreePrimorialCofinality.lean proves both finite-stage
inclusions, equality of the algebraic and closed squarefree legal spans,
and a common limiting optimal Q error. Its divisor covariance and mean
are principal restrictions of the exhaustive system. The finite primorial
optimizer uses normalized inverse-covariance coefficients; its geometric
capacity equals the genuine covariance information.

The primorial and exhaustive capacity divergences are equivalent. Exact
successive and cross-index gains retain the complete squared
optimizer-displacement term divided by both positive errors.

Open: no lower bound forces these gains to accumulate without bound.
Cofinality does not establish target closure or RH. A principal block
inverse is generally not a block of the larger inverse. CRT carries are
not discarded. Research agenda: RH/USquarefreeResearch20261016.md.

### Q-squarefree prime packets and actual covariance screening (2026-10-16)

Established: Analysis/FiniteGramScreenedInverse.lean proves the exact block
inverse action with all old coefficient corrections. RH/QCovarianceScreening.lean
specializes the general screening theorem to the actual full-Q residue
means and centered covariances. It proves R=S-V^T*C^(-1)*V,
delta=beta-V^T*C^(-1)*b, positive definiteness of R, the exact capacity
gain delta^T*R^(-1)*delta, both corrected inverse-source blocks, and the
actual normalized Gram-inverse least-squares coefficients.

Established: RH/QSquarefreePrimePacket.lean proves the complete disjoint
old/new divisor partition for a fresh prime adjoined to an actual primorial,
including the new prime from the divisor one. It proves squarefree legality,
the actual primorial capacity gain, the exact signed residual-correlation
identity, and delta(j)^2<=gain*R(j,j). A bijective conductor reindexing
identifies prime cutoff steps with the existing next primorial stage.
Composite cutoff steps are unchanged. The exact finite telescope retains
the initial capacity.

Conditional research reduction: riemannHypothesis_of_packetGain_sum_tendsto
concludes Mathlib RiemannHypothesis from divergence of the actual cutoff-gain
partial sums. Open: an arithmetic provider of that divergence. Finite
screening identities and nonnegative gains alone do not discharge it.
Research record: RH/QSquarefreePrimePacketResearch20261016.md.

### Squarefree damped Hardy norm bridge (2026-10-16)

Established: RH/DampedMobiusSquarefreeClosure.lean proves literal squarefree
legality of -sum_(d<=N) mu(d)*d^(-epsilon)*g_d and squarefree closure
membership of every norm limit. Existing unconditional cutoff convergence
for epsilon>=1/2 supplies actual squarefree legal P and Q limits with exact
arithmetic coordinates. The finite physical bound is not asserted uniform
in conductor cutoff or damping.

Established: RH/ParetoMellinHardyNorm.lean identifies the complete Pareto
norm squared with the supremum of actual Mellin line energies over
Re(s)>1/2, as an IsLUB. For bounded physical vectors it proves the ordinary
critical-line Plancherel identity, with the factor 1/(2*pi).
RH/DampedMobiusHardyBridge.lean proves the exact finite damped zeta formula,
residual Mellin formula, and equivalence of complete norm bounds with
uniform interior-line integral bounds. Its ordinary critical-line norm
identity applies to actual finite residuals, with boundedness proved internally.

Conditional research reduction: DampedHardyApproximation is a concrete
epsilon-cutoff uniform line-error assertion. The three checked consumers
prove Pareto squarefree constant closure, Q squarefree constant closure,
and actual Mathlib RiemannHypothesis from this explicit analytic premise.

Open: formalize RiemannHypothesis -> DampedHardyApproximation from actual
RH-dependent estimates and the two limiting steps. No RH-to-density axiom
or provider is introduced, no small-damping global estimate is proved,
and neither actual constant closure membership nor RH is asserted.
The finite signed indicator classification in the following section is
reused from concurrently published commit 79f8396; no duplicate module is added.
Research record: RH/QDivisorLegalityContinuationResearch20261016.md.

### Finite signed divisor legality classification (2026-10-16)

Established: Analysis/EvenPeriodicSquareJump.lean proves that an even
real integer sequence invariant modulo a positive integer and satisfying
all positive square-jump identities is two-periodic.
RH/QParityGeometry.lean reconstructs the exact Hilbert vector as
F = F(2)*qOne + 2*(F(1)-F(2))*qResidue 2.
RH/QSignedDivisorLegality.lean applies this to arbitrary finite signed
sums F of positive-conductor divisibility indicators.

For such F, closure membership is equivalent to two-periodicity on
positive coordinates together with
F(2)=0 or qOne belonging to the closed squarefree legal span.
Finite squarefree span membership is equivalent to two-periodicity and
F(2)=0; these vectors are precisely the multiples of qResidue 2.
Passing every square-jump test is equivalent to two-periodicity within
this finite signed dictionary. All coefficient signs are allowed.

There are 16 new public theorem declarations, with no unresolved
hypothesis in the unconditional classification. Two of these declarations
specialize under qOne membership or nonmembership as an
explicit hypothesis; neither is supplied by this development.
The local tests are not asserted sufficient for general legal closure
membership. Actual qOne membership and RH remain open.
Research record: RH/QSignedDivisorLegalityResearch20261016.md.

### Quantitative squarefree jump distance (2026-10-16)

Established: RH/ZetaTwoCoordinateDual.lean constructs the actual
single-site Q-Riesz vectors with their exact physical amplitudes, pairings,
and squared norms. RH/QSquarefreeJumpDistance.lean constructs the four-site
square-jump witness h_a and the continuous linear functional Lambda_a.
The exact squared witness and operator norms are
D_a = 2*zetaTwo*(a^4-a+1) > 0 for a >= 2.

For every target x and every F in the closed squarefree legal span,
the complete identity is
norm(x-F)^2 = Lambda_a(x)^2/D_a
  + norm(x-F-(Lambda_a(x)/D_a)*h_a)^2.
The signed defect and the entire norm-square remainder are retained.
For m >= 3, the actual indicator defect is -1 at a=m-1, giving
norm(qDivisor m-F)^2 = 1/D_(m-1)
  + norm(qDivisor m-F+h_(m-1)/D_(m-1))^2.
In particular, the m=3 squared error is at least 1/(30*zetaTwo).

The finite signed-indicator formula retains all coefficients and all four
site contributions. For m >= 3,
alpha*qOne+beta*qDivisor m belongs to the closed squarefree span iff
beta=0 and alpha*qOne belongs to that span.
There are 17 new public theorem declarations across the two modules.
No unresolved domain-specific hypothesis is used.

Open: use the complete multi-witness Gram matrix for stronger bounds;
prove a global norm, tail, or inverse-capacity estimate for actual legal
approximants to qOne. The finite signed square-jump classification is
now established in RH/QSignedDivisorLegality.lean. The constant has zero
square-jump defect. General sufficiency for legal closure membership,
actual constant closure membership, and RH remain unproved.
Research record: RH/QSquarefreeJumpDistanceResearch20261016.md.

### Divisibility indicators and squarefree legality (2026-10-16)

Established: RH/QDivisorLegality.lean treats the actual Q-Hilbert
divisibility indicators. No positive-conductor indicator is any finite
legal residue combination. For every m >= 3, the indicator is excluded
even from the closed squarefree residue span, without an RH assumption.

The complete signed jump identity is Delta f(a^2) = Delta f(a) throughout
that closed span. At a = m-1, the indicator's jump defect is exactly -1.
The exact exceptional identity is qDivisor 2 = qOne - 2 * qResidue 2;
hence conductor-two indicator membership is equivalent to constant
membership in the same closed squarefree span.

There are nine public theorem declarations. The checked proofs require
no unresolved mathematical hypothesis. No RH-to-squarefree-density
bridge or actual constant closure membership is asserted by this module.

### Squarefree legal Parseval coordinates and research agenda (2026-10-16)

Established: RH/QSquarefreeCoordinates.lean restricts the actual complete
divisor-wavelet Parseval isometry to the literal closed squarefree residue span.
The restriction is a linear isometric equivalence onto its closed image
coordinateSpace. It preserves norms and inner products; its ambient-ell2
adjoint is legal orthogonal projection after inverse reconstruction. The
adjoint compositions are the identity on the legal domain and the orthogonal
projection on its coordinate image. The exact squared approximation error is
the squared first-coordinate mismatch plus the complete nonconstant energy.

RH/QSquarefreeCoordinateLegality.lean passes the actual radical difference
identities to every vector in the legal closure. The four-point constraint
excludes qResidue 4 and proves coordinateSpace is proper. These necessary
constraints are not claimed to characterize the entire image or exclude qOne.

RH/QSquarefreeCoordinateApproximation.lean gives the exact finite arithmetic
columns, legal finite synthesis, and preserved full error. Target membership
is equivalent to divergence of the actual distinct-squarefree inverse capacity.
Optimizer coordinates converge to the legal orthogonal projection of the
first unit vector. The modules have 35 public theorem declarations in total.

Conditional research reduction: riemannHypothesis_of_target_mem concludes
Mathlib's RiemannHypothesis from explicit membership of the constant target
in coordinateSpace. Open: an arithmetic proof of that membership, inverse
capacity divergence, collective coordinate-tail decay, or elimination of
the target-relevant dual obstruction. RH-to-squarefree-density is also a
separate formalization obligation.

RH/USquarefreeResearch20261016.md records the precise conventions, declaration
map, provenance, and prioritized arithmetic, coordinate-tail, dual, and
coefficient-topology research tasks. Raw ordinary-ell2 synthesis operator
claims are follow-up work, not consequences asserted by the new Lean modules.

### Genuine squarefree inverse covariance capacity (2026-10-16)

Established: RH/QSquarefreeInverseCapacity.lean removes the zero entries
from the masked squarefree stage, retaining exactly the distinct squarefree
conductors 2 <= d <= n+1. Existing positivity proves that its actual
covariance matrix C_n is positive definite. The normalized coefficients
C_n^{-1} b_n / (1 + b_n^T C_n^{-1} b_n) synthesize exactly the existing
orthogonal optimizer, and inverseCapacity equals the geometric capacity.

The module proves the exact error 1/(1+inverseCapacity), the determinant
ratio det(C_n)/det(G_n), and the full arithmetic-wavelet Parseval identity.
Completion of the square retains the entire squared-norm displacement
for arbitrary legal coefficients. Capacity is monotone. Literal squarefree
closure is equivalent to divergence of this genuine inverse capacity and
to the epsilon criterion with arbitrary finite legal coefficients.
There are 18 public theorem declarations.

Conditional research reductions: riemannHypothesis_of_inverseCapacity_tendsto
and riemannHypothesis_of_forall_epsilon conclude Mathlib's RiemannHypothesis.
Open: an arithmetic proof of inverse-capacity divergence, equivalently the
stated arbitrarily small actual error. This development proves neither
that estimate nor the RH-to-squarefree-density converse.

### Canonical Q-window capacity and complete Schur arithmetic (2026-10-16)

Established: Analysis/FiniteGramSchurBounds.lean bounds the actual screened
Hilbert energy and proves it positive for an independent enlarged family.
RH/QCanonicalWindowCapacity.lean specializes to the actual inverse-Gram
normal mass m_Q(N,M), proving the exact recurrence
m_Q(N,M+1)-m_Q(N,M)=defect(N,M)^2/schur(N,M), the full signed Schur expansion,
finite telescoping, and the strict-gain criterion. At each fixed positive
head there is no terminal plateau: every finite window has a larger window
with strictly greater mass. Explicit moving-normal amplitude budgets yield
quantitative step gains; fixed-test decay is not asserted uniformly for
changing normal vectors.

RH/QCanonicalWindowSchurArithmetic.lean identifies the complete weighted
Schur energy and the signed common quotient-cell profile. Its cell-energy
identity retains the entire infinite complement. The development contains
29 public theorem declarations and five private reindexing lemmas.

Conditional research reduction: riemannHypothesis_of_cumulative_gain_lower
consumes one common positive lower threshold on the diagonal normal mass
plus finitely many actual signed Schur gains for each growing head.
Open: an arithmetic provider for this common threshold. Finite positivity,
monotonicity, and arbitrarily late strict gains do not discharge it.
Research and verification record: RH/QCanonicalWindowCapacityResearch20261015.md.

### Canonical Q/P affine minima and optimizer stability (2026-10-15)

Established: RH/QParetoAffineMinimum.lean proves exact P/Q affine
Pythagoras, the correction balance
R(x_P)=R(x_Q)+2||x_Q-x_P||_P^2+R(x_Q-x_P), and the complete minimum gap
zeta(2)*D_Q-D_P=R(x_Q)+||x_Q-x_P||_P^2.
The common-head displacement bound is
||x_Q-x_P||_P^2 <= R(x_P)/(H+1) <= D_P/(H+1)^2.
Generic finite normal equations are explicit; singular families are permitted
when those equations have solutions.

RH/QCanonicalWindowMinimum.lean constructs the actual Q inverse-Gram
normal vector from the proved independence of complete canonical residuals.
It proves positive normal mass, the exact affine energy completion and
uniqueness of the minimizing coefficients. Both finite normal equations
are discharged by actual inverse constructions.

With delta_N=||r_N||_P^2/(N+1), the unconditional bounds for every
M >= N >= 1 are 0 <= zeta(2)*D_Q-D_P <= delta_N and
||x_Q-x_P||_P^2 <= delta_N/(N+1).
The actual Q optimum also has correction at most delta_N; two independently
selected windows have squared mixed correction at most delta_N*delta_K.
Cofinal energy-gap and strong displacement limits allow arbitrary
dimension growth and require no coefficient-mass bound.

Conditional research reductions: riemannHypothesis_of_bounded_optimized_energy
consumes a uniform bound on actual Q minimum energies with growing heads.
riemannHypothesis_of_normalQ_mass_lower consumes a single positive lower
bound on 1^T G_Q^-1 1 along those growing heads. This uniform arithmetic
lower bound remains Open; positivity of each separate finite normal mass
is already established. No bound on the full minimizing energy, convergence
of raw coefficients, or RH is concluded by the unconditional comparisons.

The development adds 31 theorem declarations and five definitions.
Research record: RH/QCanonicalWindowMinimumResearch20261015.md.

### Uniform canonical Q/P Gram and covariance comparison (2026-10-15)

Established: RH/QMetricCorrectionBounds.lean realizes the full signed
metric correction as an actual Hilbert Gram form, using halfReciprocal
and correctionVector. It proves the inverse-density equality, the sharp
head bound R(f) <= zeta(2)*||f||_Q^2/(H+2), mixed Cauchy--Schwarz,
weighted signed l1 and l2/trace bounds, and covariance-change control
for arbitrary Hilbert tests.

Established: RH/QCanonicalCofinalGram.lean proves that the entire canonical
Gram discrepancy C(M,N)=zeta(2)*<r_M,r_N>_Q-<r_M,r_N>_P is a positive Gram
kernel, with C(M,N)^2 <= R_M*R_N <= delta_M*delta_N.
The discrepancy tends to zero uniformly on M,N >= H as H tends to infinity.
correctionVector(r_N) tends strongly to zero.

The exact signed quadratic identity is retained for every finite block.
Bounded-l1 cofinal signed averages have vanishing absolute Q/P energy
discrepancy even when dimension grows arbitrarily and their full energies
are unbounded. A weighted correction budget also permits unbounded l1 mass;
the l2/trace bound controls all l2-unit sources simultaneously.

The covariance-change estimate is
|zeta(2)*<f,r_N>_Q-<f,r_N>_P|^2 <= ||f||_P^2*R_N/(N+1).
It yields unconditional covariance transfer for moving tests with
||f_N||_P^2 <= C*(N+1), without pointwise physical bounds.
The complete stretched Mertens profile bounds R_N with the retained
8/(N+1) boundary and N/(N+1) factor.

RH/QParetoGramComparison.lean adds dimension-independent common-head
Gram bounds G_P <= zeta(2)*G_Q <= ((H+2)/(H+1))*G_P and genuine inverse
quadratic bounds with lower factor zeta(2)*(H+1)/(H+2).
Gram inequalities permit singular families; inverse claims state finite
linear independence explicitly.

This adds 40 theorem declarations and six definitions. No bounded full
legal energy, canonical norm convergence, or RH is concluded. The missing
full-energy arithmetic budget remains Open. Exact statements, proofs,
rates, and verification evidence are in
RH/QCanonicalCofinalGramResearch20261015.md.

### Pareto-to-Q transfer and sharper metric asymptotics (2026-10-15)

Established: eight modules add 87 theorem declarations and 11 definitions.
RH/QParetoEquivalence.lean constructs the inverse physical-sequence map toQ
and the continuous linear equivalence paretoEquiv. Strong convergence,
uniform boundedness, arbitrary subspace closure, and every indexed positive
conductor closure problem transfer with identical physical sequences.

RH/QParetoMetric.lean proves the exact equality
zeta(2)*||f||_Q^2 = ||f||_P^2 + R(f), where
R(f)=sum_{n>=1}|f(n)|^2/(n^2*(n+1)), its signed polarization, positivity,
and faithfulness. If f vanishes through H, then
0 <= R(f) <= ||f||_P^2/(H+1), improving the global factor 2 to 1+1/(H+1).

Analysis/FiniteGramMetricComparison.lean proves inverse-Gram comparison
from full synthesis-energy comparison. RH/QParetoGramComparison.lean
specializes it to genuine Q/P matrices for every finite independent family:
(zeta(2)/2)*b^T G_P^-1 b <= b^T G_Q^-1 b <= zeta(2)*b^T G_P^-1 b.
The same b is used on both sides. The actual minimum errors satisfy
D_P <= zeta(2)*D_Q <= 2*D_P, using each metric's own optimizer.

RH/QParetoOperatorTransfer.lean transports bounded operator algebra,
real eigenvector identities, and continuous annihilators by similarity.
RH/QMellinTransfer.lean retains the physical step integral and the actual
normalized-residue zeta signature. Its off-line-zero lower estimate is
(2*Re(s)-1)/|s|^2 + R(1-F) <= zeta(2)*||1-F||_Q^2.

RH/QCanonicalMetricAsymptotics.lean uses the checked exact heads and
stretched-PNT normalized-energy provider to prove, unconditionally,
zeta(2)*||r_N||_Q^2 - ||r_N||_P^2 -> 0.
The positive discrepancy is bounded by delta_N=||r_N||_P^2/(N+1), and
eventually by D/(6+log N)^2. The Q covariance constant (2/zeta(2))^2
improves to ((1+1/(N+1))/zeta(2))^2.

Conditional research reductions: RH/QBoundedCoordinateClosure.lean
transfers bounded physical coordinate limits and growing exact heads to
arbitrary Q subspace closure. Its legal-head and full-divisor-Parseval RH
consumers retain a uniform complete-energy bound as an Open arithmetic
hypothesis. No canonical error convergence, bounded legal family, or RH
is established. Q-specific means, Gram entries, and self-adjoint spectral
data must use their actual Q formulas.

Research record: RH/QParetoTransferResearch20261015.md includes the
theorem-family coverage, exact identities, existing Q arithmetic providers,
verification evidence, and the remaining arithmetic obligation.

### Moving canonical covariance and complete Q-energy gap (2026-10-15)

Established: RH/CanonicalMobiusMovingCovariance.lean proves
'moving_test_tendsto' from the exact moving physical-bound budget,
'moving_canonical_tendsto', and the complete initial-column bound
B(K,N) <= K*(1+2*K)^2*delta_N, where delta_N = ||r_N||_P^2/(N+1).
Finite Cauchy--Schwarz controls signed block tests with bounded squared
coefficient mass; convex coefficients are included.

Established: RH/CanonicalMobiusMovingCutoff.lean uses the existing checked
stretched PNT provider to prove 'energyRate_eventual_log_square':
delta_N <= D/(6+log N)^2 eventually. The concrete positive cutoff
K_N = 1 + floor(sqrt(6+log N)) tends to infinity and its full column energy
tends to zero. 'exists_growing_canonical_tests' and the signed/convex
block-pairing limits are unconditional. Constants and onset remain existential.

Established: RH/QCanonicalMovingCovariance.lean constructs the actual
Q-weighted canonical family and proves moving-test and growing-column decay
with the complete Q/P comparison constants. RH/QCanonicalAverageEnergy.lean
proves exact full Q residual Gram and infinite weighted-sum energy identities.

Conditional research reductions:
'squarefree_closure_of_bounded_residual_gram' and
'riemannHypothesis_of_bounded_residual_gram' consume a uniform upper bound
on the complete signed Q-Gram energy of cofinal sum-one averages whose
boundary conductors k+1 are squarefree. This arithmetic budget is Open.
Column decay does not establish bounded average norms, squarefree closure,
or RH. The research record CanonicalMovingCovarianceResearch20261015.md
gives the exact missing estimate and an explicitly informal diagnostic
countermodel showing why the abstract sublinear-energy bounds alone
cannot imply that estimate.

### Certified finite inverse-Gram ceilings and radius monotonicity (2026-10-14)

Established: Analysis/TruncatedGramEnvelope.lean constructs the normal
solution of an augmented finite Gram system with a positive diagonal
allowance. It proves positive normal mass, normalized selected coefficients,
the exact affine energy completion, and transfer of ceiling comparisons
from comparisons of the complete penalized quadratic objectives.

RH/CanonicalMobiusTruncatedCeiling.lean specializes to actual positive
canonical cutoffs k_i, residuals e_i=1-F_(k_i), physical Pareto weights,
Q=sum_i(1+2k_i)^2, and penalty Q/R. It retains the exact finite-energy
plus infinite-tail split, proves the complete tail allowance, and bounds
the selected actual Hilbert residual norm by the constructed inverse
normal-mass ceiling. Normalization preserves every common exact head.

The exact radius difference is
w_R*((sum_i a_i e_i(R))^2-Q*sum_i a_i^2).
Cauchy-Schwarz makes it nonpositive, proving that the constructed ceiling
is antitone in R for each fixed family. No matrix inverse, normal
solvability, or tail-boundedness provider is assumed.

Open: a uniform ceiling for selected cofinal squarefree boundary supports.
Taking all k_i+1 squarefree ensures legality by the existing membership
theorem, but the present estimates do not bound the ceiling as the
smallest cutoff grows. Increasing the support also changes Q, so fixed
radius support monotonicity does not follow. No RH or squarefree-closure
hypothesis is used or discharged by these finite results.

### Exact arithmetic quotient-cell covariance identities (2026-10-14)

Established: RH/CanonicalMobiusQuotientCells.lean gives the exact canonical
residual as H_q(n) + q b_Y, where q = floor(n/(Y+1)),
H_q(n) = sum_{k<=q} M(floor(n/k)), and b_Y = (Y+1)S_Y - M(Y).
The signed two-cutoff product retains both cutoff correction terms.

On a common quotient cell, normalized real signed averaging changes only
the constant offset. The exact cell energy is its weighted Mertens-profile
variance plus a mean square. The full Hilbert norm equality retains the
entire complementary infinite energy. Concrete interval conditions give
the actual Pareto mass 1/L - 1/U, with no analytic provider assumed.

Open: uniform upper control of these terms for cofinal prime-cutoff
families. These are arithmetic identities and a local lower constraint,
not a uniform covariance estimate or an RH proof. Common cells may be
empty for widely separated cutoffs; general cofinal averages are not
excluded. No RH or squarefree-closure hypothesis is introduced.

### Fixed-test canonical covariance decay (2026-10-14)

Established: RH/ExactHeadResidualTail.lean adds
`hilbertTailShift_norm_sq_le_of_bounded`, bounding the complete Pareto tail
by A^2/(N+1) for a physical sequence bounded by A. The exact weighted tail
identity is retained before the estimate.

RH/CanonicalMobiusCovarianceDecay.lean proves a complete squared-pairing
bound and convergence to zero against every fixed bounded physical test.
In particular, every fixed canonical residual decorrelates from later
canonical residuals. The proof uses the existing unconditional PNT
sublinear energy theorem, with no RH or squarefree-closure assumption.

Open: a uniform bound for the complete covariance energy of cofinal signed
or convex averages. The first test remains fixed in the established limit;
no uniform moving-matrix bound or weak convergence against every Hilbert
vector is asserted.

### Squarefree finite-coordinate tests (2026-10-14)

Established: RH/SquarefreeFiniteObservation.lean proves
`squarefree_finite_observation_annihilator`. If a finite linear combination
of positive-coordinate evaluations vanishes on every squarefree residue
atom, then its coefficients sum to zero, so it also vanishes on the
constant-one sequence. The proof uses existing canonical Mobius trials at
a prime boundary to match the entire prescribed finite head exactly.

Open: constant-one membership in the norm closure of the squarefree atom
span. The finite-coordinate theorem does not cover arbitrary continuous
functionals involving infinitely many coordinates, and supplies no bound
on the interpolants' tail energies. It is not an unconditional proof of RH.

### Random legal-conductor selection and exact expected projection errors (2026-10-14)

Established: 35 public theorems across four new exported modules and the
existing finite DPP law module. The general nested identity is reused from
Analysis/NestedProjectionEnergy.lean, rather than duplicated.

- Analysis/RandomSubspaceProjection.lean: exact finite expectations and
  Bochner integrals; equality precisely on supported subspaces containing
  the full optimizer, or almost surely; deterministic extraction below the
  mean; exact trial-gap remainder; convergence iff both nonnegative terms
  vanish.
- Analysis/FiniteAtomSelection.lean: literal finite atom spans, actual
  orthogonal projections, nested inclusions, and exact selected errors.
- Probability/DeterminantalAtomSelection.lean: the existing actual finite
  positive-contraction DPP PMF specialized to atom selection, exact expected
  error/equality, and supported deterministic witnesses with optional
  cardinality caps. FiniteDeterminantalLaw adds finiteLaw_apply_toReal.
- RH/QLegalAtomSelection.lean: full and actual squarefree conductor
  selections, exact errors relative to 1-p_n, equality conditions,
  conductor-DPP specializations, explicit two-stage wavelet vacancy
  averages, and both legal-family convergence equivalences.

Conditional research reductions: mean-square sampled error tending to zero
implies Mathlib RH. Its exact equivalent obligations are full legal p_n
tending to one and expected selection gap tending to zero. Both arithmetic
providers remain Open. A wavelet-label DPP is not a conductor-selection law;
the formal weighted vacancy averages describe an explicit two-stage
connection and do not assert the mixture is determinantal.

Saved source checks and eleven central axiom inspections passed
job_GQ4fG-Ed695fkJy-1L92RKQimyPqubeo (14.092 seconds) and
job_AUqHp7LhY04S_SNgWv_gpespYcZ-VqW0 (16.676 seconds), both exit code 0,
verified true. Inspected axioms are propext, Classical.choice, and Quot.sound.
Publication additionally requires the final server checkpoint.

RH/QLegalAtomSelectionResearch20261014.md gives analytic determinant proofs
for the conductor Gram L-ensemble: exact ridge mean coefficients, target
spectral leakage, sample-size formula, and finite equality obstructions.
These resolvent specializations are written analytic results, not new Lean
declarations. Target-weighted growing-Gram leakage, sparse sample-size
bounds, and the full legal-density/CRT expected-tail arithmetic providers
remain Open.

### Q divisor DPP growing windows and Poisson counts (2026-10-14)

Established source results: eight modules with 60 public theorems, one private
helper, and eight definitions. All eight saved source modules and the six
central-declaration axiom audit passed job_uzS396cvn-4Ce2Dchm3bbXZf888j2a6u
(exit code 0, verified true, 31.686 seconds). Every inspected declaration uses
only propext, Classical.choice, and Quot.sound. Final publication uses the
server checkpoint and its required project validation.

- NumberTheory/GcdWindowMoments.lean: exact gcd-fiber grouping and the
  real-exponent window moment bound for every exponent greater than one.
- RH/QDivisorDPPOverlapPower.lean and RH/QDivisorDPPGrowingWindows.lean:
  reuse the existing exact overlap to prove, without arithmetic hypotheses,
  an off-diagonal square-sum bound D_e h^(5-4e)/(x+1)^(4-4e), 0<e<3/4,
  uniform in the projection rank, plus its geometric-budget limit consumer.
- Probability/DeterminantalPoissonLimit.lean: exact spectral square identity,
  signed logarithmic remainder, conditional PGF and vacancy limits, and the
  exact diagonal/off-diagonal square-sum decomposition.
- Probability/ProbabilityGeneratingCoefficients.lean and
  Probability/DeterminantalCountPoissonLimit.lean: PGF coefficient convergence
  and actual DPP count masses tending to exp(-lambda)*lambda^k/k! for all k.
- RH/QDivisorDPPPoisson.lean: actual Q-law count and vacancy consumers;
  consecutive-window specialization retaining mean, rank-cube, and geometric
  budgets explicitly. These are conditional research reductions.
- Analysis/PeriodicWeightedMean.lean: exact finite Abel identity and weighted
  remainder bound, with a generic nonnegative periodic discrepancy theorem.

Open formal providers: Q-wavelet period averages and their weighted-mean
specialization; concrete positive-mean arithmetic windows; finite Fourier
norm estimates for location-comparable windows. Written proofs in
RH/QDPPGrowingWindowsResearch20261014.md construct rank=t^5, x=t^8,
h=floor(lambda*zeta(2)*x^2/S_rank), and additional x,h of order rank^2,
with positive-mean Poisson limits. These analytic constructions are not newly
checked Lean specializations. Superquadratic locations force empty tails in
the written analysis. Other continuum regimes and zeta spectral connections
remain unresolved; no RH or universal continuum-exclusion theorem is claimed.

### Legal-residue projection DPPs and the constant-parity RH target (2026-10-14)

Established: 53 new theorems in five exported modules. All five saved source
modules and the 16 central-declaration axiom audit passed
job_ckDopHaizfaW5vhguVHyDNs2Q-emhH2S (11.578 seconds, exit code 0,
verified true). Every inspected declaration uses only propext,
Classical.choice and Quot.sound. Publication uses the final server checkpoint.

- RH/QDivisorProjectionDPP.lean (13 theorems): actual positive-contraction
  DPP for any Q subspace in the complete divisor-wavelet coordinates;
  exact constant occupation/vacancy, trial-error Pythagoras and nested diagonals.
- RH/QDivisorProjectionParity.lean (6 theorems): exact normalized parity
  residual, constant-parity kernel block, actual joint occupation 4p-3,
  and p >= 3/4 whenever the conductor-2 residue belongs to the subspace.
- RH/QLegalResidueDPP.lean (30 theorems): actual full and masked squarefree
  legal laws; constant vacancy equals full optimizer error; p = I/(1+I);
  monotonicity, strict finite p<1, closure and CRT equivalences; full trial-error
  consumer; exact parity zero-limit equivalence; real reweighted law invariance.
- Analysis/AtomSpanReweighting.lean (1 theorem): independent nonzero scalar
  weights preserve every atom span over a division ring.
- Analysis/PrimeOrdinateFloorPhase.lean (3 theorems): exact cancellation of
  integer parts from normalized unit-circle phases, prime-log specialization,
  and fixed complex-dictionary span invariance under arbitrary ordinate phases.

Conditional research reductions: legal p_n --> 1 or legal L_n(1,2) --> 0
implies Mathlib RiemannHypothesis, by reusing the actual legal-closure/Mellin
consumers. Neither limit is proved here. The squarefree p_n --> 1 equivalence
with SquarefreeExactHeadTailBound retains the substantive uniformly bounded
weighted-tail obligation. That arithmetic provider remains Open.
Zero-phase/equidistribution-to-capacity or trial-energy estimates remain Open.
The inspected FMZ continuous-test consumer retains its explicit classical
UniformSelbergDensity(1/4) provider, not formalized in that development.

Sites are divisor-wavelet labels: site 1 is qOne. The earlier complete-basis
moving-physical-site overlap theorem does not bound this dense legal
projection's fixed-mode parity entry. No RH converse, continuum-unfolding
exclusion, or Hilbert--Polya/zeta spectral identification is claimed.
See RH/QLegalDPPResearch20261014.md for the exact CRT budget, tested sieve
obstructions, phase limitations, theorem inventory, and verification scope.

### Q divisor DPP global overlap and independent moving windows (2026-10-14)

Established: 54 new theorems in four exported modules. Final source-module
verification and the 11 central-declaration axiom audit passed in
job_XVI1iRRut29tJv5d814MWJ3dEtOXDb6Z (18.002 seconds, exit code 0,
verified true). The inspected central declarations use only propext,
Classical.choice, and Quot.sound. Final publication uses the server checkpoint.

- RH/QDivisorWaveletOverlap.lean (25 theorems): actual multiplicative overlap
  arithmetic function; prime-power bridge; exact finite divisor Euler products
  and saturated ratio identities; finite prime correction and gcd budgets.
- RH/QDivisorDPPOverlap.lean (14 theorems): absolute summability; the exact
  global overlap (g^2/(nm)) product_(p in D) 2(1-p^(-2)); Euler limits along
  exhaustive factorial prime sets; actual kernel bound (g^2/(nm))2^card(D)
  and K_N(n,m)^2 <= 4g^2/(nm); arbitrary finite basis subsets and diagonal tapers.
- Probability/DeterminantalIndependentLimit.lean (5 theorems): exact occupied/
  vacant finite configurations, their complete independent Bernoulli limit
  from diagonal kernel convergence, and compact marginal subsequences.
- RH/QDivisorDPPIndependentWindows.lean (10 theorems): explicit fixed-offset
  bound, uniform off-diagonal decay for arbitrary rank sequences, all-pattern
  Bernoulli convergence, automatic Bernoulli subsequences, and probability-level
  exclusion of nontrivial unit-lattice sine limits.

The limit consumer assumes marginal convergence; the subsequence theorem
supplies it from compactness of the actual finite marginal cube. The sine
exclusion assumes adjacent marginals tend to rho with 0<rho<1 and rules out
the sine two-point law. No RH, stationarity, or inter-rank coupling is assumed.

Conditional research reduction: basisKernel_scaled_tendsto_zero_of_gcd_budget
retains the explicit obligation 4 a_N^2 gcd(n_N,m_N)^2/(n_Nm_N) --> 0.
A general continuum unfolding satisfying this budget remains Open.
Unresolved continuum regimes and Hilbert--Polya/zeta identification remain Open.
The complete basis includes the constant mode and proves no legal-residue
approximation result. See RH/QDPPOverlapVerification20261014.md for exact
declarations, proof structure, verification scope, and remaining API packaging.

### Q divisor DPP spectral tails and arithmetic window bounds (2026-10-14)

Established: 53 new theorems in five exported modules. Targeted source and axiom
audit job_zX7LwpDDPKzHBQ1dSU4ELkkn3l8Dqa5I succeeded (18.051 seconds);
supplemental job_PswJuw8N32hUmQbI1s_YMgJ-NVcde599 displayed the 22 initially
truncated axiom results (4.839 seconds). All use only propext, Classical.choice,
and Quot.sound.

- RH/QPrimeWaveletOverlap.lean: exact prime-local reverse spectral masses,
  their positivity, support and normalization, and full local absolute overlap.
- RH/QDivisorWaveletBounds.lean: absolute wavelet <= Jordan weight <= conductor
  squared, and the resulting arithmetic energy bound.
- RH/QDivisorDPPSpectralTails.lean: actual signed Parseval tails; a normalized
  auxiliary PMF whose CDF and tail are occupancy and vacancy; actual kernel trace
  N and almost-sure particle count N; complementary-kernel Cauchy--Schwarz.
- Probability/DeterminantalWindowBudgets.lean: moving finite-window occupation
  and gap convergence from vanishing vacancy or occupation budgets.
- RH/QDivisorDPPArithmeticBounds.lean: the exact arithmetic diagonal,
  K_N(n,n) <= N(N+1)(2N+1)/(6 zeta(2)n^2), exact rough-site diagonal scaling,
  prime-above-cutoff bound, H_N --> zeta(2), and far-window emptiness when
  h_N N^3/x_N^2 --> 0.

The asymptotic window theorem assumes its explicit geometric budget. These
providers use the complete divisor basis including the constant mode; they
prove no legal-residue approximation estimate and no new RH theorem.

The global overlap, Euler limits, gcd bounds, and fixed-offset Bernoulli/sine
results are now checked by the continuation above. Open in Lean: independent-
prime identification of the auxiliary PMF; the 2n/N vacancy estimate and
sharper entire-tail estimate; the remaining continuum and Poisson providers;
any legal-residue or zeta-identification bridge. See
RH/QDPPArithmeticVerification20261014.md for the earlier checked scope and
RH/QDPPOverlapVerification20261014.md for the new providers.
Publication uses the final server-gated aggregate checkpoint.

### Real squarefree residue matrices and the unbounded limit (2026-10-14)

Established: 37 new theorems in three exported modules.
Analysis/MatrixMaximalRayleigh.lean supplies the genuine maximal Rayleigh
eigenvalue for a nonempty real symmetric matrix.
RH/SquarefreeResidueMatrix.lean constructs the complete squarefree conductor
Gram kernel and its real square heads, proves positivity, a non-integer entry,
conductor convergence, the exact H_N=D_N M_N D_N normalization, and the
signed row relation H(1,m)-H(2,m)-H(3,m)+H(4,m)=0.
RH/SquarefreeResidueMatrixGrowth.lean proves a largest eigenvalue of the
odd-site principal submatrix is at least N/(4 zeta(2)) and tends to infinity.
It also proves the first infinite column is not l2, no operator with that
literal column can include e_1 in its domain, and the truncated columns have
no l2 coordinatewise limit.

Persisted-module verification job_sAK4VAYu7k81gOtygxJgY4AyU4PsXv5q passed
(exit 0, verified=true, 15.878 seconds). Publication uses the final
server-gated aggregate checkpoint; its terminal result is reported separately.
See RH/SquarefreeRealMatrixInfinity20261014.md for exact scope and interpretation.

Complete axiom audit job_bHVZoZl1jkRJldh_n0fEC8J5MYvIqKSh passed for all 37
theorems (exit 0, verified=true, 5.053 seconds), using only propext,
Classical.choice, and Quot.sound.

Open: a densely defined selfadjoint operator, a discrete spectrum with ordered
eigenvalue convergence, an exact completed-zeta determinant/zero identification,
and an arithmetic reason for the 2 pi scaling. No Hilbert--Polya realization
or new RH theorem is asserted. The domain obstruction does not exclude every
smaller domain or a different operator construction.

### Q divisor DPP finite rank and moving windows (2026-10-14 UTC)

Server source builds and the 21-theorem axiom audit passed on 14 October 2026
in `job_p4TWFKadHYuhQO_T8qA9lu0lh8EBGj5c` (exit code 0, `verified: true`).
All new declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

- `Analysis/FiniteFeatureKernel.lean`: every finite feature-kernel matrix
  factors through its feature space, has rank at most the feature count,
  and has zero determinant when its size exceeds that count.
- `RH/QDivisorDPPWindows.lean`: exact Q-DPP zero occupation probability for
  more than N distinct sites; moving-window count and vacancy expectations,
  gap determinant, pair covariance, and count variance.
- `RH/QDivisorDPPArithmeticWindows.lean`: the exact physical arithmetic kernel;
  identical finite divisor signatures force zero two-point occupation.

Written unconditional analysis in `RH/QDPPMovingWindowsResearch20261014.md`
proves an exact prime-product occupation law, moving-head saturation budgets,
far-tail bounds, and an absolute-overlap Euler product. The overlap bounds
rule out nontrivial unit-lattice sine limits. They also exclude specified
continuum regimes and give conditional Poisson count limits when the stated
mean and rarity conditions hold, including holes on the square-root head scale.
These analytic estimates and limits are not newly Lean-verified declarations.

Open: formalize the prime-product and overlap providers; analyze continuum
scales outside the proved obstructions; supply any zeta-identification bridge.
No RH or Hilbert–Pólya realization is asserted. Publication uses the server-gated
aggregate checkpoint; its final result is reported with task completion.

### Q block averages preserve growing exact heads (2026-10-13)

Conditional research reduction: `RH/QExactHeadAverages.lean` now defines
`blockAverage` and proves `exists_legal_exact_head_block_averages`.
Given legal Q candidates with exact heads through N and one uniform bound
on their full squared Q residuals, a strictly increasing subsequence has
moving equal-weight block averages that remain legal, equal one through
the block length, and converge strongly to `qOne`.
`blockAverage_eq_prefix_difference` retains the exact identity with two
prefix averages. `blockAverage_head` verifies the literal physical values.
Open: construct the uniformly bounded legal candidate family. No new RH
proof, bound provider, or verification of the paper's sharper block rate is
claimed. Source: the user-supplied CRT carry note and bounded-tail request.

### Q divisor DPPs and positive spectral determinant limits (2026-10-13)

Established structural results:

- `RH/QDivisorDPP.lean`: the complete Q divisor basis defines actual finite-rank
  projection DPP laws. The kernel is an explicit wavelet sum, vacancy is exact
  projection-error energy, kernels converge to the identity, and every fixed
  finite window fills in probability.
- `Probability/DeterminantalComplexGenerating.lean`: actual complex generating
  expectations for finite DPP laws and countable-law finite windows; original-Gram
  determinant ratios; positive weighted feature matrices and real-zero consumers.
- `Probability/ContinuousProjectionCompression.lean`: zeros of
  `det(I-z^2 A)` are real when the finite complex matrix A is positive semidefinite.
- `Analysis/PositiveSpectralNonvanishing.lean`: an exact imaginary-part identity,
  dimension-independent compensated nonvanishing, and nonreal nonvanishing for
  moving nonnegative spectra with pointwise limits at z and i/4.
- `Analysis/PositiveSpectralProduct.lean`: fixed summable positive-spectrum
  partial products converge and determine any pointwise or locally uniform limit.
- `Analysis/LogarithmicHeatSum.lean`: the scalar logarithmic heat sum equals
  zeta in Re(s)>1; no unbounded operator or operator trace is asserted.

Conditional research reductions:

- `RH/HilbertPolyaPositiveProduct.lean`: fixed-spectrum finite-product
  identification is equivalent to the existing infinite-product representation
  and implies Mathlib RH.
- `RH/HilbertPolyaMovingSpectralLimit.lean`:
  `riemannHypothesis_of_strip_positive_matrix_limit` and its locally uniform
  corollary allow changing positive matrices and ranks.

Open: construct the required identification with
`s*(s-1)*completedRiemannZeta s`; construct sampled exact interpolants and prove
their mean is the optimizer; establish any required infinite-product passage or
operator realization. Full-basis filling alone proves neither legal-residue
density nor a GUE scaling limit. See `RH/QDPPHilbertPolyaResearch20261013.md`.

### CRT exact heads, escaping Q energy, and optimizer parity (2026-10-13)

Established: `RH/QExactHeadEscape.lean` constructs legal exact-head candidates
with every fixed coefficient eventually equal to -mu(d), pointwise limit one,
but squared Q error at least (N+1)^2. The same lower bound is retained in
the complete Jordan-weighted Parseval sum. This rules out inferring norm
convergence from exact finite cancellation and coefficient limits alone.

`RH/QCRTDivisorHead.lean` constructs the density-repaired full-divisor
CRT candidate, proves its exact coprime-count identity, covered heads,
periodicity, reflection constant L*rho_L, exact period variance identity,
and full-Q error >= (1-L*rho_L/2)^2/(zeta(2)*L).

`RH/QRamanujanCoefficientInversion.lean` proves finite multiple-transform
inversion for actual packetCoefficient values and distinguishes them from
orthogonal Q-wavelet coefficients using the single atom g_2.
`RH/QOptimizerParity.lean` proves the actual optimizer parity coordinate
equals three times its complete residual energy, is positive at every
nonempty finite stage, and tends to zero iff one is in the full legal closure.

Conditional research reduction: `RH/QOptimizerParityRH.lean` transfers
full Q closure to the Pareto Mellin theorem and derives RH from vanishing
optimizer energy, parity coordinate, or the literal arithmetic Parseval sum.
Open: the vanishing limit or a uniformly bounded legal exact-head family.
No unconditional RH proof or RH-to-approximation assumption is used.
The lcm-family divergence deduction and two-atom mean repair are written
mathematics in `RH/QCRTParsevalConstruction20261013.md`, distinguished
there from the checked finite declarations.

### Q floor Euler calculus and an undamped-prime obstruction (2026-10-13)

Established: `Analysis/ClosedInvariantCalculus.lean` constructs the closed
algebra of bounded operators preserving a closed real subspace. Exponentials
preserve membership in both directions. The explicit log(I-T) series preserves
the subspace; convergence is separately proved from summable power norms.
Summable Neumann powers give exact two-sided inverses of I-T.

`RH/QFloorDilation.lean` realizes T_m f(n)=f(floor(n/m)) on the actual
Q Hilbert space, with T_m T_d=T_(md), squared norm bound 2/m, and the exact
identity T_m g_d=g_(md)-g_m/d. Both the legal span and its closure are invariant.
`RH/QFloorEulerOperators.lean` proves convergence of every nontrivial
integer Neumann series, including m=2; each Euler factor and every finite
prime product preserve legal-closure membership in both directions.
`RH/QFloorEulerCalculus.lean` proves actual convergence of the local
logarithm series and closure preservation for logarithms and exponentials.
`RH/QFloorEulerVonMangoldt.lean` identifies that convergent series as
log(I-T_p)=-sum_(k>=1) Lambda(p^k)/log(p^k) T_(p^k).
No exp/log inverse identity or undamped infinite-prime product is asserted.

`RH/QFloorEulerCandidates.lean` constructs literal legal residue sums
E_(P,m)=sum_(d|P) mu(d)(g_(md)-g_d/m), with exact physical value
C_P(n)/m-C_P(floor(n/m)); C_P counts positive integers coprime to P.
`RH/QFiniteEulerAction.lean` identifies this with the finite Euler
product applied to g_m for distinct primes. At factorial cutoff Y!, the
candidate agrees through coordinate Y with (1/m)qOne-T_m qOne, hence
converges pointwise by eventual equality.
Established obstruction: `RH/QFloorEulerEscape.lean` proves
norm(E_(Y!,m))_Q tends to infinity for every fixed m>1. The proof retains
the exact Pareto decomposition and uses the existing primitive-sieve escape
plus the scaled-isometry gap (sqrt(m)-1)/m. It uses no PNT or open hypothesis.

`RH/QFloorZetaEscape.lean` separately treats coefficient truncations
Z_N=sum_(d<=N)T_d, retaining the exact full energy
norm(Z_N qOne)^2=N/zetaTwo+sum_(n outside [1,N]) Q(n) N^2.
It also proves norm(Z_N g_2)^2 >= N/(16*zetaTwo) and unboundedness on
this fixed legal atom. These coefficient truncations are not identified
with finite prime products.
`RH/QPrimeProductEnergy.lean` and `RH/QPrimeProductTarget.lean`
give complete actual-Q finite-prime mixed moments and derivative-target
errors, including all cross terms and the singleton mass 1/zetaTwo.
Divisor observables are not asserted to be legal residue primitives.

Open: the global capacity/supremum statement and convergence of legal
candidates to qOne. Neither local functional calculus nor pointwise
convergence supplies the missing full-Q bound. The established divergence
excludes the displayed undamped Euler family, not every possible legal
family, damped construction, or exact-head averaging method.

### Explicit Q candidates, Ramanujan coordinates, and exact-head averages (2026-10-13)

Established finite identities: `RH/QRamanujanPackets.lean` represents the
integrated Ramanujan packets as actual Q Hilbert vectors, proves divisor
inversion, and gives the exact finite coefficient transform
a_q = sum_{q | d_i} c_i / d_i for arbitrary positive conductor lists.
`RH/QFullResidueProjection.lean` defines the full-conductor candidate by
the genuine inverse Gram matrix on conductors 2 through n+1, proves legal
stage membership and equality with the actual orthogonal projection, and
proves its unconditional limit is the projection onto the legal closure.

`RH/QExplicitCandidates.lean` gives the same candidate in finite Ramanujan
coordinates and proves the exact full error 1/(1+capacity_n), where capacity
is computed from the genuine covariance inverse. Convergence to qOne is
equivalent to capacity divergence. Any legal exact-head family with a
uniform actual Q error bound supplies convergence of this fixed explicit
matrix sequence.

`RH/QExactHeadAverages.lean` proves coordinate totality, weak residual
convergence, complete signed Gram and infinite weighted error identities,
and constructs legal finite equal-weight averages of a sparse subsequence
with squared error at most B/m + 4/m^2. Its arithmetic-tail entry point
uses positive periods, exact physical heads, and a uniform finite sum
sum_{a=N+1}^{L_N} |1-F_N(a)|^2/a^2 <= B.

`RH/QMobiusExactHead.lean` supplies the explicit arithmetic family
H_N = -sum_{d<=N} mu(d) g_d + (N+1) (sum_{d<=N} mu(d)/d) g_{N+1},
its actual Q encoding, legality, and exact agreement with one through N.
A uniform full Q error bound for this specific family supplies both the
sparse-average and fixed inverse-Gram convergence conclusions.

Established obstruction: `RH/QMixedConductorObstruction.lean` retains
an exact six-square identity and proves the fixed squared Q gap
1/(74*zetaTwo) for conductor-six charge zero, including prime-power-only
integrated Ramanujan packets and residue sums omitting conductor six.

Conditional research reductions, not unconditional approximation of one.
Open: divergence of the displayed covariance information, or a checked
provider of the uniform actual Q error / finite arithmetic tail bound.
The ordinary Hilbert, legality, inversion, and finite-error identities
require neither RH nor those open arithmetic inputs.

### Weighted Q-refinement energy and greedy obstruction (2026-10-13)

`RH/QWeightedRefinementEnergy.lean` proves the exact full-Q quadratic
`paired_fullError_quadratic`, its infinite-sum form, all signed direction
cross terms, completed square, optimal finite weight, zero-direction case,
and `optimized_telescoping`. It reuses the actual QHilbert residue vectors,
the published paired refinement identity, and QPrimeSieve.fullError.

Unconditional arithmetic obstruction: `first_step_unique_minimum` gives
u_2=2 for the canonical first step. `greedy_seed` and
`zero_reciprocal_preserved` identify its absorbing zero reciprocal mass.
`frozen_fullError_lower` and `frozen_not_tendsto_zero` show that every
subsequent sequence of real weights and multipliers greater than 2 leaves
error at least 1/(4*zetaTwo). Summability is proved, not assumed.
This rules out that greedy construction, not the full legal span.

Open for repaired constructions: full infinite-tail control and exhaustion
of the initial error by exact increments. The infinite exhaustion criterion
is a paper-level consequence here, not a newly formalized convergence theorem.
[Research record and scope](RH/QWeightedRefinementResearch20261013.md).

### Primewise zero-ordinate twists and Euler corrections (2026-10-13)

Established local results: `Analysis/PrimeOrdinateTwist.lean` proves 13 results
on the completely multiplicative extension of independently prescribed prime
phases, unit modulus, and the exact absolute-convergence boundary Re(s) > 1.
`Analysis/PrimePhasePerturbation.lean` proves 15 results on power discrepancies,
prime-power convolution, the exact finite remainder, the local Euler correction
bound, and its convergent geometric generating series.

Paper-level research reduction (not a Lean theorem): selecting distinct actual
zero ordinates with prime phases within p^(-2) of -1 gives a nonvanishing
analytic correction to zeta(2s)/zeta(s). Its holomorphic continuation to
Re(s) > 1/2 and its square-root summatory bound are RH-equivalent.
Open formalization obligations: zero-ordinate density and selection; global
multiplicative convolution and normally convergent correction product; classical
Liouville/RH transfer. Open arithmetic obligation: square-root cancellation
for the selected coefficients. No proof of RH or an unconditional density
improvement is asserted.
[Paper proof, exact status, and handoff corrections](RH/PrimeOrdinateTwistResearch20261013.md).

### Finite Weil normalization and shift-aware Schur certificates (2026-10-13)

Established: `RH/FiniteWeilNormalization.lean` proves the finite integral
normalization discrepancy, its closed formula, strict positivity, and the
lower bound Delta(L) >= L/2 through L = 2 log 2. It transfers whole-form
lower bounds with the exact scalar loss. Integrability is explicit.
`LinearAlgebra/ShiftedSchurCertificate.lean` proves an exact sum-of-squares
certificate, the changed inverse-tail contribution to a scalar Schur margin,
and rational counterexamples to two invalid margin transfers (21 theorems total).

Conditional research reduction: `finite_weil_lower_bound_of_block_envelope`
applies the corrected certificate to the actual finite gamma-integral formulas.
Open: Fourier coefficient identification, validated corrected core/tail and
coupling bounds, a fresh endpoint positivity certificate, and cofinal arithmetic
positivity. No RH claim or old endpoint-certificate validity is inferred.
[Scope, verification evidence, and remaining obligations](RH/FiniteWeilNormalizationAudit20261013.md).

### Innovation exponents and the Burnol logarithmic barrier (2026-10-13)

Established scalar implications: `Analysis/InnovationLogBarrier.lean` proves the
sharp parameterized late quartic cap, excludes every eventually uniform real
exponent 0 < p < 4 under an explicit reciprocal-index envelope, bounds the
number of quadratic contraction stages, and proves the sharp quartic constant
restriction eta*c^2 <= 2. A reciprocal model certifies rate compatibility of
exponent four. A sparse cofinal linear lower bound is impossible for positive
antitone convergent residuals.

Established transfer: `RH/BurnolParetoTransfer.lean` maps a lower bound on
literal continuous fractional-part functions to the actual full-residue
optimizer, preserving cutoff and squared norm exactly.
`RH/ActualInnovationLogBarrier.lean` specializes the obstructions to the
existing actual optimizer and assembles the continuous-input contradiction.

Conditional research reduction: the actual logarithmic envelope still requires
a provider of the published Burnol analytic theorem. Open: that analytic Lean
provider and any cofinal positive quartic arithmetic innovation lower bound.
The older two-seed budget distance is distinguished from the full-residue energy.
No RH claim is made.
[Proofs, schedule audit, analytic boundary, and exploratory numerics](RH/InnovationLogBarrierAudit20261013.md).

### Subpolynomial CRT tails and explicit prime windows (2026-10-13)

Established: `RH/CRTReciprocalPowerObstruction.lean` proves the sharp
zeta(2) Pareto/finite-energy comparison and the explicit positive-power
lower bound forced by any actual off-critical zero.
`RH/ParetoReciprocalWindow.lean` preserves the exact window/tail split
and controls the infinite remainder by an amplitude envelope.
`RH/CanonicalPrimeSubpolynomialWindow.lean` proves squarefree support
for the canonical Mobius trial at a prime boundary and full error <= E(p)+1,
where E(p) is the explicit reciprocal-square sum from p through 4*p^2.

Conditional research reductions: `RH/CRTSubpolynomialTail.lean` weakens
uniform boundedness to logarithmic subpolynomial growth, a sparse infimum
criterion, or one finite reciprocal-exponent certificate per stage.
The canonical prime module proves RH from the corresponding explicit E(p)
growth provider. `Analysis/VanishingExponentBudget.lean` supplies the
generic vanishing-exponent-to-log-growth implication.
Open: the original bounded family and the weaker finite-energy providers.
No unconditional RH proof is claimed.
[Exact formulas, quantifiers, and remaining arithmetic goal](RH/CRTSubpolynomialPrimeWindow20261013.md).

### Actual Q residue covariance, prime coordinates, and sieve obstruction (2026-10-13)

Established finite algebra: `LinearAlgebra/CenteredNormalEquations.lean`
preserves the exact rank-one normalization, mean-one variance remainder,
solution-independent information and full block Schur solve/update.

Established actual-Q consumers: `RH/QCovarianceInverse.lean` identifies
covariance forms with Hilbert norms and computes the full Q error.
`RH/QCovarianceInvertibility.lean` proves positive definiteness for distinct
conductors greater than one, genuine inverse formulas, the determinant update,
and optimal error `det V / det G`. `RH/QSquarefreeCapacity.lean` proves
capacity divergence iff actual squarefree closure iff the established exact-head
bounded-tail property, its unconditional RH consequence, and exact monotone
capacity increments. Masked stages use solvable systems without a false inverse.

Established exact moments: `RH/QResidueMoments.lean`,
`RH/QDilationMoments.lean`, and `RH/QDivisibilityResidueCoefficients.lean`
give finite trigamma means/Gram entries, actual inverse-square divisibility
conditioning, and the signed Mobius divisor-coordinate formula.

Established prime and CRT tools: `RH/QPrimeOrthogonal.lean` and
`RH/QPrimePowerOrthogonal.lean` prove finite squarefree and full-exponent tensor
orthogonality under actual Q, including local telescoping inversion.
`RH/QDivisibilityDensity.lean` transfers Noor totality to all actual Q
divisibility indicators. `RH/QResidueRefinement.lean` gives exact atom
refinement, weighted finite extensions, and density-factor updates.
`RH/QPrimeSieve.lean` proves the Mobius sieve identity, finite Euler product,
exact head error, and an unconditional full-error lower bound `1/(4*zetaTwo)`
excluding naive primorial Mobius convergence to one in L2(Q).

Established full assembly: `RH/QCovarianceMatrixInverse.lean` proves the
literal Sherman--Morrison inverse. `RH/QExpectationIntegral.lean` supplies the
actual Bochner-integral/weighted-series bridge. `RH/QDivisorWaveletDensity.lean`
and `RH/QDivisorWaveletFactorization.lean` provide unconditional dense span and
the exact arithmetic Jordan Gram diagonal. `RH/QDivisorHilbertBasis.lean`
assembles the complete orthonormal basis and full residue Gram/error Parseval
identities. `RH/QArithmeticCapacity.lean` identifies the complete Jordan-weighted
arithmetic energy with the actual squarefree stage error.

Conditional research reduction: `capacity_tendsto_iff_riemannHypothesis`
retains an explicit analytic RH-to-squarefree-Q-density provider.
Open: prove that provider and derive global residue-capacity or weighted-sieve
tail estimates. Finite invertibility or divisibility totality does not discharge
these obligations. Wolfram calculations are not part of this formalization.
[Exact scope and research agenda](RH/QPrimeStructureResearch20261013.md).

### Sharp Q comparison and squarefree geometric converse (2026-10-13)

Established: `RH/ZetaTwoCRTReciprocalEnergy.lean` proves
B_L/zeta(2) <= full Q squared error <= B_L, together with both
boundedness and zero-limit equivalences for varying periods.
`Analysis/FiniteObservationApproximation.lean` preserves finite continuous
linear observations exactly during subspace approximation.
`RH/CRTSquarefreeConverse.lean` identifies the literal squarefree span and
proves closure membership equivalent to uniformly bounded exact-head tails;
closure also supplies arbitrarily small tails at each fixed head.
`RH/ZetaTwoCRTSquarefreeConverse.lean` proves the identical criterion in Q,
including both directions of the actual P/Q squarefree closure transfer.

Conditional research reduction: `RH/CRTSquarefreeBoundedTail.lean`,
`riemannHypothesis_of_squarefree_span_bounded_tail`, formalizes the
literal cofinal squarefree divisor-span sufficient goal with a finite Icc tail.
Open: construction of the uniformly bounded family and the separate analytic
RH-to-squarefree-density implication. No proof of RH is claimed.
[Exact statements and scope](RH/CRTSquarefreeQConverse20261013.md).

### Reciprocal-square CRT exact-head criterion (2026-10-13)

Established: `RH/ParetoCRTReciprocalEnergy.lean` bounds the complete
periodic Pareto energy by twice its finite reciprocal-square certificate
and gives exact removal of initial zero coordinates.
`RH/NormalizedResidueExactHeadCharges.lean` extracts normalized coefficients
and proves the exact-head identities c_m=-mu(m) and sum c_d/d=1.
`RH/CRTReciprocalCertificate.lean` certifies the period-six error
1669/27684<1/16 by exact arithmetic.

Conditional research reduction:
`RH/CRTReciprocalExactHeadRH.lean`,
`riemannHypothesis_of_cofinal_divisor_reciprocal_bound`.
Actual finite divisor-supported sums, cofinal exact initial intervals,
and one uniform reciprocal-square certificate bound imply Mathlib's
RiemannHypothesis. Legality, boundedness of each finite sum, periodicity,
and the Mellin closure-to-RH implication are proved dependencies.
Open: a provider for the uniform arithmetic energy bound.
The theorem permits all divisor supports, including squarefree periods.
The geometric converse is supplied above; the analytic RH converse remains Open.
[Scope and research obligation](RH/CRTReciprocalExactHead20261013.md).

### Exact-prefix CRT reduction to one tail moment (2026-10-13)

Four recovered modules passed server check
`job_CfF-ItEXLk9irhbBIdf40jU-kB3HtFhC` (exit 0, verified true).
Ten axiom checks returned only `propext`, `Classical.choice`,
and `Quot.sound`. Final checkpoint
`job_E8SG2DV7UeuZtjtHgYh3lbPhsF5Krxan` succeeded on 2026-10-13
at 07:27:49 UTC and published
`85f1a6f673381dbde48f418a8b532e11d95b9c9b` (`pushed: true`).
Its full-scope incremental validation built the aggregate project and all
four changed-module targets in 58.617 seconds. The four recovered sources
match the published files exactly; the integrated publication gate is
satisfied. This status reconciliation is documentation-only.

- `Analysis/AffineObservationProjection.lean`: affine optimizer with
  one scalar observation, exact minimum, full square remainder, uniqueness.
- `RH/ExactHeadTailMoment.lean`: exact prefix iff one reciprocal tail
  moment after the Mobius head is fixed; finite legality, positive
  denominator, attained complete minimum, dictionary monotonicity.
- `RH/ExactHeadCRTExample.lean`: three complete-energy M=1 formulas.
- `RH/CanonicalMobiusErrorEnergy.lean`: unconditional PNT-backed
  complete error-energy limit E_N/N -> 0.

**Conditional research reduction**:
`riemannHypothesis_of_cofinally_bounded_tailMinimum`.
**Open provider**: a uniform bound on the complete optimized error at
cofinally many prefixes for a nonempty finite dictionary schedule.
The sublinear canonical error does not supply this bound.

The manuscript's literal determinant, fixed-anchor representation,
unrestricted-infimum dichotomy, and constant-12 estimate are not newly
certified here. The existing RH-to-natural-density assembly retains its
analytic Baez-Duarte provider; the new bounded-minimum-to-RH implication
does not use it. Provenance: user-supplied CRT record of 2026-09-30.
[Verification and recovery record](RH/ExactHeadCRTVerification20261013.md).

### Resonance-cell nullspace and actual logarithmic boundary gain (2026-10-12)

`LinearAlgebra/ResonanceCellPotentials.lean` adds eighteen public theorems:
exact selected-cell interval, simultaneous common-potential classification,
signed chain reconstruction, short boundary anchors, and the complete
source-displacement square certificate with coefficient 6/5.

`RH/ResonanceCellBoundary.lean` adds sixteen public theorems and three
private proof helpers. The old-anchor and commuting providers are discharged
for the actual Pareto constant-target residual. The legal root correction
uses one or two ternary boundary packets and has complete norm at most
`B_M = 8 log(M+1) + 8 ||digitHilbert 3 1||^2 + 996`.
The exact enlarged projection gain satisfies `lambda_M^2 <= B_M Delta_M`.
No RH assumption or source minorant is used. Both modules are exported.

Established: the stated finite identities, actual-source specialization,
and logarithmic common-mode gain. The geometric rank formula in the proof
record is proved on paper and checked finitely, not a Lean rank declaration.
Open: control of the uncovered canonical sources and a noncircular actual
residual minorant sufficient for the global logarithmic gain target.

Persisted-module audit `job_eQvm3yiuapEa53Pcga6IUGNLXLCbhXUV` passed
(exit 0); decisive axiom output is only `propext`, `Classical.choice`,
and `Quot.sound`. Publication requires the final server checkpoint.
[Proof and finite Wolfram record](RH/ResonanceCellBoundary20261012.md).
Provenance: the supplied global approximation/resonance-blind-pattern
handoff and existing exact generator identities; no novelty claim.

### Rate obstruction to prime-only gain certificates (2026-10-12)

Five theorems and two definitions extend `RH/PrimeSensorGain.lean`.
The actual dyadic relative gain is exactly the normalized prime observation
plus the normalized remainder square. If the prime observation schedule is
summable, distance decay to zero is equivalent to nonsummability of that
actual remainder schedule. No decay or nonsummability provider is proved.

`RH/PrimeSensorGainRateBarrier.lean` adds eight theorems and one definition.
The actual new-prime block has at most `2^n` indices. A bound `|c_q| ≤ C/q`
gives observation energy at most `C²/(2*2^n)`. Combined with the explicit
distance floor `D_(2^n) ≥ L/(n+1)`, the normalized observation is bounded
by the summable schedule `C²/(2L)*(n+1)*2^(-n)`. Every nonnegative
minorant is then summable. This limits one possible use of the preceding
prime-only sufficient criterion; it does not invalidate that criterion.

Established: finite cardinality/energy estimates, the complete actual
gain split, and the summability/convergence equivalences as stated.
Conditional rate obstruction:
`dyadicNewPrime_minorant_summable_of_mobius_scale`.
Open: uniform actual moving-prime coefficient control.
Analytic formalization pending: the classical logarithmic distance floor
and its actual two-seed comparison.
Open: actual full-gain or remainder nonsummability.

Persisted-module check `job_krVfzyikEMLyr9lpPh3n0fpw4iL8-7HO` passed
(exit 0); decisive axioms are only `propext`, `Classical.choice`,
and `Quot.sound`. Final server checkpoint acceptance precedes publication.
[Gap attempt and finite tests](RH/PrimeSensorGapAudit20261012.md) documents
the reviewed RH-dependent approximation theorem, the explicit hypotheses,
and complete-tail numerical checks through cutoff 64. RH remains unresolved.
Provenance: the supplied handoff and the request to attack its actual gap;
the finite rate obstruction is derived here without a novelty claim.

### Closed endpoint for the Pareto first-coordinate budget (2026-10-13)

`Analysis/RealCofinalLimits.lean` records elementary cofinal limit lemmas.
`RH/FirstCoordinateEndpoint.lean` reuses the existing exact normalized
dyadic identity and retains its first-coordinate contribution:
`(2-sqrt 2)*limitEnergy + (sqrt 2/4)*r(1)^2 <= r(1)`.
Thus a nonzero residual has a strict detector gap. The endpoint upper bound
`r(1) <= (2-sqrt 2)*limitEnergy` forces the actual residual to vanish.

The cofinal conditions `F_n(1) >= 1-epsilon` and
`1-F_n(1) <= (2-sqrt 2)*energy n + epsilon` are each equivalent to residual
vanishing. Their RH consumers are conditional research reductions.
Open: supply either bound for the actual projections at arbitrarily late stages.

`RH/FiniteDyadicEndpoint.lean` retains the entire normalized mismatch square
and the actual energy gain in a mixed-scale identity and quadratic bound.
`RH/GramEndpointCriterion.lean` gives the concrete finite statistic
`v^T G^-1 b - (2-sqrt 2)*b^T G^-1 b`, its exact unconditional limit, and
the cofinal threshold `sqrt 2-1`.
Open: prove that arithmetic cofinal threshold. Matrix positivity alone does
not supply it. The classical RH converse is not newly formalized here.

Source: Christian Noack's Pareto parity agenda and direct deductions from the
existing `firstCoordinate_eq_energy_add_dyadicRemainder`; no novelty claim.
The stronger quadratic bound and endpoint consumer passed isolated server
job `job_yJ7mmCx1osxECbpjg-eg_HuZmLj-IJAb`; selected dependencies use only
`propext`, `Classical.choice`, and `Quot.sound`. The final targeted module
and six-theorem axiom check passed in `job_s4ANi3y_gdYxmNKog7JoD_cH462L0WN1`
(exit 0), with only the same standard foundations. The four modules contain
24 theorems and one definition. An earlier automatic approval review blocked
publication. Subsequent server checkpoint
`job_jTimVyxmc7257OMYXJ8nOuhIWMSzv9_e` validated the aggregate, all four changed
modules, and integrated source, then published commit
`c62d051c28fc6edaf6c68231acf4ce75d8a591c3`.
The actual finite cofinal arithmetic budget remains Open.

### Quadratic Pareto endpoint and odd-coordinate signs (2026-10-13)

Fifteen theorems and one definition extend the actual Pareto endpoint program:
`Analysis/QuadraticDetectorBudget.lean` (2 theorems),
`RH/FirstCoordinateQuadraticBudget.lean` (5 theorems, one definition), and
`RH/ParetoOddCoordinateSignCriterion.lean` (8 theorems).

The existing quadratic detector permits the larger closed cofinal allowance
`c*energy n + (sqrt 2/4)*(c*energy n)^2`, where `c=2-sqrt 2`.
This cofinal upper budget is exactly equivalent to actual residual vanishing.
The qualitative condition `limitProjection(k) <= 1` at every odd `k >= 3`
is also equivalent to zero residual. A surviving defect therefore has an odd
overshoot witness. The sign criterion needs no uniform rate in the coordinates.

Established: scalar detector strictness, the stated actual residual
equivalences, and their conditional RH consumers.
Open: the actual cofinal optimizer upper budget.
Open: the odd-coordinate limiting upper-bound provider.
The larger `3/2` quadratic allowance remains a paper resolvent argument;
it is not formalized by these three modules. RH remains unresolved.

The coherent 15-theorem check `job_QCvb8j5dfISo7GrOxLZtP7OWrK-d7ZmV` passed
(exit 0). Both decisive RH consumers depend only on `propext`,
`Classical.choice`, and `Quot.sound`. Persisted modules and reverse dependents
must pass the mandatory server checkpoint before publication.
Persisted-module audit `job_0rW7Z15dBT_ovJ8MItFrPvnnG-lBqhUn` also passed
(exit 0): all three owning modules compiled, and six selected theorem
dependency reports contained only the same standard foundations.
Aggregate server build `job_22cwq7Byye1a8jDMFPprVmOwQvFvXC7i` passed
(`lake build RiemannResearch --quiet`, 58.6 seconds). Publication remains
subject to the mandatory push-enabled server checkpoint.
Source: Christian Noack's supplied Pareto parity continuation, Section 6,
and direct scalar deductions from `firstCoordinate_energy_quadratic_lower`;
no novelty claim is made.

### Sharp finite prime observations and actual legal gain (2026-10-12)

`RH/PrimeSensorProjection.lean` adds nineteen proved theorems and three
definitions. It explicitly inverts the normalized actual prime sensor Gram
`2I + 2vvᵀ`, where `v_q = 1/q`, without a matrix inverse dependency.
For `E = sum c_q²`, `t = sum c_q/q`, and `S = sum 1/q²`, the exact
minimum observation energy is `J = (E - t²/(1+S))/2`. The interpolation
and complete physical error identity retain the remainder square.
The improvement over `E/(2(1+S))` is the exact nonnegative pair sum
`sum_(q,r) (c_q/r - c_r/q)² / (4(1+S))`; its harmonic specialization
also identifies a pattern with zero improvement.

`RH/PrimeSensorGain.lean` adds ten proved theorems and one definition.
The exact energy is applied to the actual full-budget optimizer increment,
with complete stage and finite cumulative remainder identities. A
hypothetical off-line zero imposes a finite observation budget; exceeding
it gives an explicit conditional zero-exclusion certificate.
Both modules are exported from `RiemannResearch.lean`.

Established: the exact finite interpolation, optimality, completed squares,
sharp observation bounds, actual distance-drop identities and stated
finite zero-exclusion implications.
Conditional research reduction:
`riemannHypothesis_of_primeObservedFitEnergy_minorant`.
Open: a proved lower schedule for the normalized actual observed energies.
Open: nonsummability of that successful nonnegative schedule.
No provider for either obligation or for the logarithmic gain target is
claimed. The sensor interpolant is not claimed to be a legal correction.

Persisted-module audit `job_r9V0YdnK2ntci3DdvRfjZ7pv9u8GvE0X` passed
(exit 0). Decisive theorem axiom output is only `propext`,
`Classical.choice`, and `Quot.sound`. Final publication requires the
server checkpoint's validation of the changed modules and dependents.
The proof record includes 50/80-digit Wolfram checks with complete
periodic infinite-tail weights and singular Gram pseudoinverses:
[Prime sensor proof record](RH/PrimeSensorProjection20261012.md).
Provenance: the supplied consolidated Pareto/zero-ordinate handoff supports
the problem and prime-coordinate strategy; the finite refinements are
derived here from existing exact sensor identities, with no novelty claim.

### Exact two-zero Pareto Mellin obstructions (2026-10-12)

`RH/ParetoMellinTwoKernel.lean` adds nine declarations: conjugation of the
literal kernel and physical transform, cross-kernel integrability and its
exact Gram entry, the two-kernel test and its L² membership, exact pairing,
complete signed energy, and exact completed-square remainder.

`RH/ParetoMellinZeroPairObstruction.lean` adds eleven declarations. For
`q = (2 Re s - 1) / |s|²`, the explicit conjugate-pair coefficient has both
target signature and continuous energy equal to `2q - q²`. This charge is
positive and strictly greater than `q` for nonreal `Re s > 1/2`. An actual
zero then gives the exact physical error identity
`||one - f||² = 2q - q² + integral(remainder norm²)` for every vector in the
actual legal residue closure. The corresponding lower bound and a
witness-based zero-free certificate follow. The unrestricted two-zero
variational identity and bound preserve the complete signed cross term.

The coherent development check `job_hUW7HoyY-_Bt6Ba8i7ZVT1dAT5bwJmlC`
succeeded (exit 0); axiom output for the decisive theorems is only
`propext`, `Classical.choice`, and `Quot.sound`. Publication requires the
server checkpoint's validation of the final modules and integrated source.

Established: these exact analytic identities and implications use actual
zeta zeros and actual legal-closure membership as stated antecedents.
Open: unconditional decay of the actual optimizer errors; RH is unresolved.
See [the proof record](RH/ConjugateZeroMellinObstruction20261012.md).
Provenance: finite Mellin Gram specialization of the classical Burnol
obstruction strategy; no mathematical novelty claim is made.

### Stable foundations and wider dependency cleanup (2026-10-11)

Fifty-five existing declarations (53 public and two private helpers) move
verbatim into narrower mathematical owners. Public names, statements, proof
bodies, attributes, and research-obligation status remain unchanged.

- `RH/ArithmeticCumulativeBasic.lean` owns the 19 arithmetic primitives and
  cumulative-sum identities previously mixed with signed Green-energy proofs.
- `RH/ParetoWeights.lean` owns the Pareto weight, its normalization and limiting
  lemmas, and square-to-absolute summability. Geometric-mixture and Gibbs
  operator proofs import this foundation.
- `RH/ParetoHilbertPhysical.lean` owns ten physical-coordinate definitions and
  identities previously in `ParetoGibbsHilbert`; `sum_mobiusDifference` now
  belongs to the existing `ParetoResidueDuality` inversion foundation.
- `RH/ResidueTailCertificate.lean` owns the certificate predicate and four
  elementary annihilator declarations; tail regularity remains separate.
- `Analysis/CesaroMeanEnergy.lean` owns `conditionalWeight`, its positivity,
  and `bounded_mean_energy_summable`. The existing
  `Analysis/CesaroFiniteCalculus.lean` now owns
  `RiemannResearch.Probability.ConditionalIID.cesaro`.
- `Analysis/ActualZeroOrdinateSummability.lean` owns
  `RiemannResearch.Analysis.ActualZeroOrdinate.reciprocal_ordinate_summable`.
- `NumberTheory/PositiveDilationSum.lean` owns `positive_dilation_sum`.
- `RH/WeilExplicitFormula/Tail/WindowCount.lean` owns
  `Zeta23.Tail.LocalCount.ofWindowCount`. The existing `Statement/SeamClosed`
  owns `Zeta23.trivial_chain`; `FromPNTPlus/Auxiliary` owns root `deriv_ofReal`.
- The RH application `riemannHypothesis_of_bounded_exact_subspace_heads`
  moves to existing `RH/BalancedExactHeadEnergy.lean` under its original
  `RiemannResearch.RH.Pareto` namespace. `ParetoExactHeadClosure` retains its
  three general closed-subspace theorems.

The wider import-only cleanup names actual declaration owners and removes
unrelated application paths. See
[the foundation dependency audit](RH/LakeDependencyAuditFoundations20261011.md)
for preservation hashes, combined graph effects, and verification scope.

### Broader structural Lake dependency cleanup (2026-10-11)

Thirty-two existing declarations, including one private helper, are relocated
with their statement and proof/definition text preserved. Public names and
mathematical status are unchanged. The new ownership is:

- `NumberTheory/MobiusReciprocalSum.lean`: the reciprocal Möbius sum and four
  scalar finite-sum/Cesàro identities formerly in canonical Hilbert applications.
- `NumberTheory/PrimeNumberTheorem/MobiusReciprocal.lean`: the existing PNT
  limit `RiemannResearch.RH.Pareto.mobiusReciprocalSum_tendsto_zero` and its
  private range-conversion helper.
- `RH/ConditionalMeanEnergy.lean`: `conditionalMeanError`,
  `conditionalMeanSquare`, their nonnegativity lemmas, `mean_eq_one_of_head`,
  and `legal_conditionalMeanSquare_summable` in `RiemannResearch.RH.Pareto`.
  Its RH criterion `riemannHypothesis_of_bounded_conditionalHeadMinimum`
  now belongs to `RH/ConditionalMeanMinimumCriteria.lean`.
- `RH/MellinCriticalPoint.lean`: `criticalPoint` and its three basic lemmas in
  `RiemannResearch.RH.Pareto.MellinFrequency`.
- `RH/MobiusDifferenceCLM.lean`: anchored evaluation and Möbius-difference
  continuous linear maps, with their two application lemmas.
- `RH/ParetoResidueDuality.lean`: residue/packet boundedness lemmas;
  `RH/ParetoDilation.lean`: bounded-error and weighted-summability lemmas;
  `RH/ParetoSequenceCertificates.lean`: the specialized
  `primePowerCombination_noiseSignal_floor` theorem formerly in `ParetoNoiseSignal`.
- `RH/DilationWaveletAlgebra.lean`: `hilbertDilation_digit_one_sequence`;
  `RH/ArithmeticCumulativeEnergy.lean`: `fullSquaredNorm`.
- `RH/WeilExplicitFormula/GammaFacts/DigammaGrowthWide.lean`:
  `Zeta23.ThmE.digamma_growth_wide`, formerly in the character explicit formula.

No result or open research obligation changes. See
[the broader dependency audit](RH/LakeDependencyAuditBroader20261011.md) for
the complete relocation record, graph measurements, and validation scope.

### Structural Lake dependency cleanup (2026-10-11)

Sixteen existing declarations move verbatim with their fully qualified names,
statements, hypotheses, attributes, and proof or definition bodies preserved:

- `RH/WeilExplicitFormula/RvM/CompletedZeta.lean` now owns the six completed-zeta
  analyticity, factorization, zero-equivalence, and nonvanishing lemmas formerly
  in `RvM/CountByIntegral.lean`, under the unchanged `Zeta23.RvM` namespace.
- `RH/ZetaStripReflection.lean` now owns
  `RiemannResearch.RH.riemannZeta_one_sub_eq_zero_of_strip`, formerly in
  `RH/NymanAutocorrelationNullity.lean`.
- `Analysis/SmoothSuperexponentialDecay.lean` now owns the smooth decay class
  and its six general closure/accessor lemmas, formerly in
  `RH/NymanCompletionAdmissibility.lean`, under `RiemannResearch.Analysis`.
- `Analysis/MellinCesaroSummability.lean` now owns
  `RiemannResearch.RH.Pareto.conditionalMellinDualSquare` and
  `conditionalMellinDualSquare_nonneg`, formerly in `RH/ConditionalMeanRHBridge.lean`.

No mathematical result or research-obligation status changes. Consumers use
narrower imports. See [the follow-up dependency audit](RH/LakeDependencyAuditFollowup20261011.md)
for exact declaration names, source-preservation evidence, and validation scope.

### Exact ordinate counting windows and pair-correlation reductions (2026-10-11)

Four principal finite results and actual-zero assembly passed the combined server
candidate in `job_PR_vKXrffVXh4S7Sk0zbCHyXnY3GkstC`; final project verification
and publication are gated by checkpoint. See RH/OrdinatePairCorrelationVerification20261011.md.

Established finite results (no RH or simplicity assumption):
- OrdinateWindowVariance: exact clipped first/second counting moments, support
  specialization, and triangle = squared mean + centered count variance.
- OrdinateTriangleSecants: hinge convexity, inclusive/strict secant counts,
  collision-atom lower bound, and quantitative transfer of three energy errors.
- CosinePolynomialMeanSquare: complete signed finite cosine mean square with
  difference and sum frequencies retained; zero and even cosine kernels.
- ActualZeroWindowVariance: actual multiplicity-copy count and variance identity
  with explicit geometric lower-support and exact mean normalization.

Conditional research reduction and Open obligations:
- Paper: prime polynomial mean square reaches cutoff X=T by the classical
  Montgomery--Vaughan theorem; actual beta-sensitive contour residual is exact.
  These analytic inputs, PNT/Fujii and vague/asymptotic transfer are not newly
  formalized by the four finite modules.
- Open: signed actual prime/residual covariance plus residual energy converges
  to the high-frequency sine-variance tail for every fixed positive window.
  RH/OrdinatePairCorrelation20261011.md (5.7)--(5.8) gives the exact target.
- Open: a usable uniform microscopic Selberg-type analytic approximation.
  No ordinate PCC or global RH conclusion is asserted.

### Two-seed zero budgets and sharp joint-prime contrast certificates (2026-10-11)

Established without assuming RH:

- Analysis/ResidualGainBudget.lean: exact finite log-ratio accounting and
  ordinary/logarithmic gain budgets from a positive finite residual floor.
- RH/DyadicGainZeroBudget.lean: the actual two-seed projection distance obeys
  the Mellin floor of each hypothetical zero with Re(s)>1/2 and s!=1.
  This supplies finite and infinite explicit gain budgets, summability, and
  finite zero-exclusion certificates from actual gains or legal screened costs.
- RH/MultiPrimeContrastObstruction.lean: actual prime-coordinate Riesz Gram
  entries, the complete finite quadratic form including its rank-one term,
  a joint completed-square contrast error identity, an explicit feasible
  minimum-norm coordinate model, and the actual finite-budget distance floor.
  The model's feasibility is for the finite coordinate constraints only.

Conditional research reductions:

- zeta_ne_zero_of_dyadic_log_cost: Open construction of finite legal screened
  witnesses whose exact log-cost charge exceeds the stated zero budget.
- Actual dyadic gain divergence and the note's logarithmic gain lower bound
  remain Open. No actual-zero Haar cancellation, two-seed density, RH converse,
  or unconditional RH provider is added.

See RH/HaarResidualGainContinuation20261011.md for the exact formulas and
the distinction between complete legal gains and contrast-only corrections.

### Consecutive zeta ordinates, gap weights, and empty windows (2026-10-11)

Twelve Analysis modules add exact finite phase transport, signed quadratic,
cubic and quartic remainders, endpoint corrections, controlled-lag diagonal
Haar convergence for all continuous pair tests, gap-weighted Haar and selected
normalized-gap means, and the finite marked stop-loss/empty-window mechanism.

ActualConsecutiveOrdinates constructs sorted actual-zero copies with their
analytic multiplicities, without RH or simplicity. ActualConsecutivePhase
identifies the chronological diagonal sums with the existing actual FMZ sums;
ActualConsecutiveGapWindows specializes the exact geometric identities to
actual chronological gaps. The final padded endpoint at T and the omitted
initial interval remain explicit.

Classification of the actual asymptotic conclusions: **conditional research
reductions**. **Open:** a Lean provider of UniformSelbergDensity (1/4).
**Open:** actual Fujii squared/cubic/quartic gap-moment providers and rates.
**Open:** actual global-sequence/triangular-row assembly for the abstract
continuous distribution laws. **Open:** positive-threshold marked stop-loss
factorization; zero-threshold/first-moment results do not prove independence.
No RH assumption, project-local axiom, or placeholder proof is introduced.
See RH/ConsecutiveOrdinateHarmonicAnalysis20261011.md for theorem scope,
provenance, exact normalization and the complete obligation ledger.

### Strengthened finite-prime FMZ conditional on Selberg (2026-10-11)

The finite-prime Analysis assembly culminates in
ActualPrimeTorusFMZContinuous.tendsto_centered_continuous_div_poisson_of_selberg.
For arbitrary continuous f on the actual finite prime torus, conventional
Fourier decay B > card(P) + 1 implies the actual multiplicity-weighted FMZ
limit with product-Haar centering and the explicit sum of centered Poisson
kernels. The simultaneous rational majorant is now linear in log height.
The weighted Wiener condition is exactly sum_k norm(fhat(k)) *
[1 + sum_p abs(k_p) log(p)] < infinity, improving the former quadratic weight
and sufficient B > card(P) + 2 threshold. Uniform rational Landau limits,
zero-count bounds, prime arithmetic, mixed modes, product Haar coefficients,
lattice summability and actual Fourier reconstruction are proved.

The sole remaining analytic premise is UniformSelbergDensity (1/4).
Classification: **conditional research reduction**. The classical Selberg
provider is still **Open as a Lean formalization**. No RH premise, placeholder
or project-local axiom is introduced. The strengthened full theorem passed
server job_bXTEotl9WOMZJz3Wm35qHgWyJYJaLFLp with only standard foundational
axioms. Publication is gated by the final checkpoint's exported-project build.
See RH/FinitePrimeFMZAssembly20261011.md for exact formal scope and
RH/FMZStrengtheningWeil20261011.md for the quantitative paper deductions,
signed prime Gram and fourth-moment identities, infinite-prime measure
obstruction, and full Weil/Pareto obligations still needed for RH.

### Precise Selberg density input and strengthened actual-zero deductions (2026-10-11)

Analysis/ActualZeroSelbergDensity adds twelve theorems:
the exact power/exponential equivalence; inclusive-to-strict actual count
transfer; reflected two-sided and normalized tail bounds; the real-exponent
loglog/log window rate; general-exponent FMZ comparison and every fractional
frequency band; the classical 128 C / 3 specialization; and the uniform-input
fixed-mode limit. Existing Riemann--von Mangoldt supplies the count normalizer.

Classification: **conditional research reduction** when a Selberg input is
required. Selberg's one-quarter bound is an established unconditional theorem
on paper; a checked provider of UniformSelbergDensity (1/4) is **Open as a Lean
formalization**. No RH assumption or project-local axiom is introduced.
Five selected axiom reports in server job
job_g_2EoPheTC2qaVQM4c7q5f5fwp51Dpne contain only standard foundations.
Final publication requires the server checkpoint.
See RH/SelbergDensityStatus20261011.md for exact scope and provenance.

### Recovered actual-zero FMZ, circle Poisson, and Pareto bridges (2026-10-11)

Eight new modules and the strengthened existing ActualZeroCoshMass passed the
combined server import check `job_sOL1L-tn_natEbX91GhBXduzZZD9XHAh`.
Thirteen selected transitive axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. Publication uses the final server
checkpoint's audit and affected-module validation of the integrated delta.
Precise scope and recovery provenance are in RH/FMZHaarParetoRecovery20261011.md.

- ActualZeroFMZComparison: actual ordinate/Landau comparison conditional on the
  displayed Selberg right-tail bound; complete finite endpoints, rational
  majorant, both frequency signs, and the explicit small-frequency constant.
- PoissonHaarSpecialization: actual normalized-circle Poisson kernel, both
  Fourier signs, real rational density, strict positivity, mass one, centering,
  and even-power multipliers for the displayed legal radii.
- ArithmeticWeightedFourierRemainder: exact signed deterministic Fourier
  aggregation with explicit modewise and summability premises.
- ParetoHorizontalZeroBridge and ActualZeroReciprocalConstant: actual signed
  legal candidates and inverse-Gram optimizer, all-sign multiplicity-weighted
  reciprocal sum, positive explicit C0, E4 <= e S2 / 4, S2 <= C0, and
  Qn <= 1 - 4 E4 / C0; no RH or simplicity premise.
- ParetoResidualBoundaryEnergy and ParetoFiniteMellinHalfPlane: full signed
  finite Mellin identity on Re(s) > 0, s != 1, and the exact critical-line zeta
  energy with denominator 1/4 + t^2, target cross term, and complete norm square.
- ActualZeroCoshMass and ActualZeroParetoCoshBridge: sharp two-sided bounds for
  the existing convergent regularized cosh mass and its actual Pareto-error bound.

Open obligations remain explicit: the classical Selberg Lean provider,
and Pareto residual convergence or cosh-mass vanishing. The later finite-prime
assembly discharges the rational Landau, mixed-mode and Haar/Poisson tasks.
The resulting conditional Fourier theorem does not prove RH.

### Recovered harmonic analysis and analytic reciprocal developments (2026-10-11)

Twenty recovered modules passed the combined server import check in
`job_qLV5LgK5vCeCoU--RBHGL-2xcKlhEXoH`; publication is gated by the final
server checkpoint. Validation and interrupted jobs are recorded in
RH/LeanRecoveryStatus20261011.md. Exact signed identities and explicit analytic
premises are retained throughout.

Structural results verified by the combined server check:
- LagPhase and PrimePhaseTorus: exact lag-boundary cancellation, quotient-metric
  estimates, actual prime-phase characters and two-prime injectivity.
- ActualPhaseGramExpansion: complete signed actual phase Gram expansion and
  equivalence of residual decay to decay of its displayed cosh correction.
- ActualZeroCoshMass: convergent regularized cosh mass, its two-sided comparison
  with horizontal fourth energy, and its zero criterion equivalent to RH.
- BalancedPowerTransfer, BalancedTuplePhase, FrequencySpreadInterval: exact
  power-error transfer, balanced tuple identities and interval spread bounds.
- FiniteCollisionCertificates: finite collision excess and injectivity tests;
  ActualZeroBalancedTuplePhase and ActualOrdinateCollisionCertificates provide
  actual-zero specializations with analytic multiplicity preserved.
- AnalyticCircleSquareBounds, EmpiricalCompactCircleControl and
  ActualAnalyticPolynomialControl: scalar-to-compact analytic control, entire
  Dirichlet polynomials and exact actual-zero weighted averaging.
- TruncatedMobiusConvolution, AnalyticDirichletPolynomial and
  ProductFrequencyDispersion: exact product coefficients, signed residual
  polynomial and product/fiber frequency-dispersion identities.
- EmpiricalReciprocalTransfer and ReciprocalRateBalance: finite empirical
  product-error identities, moment/density transfers and rate balancing.
- AbsoluteReciprocalCompatibility and AnalyticAbsoluteReciprocal: unconditional
  quantitative reciprocal compatibility on half-planes Re(s) >= sigma > 1.

Conditional research reductions and Open obligations:
- Actual phase/lag limiting laws: Open analytic equidistribution and decay
  providers in the displayed theorems; no Haar or Poisson law is assumed proved.
- Cosh-mass RH criterion: Open proof that the nonnegative mass vanishes.
- Collision-based global criticality: Open cofinal small-excess certificates;
  finite conditional tests do not prove RH or simplicity globally.
- Actual compact reciprocal laws in 1/2 < Re(s) < 1: Open the requisite scalar
  empirical second-moment/FMZ estimates and divisor-tail/counting providers.
  Compactness and rate transfers alone do not discharge these obligations.


### Quantitative sampling and finite collision certificates (2026-10-11)

Prior local validation: the 31 modules compiled under Lean 4.33.0-rc2;
the combined import and selected transitive axiom reports passed.
Repository integration and publication are subject to the mandatory server
checkpoint, which validates the integrated source tree before publication.

Established finite results:
- RationalLogSeparation, LogarithmicTailCounting, LogarithmicMatrixMoments:
  rational nonresonance separation and factorial logarithmic matrix moments.
- ZeroSamplingErrorTransfer, ZeroSamplingHilbertSchmidt, WeightedSamplingSchur,
  HigherPowerErrorTransfer, BalancedSamplingErrorTransfer,
  WeightedBalancedSampling and logarithmic specializations: exact signed
  perturbation identities and weighted Schur/Hilbert-Schmidt transfers,
  retaining the mixed square remainder.
- ActualPrimePowerWeightedRows: exact directed-entry identification and
  unconditional weighted rows from the existing elementary Mertens theorem.
- OccurrenceCollisionMultiplicity, OccurrenceCollisionWeightedEnergy,
  OrdinateTriangularIntegral, ActualZeroCollisionMultiplicity,
  ActualZeroTriangularIntegral: exact occurrence/multiplicity aggregation,
  triangular integral, even collision excess and finite criticality/simplicity
  certificates. Their small-energy premise is not proved globally.
- OrdinateCollisionSharpRemainder, OrdinateCollisionConsecutiveSpacing:
  4*pi^2*C/(3*R^2*delta^2) remainder for ranked finite families with the
  displayed positive consecutive spacing. No actual height-only gap bound.
- PrimeThirdMomentIntegral: exact cubic-logarithm improper tail integral.

Conditional actual-zero conclusions:
- ActualZeroDensityTransfer and ActualZeroLogarithmicEntryBound: the 128*C_D/3
  correction and actual rational entry bounds, retaining exponential density.
- ActualLogarithmicCovarianceAssembly and ActualLogarithmicPairCovariance:
  exact sampled diagonal subtraction and coefficient-uniform actual single
  and pair covariance. Actual Landau and arithmetic providers are discharged;
  the displayed exponential strict-tail density hypothesis remains.

Open formalization obligations: a Selberg exponential density provider; the sharp paper
FMZ height error; actual balanced-tuple/little-o assembly; the complete
prime-tail/Haar/Gaussian theorems; or a proof of the global collision-energy
condition. The current height remainder is the proved coarser Landau envelope.

### Unconditional ordinate kernels, second energy, and growing Fourier tests (2026-10-11)

Established without RH:
- Analysis/FrequencySensitiveGramBounds.lean: exact weighted frequency spread,
  including its negative square; translation invariance; variance-sensitive
  complex Gram error bounds and exact signed three-term splitting.
- Analysis/SummableOrdinateKernel.lean: absolutely convergent positive-definite
  kernels, exact finite-plus-tail identity, full uniform tails, and moving-test
  convergence under the actual coefficient-times-tail budget.
- Analysis/ActualZeroSecondEnergy.lean: convergence of the actual multiplicity-
  weighted second horizontal energy E2; E4 <= E2; exact curvature moment
  sum gamma^2*w4 = E2-E4; individual displacement bounds; E2=0 iff RH.
- Analysis/ActualHorizontalEnergyKernel.lean: actual beta-sensitive kernel,
  K(0)=E4, positivity, all-frequency height-tail bound E2/(1+H^2), and growing
  coefficient tail control. These results do not establish E2=0 or E4=0.
- Analysis/ActualDirichletPolynomialGram.lean: exact squared-polynomial sum over
  actual zeros equals its full integer-frequency Gram form, with multiplicity.

Conditional research reductions:
- growingGram_signed_remainder_tendsto_zero: Open analytic entrywise provider
  for the chosen family and its vanishing weighted budget.
- sampledSquare_prime_remainder_bound: Open formal sharp actual-ordinate FMZ
  remainder provider; signed von Mangoldt prime-power matrix is preserved.
- riemannHypothesis_of_detecting_height_tests: Open construction of one family
  satisfying strict energy detection and finite arithmetic cancellation. Its
  tail is supplied under an explicit geometric cutoff/coefficient-growth
  budget. No such detecting/cancelling arithmetic provider is proved here.

RH/MovingFrequencyMobiusLaws20261011.md contains independently audited PAPER
proofs from FMZ Lemmas 1-2: positive Mobius secondary law, full polynomial L2
tails, random analytic laws, and empirical reciprocal compatibility. These
analytic statements are not completely Lean-formalized. Actual shifted-zeta
identification, BSY vanishing and Bagchi recurrence remain Open.
See RH/UnconditionalHarmonicContinuation20261011.md for the precise boundary.


### Actual squarefree residual laws, full inverse Gram, and variation (2026-10-11)

Established structural identities and conditional geometric branches:

- Analysis/ProjectionResidualSampling.lean proves exact nested residual
  covariance and projection-enlargement finite-head bounds.
- Analysis/CoordinateSquareVariation.lean and ProjectionResidualVariation.lean
  prove the complete countable coordinate-square total-variation bound from
  the Hilbert angle, then specialize it to genuine nested residuals.
- RH/SquarefreeResidualSampling.lean uses every squarefree conductor in the
  actual Pareto dictionary. It proves positive finite-stage residual energy,
  normalized physical site masses, the exact limiting/enlargement energy
  identity, escape iff target membership iff zero limiting energy, and the
  filtered full-inverse Gram projection. Its closure is identified exactly
  with all original squarefree conductors d>1; no target approximation follows.
- Analysis/FiniteWeightedResidualGram.lean and RH/SquarefreeResidualHeadGram.lean
  preserve the complete signed finite-head numerator W-2*c.B+c.H.c and its
  actual denominator 1-b.(G^-1 b). Coefficients come from the full Hilbert
  Gram inverse before any head restriction, including composite conductors.
- RH/SquarefreeResidualVariation.lean proves TV^2 <= (e_n-e_m)/e_n for n<=m,
  the limiting version under explicit nonzero limiting energy, normalized
  limiting masses and full TV convergence in that branch. Its exact site-law
  decomposition retains the signed cross charge and the enlargement square.

The RH consumer is a **conditional research reduction**. Open: actual
finite-head escape (equivalently squarefree constant-target membership or
zero limiting energy). The formal RH-to-squarefree-membership direction,
primorial finite-stage cofinal comparison, countable DPP coupling, and the
analytic Mellin/Gram obstructions are not supplied by these modules. The
compensated two-three cofinal arithmetic provider remains Open. RH is not proved.

### Infinite actual Gaussian Laplace bridge and sharp tail reductions (2026-10-11)

- Analysis/GaussianLaplaceBridge.lean proves exact complex exponential
  integrals, countable absolute Fubini, explicit infinite integrability,
  positive-time summability and summability of the full reciprocal spectrum.
- Analysis/ActualZeroGaussianLaplace.lean assembles the complete actual-zero
  H/R Laplace identity for every x>1/2, with both signs and analytic
  multiplicities. Critical-strip bounds and existing reciprocal-square
  summability discharge its analytic inputs; neither RH nor zero-height
  or additional zero-counting hypotheses are assumed.
- Analysis/GaussianHankelInterpolation.lean constructs real quadratic
  interpolants for arbitrary finite cutoffs and proves exact negative cores
  plus sharp signed and absolute-complex infinite-tail budgets.
- Analysis/GaussianGrowingDegreeTail.lean retains the full numerical
  prefactor and proves decay under d(T)*log(T)/T^2 -> 0, including the
  concrete O(T*log(T+2)) sufficient condition.
- Analysis/GaussianHankelTailBridge.lean connects that limit to full infinite
  polynomial-square negativity. This is a conditional research reduction:
  actual distinct-node cutoffs, absolute Gaussian-polynomial summability,
  uniform interpolation normalization and growth, and the complete numerical
  shell-tail provider remain Open. Ordinary Gaussian moment/Hankel
  identification, the centered xi'/xi identity, and independent actual
  arithmetic positivity or E4=0 remain Open.
- Five modules contain 77 supporting public theorems. Exact-module import
  job job_js_Ll8edCU-zOCwibn5RDWIAC-r9NpPi compiled all five standalone modules
  with verified=true; nine important
  foundation reports use only propext, Classical.choice and Quot.sound.
  Publication checkpoint job_e7YbE5E25oK0rxrUNAhso2UY87rzwOdY passed with
  validation scope affected_modules for the five new modules and published
  commit 09109d452e6a1e6d6b5862072fb6a08fc242bf8d.
  See RH/InfiniteGaussianAnalyticBridge20261011.md.

### E4 vanishing attempt: exact ordinate-information obstruction (2026-10-10)

- Analysis/FiniteQuartetOrdinateBlindness.lean proves identical signed
  ordinate lists and all real ordinate observables for the line/displaced
  quartets, exact positive horizontal energy, open-strip membership,
  exactly zero cutoff tails, and isolated Gaussian heat Hankel negativity.
  Lists retain analytic-copy multiplicity. Eleven public theorem declarations.
- These are artificial spectral models, not alternate actual zeta zeros.
  The complete arithmetic explicit formula is not preserved.
- RH/E4ProofAttempt20261010.md records the exact signed-argument/prime
  cancellation needed for E4=0, plus a complete interpolation/tail paper
  proof. The new Laplace bridge and conditional Gaussian components are
  recorded in the 2026-10-11 continuation above; the full actual Hankel
  identification and numerical tail provider remain Open.
- Actual E4=0 and independent arithmetic positivity remain Open.
  Source bundle job_hE8Tg0r-DAL-F8TpPC6upyPoYvnB3JXb passed, verified=true;
  printed foundations use only propext, Classical.choice and Quot.sound.
  Final acceptance and publication are the introducing server checkpoint.

### Exact actual-zero horizontal defects (2026-10-10)

- Analysis/ActualZeroHorizontalEnergy.lean proves unconditional summability
  of the multiplicity-weighted all-zero energy E4=sum m*(re-1/2)^2/(1+im^2)^2,
  nonnegativity, singleton detection, and E4=0 iff Mathlib RiemannHypothesis.
  The equality E4=0 is Open; the equivalence assumes no domain-specific input.
- Analysis/ResolventHorizontalDefect.lean proves the complete reflected
  rational gap identity and explicit two-sided constants 1/5 and 9. The sign
  and height conditions remain visible in each estimate.
- Analysis/DeterminantHorizontalDefect.lean proves the exact positive
  polynomial certificate and maximum-ratio square remainder; factor equality
  detects displacement without a lower-height hypothesis.
- Analysis/ActualZeroHorizontalDefect.lean assembles reflection before any
  estimate, retains actual analytic multiplicities, and proves finite and
  cofinal determinant-gap detection for all positive-height actual zeros.
- Analysis/ConjugatePairHankel.lean proves an isolated conjugate-pair
  determinant is -4*normSq(v)*im(z)^2 and supplies negative directions plus
  an explicit tail-error budget. No infinite-tail provider is asserted.
- Five modules contain 37 supporting public theorems. Actual-source bundle
  job_xB9pfBSLHvCFL_byfhyyt1jqM5C9lybW succeeded with exit code 0 and verified
  true. Important printed foundations use only propext, Classical.choice,
  and Quot.sound. Final project acceptance is the introducing checkpoint.
- Infinite xi-product/resolvent/Laplace identifications are paper proofs in
  RH/OrdinateHorizontalDefects20261010.md. The all-zero Laplace exchange is
  now proved in Analysis/ActualZeroGaussianLaplace.lean; the centered
  xi-product identification and reverse comparisons and E4=0 remain Open
  arithmetic obligations. These are conditional research reductions toward
  RH, not unconditional proofs of RH or new zero-density estimates.

### Ordinate spectral kernels and sharp Hankel certificates (2026-10-10)

- Analysis/OrdinateSpectralKernel.lean proves positive finite spectral Gram
  forms, exact zero-energy detection, unitary modulation, collision-energy
  limits and fixed-support coefficient-uniform Parseval and strict detection.
  FourierCancellation is explicit; its actual-zeta provider remains Open.
- Analysis/SharpSpectralGram.lean preserves the diagonal exactly and improves
  the quadratic-error factor from card to card minus one.
- Analysis/HankelMomentPositivity.lean proves the singular 2-by-2 PSD criterion,
  negative directions, entrywise-limit closure, atomic Hankel squares,
  moment log-convexity and ratio monotonicity.
- Analysis/ActualOrdinateSpectralKernel.lean proves finite Gaussian spectral
  positivity and moment log-convexity for the actual riemannZeta zeros, with
  analytic multiplicities. It assumes neither RH nor simplicity.
- Full-zero Gaussian growth, the explicit formula and all-orders RH criteria
  remain paper proofs in RH/OrdinateHarmonicTheory20261010.md. Their analytic
  Lean formalization is Open; all-orders arithmetic positivity is Open.
  These ordinate-only finite results do not prove RH.
- Final source acceptance is the introducing server checkpoint. Foundation
  axiom reports do not discharge analytic hypotheses.

### Actual annular limsup exponents and complete residual transfer (2026-10-10)

- Analysis/LogarithmicGrowth.lean proves the exact equivalence between zero
  logarithmic growth exponent and eventual subpower upper growth, including
  signed functions. Absolute subpower perturbations preserve the exponent.
  The extended-real definition requires no assumed boundedness.
- RH/AnnularEnergyGrowth.lean retains the complete equality E_A=M+R+T,
  including the full lattice signed cross term and square. The actual prime
  and centered energy exponents agree and belong to [0,1] unconditionally.
- Every strip zero with real part beta forces exponent >=2*beta-1. This is
  the actual limsup obstruction; it assumes no zero simplicity or all-cutoff
  lower bound. Zero actual energy exponent implies RH through the proved
  membership and Mellin continuation dependencies.
- Under the explicitly Open absolute-subpower model bound, the complete
  signed residual has exactly the same exponent. Its subpower upper bound
  then implies RH. These are conditional research reductions: the actual
  model bound and signed-residual cancellation bound remain Open.
- The two new modules contain 31 public theorems. The combined application
  passed server source job job_0V_cGnOYYHmRKVvPbso7uzPNTPa4dGPr with exit
  code 0, verified true, and no warnings. Final project acceptance is the
  introducing checkpoint. See RH/AnnularGrowthContinuation20261010.md.
- All 31 printed theorem foundation reports use only propext,
  Classical.choice, and Quot.sound. These reports do not discharge the
  actual zero-exponent, model, or residual hypotheses.

### Subpower annular energy and cofinal zero-growth obstruction (2026-10-10)

- Analysis/SubpowerPrefixMellin.lean proves eventual prefix-power weighted
  integrability without a coefficient-sign premise, and exact finite-prefix
  comparisons from weighted energy without a continuity premise.
- RH/AnnularSubpowerEnergy.lean proves that eventual subpower critical energy
  is equivalent to every actual H_a membership with a>1/2, and implies RH
  through the proved actual Mellin continuation. This weakens the preceding
  logarithmic arithmetic premise. The actual subpower estimate remains Open.
- Actual prime and centered subpower targets are equivalent using the full
  signed lattice correction and its square. No prime-pair cancellation is
  asserted. These RH implications are conditional research reductions.
- Every strip zero with real part beta>1/2 forces arbitrarily distant
  violations of every C*X^p envelope for 0<=p<2*beta-1. No simplicity premise
  or all-cutoff lower bound is used; the endpoint is not claimed.
- All 13 public theorem axiom reports passed combined server job
  job_6XWki38R7C8-rPF7nxIr_DUz8NdueN8W with only propext, Classical.choice,
  and Quot.sound. Final project/module acceptance is the introducing
  checkpoint. See RH/AnnularSubpowerContinuation20261010.md.

### Actual annular energy implies RH (2026-10-10)

- Analysis/LogarithmicPrefixMellin.lean proves complete finite integration
  by parts, prefix-power weighted integrability, and that an all-cutoff
  logarithmic critical-energy bound supplies every H_a with a>1/2.
- Analysis/ActualAnnularContinuity.lean proves global continuity and
  measurability of the actual infinite prime vector by locally finite sums.
- RH/AnnularMellinContinuation.lean proves meromorphic germ continuation
  from the actual Re(s)>1 identity throughout a punctured half-plane.
  It removes the local identity provider and proves that actual H_a
  membership excludes every zero with Re(s)>a, for 0<=a<1. Every
  positive zero multiplicity is retained; no simplicity premise is used.
- RH/AnnularEnergyRH.lean proves ActualPrimeEnergyUpperBound implies RH
  and, by exact signed lattice transfer, ActualEnergyUpperBound implies RH.
  The signed-residual implication needs only ActualModelLogBound and
  ActualSignedResidualUpperBound. These are conditional research reductions.
- The sufficient energy-to-RH analytic direction is discharged.
  ActualPrimeEnergyUpperBound, ActualEnergyUpperBound, ActualModelLogBound,
  and ActualSignedResidualUpperBound remain Open arithmetic obligations.
  The converse RH-to-logarithmic-energy direction and the full
  ActualRHEnergyCriterion equivalence remain Open.
- These four exported modules contain 17 public theorems. The assembled
  import passed server job job_8TUk4RtxzD0U48hNcmUmsvFZFTX6EC0F; nine
  decisive axiom reports use only propext, Classical.choice, and Quot.sound.
  Final aggregate-project and changed-module validation is the introducing
  checkpoint. See RH/AnnularEnergyContinuation20261010.md.
- RH/AnnularLatticeMellinPaper20261010.md gives a separate paper proof of
  the deterministic lattice Mellin entire continuation and exact moments.
  That appendix remains a paper proof. The later specialized subpower and
  cofinal energy-exponent corollaries are now formalized in
  RH/AnnularSubpowerEnergy.lean, as recorded above.

### Exact annular lattice decay and arithmetic energy transfer (2026-10-10)

- RH/AnnularLatticeCorrection.lean proves the exact all-positive-real-cutoff
  Bernoulli remainder, including fractional endpoints. RH/AnnularLatticeBounds
  proves the sharp bound |delta(x)| <= 10/(27*x^2), equality at x=8/3, and
  optimality of the global coefficient. No prime-correlation premise is used.
- Analysis/SignedLatticeEnergy.lean retains the full signed cross term and
  correction square. RH/AnnularCriticalEnergyTransfer proves the actual
  ActualLatticeDecay provider, all-real-cutoff energy difference bound
  1105/5832, and convergence to the absolutely convergent signed integral.
  The actual prime and centered O(log X) critical-energy bounds are equivalent.
- Analysis/ActualAnnularLatticeWeighted.lean proves actual global measurability,
  lattice membership in H_a for a>-2, norm square <=100/(729*(2a+4)), and
  equivalence of actual prime/centered membership on that range. Its Mellin
  transform is analytic on Re(z)>-2, with square norm bound
  100/(729*(Re(z)+2)^2), and uniform square bound 25/729 on Re(z)>0.
- These five modules contain 49 public theorems. The combined server source
  check succeeded; final project validation is the introducing checkpoint.
  See RH/AnnularLatticeContinuation20261010.md for declarations and evidence.
- The RH and signed-residual wrappers are conditional research reductions:
  ActualRHEnergyCriterion and ActualModelLogBound remain Open as stated.
  ActualSignedResidualUpperBound and infinite prime-vector control remain Open.

### Annular arithmetic, Mellin evaluations, and exact residuals (2026-10-10)

- RH/AnnularArithmeticWeight and AnnularArithmeticIntegrals prove the actual
  weight support, sharp maximum 7/24, exact centering, mass 7/64, and square
  mass 35/1536. LinearAlgebra/FinitePrimePairResidual and FiniteIntegralGram
  provide ordered signed decompositions and the genuine integral Gram identity.
- RH/ActualAnnularKernel proves local integrability, all-cutoff nonnegative
  actual energy, Q=M+R, exact diagonal/triangle splits, and ratio-eight boundary
  vanishing. Prime powers and both singleton terms are retained.
- RH/ActualRieszTwoConvolution, ActualRieszTwoAnnularCutoff,
  ActualRieszTwoMellin, and ActualAnnularMellin prove the actual second-Riesz
  convolution and the centered Riesz and annular Mellin identities on Re(s)>1.
  Critical-strip integral convergence or continuation is not assumed.
- Analysis/WeightedMellinTopologyTargets, WeightedMellinLogarithmicKernel,
  WeightedMellinDerivativeTopology, WeightedMellinDerivativeSharpness, and
  WeightedMellinDerivativeCauchy prove all derivative evaluations, their sharp
  factorial coefficient, actual extremizers, difference bounds, and full-zero
  uniform bounds under genuine weighted energy membership. The truncation
  Membership/Envelope modules prove every-weight membership, entire transforms,
  and explicit finite arithmetic norm control; infinite-vector control is Open.
- Analysis/AnnularMellinMultiplier and RH/AnnularMellinRH and
  AnnularMellinPoleOrder retain every strip zero and prove multiplier
  nonannihilation, the exact simple-pole order, and the meromorphic analytic RH
  criterion. Analysis/WeightedMellinPoleObstruction retains its local identity
  premise. RH/AnnularZeroSpectralTargets records complete multiplicities and
  explicitly Open full-zero formula, spectral limit, and growth obligations.
- Analysis/TwistedRieszFilterAlgebra, TwistedRieszFilterOrder,
  RieszOrderUniformCoupling, and RieszOrderMidpointCoupling prove every finite
  smoothing-order response and a strictly improving uniform Gaussian family,
  with coefficients 5, 89/18, 1111/225. HigherRieszLocalization proves scalar
  summability transport; its actual Fourier envelope premise remains Open.
- NumberTheory/PrimePairEulerProduct and PrimePairEulerProductTail prove
  positive convergence, 1/2 <= C2 <= 11011/16384, and an explicit tail enclosure.
  RH/AnnularPrimePairTargets uses that actual product and proves parity signs.
  RH/AnnularModelCoefficientBounds proves cW < -51611/1536000 < -1/32 without
  extra logarithm bounds. Identification as a model slope still requires the
  Open singular-series/PNT asymptotic. CenteredResidualTransfer exposes every
  model and energy premise needed to transport actual signed estimates.
- RH/RawPrimePowerEnumeration constructs the infinite increasing complete
  enumeration of actual prime powers. RawPrimePowerContinuationTargets proves
  exact raw cell assembly including initial energy 1 and endpoint corrections.
  The quantitative prime-gap, arithmetic grid, and signed residual bounds are
  Open. The residual RH equivalence retains ActualModelLogBound and
  ActualRHEnergyCriterion; neither is supplied by proposition definitions.

The combined source check audited all 320 public theorems and used only
propext, Classical.choice, and Quot.sound. See ANNULAR_FORMALIZATION_20261010.md
for exact evidence, scope, and the remaining paper obligations.

### CRT escape, exact reversal, and every fixed sampling factor (2026-10-09)

- RH/ArgumentSamplingClosure.lean constructs the actual factor-a sampling
  operator, retains its exact physical weight correction, and proves its sharp
  norm a for every positive natural a. For every a>=2 the complete sampled
  residue sequence converges to the constant in the physical Hilbert norm.
- The generator test, invariance iff constant membership, and invariance iff
  full residue density are unconditional closure equivalences. The theorem
  riemannHypothesis_of_argumentSampling is a conditional research reduction:
  ArgumentSamplingInvariant a remains Open for every fixed a>=2. The
  literature RH-to-closure converse is not introduced as an axiom.
- RH/ReversedResidueComplement.lean retains the full divisibility-site
  correction in pointwise, square, infinite-series, and actual Hilbert norm
  equalities. The finite conductor-four functional certificates distinguish
  full-residue invariance from squarefree-only invariance.
- NumberTheory/FactorialCRTSeparation.lean proves all-factorial residue
  separation, escaping witnesses, arbitrarily large finite-prefix witnesses,
  and the exact forall-exists versus exists-forall counterexample.
- These three modules contain 43 checked theorem bodies and 8 definitions.
  The central axiom checks use only propext, Classical.choice, and Quot.sound.
  Quantitative DPP leverage and finite Gram defect decay are paper results in
  RH/CRTOrbitSamplingContinuation20261009.md; the decay provider remains Open.


### Bagchi squarefree closure: formal bridges and open analytic limits (2026-10-09)

- RH/SquarefreeArithmeticSaturation.lean now defines the actual finite
  damped Möbius cutoff, proves exact squarefree support and packet membership,
  and transfers the two strong limits in Bagchi's proof to
  SquarefreeCenteredApproximation.
- The limit-transfer theorem keeps the cutoff-length and damping-to-zero
  limits as explicit hypotheses. The fresh-prime repair also yields the
  corresponding exact mean-one squarefree packet approximation.
- RH/ZetaTwoParetoTransfer.lean now proves both complete weight comparisons
  between the inverse-square and Pareto Hilbert norms.
- Bagchi's RH-dependent Littlewood, Lindelöf, and Hadamard/Gamma domination
  estimates remain Open as Lean providers. The exact implication
  RiemannHypothesis → SquarefreeCenteredApproximation is not yet proved.
  Optimizer cancellation and RH remain separate open problems.

### Complete resolvent recovery and stronger permanent obstruction (2026-10-09)

- RH/ZetaTwoResolvent.lean proves complete infinite weighted resolvent Cauchy,
  the exact integer mass H_M/zetaTwo through finite telescoping including its
  terminal remainder, and the actual-stage recovery bound
  error n <= (H_M/zetaTwo)*(sqrt(secondMoment n)+1/M), for every n and M>0.
  Its complete correction form keeps quarticFloor + weightedMismatch - screening.
- RH/ZetaTwoDualEightObstruction.lean realizes the literal radical dual at
  8 -> 2 in QHilbert. The rational mixed witness 16*f4+f8 proves that every
  universal first-moment cap is at least 1337/3979 and every universal
  compressed-square cap is at least (1337/3979)^2, at every actual stage.
  It retains the exact signed two-dual cross term and the entire positive
  remainder in the complete optimizer correction identity.
- These are unconditional estimates and structural limitations. No actual
  moment decay or positive signed-correction decay provider is established.
  RH remains Open. The arbitrary-conductor digamma parameterization and
  geometry-sharpness argument are paper results in
  RH/ConductorRecoveryStatus20261009.md, not new formal analytic providers.

### Target-specific reciprocal bases and permanent universal-cap obstruction (2026-10-09)

Twenty-five structural theorems pass coherent source-body checks and axiom audits
using only propext, Classical.choice, and Quot.sound. A twenty-sixth theorem
assembles their cofinal consumer with the existing Mellin RH transfer; native
validation and publication remain checkpoint-gated.

- Analysis/RadicalDifferenceTotality.lean adds squarefree-base linear rigidity,
  zero detection from inverse-index decay or summability, and finite stability
  of both coordinate and backward-difference errors.
- RH/ZetaTwoRadicalRowCriterion.lean proves the actual projection-residual
  radical relation and exact squarefree closure criterion using signed
  reciprocal differences only at fixed squarefree bases, with a cofinal
  consumer requiring no division by the moving error.
- RH/ZetaTwoReciprocalObstruction.lean realizes the literal four-site dual in
  QHilbert and proves all-stage universal first-moment and compressed-square
  caps are at least 1/3 and 1/9. Its complete signed reciprocal row survives
  screening. These lower bounds concern all-direction caps, not the target
  residual's moment.
- RH/ZetaTwoParetoTransfer.riemannHypothesis_of_cofinal_squarefree_reciprocal_differences
  is a conditional research reduction. Its infinitely many fixed-base decay
  inputs remain Open. RH is not proved.

Bagchi's squarefree converse is established in the literature; the missing
kernel-verified analytic provider is kept separate. The full trigamma-tail
error certificate and gradient noncoercivity are paper results, not newly
formalized Hilbert applications. See RH/TargetSpecificReciprocalAdvance20261009.md.

### Target-only moments and radical first-moment saving (2026-10-09)

66 new public theorem bodies passed coherent source check
`job_P2B73ELz1Fwm918oQYI3VSs8fXWNjMTa`, exit code 0.
The decisive transitive audits use only propext, Classical.choice and Quot.sound.

- RH/ZetaTwoReciprocalBound.screened_sq_le_firstMoment applies the universal
  cap only to the complete screened image, without radical compatibility.
- RH/ZetaTwoTargetFirstMoment.secondMoment_le_firstMoment proves the requested
  actual-stage bound m2 <= (10745/28906)*(a/e) for every n>=4.
  Its bracket (a/e)^2 <= m2 and exact Mobius displacement identities retain
  all signed pairings, complete tails and optimizer correction terms.
- RH/ReciprocalRadicalFourCertificate.lean and RH/ZetaTwoRadicalFourBound.lean
  use the proved four-site identity only for the actual residual. The strengthened
  196-site head plus complete infinite tail gives trace <= 8358527/9196500 < 10/11.
  Thus a/e <= 3/10 and m2 <= 6447/57812 for every n>=4. These replace the earlier
  caps 39138061/126426000 and 84107693089/730893991200.
- radical_threeTenths_gap_lower retains the positive complete-tail remainder
  (21203/101161500)*radicalTailEnergy. complete_trace_cap_lt_ten_elevenths
  exposes the rational threshold. target_secondMoment_cap_lt_permanent_floor
  proves 6447/57812 < (1337/3979)^2: the actual target cap is strictly below
  the permanent lower bound for caps on every orthogonal-complement vector.
  The strengthened infinite certificate passed coherent check
  job_e5D6gpDX8UJ8PaoJLRgDBBdExlij0bw0 with only standard foundations.
  See RH/TargetMomentCapSeparation20261009.md for the continuation.
- The first-moment closure criterion and the direct harmonic resolvent recovery
  are established. riemannHypothesis_of_cofinal_firstMoment is a conditional
  research reduction: its cofinal normalized first-moment decay provider is
  Open. A positive constant saving is not asymptotic decay.
- The finite-head escape characterization is a paper consequence, not another
  formal declaration. See RH/TargetFirstMomentStatus20261009.md for the exact
  certificate, correction formula, verification scope and remaining obligation.


### Complete actual reciprocal-operator bounds (2026-10-09)

73 public theorems in five modules complete the infinite reciprocal certificate
and its specialization to the existing inverse-square Hilbert-space optimizer.
The coherent full-body check and transitive public-theorem axiom audit use only
propext, Classical.choice, and Quot.sound. No moment cap is an assumption of the
actual stage theorems.

- Analysis/InfiniteWeightedCauchy.lean: one theorem passes from the exact finite
  Cauchy inequalities to complete summable signed pairings.
- RH/ReciprocalInfiniteCertificate.lean: 16 theorems prove the complete positive
  tail from site 37, retain the signed 34-site Gram cross term, and assemble the
  original coefficient 4137/4160 < 1 and a sharper rational head certificate.
- RH/ReciprocalConductorFiveCertificate.lean: 14 theorems verify adjusted signed
  recovery rows, all thirty residue channels, and the complete head-tail
  coefficient 3329/3708 < 1.
- RH/ZetaTwoReciprocalBound.lean: 25 theorems prove actual residue normal equations,
  both head squares, infinite weighted Cauchy assembly, positive reciprocal-form
  Cauchy, and the actual projection compression. For 2 <= n the unconditional
  second-moment caps are 9/49 and the stronger 11449/62500.
- RH/ZetaTwoConductorFiveBound.lean: 17 theorems add the exact complete zero charge
  from conductors three and five. For 4 <= n the second-moment cap improves to
  9/64, then to (10745/28906)^2 by retaining the strict positive tail remainder.
  Both mismatch and screening squares and the full quartic floor are preserved.

These are fixed positive bounds. The moving-stage cofinal saving of the actual
normalized positive signed correction remains Open; RH is not established.
See RH/ReciprocalOperatorLeanStatus20261009.md for exact declarations,
certificates, retained remainders, and the remaining provider.

### Radical dual common kernel and rational reciprocal head certificate (2026-10-08)

Thirty-five public theorems passed coherent full-body checks. The actual
inverse-square common-kernel theorem uses only the two displayed radical
difference families and inverse-square summability, which is supplied
internally by QHilbert. No RH hypothesis is used.

- Analysis/RadicalDifferenceTotality.lean: exact adjacent-value recovery,
  affine power amplification, normalized summability decay, and the complete
  power/radical-invariance common-kernel theorems.
- RH/SquarefreeRadicalDifference.lean: exact residue jumps and radical
  reduction, the literal legal squarefree residue-span and target-residual
  identities, continuous physical evaluations and strong-limit preservation,
  complete signed reciprocal-row recovery, and the actual QHilbert trivial
  common kernel.
- RH/ReciprocalHeadCertificate.lean: exact rational 34-site head bounds,
  residue trace control, signed Young inequality, and full-tail scalar
  certificate with coefficient 4137/4160 < 1.

The complete reciprocal-operator formalization above now supplies the actual
screened-moment cap 9/49 < 3/16, its infinite weighted-Cauchy assembly, and its
operator specialization, with stronger exact rational and conductor-five caps.
Bundled augmented-dual density remains paper-level assembly of the checked
common kernel. The cofinal positive correction saving remains Open.
See RH/RadicalDualAdvance20261008.md, RH/ReciprocalHeadCertificate20261008.md,
and RH/ReciprocalOperatorLeanStatus20261009.md for proofs and scope.

### Exact inverse-square optimizer cancellation and cofinal RH criterion (2026-10-08)

Twenty modules formalize the exact optimizer continuation, with 243 public
theorems. Coherent source checks and every public theorem's axiom audit use
only propext, Classical.choice, and Quot.sound; native publication remains
checkpoint-gated. The positive signed cancellation estimate is an explicit
remaining arithmetic hypothesis.

- LinearAlgebra/RankOneAnnihilatorSchur.lean,
  LinearAlgebra/WeightedOptimizerResolvent.lean, and
  LinearAlgebra/TwoVectorGramCompletion.lean: 23 theorems retain complete block
  squares, ambient positivity, exact inverse action and the signed two-vector
  cross term. No coupling bound or inverse existence is silently assumed.
- Analysis/SignedOptimizerMoment.lean and
  Analysis/CompressedMomentZeroCriterion.lean: 24 theorems give literal norm
  floors, optimizer mismatches, screening, the twice-compressed moment,
  signed/positive-part equivalences and a genuine cofinal limiting-residual
  consumer without monotonicity assumptions.
- Analysis/NormalizedProjectionWeakConvergence.lean,
  Analysis/FiniteHeadWeakContinuity.lean, and
  Analysis/CompactWeightedFloorNormalization.lean: 12 theorems prove canonical
  unit residuals are weak-zero and assemble normalized-floor convergence from
  absolute floor decay and finite-head operator geometry.
- Analysis/FiniteResolventRadau.lean and
  Analysis/ResolventRadauIntegral.lean: 34 theorems retain complete-square and
  both endpoint Radau remainders, literal infinite-support integrals, remainder
  integrability, four-moment equations and exact finite Cramer coefficients.
  Physical spectral measures and the proposed rational caps are not supplied.
- RH/ZetaTwoConductorFour.lean, RH/ZetaTwoDualBlock.lean, and
  RH/ZetaTwoPolygammaResidues.lean: 43 theorems prove complete finite-support
  infinite-sum pairings, exact marked Gram rows/determinants, actual all-order
  polygamma residue weights, shifted tails and full periodic mixed moments.
- RH/ZetaTwoMobiusQuarticFloor.lean and
  RH/ZetaTwoMobiusQuarticFloorDecay.lean: 22 theorems prove exact full floor-tail
  identities, the actual squarefree quartic variational bound and unconditional
  saving by every fixed logarithmic power using the existing Mertens provider.
- RH/ZetaTwoHilbertSpace.lean, RH/ZetaTwoReciprocalCompactness.lean,
  RH/ZetaTwoWeightedFloorNormalization.lean, RH/ZetaTwoOptimizerStage.lean, and
  RH/ZetaTwoParetoTransfer.lean: 85 theorems realize the actual inverse-square
  Hilbert space and reciprocal operator, prove strong stage limits, finite
  error positivity, the complete signed identity, unconditional normalized
  quartic-floor and negative-part decay, exact closure/positive-correction
  criteria, the exact positive limiting second moment off closure, and bounded
  physical transfer into the established Mellin theorem.

New all-stage limit:
`RiemannResearch.RH.ZetaTwoOptimizerStage.secondMoment_tendsto_exact_positive_limit_of_not_mem_closure`.
Under the explicit nonclosure hypothesis, the normalized second moment converges
to the exact positive residual-norm quotient. This does not discharge positive
signed-correction decay or prove RH.

Key actual consumer:
`RiemannResearch.RH.ZetaTwoParetoTransfer.riemannHypothesis_of_cofinal_positiveCorrection_decay`.
Its remaining input is cofinal decay of the actual positive signed correction
`max (signedCorrection (κ j)) 0 / error (κ j)`. RH itself is not established.
The inverse-log error lower bound remains an open formal provider for relative
logarithmic rates, and the RH-to-squarefree-approximation converse is not added.
See RH/ExactOptimizerLeanStatus20261008.md for the precise provider ledger and
RH/LiteratureClosureRoutes20261009.md for sourced closure routes and their gaps.

### Actual compensated source, constructive horizons, and complete quartic tails (2026-10-09)

138 public theorems formalize exact finite geometry and unconditional complete
physical tail bounds. Substantive arithmetic hypotheses remain explicit; the
Riemann Hypothesis is not established. See
RH/ActualCompensatedTailLeanStatus20261009.md for the provider ledger.

- Analysis/CompensatedSourceCertificate.lean and
  Analysis/FiniteGramSourceTranslation.lean: 49 theorems give sharp scalar
  certificates, weighted summability/divergence transfer, constructive cofinal
  normalized-error horizons, scalar zero-defect/divergence equivalence, and
  the exact observed inverse-Gram radius. The entire unobserved residual square
  is subtracted rather than omitted.
- Analysis/ProjectionTailSummability.lean and
  LinearAlgebra/FiniteIndependentSource.lean: 7 theorems preserve complete
  projection-energy telescoping and give the finite signed-source independence
  consumer. Its actual Baker and trace providers remain Open.
- LinearAlgebra/MeanOneBlockSchur.lean and
  LinearAlgebra/MeanOneSchurCoupling.lean: 8 theorems retain both rank-two source
  terms and the exact signed energy completion, its sharp orthogonal lower
  bound, and the division-free zero-second-source endpoint.
- RH/PhysicalSourceProjection.lean, RH/PhysicalResidualMean.lean and
  RH/PhysicalScreenedSource.lean: 15 theorems prove actual finite error-floor
  normalization, exact residual means and full physical source identities.
  Nonzero residual mean and strict mean-one penalty are conditional research
  reductions with BakerVonMangoldtSeparation as an Open formal provider.
- RH/PhysicalCompensatedSource.lean: 21 theorems construct the whole tail-old
  target, actual innovations and observed radius; identify source capacity with
  E_old-E_new and the translated source with the head plus complete tail-fit
  observations; and prove the actual nested-chain certificate divergence
  equivalence with no supplied source-radius, gain-sign or summability input.
- RH/ParetoMobiusHeadInterpolation.lean,
  RH/ParetoOptimizerTailSummability.lean and
  RH/ParetoOptimizerTailGeometricBudget.lean: 38 theorems supply unconditional
  finite-stage full-tail leakage, actual quartic optimizer-tail summability and
  the sharper allowance 16 norm(v)^2 [1/B+B^8/(B^12-1)]. The exact limiting
  projection defect and the complete final square-root cross contribution
  remain in every total budget; positive defect is still allowed.

Open: the prescribed-stage actual optimizer-tail/trial-energy product saving,
actual normalized cumulative gain/certificate divergence, and the quantitative
moving-stage signed-source estimates that would force it. Clean axiom reports
verify only the exact theorem types, including their explicit hypotheses.

### Actual inverse-square integer probability and prime independence (2026-10-08)

Established: RH/ZetaTwoProbability.lean, RH/PrimeValuationIndependence.lean,
and RH/ZetaTwoPrimeConsumers.lean add 41 public theorems (7 + 10 + 24).
The coherent full-body check succeeds; all 41 public axiom reports use only
propext, Classical.choice, and Quot.sound. Native publication is checkpoint-gated.

- Actual normalized PMF and measure on positive integers, with positive summable
  normalizer identified with riemannZeta 2; measure_dvd gives Q(m divides K)=m^-2.
- Exact prime-power tails and geometric valuation masses; iIndepFun_primeValuation
  proves independence for any injective family of actual primes.
- Exact finite Boolean and valuation pushforward masses, and actual expectation
  transfer to FinitePrimeLikelihood and FinitePrimeDivisibilityMoments.
- All finite-configuration observables belong to every L^r(Q); exact likelihood
  mean, second moment, tilt, divisibility moments and complete derivative Gram.
- Actual conductors are squarefree; union equals lcm. Normalized residue differences
  equal 1/d minus the divisibility indicator. The existing CRT reference kernel
  divided by zetaTwo is the actual Gram kernel of scaled divisibility indicators.

This closes the integer-law bridge left separate in the salvage49 status note.
Squarefree approximation, bounded discrete integration, small-damping energy,
and RH remain separate Open research obligations. No independence-to-RH inference.
See RH/ActualZetaTwoPrimeBridge20261008.md and its verification JSON manifest.

### Rank-two mean optimization and critical-zero audit (2026-10-08)

LinearAlgebra/RankTwoResidualMean.lean contains eight finite algebraic theorems
and one definition. A coherent isolated Lean check passes with exit code zero;
all eight axiom reports use only propext, Classical.choice, and Quot.sound.
Theorems derive the residual mean and energy system from an actual matrix
normal equation, solve it exactly, cancel both complete rank-two logarithmic
terms under mean one, retain the full core quadratic remainder, and identify
the exact correction-square penalty and signed error numerator.

The original continuation treated arithmetic Gram identity, inertia and
constrained-mean closure on paper. The physical advance below now supplies
their Lean applications; other claims in that paper retain their stated status.
The paper proves that the proposed coarse stretched-tail saving
N exp(-a h(N)) S_N -> 0 for 0<a<eta is impossible: a critical-line zero and
the unconditional trial-energy envelope force this quantity to infinity.
It also improves the finite optimizer tail term from M^3/N to M^2/N using the
classical large sieve, and proves the exact mean-one algebraic-core criterion
and unconditional logarithmic coupling cancellation o(L^(-1/2)).

Conditional research reductions: actual strict source feedback, actual trial
energy-tail product saving, algebraic-core saturation gamma_L -> 4*pi, and the
formal RH-to-squarefree approximation converse remain Open. No RH proof is
claimed, and the invalid coarse stretched upper envelope is not a provider.

### Physical arithmetic core and mean-one optimizer (2026-10-08)

Sixteen new modules passed one coherent isolated Lean compilation (exit code 0).
All 227 public declarations passed a transitive axiom audit restricted to
propext, Classical.choice and Quot.sound. The publication checkpoint separately
validates actual module imports and affected project dependents.

RH/CotangentBridge, CotangentMultiplication, ArithmeticPacketCore and
CotangentContraction identify the actual full Pareto Gram with the originally
specified double-cotangentV core. Signed Mobius, single-conductor and
simultaneous-divisibility corrections are retained until their proved cancellation.
LinearAlgebra/MeanOneCoreInertia and RH/PhysicalPacketCore, ArithmeticCoreInertia
prove nonsingularity, negative charge and exact Lorentz decomposition for every
squarefree divisor stage L>2, then actual ordinary mean-one optimization and
uniqueness. RH/MeanOneSix proves C_6=-8*sqrt(3), coefficients (2/3,1/2,1/6),
and minimum 1-pi/(2*sqrt(3)). RH/MeanOneRepair proves equality of the full
squarefree packet closure and its ordinary mean-one subfamily.

LinearAlgebra/MeanOneSchur and MeanOneBlockSchur retain the signed mixed update
and negative mean-tangent correction. RH/MeanOnePeriodObstruction and
PhysicalPeriodObstruction prove complete-period completion and reflection
floors, including E>=2/(L^2-1). RH/PhysicalCoreMonotonicity and MeanOneChargeBounds
prove actual error antitonicity and charge monotonicity. For 6 dividing L>2,
-8*sqrt(3)<=C_L<-4*pi. Every nested such divisor chain converges to a value
in [-8*sqrt(3),-4*pi]; identifying it with -4*pi remains Open.

RH/ArithmeticCoreRHCriterion proves the charge-limit-to-RH implication with
the endpoint as an explicit unproved hypothesis. The RH-to-squarefree converse
remains Open. Rational-angle algebraicity and the complete signed Schur
investigation are formalized in the following advance.
See RH/PhysicalMeanOneAdvance20261008.md and its verification JSON manifest.
No RH proof is claimed; the invalid coarse stretched-tail estimate is excluded.

### Arithmetic observations, squarefree geometry and improved trial (2026-10-08)

Nine new modules and all 192 public declarations passed one coherent isolated
Lean check and transitive axiom audit: only propext, Classical.choice and
Quot.sound. The publication checkpoint validates actual imports and affected
project dependents. See RH/PhysicalArithmeticObservations20261008.md and JSON.

RH/ArithmeticCoreAlgebraicity proves rational-angle, original signed core,
matrix inverse, actual arithmetic/physical charge and coefficient algebraicity.
Total Matrix.inv algebraicity does not assert nonsingularity. Existing odd-prime
inertia providers discharge genuine squarefree L>2 constrained-minimum premises.
RH/ArithmeticMinimumTranscendence proves the minimum has the same algebraicity
status as pi; NumberTheory/Transcendence now discharges pi transcendence for
the actual finite-minimum corollary, with no supplied hpi premise.

LinearAlgebra/MeanOneSchurCoupling proves complete signed Schur Cauchy, its
solved-block specialization, and source-limit bounds under explicit positivity
and limit premises. The corrected charge equals the existing 4*pi/Q bound.
An abstract positive rank-one source model has limit -5*pi; it is not physical
arithmetic and does not refute saturation of the actual packet system.

RH/PhysicalSchurReindex and PhysicalSchurCoupling identify the actual old,
cross and fresh blocks, prove the full mean-tangent and ordinary Schur forms
positive, and discharge genuine inverse-Schur positivity. Actual A/B/C signed
updates and Cauchy need only nested legal packets and an old odd prime.
Actual A<0, B<-pi and T=A*C-(2*pi+B)^2>0 are proved; finite denominator
premises in the corrected source-charge formula are internally discharged.
At this earlier snapshot the source projection charge was only a scalar
expression. PhysicalSourceProjection now identifies it with the actual
inverse-Gram solve, as recorded in the following established advance.

RH/SquarefreePacketBasis proves both original physical finite basis transforms,
complete error equality and ordinary-mean transfer with both endpoints retained.
RH/SquarefreeStageExhaustion supplies actual nested exhaustive squarefree
primorial periods. RH/SquarefreeArithmeticSaturation proves global centered
approximation iff mean-one packets iff actual stage minima arbitrarily small
iff vanishing errors iff charge saturation on every exhaustive divisor chain.
These are equivalences of unproved approximation/endpoint assertions.

RH/MeanOneThirtyTrial proves an exact ordinary mean-one trial at conductors
(2,3,5,6), coefficients (1/2,1/3,1/5,1/60), with complete error 1-pi*K/10800,
K=797*sqrt(3)+1224*cot(pi/5)+648*cot(2*pi/5). The actual minimum is at most
this value, strictly below the L=6 minimum. Every physical 30|L>2 has charge
at least -43200/K. The actual primorial arithmetic charge converges to a value
in [-43200/K,-4*pi]; equality with -4*pi remains Open.

Conditional research reductions: RH-to-squarefree centered approximation remains
Open as hReverse; unconditional arithmetic C_infinity=-4*pi remains Open.
Actual A->0 and B->-2*pi are discharged by PhysicalSourceLimits below.
No RH proof is claimed.


### Actual physical source limits and complete signed correction (2026-10-08)

Established: RH/PhysicalSourceProjection.lean and PhysicalSourceLimits.lean
contain 38 theorems and 6 definitions. All 44 public declarations pass one
coherent full-body Lean check and a compact transitive axiom audit restricted
to propext, Classical.choice and Quot.sound. Publication validates actual
imports and affected dependents. See RH/PhysicalSourceLimits20261008.md and JSON.

PhysicalSourceProjection proves actual projection and ordinary-mean dual normal
equations, identifies Q with the existing actual inverse-Gram solve, and retains
the complete Gram displacement square and exact ordinary-mean error penalty.
The large-prime physical norm implies T<16*pi*(-C)*p/(3*(p-1)^2), hence T->0,
A->0 and B->-2*pi on the actual primorial chain, with no RH hypothesis.
PhysicalSourceLimits supplies all legal, inertia, bounded-charge and
prime-exhaustion premises. The previous physical Schur limit theorem now yields
0<=(2*pi+B_n)^2/(-A_n)<=C_infinity-C_n, so the normalized signed square tends
to zero. The corrected charge tends to -C_infinity, and the actual projection
charge Q_n tends to 4*pi/(-C_infinity).

The actual source-limit realization and physical Q identification are now
Established. Unconditional endpoint C_infinity=-4*pi and the analytic
RH-to-squarefree reverse remain Open. No RH proof is claimed.

### Actual optimizer limits and quantitative endpoint obstruction (2026-10-08)

Established: RH/PhysicalOptimizerLimits.lean adds 13 theorems;
RH/PhysicalZeroObstruction.lean adds 9 theorems and one definition.
All 23 public declarations pass one coherent full-body Lean check and a
transitive axiom audit restricted to propext, Classical.choice and Quot.sound.
Publication separately validates actual imports and affected dependents.
See RH/PhysicalOptimizerCompletion20261008.md and its verification JSON.

The complete physical displacement between actual mean-one and projection
optimizers is exactly 4*pi*D^2/(gamma*T)=R*Q/gamma. Both complete errors tend
unconditionally to 1+4*pi/C_infinity; their full physical displacement square
tends to zero, and their values agree asymptotically at every fixed site.
An unconditional existence bundle supplies the actual negative charge limit.
Pointwise agreement does not assert convergence of either optimizer to one.

Actual Q_n->1 iff physical charge saturation iff complete centered squarefree
approximation. The Q_n->1-to-RH theorem is a conditional research reduction:
its actual saturation provider remains Open; the equivalence supplies neither
assertion. The analytic RH-to-squarefree reverse remains separately Open.

For every hypothetical zeta zero rho with Re(rho)>1/2 and rho!=1, the existing
actual Mellin separation transfers to the complete physical synthesis.
The Gram displacement and full signed mean-one penalty remain beside its
floor delta=(2*Re(rho)-1)/norm(rho)^2. Passing to the actual limit gives
delta<=1-4*pi/(-C_infinity) and
C_infinity<=-4*pi/(1-delta)<-4*pi. No existence of such a zero is asserted.
The arithmetic endpoint C_infinity=-4*pi remains Open. No RH proof is claimed.

### Exact physical mean repair, source rates, and π premise discharge (2026-10-08)

Established: RH/PhysicalMeanRepairProjection and PhysicalSourceRates add
18 theorems; five NumberTheory/Transcendence modules add 27 attributed
Lindemann-assembly declarations. The existing physical-minimum transcendence
theorem now discharges pi transcendence internally and has no hpi premise.

All 540 listed public declarations across the combined 37-module source set
pass a coherent Lean body check and transitive axiom audit restricted to
propext, Classical.choice and Quot.sound. Publication additionally checks
actual imports and affected dependents. See
RH/PhysicalSourceVerificationAdvance20261008.md and its verification JSON.

The actual full Gram projection is unique, its charge is monotone, and the
ordinary mean-one optimizer equals its exact signed mean-dual repair:
c0 = u + ((2*pi+B)/C)*v. Its complete error penalty is
(2-phi dot u)^2/(phi dot v) = 4*pi*(2*pi+B)^2/((-C)*T).
On primorials it is at most 4*pi/C_n-4*pi/C_infinity.

For prime p in a legal physical set, -A<4*(-C)*p/(3*(p-1)^2) and
(2*pi+B)^2<4*C^2*p/(3*(p-1)^2), with simpler inverse-prime bounds.
The actual primorial application discharges membership and all geometry:
-A_n<128*sqrt(3)/(3*p), (2*pi+B_n)^2<1024/p for prime p<=n+3.
These unnormalized source rates supply no normalized-correction rate or
arithmetic charge endpoint.

The five pi modules adapt Trevor Morris's Apache-2.0 formalization at
gotrevor/lean-formalizations commit bad0e21a37874f09f45072dad6225de55742e6c5.
The concrete RH consumer is ArithmeticMinimumTranscendence; provenance is
retained in each module. No novelty claim is made for this known theorem.

Unconditional arithmetic C_infinity=-4*pi and the Lean analytic
RH-to-squarefree approximation provider remain Open. No RH proof is claimed.

### Recovered analytic proofs and cancellation-preserving digamma differences (2026-10-07)

The prior thirteen Mellin/zeta/digamma modules and their validation survived
at published commit 04db1cc. Two additional modules contain 20 public theorems
and one private helper. Their coherent Lean check passes; all 20 new public
axiom reports and three recovered provider reports use standard foundations only.

- RH/DigammaBernoulliDifferences.lean: exact common-kernel cell differences,
  complete signed HasSum subtraction, strict monotonicity of every signed
  positive-real digamma error, exact next-order remainder difference, sharp
  first-omitted DIFFERENCE bounds, and exact actual digamma difference formulas.
- RH/ParetoProgressionBernoulliBounds.lean: complete actual CRT weight enclosures
  with the first physical-site mass retained exactly, full error identity,
  all-order strict signed and absolute bounds, and certified even/odd brackets.

For every N and 0 < x < y, 0 < (-1)^(N+1)*(E_N(x)-E_N(y))
< |B_(2N+2)|/(2N+2)*(x^(-2N-2)-y^(-2N-2)). No summand, boundary or full
remainder is discarded. The CRT application covers 1 <= r <= Q, including
r=Q and Q=1. Arithmetic residual-vanishing providers remain Open.
RH/LeanSalvageDigammaDifferences20261007.md records formulas and verification.

### Actual Mellin/zeta and all-order digamma formalization (2026-10-07)

Thirteen new modules contain 124 public theorem declarations and 13 private
proof helpers. Targeted builds through actual project imports pass. A coherent
24-theorem axiom audit contains only propext, Classical.choice, and Quot.sound.

- RH/ParetoAtomMellinSignature.lean and ParetoBeurlingMellinObstruction.lean:
  actual corrected fractional-part Mellin/zeta identity, holomorphy, removable
  value at one, actual atom closure annihilation and quantitative physical distance.
- RH/ParetoZetaSeries.lean, DigammaSmallArgument.lean, DigammaLaurentSeries.lean,
  and DigammaComplexLaurent.lean: actual zeta coefficients, all finite rational
  remainders, full convergent real/complex Laurent series and literal CRT weights.
- RH/DigammaAsymptotic.lean and the Bernoulli Cells/Remainder/Bounds/Estimates/
  SignedRemainder modules: actual complete integral remainders at every order,
  real-axis reality, harmonic bounds, and strict signed first-omitted-term bounds.
- Analysis/BernoulliEndpointDefect.lean: actual Fourier endpoint sign and strict
  midpoint positivity at every even Bernoulli order.

For all N >= 0 and x > 0, the literal digamma error after N even terms satisfies
0 < (-1)^(N+1)*E_N(x) < |B_(2N+2)|/((2N+2)*x^(2N+2)). The complex Laurent
identity holds on the punctured unit disk. This is not a complex-sector
all-order Bernoulli theorem or a new RH proof. Arithmetic cumulative gain,
approximation converse/squarefree provider, and named continuum norm assembly
remain Open. RH/MellinZetaDigammaFormalization20261007.md records exact domains,
proof strategy, declaration inventory, and verification evidence.

### Verified independent-prime and zeta-weighted continuation (2026-10-08)

Eight modules contain 73 checked public theorems and 20 definitions. All 49
previously unverified theorem statements are preserved. Coherent Lean checks
pass, and the complete 73-declaration axiom audit uses standard foundations only.

- RH/FinitePrimeLikelihood and FinitePrimeDivisibilityMoments: exact explicit
  finite Boolean product law, likelihood/change-of-law identities, monomial
  moments, complete differentiated Gram entries, diagonal and orthogonality.
- RH/PrimeSieveSecantAlgebra: exact signed secants, convex bounds and full
  coefficient variation. Prime arithmetic/asymptotic specialization remains Open.
- RH/ZetaTwoPeriodMeanBounds: actual residue coefficient mean bound from the
  first period, with both signed coefficient moments and explicit summability.
  The stronger all-period bound is not supplied by this module.
- RH/ExactHeadMeanGap, PrimeSieveTwoCutoffHead and PrimeSieveTwoCutoffMean:
  complete tail mean-gap lower bound, actual signed factorial-sieve interpolation,
  full rough-count residual, actual divisor-logarithmic mean and exact secant.
- RH/ZetaTwoDampedEnergyTransfer: complete inverse-square/Pareto membership
  equivalence, inclusive half-damping endpoint, and existing Burnol RH consumers.

Conditional research reductions: admissible arbitrarily small damping energy
remains Open; RH is not proved. The integer-law probability bridge, complete
finite derivative optimizer, prime-sum/Mertens specialization, and formal
RH-to-squarefree-approximation provider also remain Open in this continuation.
The squarefree-seed/dilation span is not identified with the literal squarefree
dictionary. RH/Salvage49ResearchStatus20261008.md records exact assumptions and
verification; RH/IndependentPrimeResearchContinuation20261007.md preserves the
research development and agenda.

### Recovered Beurling, CRT weight, and optimized gain continuation (2026-10-07)

Five additional modules contain 64 theorem declarations. Coherent isolated Lean
compilation and eight selected axiom reports pass with standard foundations only.
The recovered proofs retain complete signed sources, finite endpoints, and the
actual optimizer correction square.

- Analysis/FiniteKrylovGain.lean: exact two-direction Schur optimum, source-moment
  variance bonus, positive centered third moment, and Hilbert trial adapters.
- Analysis/StepCorrectionGain.lean: sharp structural error transfer, equality
  witness and orthogonal split; scalar consumers of supplied complete norm identities.
- Analysis/FiniteSignedTailCharge.lean: signed finite Abel summation with endpoint
  and exact transport retaining the finite old source.
- Analysis/BeurlingAnnihilator.lean: quantitative continuous-functional separation,
  nonconvergence, and closed-span obstruction for an actual annihilating functional.
- Analysis/FiniteCRTWeightBounds.lean: literal physical head and two-sided finite
  inverse-square tail bounds, without substitution of a uniform residue law.

The subsequent actual Mellin/zeta and all-order digamma entry above discharges
the Mellin/zeta, infinite CRT digamma, zeta-coefficient and harmonic adapters.
Named continuum constants and complete correction-norm assembly remain Open.
Open arithmetic provider: actual cumulative normalized gain forcing residual
errors to zero. No new RH proof or formalized approximation converse is claimed.
RH/BeurlingDigammaSalvage20261007.md retains the five-module verification record;
its analytic coverage is superseded by RH/MellinZetaDigammaFormalization20261007.md.

### CRT formalization, physical norms, and actual canonical optimum (2026-10-07)

Nineteen new modules contain 208 theorem/lemma declarations. Each passes isolated
Lean error diagnostics; selected axiom reports contain only standard foundations.
RH/RH_CRT_Formalization_Audit_20261007.md records attachment coverage and scope.

Established structural results include native projection/adjoint compression,
actual finite conductor-span dilation legality, bounded finite certificates and
summable fixed-compression sources, optimal final-ray bonuses, exact quadratic
reciprocal completion, the complete physical atom norm with its convergent
covariance correction, a sharper integrable reflected-cell bound, and a constructed
actual canonical residual Gram inverse with unique weights and monotonicity.
Exact squarefree step energy transfer and weighted Mellin signature decay are proved.

**Conditional research reductions and Open providers**:
- Canonical inverse-normal-mass RH consumer: Open cofinal subpolynomial optimized
  energy bound. Actual finite inverse geometry is discharged.
- Bounded-prefix-floor signed RH consumer: Open actual cumulative signed tail and
  normalized-head budget. Its exact negative-prefix correction is retained.
- Prime gain consumers: Open unbounded cumulative normalized actual arithmetic gain
  or the stated signed-window budget.
- Squarefree converse: Open formal proof of the published RH-conditional damped
  approximation theorem. Finite support and complete step energy transfer are proved.
- Named continuum constant log(2*pi)-gamma and its full cell regrouping, finer global
  bounds, and asymptotic: Open analytic formalization.
- Actual spectral-moment and signature providers from Four Improvements: Open.


### Actual source product, derivative, and defect obstruction (2026-10-07)

Unconditional finite identities and actual-source assembly:

- Analysis/FiniteSpectralResolvent.lean preserves the exact full remainder
  D(t)+(t-1)S-T=(t-1)^2 sum w*lambda/((1+lambda)^2*(t+lambda)).
  It proves T+S<=q^2+2sqrt(U*S) from a full all-scale trial estimate,
  including zero cases, and S=F(1)+F'(1), D'(1)=-S.
- RH/ParetoOriginalSourceCoordinates.lean identifies the original source as
  b=(3,1,0,...). No later Gram interaction is discarded.
- RH/ParetoCompactTailProduct.lean reuses the existing exact signed projection
  identity. For the literal complete compact trial, L_m->delta and
  L_m^2<=P_m=U_(4m+4)*S_(4m). Every a<delta^2 is eventually below P_m.
  A positive defect would force (4m+4)*S_(4m)->+infinity using U_N/N->0.

**Conditional research reductions**:
riemannHypothesis_of_compactFourfold_cofinal_tailProduct and
riemannHypothesis_of_compactFourfold_arbitrarily_late_small_tailProduct
require actual product smallness. The more flexible
riemannHypothesis_of_compactFourfold_cofinal_product_fraction requires
P_(k_m)<=theta*T_(4k_m)^2+E_m cofinally, theta<1, E_m->0.
Each arithmetic upper provider remains **Open**. No converse is asserted.

- RH/CanonicalMobiusLogEnvelopeEnergy.lean proves the finite uniform-Mertens
  transfer: with h=epsilon*(1+log(1/epsilon))<=1/2 and |M(y)|<=epsilon*y
  for every y>=N, |m_N|<=5h and ||A_N||^2/N<=3/N+260h. The complete
  infinite physical tail is retained; no RH premise is used.

Paper progress (not new Lean providers): sharper stretched-rate corollaries,
complete trial constants 5130 and 1122, and full original Gram inverse/Schur
transport.
Source, Wolfram record and next steps:
RH/ParetoSourceProductAdvance20261007.md and
RH/ParetoUniformMertensEnergyTransfer20261007.md.

### Actual conductor-scale source escape and bounded-tail consumer (2026-10-07)

Unconditional exact arithmetic and full-source Hilbert geometry:

- Analysis/FiniteSpectralResolvent.lean proves the complete-source resolvent
  relation, cap-gap identity, rational and threshold contrast certificates,
  literal head-adjoint source realization and exact signed variational
  completion with both full physical energy squares retained.
- RH/ParetoCompactTrialEnergy.lean proves, for N=4m+4, the exact identity
  u_N=14 A_(4m+3)-13 D_2 A_(2m+1)+3 D_4 A_m. The complete squared norm
  retains all three signed cross terms. Existing unconditional canonical
  Mobius sublinear energy then gives ||u_N||^2/N->0.
- RH/ParetoActualSpectralResolvent.lean applies the actual full-stage
  variational completion: sourceDeficit(t)<=headTrial^2+tailTrial^2/t-e_N.
  For every c>0, sourceDeficit_(4m)(c(4m+4))->0 and the entire actual
  source highMass_(4m)(c(4m+4))->0. No fixed-threshold tightness is inferred.
- The coherent isolated candidate passed Lean with exit 0 and no warnings;
  the source escape, threshold contrast and cofinal RH consumer axiom audits
  use only propext, Classical.choice and Quot.sound.

**Conditional research reduction**:
RH/ParetoConductorTailCriterion.lean proves
riemannHypothesis_of_compactSpectrum_fourfold_cofinal_bounded_tail.
Its Open arithmetic provider is eventual (4k_m+4) S_(4k_m)<=B for some
finite B>=0 and cofinal k_m. Source escape and all geometric limits are
internally supplied. The whole-fourfold version is also proved.
This bound, fixed-threshold tightness and the previous strict cofinal
double-log contrast remain Open; none follows from the linear moving cutoff.
Source and precise continuation: RH/ParetoSourceResolventAdvance20261007.md.

### Actual complete-source double-log upper budgets (2026-10-07)

Unconditional arithmetic conditioning, source identities and moment estimates:
- Analysis/FiniteSpectralMomentUpper.lean retains the exact complete identity
  M=Phi(L)T-C+P. The cap contrast C is nonnegative; the full source remainder
  satisfies P^2<=B*S, P<=T and P<=(1+Phi(L))*S. A correction-weighted
  outer-log Jensen bound is proved by exact tangent cancellation.
- RH/ParetoActualSpectralMomentUpper.lean discharges every stage eigenvalue
  cap from the actual Mobius repair: lambda_i<=144(n+3)^2-1, preserving the
  unit head square. The literal mass is exactly 134-headError and tends to 134.
  It proves P<=sqrt(134S)->0, the full signed upper bound
  M<=Phi(L)T-C+sqrt(134S), and the conductor-scale endpoint upper floor:
  for every c>delta, eventually M/log(1+log(n+3))<c.
- Seven isolated axiom audits use only propext, Classical.choice, Quot.sound.
  The final coherent source passed Lean with exit 0 and no warnings.

Conditional research reduction:
riemannHypothesis_of_actual_compactSpectrum_cofinal_contrast constructs
the canonical feedback error epsilon+P/D internally. Its SINGLE Open
arithmetic provider is C_(k_n)>=(Phi(L_(k_n))-theta*D_(k_n))*T_(k_n)
-D_(k_n)*epsilon_n, with k_n cofinal, theta<1 and epsilon_n->0.
The exact finite equivalence to the original complete-source budget retains P.
No strict fraction, RH or source tightness is inferred from a polynomial cap.
Source and continuation: RH/ParetoCompleteSourceMomentBudget20261007.md.

### Explicit complete-tail Mobius head repair (2026-10-07)

Unconditional finite arithmetic and Hilbert geometry; no RH premise.

- RH/ParetoMobiusHeadInterpolation.lean constructs unit steps by full
  canonical Mobius dilation and exact boundary relocation to conductor H+1.
  Every physical coordinate through H is interpolated, every conductor is
  retained, and the entire infinite norm obeys ||T_H y||<=12H ||Q_H y||.
  The linear map and its bounded continuous version are constructed.
- finiteSpace_norm_le_head: ||f||<=12H ||Q_H f|| for every f in the entire
  H-dimensional legal stage; interpolation is the actual inverse of its head.
- RH/ParetoMobiusConstrainedEnergy.lean constructs a complete legal repaired
  projection with exact error ||r_M||^2+||T_H r_M||^2. For H<=M the actual
  exact-head error infimum satisfies
  ||r_M||^2+||Q_H r_M||^2<=E_HM<=||r_M||^2+144H^2||Q_H r_M||^2.
  No repair cap is left as an assumption.

Open arithmetic: literal source tightness or the strict cofinal spectral
moment feedback. Open formalization: RH -> BaezDuarte.CenteredApproximation.
The centered/Pareto norm and closure transfer already exist in
BaezDuarteCenteredBridge. Source and next steps:
RH/GreenParetoHeadRepairAdvance20261007.md.

### Actual canonical-envelope spectral consumer (2026-10-06)

Unconditional geometric providers and a **conditional research reduction**.

- Analysis/FiniteSpectralDependentEscape.lean: the sharp moment lower floor
  permits eventual envelope hypotheses; strict feedback can be supplied only
  on a cofinal sequence.
- RH/ParetoActualSpectralLimits.lean: J_n->delta with T_n=J_n+S_n retained;
  the literal sigma_n=S_n+1/(n+1) is positive, dominates the entire optimizer
  tail, tends to zero and is eventually below one. The canonical lower floor
  has no additional geometric hypotheses.
- riemannHypothesis_of_actual_compactSpectrum_cofinal_canonical_feedback:
  requires k_n->infinity, theta<1, E_n->0 and the complete-source normalized
  arithmetic moment upper budget only along k_n. All envelope inputs are
  internally discharged.

Open arithmetic: actual tightness or the strict cofinal moment budget.
Open formalization: RH-to-density converse. No arithmetic provider is inferred
from the unconditional geometric limits. Source: the supplied continuation
and exact actual full-stage geometry. See Section 7 of
RH/GreenParetoSpectralLimitsAdvance20261006.md.


### Actual spectral limits, sharp moment feedback and relative signed gaps (2026-10-06)

Unconditional geometry and conditional research reductions; complete tails
and every signed interaction remain explicit. Eight new focused modules:

- RH/ParetoCompactCutoffLimits.lean: strong physical cutoff convergence,
  independently cofinal moving cutoff convergence, actual optimizer tail decay.
- RH/ParetoCompactSourceLimits.lean: exact shifted charge dilation formula,
  unconditional PNT decay, conductor-stage membership and actual head-error decay.
- RH/ParetoActualSpectralLimits.lean: literal actual S_n->0 and T_n->delta,
  fixed-threshold escaped mass ->delta, tightness iff one_mem_closedSpace,
  actual tightness-to-RH and strict double-log feedback-to-RH consumers.
- Analysis/FiniteSpectralMomentObstruction.lean: coefficient-one eventual
  normalized moment lower floor, sharp additive-log2 finite envelope,
  any theta<1 feedback absorption.
- Analysis/FiniteSpectralDependentEscape.lean: changing-dimension full-source
  escape, tightness equivalence and sharp moment consumers.
- Analysis/CumulativeRelativeFloor.lean: normalized negative-prefix variation
  automatically vanishes under O(terminal prefix) excursions and diverging mass.
- RH/ParetoCumulativeRelativeFloor.lean: actual cumulative signed RH consumer
  using that automatic penalty limit.
- Analysis/FiniteConstrainedProjection.lean: constructed unique constrained
  projection, exact inverse correction, full Pythagorean completion,
  delta+head^2 <= E <= delta+C^2 head^2 from an explicit legal repair norm cap.

Open arithmetic: actual source tightness or strict normalized moment feedback;
actual cumulative signed budget and normalized numerator with relative floor;
concrete optimized complete-error decay and support schedule.
Closed finite formalization: concrete Mobius O(H) repair with cap 12H and
the actual complete constrained-energy comparison; see the 2026-10-07 entry.
Open formalization: RH -> BaezDuarte.CenteredApproximation.
The previously open unconditional actual spectral sequence assembly is closed.
Decisive isolated check and seven axiom audits passed with only standard
foundations. See RH/GreenParetoSpectralLimitsAdvance20261006.md.

### Cumulative variation, exact-head closure, literal spectrum and retained signature (2026-10-06)

**Unconditional finite geometry and conditional research reductions.**
Complete signed interactions, boundary terms and infinite-tail norm squares
remain explicit. No arithmetic provider or RH converse is inferred.

- Analysis/CumulativeSignedGap.lean: exact signed Abel boundary and
  negative-prefix residual-variation penalty. Intermediate cumulative
  prefixes may be negative, even unbounded below.
- RH/ParetoCumulativeSignedGap.lean: actual RH consumer from a cofinal
  complete signed budget and normalized signed head+budget+penalty smallness.
- RH/CanonicalMobiusHeadRepair.lean: arbitrary fixed-head approximation iff
  actual closed-span membership; every prescribed positive complete-error
  budget is attainable with unrestricted finite support after membership.
- RH/CanonicalMobiusHeadErrorCriterion.lean: cofinal bounded complete errors
  with exact growing heads iff actual closure membership.
- Analysis/FiniteConstraintClosure.lean: quantitative continuous exact repair.
- RH/CanonicalMobiusSharpResidualEnergy.lean: unconditional canonical complete
  error <= 4N+1/(N+1). RH/ResidualEnergyHistoricalTargets.lean now proves
  linearExactHeadUpperWitness, closing LinearExactHeadUpperWitnessTarget.
  This linear ceiling is not a subpower estimate or an optimality claim.
- Analysis/FiniteHeadTailSpectralRealization.lean and
  RH/ParetoActualHeadSpectrum.lean: literal full-stage head image, constructed
  inverse head lift, complete positive tail spectrum, actual optimizer fit,
  correction squares S+J, source mass and exact projection error e+T.
- Analysis/FiniteSpectralEscape.lean: if T_N->delta and S_N->0, source mass
  above every fixed positive threshold tends to delta. Eventual tightness
  iff delta=0; moving thresholds also work when (1+R_N)S_N->0.
- RH/LocalizedMellinHeadSignature.lean: exact full complex head signature
  and head square; RH under subpolynomial complete-error growth and positive
  weighted signature growth only on unbounded indices. No head-norm limit.

Open (arithmetic): actual cumulative signed budgets and normalized smallness;
complete optimized/affine error growth; literal spectral tightness or source
moments; actual Mellin-signature noncancellation.
Closed by ParetoCompactCutoffLimits, ParetoCompactSourceLimits and
ParetoActualSpectralLimits: cutoff convergence, actual compact head-error
decay, optimizer-tail decay and the actual sequence-to-RH spectral consumer.
The normalized double-log lower-floor obstruction >=delta is also formalized.
Open (formalization): RH -> BaezDuarte.CenteredApproximation.
Closed by ParetoMobiusHeadInterpolation and ParetoMobiusConstrainedEnergy:
the concrete complete O(H) repair with cap 12H and the actual exact-head
error infimum comparison, with no repair norm assumption remaining.
Earlier source status was stale: reciprocal-charge nonvanishing, complete
canonical affine exhaustion and continuous head repair were already proved.
See RH/GreenParetoGitHubAdvance20261006.md for exact hypotheses, proof
derivations, verification records, primary sources and an improved next prompt.

### Moving gaps, mixed trials, approximate heads and double-log source budgets (2026-10-06)

**Conditional research reductions.** The actual RH consumers expose their
arithmetic providers. All finite identities retain complete signed interactions.

- `Analysis/MovingSignedGap.lean`: exact signed absorption and zero-defect
  consumers for positive stage-dependent gaps, without a uniform lower gap.
- `RH/ParetoMovingSignedGap.lean`: actual RH from cofinal legal trials, an
  eventual complete signed budget, and head/additive errors little-o of the gap.
- `Analysis/FiniteSpectralDoubleLog.lean`: finite double-logarithmic envelope
  bound and cofinal defect-zero consumer; unbounded moments are allowed.
- `RH/ParetoAffineHeadTrials.lean`: complete mixed residual Gram identity and
  actual canonical Mobius affine-trial RH consumer. No individual energy cap
  or reciprocal-charge crossing premise is needed.
- `RH/LegalApproximateHeadSubpolynomial.lean`: actual localized power floor
  for small physical residual heads, and RH from head norm convergence plus
  subpolynomial complete residual-energy growth. Exact interpolation is dropped.

Open: provide the signed moving-gap budget and relative head/additive errors.
Update: the literal finite full-conductor spectrum is now constructed in
RH/ParetoActualHeadSpectrum.lean. Its asymptotic sequence assembly remains a
formalization task; the arithmetic normalized double-log moment estimate is Open.
Open: construct normalized affine weights with subpolynomial complete mixed
Gram growth, or legal approximate-head trials with the stated full-energy growth.
The new implications do not establish RH or a converse for prescribed families.
Source: user-provided Green-Pareto-Schur continuation, Sections 17-28, and
the requested strengthening. See `RH/GreenParetoStrongerConditions20261006.md`
for exact hypotheses, scope, primary-source context and Wolfram diagnostics.


### Crossing-balanced squarefree windows and subpolynomial RH reductions (2026-10-06)

**Conditional research reductions.** All displayed complete identities and
analytic obstructions below are unconditional under their explicit finite
construction hypotheses. The RH consumers keep the arithmetic providers Open.

- `Analysis/SubpolynomialWindowGrowth.lean`: logarithmic contradiction to a
  positive-power floor and transfer under a fixed multiplicative budget.
- `RH/BalancedSquarefreeCrossing.lean`: actual canonical Möbius trial at a
  reciprocal-charge crossing, squarefree boundary/support, convex parameter,
  source charge zero, exact head, endpoint and full pointwise error bound.
- `RH/ParetoFiniteWindowEnergy.lean`: actual complete norm = finite square
  window + whole farther tail, far bound one, exact window mass, full signed
  quadratic decomposition, diagonal < 1, signed pair >= -1/2, and sharp
  square-root comparison between trial and residual window energies.
- `RH/LocalizedMellinObstruction.lean`: sharp localized residual power lower
  bound at an actual zeta zero, using the actual Mellin/legal-space theorem.
- `RH/LegalExactHeadSubpolynomial.lean`: actual RH from cofinal legal exact-head
  trials, full error certificates, and literal subpolynomial growth.
- `RH/SquarefreeWindowSubpolynomial.lean`:
  `riemannHypothesis_of_subpolynomial_crossing_window` specializes this to the
  actual crossing-balanced family; `riemannHypothesis_of_subpolynomial_positive_crossing_pairs`
  uses the positive part of the complete signed unequal-pair sum. The pair is
  half the ordered unequal-pair sum, retaining every interaction.
- `RH/CompactTargetMellinObstruction.lean`: actual compact target transform
  `(14-26*2^(-s)+12*2^(-2s))/s`, nonvanishing for Re(s)>1/2, and conditional
  compact-target subpolynomial RH consumer with a complete error budget.
- `RH/CompactShiftedMobiusSource.lean`: explicit shifted source formula and
  actual arithmetic coefficient bound `|nu(n)| <= 40`.
- `RH/CompactCorrectedTrialWindow.lean`: actual corrected compact lift, source
  floor inversion, legality, exact expanding head and endpoint, actual
  orthogonal head bound `400/(N*(N+1))`, complete certificate bounds with the
  whole far tail bounded by 1600, and its conditional RH consumer.
- `RH/ParetoCompactHead.lean`: reusable actual head norm equals the sole
  endpoint energy when the strict initial head vanishes.
- `RH/PrimorialExtrapolationObstruction.lean`: actual finite atom formula,
  prime-divisor regrouping to the paper's extrapolant, complete norm/error
  lower bounds, and cofinal divergence of its complete physical energy.

Open: provide a checked cofinal crossing sequence (the classical oscillation
argument in the continuation is not formalized by these modules).
Open: prove literal subpolynomial growth of the complete crossing window, or
of the positive part of the complete signed squarefree pair energy.
Open (formalization): supply checked cofinal compact cutoffs with
`|xi_N| <= 20/N` from the continuation's classical small-charge argument.
Open: prove literal subpolynomial growth of the compact residual certificate
on those cutoffs. No RH converse or unconditional RH proof is asserted.
Source: user-provided Green--Pareto--Schur continuation, Sections 21--26
(statements and proof strategies); no mathematical novelty claim is made.


### Signed physical trial tails and relative logarithmic source growth (2026-10-06)

**Conditional research reductions.** The actual Pareto trial consumers conclude
RH from explicit cofinal arithmetic providers; these providers are Open.

- `Analysis/HeadTailPairing.lean`: exact residual and complete correction signed
  identities, with both full tails retained; Cauchy/product and cofinal bounds.
- `Analysis/HeadTailConditions.lean`: cofinal/frequent/absorbed/growing product
  conditions, signed head-error limit and strict-fraction cancellation, and
  conditional forced divergence of trial-tail energy.
- `Analysis/FiniteSpectralBudget.lean`: finite nonnegative source data, exact
  `correction_eq_headDisplacement_add_optimizerTail`, full threshold
  comparisons, logarithmic/general moment and screening budget consumers.
- `Analysis/FiniteSpectralRelativeLog.lean`:
  `correction_le_relative_log_envelope` gives
  `T ≤ sigma + sqrt sigma + 2 L / log (1 / sigma)`;
  `limit_eq_zero_of_cofinal_relative_log_envelope` allows unbounded log moments
  when `L / log (1 / sigma) → 0`, on a cofinal positive tail envelope.
- `RH/ParetoCompactHead.lean`: actual orthogonal cutoff at physical sites
  `1,...,N`, coordinate formula, symmetry, Pythagoras, contraction and linearity.
- `RH/ParetoTrialTailConditions.lean`:
  `twoThree_actual_trial_signed_identity` proves `D = H + L` for every legal
  trial, and `twoThree_actual_trial_head_pair_abs_le` bounds only the head error.
  `riemannHypothesis_of_cofinal_signed_trial_fraction` and
  `riemannHypothesis_of_cofinal_approximate_head_tail_product` invoke the existing
  compact-dual RH criterion. Normal equations and residual convergence are
  supplied by the actual projection, with no exact head-lift construction.

Open: construct legal trials with cofinal head-error convergence.
Open: prove the signed strict-fraction provider, or the full tail-product
smallness provider, for those trials.
Open: construct the actual whitened arithmetic spectral/source realization in
Lean and identify its finite sums with the correction and optimizer-tail energy.
Open: prove the arithmetic relative-logarithmic growth estimate.
The sharp Jensen lower bound remains a paper proof. No RH converse is used.
Source: user-provided Green-Pareto-Schur continuation, Sections 12, 17 and 18
(statements and signed proof strategy). See
`RH/GreenParetoTrialConditions20261006.md` for exact assumptions and scope.

### Exact compensated Schur budget and compact dual target (2026-10-06)

RH/CompensatedTwoCoefficientSchur.lean proves the actual signed Schur
increment, its complete old-stage inverse screening, stage-zero and stage-two
telescoping, absolute summability, and the exact series sum. The equivalent
signed cofinal budget has a conditional RH consumer; convergence alone is
not its arithmetic provider.

RH/CompensatedTwoCoefficientCriterion.lean additionally identifies the
compact dual target, retains both whole approximation defects in the finite
completion, and proves dual-target membership and dual-error convergence
equivalent to constant-target membership. Its RH consumer assumes actual
dual-error convergence.

Open: the signed cofinal lower bound or compact dual saturation. The
periodic finite dual floor, normalized gain application, Burnol-inherited
logarithmic cap, and prime sufficient providers are paper deductions in
RH/FixedGramAdjointContinuation20261006.md, Section 19. No gain divergence
or RH-to-target-membership converse is supplied.

### Actual fixed-Gram dyadic adjoint and compensated coefficient bridge (2026-10-06)

RH/ActualDyadicAdjointDefect.lean proves actual equations (21), (22), and
(37), including convergence and the full nonnegative pair-variance series.
RH/DyadicCanonicalLeakage.lean proves equation (28) with both orthogonal
norm squares, the actual scalar energy premise, the stronger signed
obstruction, and the compensated surplus. Analysis/DyadicAdjointDefect.lean
supplies the reused adjoint-square and leakage/contradiction algebra.

RH/CompensatedTwoCoefficientCriterion.lean identifies the statistic with
the complete inverse Gram, keeps both finite signed enlargement terms,
and proves cofinal lower control iff the actual residual is zero, iff
constant-target membership holds. Its RH consumer is a **conditional
research reduction**.

Open: TwoThreeCompensatedCofinal, the actual cofinal arithmetic provider
for 3*c[n,2]+c[n,3]-4+(23/24)*(1-Q[n]), or fixed full-inverse saturation.
The reverse formal RH equivalence exposes the separate hypothesis
hTarget : RiemannHypothesis → hilbertOne ∈ closedSpace.
The Mellin jets and equation (39) are not formalized here. RH is not proved.

### Quadratic first moments and flexible signed mollifier budgets (2026-10-05)

Analysis/ComplexQuadraticDetectorMoments.lean proves log(1+x^2)<=x^p
for x>=0 and 1<=p<=2, complex quadratic-detector domination, and its
interval-integral version with explicit integrability assumptions.

Analysis/ActualMollifierSignedBoundaryBudget.lean applies this bound to the
actual zeta detector and constructs SignedLeftRectangleBudget from concrete
moment and compatible-horizontal estimates. Its new finite-X count consumer
requires only X>=37, replacing X>=T+37, with the exact extra term
(T+1)(-log(1-36/X))log T/(2*pi*eta). These are conditional reductions:
the near-line moments, Gabriel interpolation, and horizontal estimates remain
analytic provider obligations.

RH/MollifierFirstMomentContinuation20261005.md proves on paper a
height-independent signed right bound Li_2(36/X)/log(X+1)<=1 and a
first-moment shrinking-tail refinement. Those analytic series and moment
arguments are not asserted to be kernel-formalized, and normalized tail
decay does not prove RH. The original finite head, full N(T), detector
multiplicities, and compatible boundary signs are retained.


### Proved Littlewood identity and unconditional signed right boundary (2026-10-05)

**Established analytic rectangle providers.**
Analysis/ComplexIntegralLogLift.lean constructs differentiable logarithm
lifts from FTC. Analysis/ComplexLittlewoodBoundary.lean proves the complete
signed Littlewood boundary identity from actual analyticity and border
nonvanishing; no log-lift or hLittlewood premise remains.
Analysis/ComplexRectangleZeroCount.lean proves the weighted finite analytic
order identity and arbitrarily small outward zero-free rectangles.
Analysis/ActualMollifierRectangleContour.lean includes the actual zeta window
in the full detector zero count, retaining extra detector orders.
Analysis/ActualMollifierBoundaryAvoidance.lean preserves the original closed
top T and exactly expands the H<gamma<=T window into the original and both
added windows. The original finite-height subtraction is retained.

**Established unconditional Mobius-tail right provider.**
Analysis/ZetaAbsoluteConvergenceBounds.lean proves the integral-test zeta
bound for Re s>1. Analysis/ActualMollifierRightBoundary.lean proves the exact
Mobius tail identity, ||zeta M_X-1||<=6/sqrt X on Re s=3/2 and, for X>=37,

    -integral_H^T log|h_X| <= -(T-H)log(1-36/X)
      <=36(T-H)/(X-36).

The detector is nonzero and its log norm is continuous on that right line.
These are independent absolute-convergence constants; the paper's numerical
C5 and near-line moments are not claimed to be imported.

**Conditional analytic reduction with a strictly weaker remaining budget.**
Analysis/ActualMollifierSignedBoundaryBudget.lean proves
shrinking_harmonic_tail_of_leftRectangleBudget using the concrete mollifier
cutoff ceil(T)+37. Only ExpandedLeftRectangleBudget remains: a bound on the
signed left log integral plus compatible top-minus-bottom argument integrals
at one admissible source cutoff on an outward rectangle. The automatic right
term contributes at most 18 log T/(pi eta), absorbed into B3 log T.
All logarithm lifts, contour identities, detector counting, boundary
avoidance and asymptotic transfers are proved. The strict J(T,sigma)
subtraction, D(H,sigma), full N(T), multiplicities, reflection, composites
and negative sinh contribution are preserved.

**Open:** the quantitative signed left-and-horizontal provider, including
the cited Gabriel/mollifier-second/zeta-fourth-moment argument and source
constants. A fully unconditional shrinking strict-tail provider is not
claimed. The weakest count-only interface is still the one-point density
difference below. Principal new audits contain only propext, Classical.choice
and Quot.sound; no source theorem is an axiom.

Report: RH/StrictShrinkingTailProvider20261005.md.


### Strict shrinking-cutoff harmonic transfer (2026-10-05)

**Established exact counting and unconditional cutoff/remainder transfers.**
Analysis/ActualZeroDensityWindow.lean proves the multiplicity-preserving
finite-height split D(T,sigma)=D(H,sigma)+D(H,T;sigma), and exactly

    strictTail(T,delta)=2*(D(T,1/2+delta)-J(T,1/2+delta)),

where J counts equality copies at the closed density threshold.
The strict bad-mask boundary, reflection and original full N(T) are retained.
Analysis/NonlinearZeroDensityRate.lean now includes the positive-part inverse
cutoff and its least-cutoff characterization and eventual 1/32 range.
Analysis/ActualHyperbolicLogRemainder.lean proves that the retained fixed count
N(H), log-square and logarithmic terms vanish after multiplication by W_d/N(T)
whenever d>=1 and log d<=log T/2 eventually. Analysis/LogMarginAsymptotics.lean
contains the general real scalar asymptotic lemmas.
Analysis/ActualZeroDensityCutoff.lean proves sourceCountCutoff_shrinking:
if log d/log T->0 and omega/log T->0, the exact actual-count cutoff tends
to zero and eventually lies in [0,1/32], without a density premise.

**Established detector, weighted identities and source admissibility.**
Analysis/ComplexQuadraticZeroDetector.lean proves the full analytic order
sum. Analysis/ActualMobiusZeroDetector.lean defines the finite actual Mobius
mollifier, proves its real-line limit is one and its order is finite, and
proves detector order = original zeta multiplicity + mollifier order.
Analysis/ActualZeroDensityLogExcess.lean proves the exact threshold-window
decomposition, the extra mollifier contribution and the finite complement
sum before using their nonnegativity. The threshold remains closed.
Analysis/ComplexLogRectangleBoundary.lean retains all four signed integrals
and explicit horizontal argument lifts; a common additive lift change
cancels exactly. No principal-argument compatibility is asserted.

Analysis/ActualZeroDensityCutoff.lean additionally proves
sourceAdmissibleCutoff_shrinking: for fixed eta>0, replace the inverse cutoff
by max(inverse cutoff,2*eta/log T). It tends to zero, eventually lies in
[0,1/32] and strictly exceeds eta/log T. Its canonical left line
1/2+delta-eta/log T is strictly above 1/2. The exact rate difference and
monotonicity in Analysis/NonlinearZeroDensityRate.lean prove that this
larger physical cutoff preserves the inverse-rate exponential budget.

**Conditional research reduction: the actual detector route.**
Analysis/ActualMollifierDensityTransfer.lean proves the finite count and
complete harmonic consequences of a detector-weighted window bound and
exposes optional Littlewood/full-boundary premises.
shrinking_harmonic_tail_of_admissibleDetector assumes only the eventual
weighted estimate at the canonical left line and refined cutoff, with
X(T)>=1. Analysis/ActualHyperbolicShrinkingTail.lean proves
shrinking_harmonic_tail_of_admissibleDifference from the one-point count
estimate at that same admissible cutoff. Both imply delta->0,
(strictTail/N(T))*W_d->0, actualSignedTailBudget->0 and
||signedBadHyperbolic||->0 under the existing prescribed growth conditions.
The strict equality subtraction, retained finite-height count, reflection,
multiplicities, full N(T), negative sinh square and composites survive.

**Open:** the one-point actual density estimate remains the minimal
count-only analytic interface. The stronger sufficient detector estimate
has not been proved. Littlewood, compatible lifts, boundary avoidance and
the right-side provider are now established in the continuation above.
The signed left-and-horizontal bound via Gabriel/fourth-moment/mollifier
estimates and source constants remain Open. No cited theorem is an axiom.
Principal continuation audits report only propext, Classical.choice and
Quot.sound, with all domain hypotheses explicit in declaration types.

**Conditional research reduction: one actual density point suffices.**
Analysis/ActualHyperbolicShrinkingTail.lean proves
shrinking_harmonic_tail_of_inghamDifference and
shrinking_harmonic_tail_of_sourceDifference. Put L=log T, M=L+log L,
I(delta)=4*delta/(3-2*delta), K=C*T*L^3, A=2*K*W_d/N(T),
S=max(0,log A+omega), and delta=3*S/(4*M+2*S). The only analytic premise is

    D(T,1/2+delta)-D(H,1/2+delta)
      <=K*exp(-M*I(delta))+B2*L^2+B3*L.

The power-shaped consumer accepts the equivalent source exponents directly.
For C>0, B2,B3>=0, d>=1 eventually, log d/log T->0, omega->infinity and
omega/log T->0, this implies

    delta->0, (strictTail/N(T))*W_d->0,
    actualSignedTailBudget->0, ||signedBadHyperbolic||->0.

The finite bound retains D(H,sigma)-J(T,sigma); its coarse asymptotic bound
retains N(H). Both hyperbolic channels, the negative sinh square and all
composite coordinates survive. The one-point limit also supplies the existing
signed one-sided frame provider uniformly in f and makes the original
masked-good/full-operator norm difference tend to zero.

**Open domain-specific obligation:** prove the displayed actual one-point
difference estimate from the Chourasiya--Simonic analytic argument and verify
its chosen numerical parameters. It is an explicit hypothesis, not an axiom
or an imported theorem. No finite-height RH certificate is assumed.
**Separate Open obligation:** the fully screened physical Pareto transfer.
The principal base declarations and the new reductions pass #print axioms
with only propext, Classical.choice and Quot.sound; local hypotheses remain
visible in the theorem types.

Report: RH/StrictShrinkingTailProvider20261005.md.
Requested audit base: 81ecb78f890611273f961c6ca1d056c448587eb4.
The immediate descendant's independent 1/3 Landau improvement is preserved.

### Hilbert--Schmidt Landau strengthening and optimized density consumers (2026-10-05)

**Established unconditional actual residual and full form.**
Analysis/EuclideanHilbertSchmidt.lean gives finite Euclidean entry-square
certificates. Analysis/LandauHilbertSchmidtResidual.lean assembles the existing
actual nonmaxed rational Landau provider without any new analytic premise:
for T>=9 and N(T)>0, the complete signed residual obeys

    ||E_d(T)|| <= C/N(T) * [2*d^3+2*d^2*log(T+3)^2+3*d^2*log(T+3)].

Eventually log d(T)<=a+log(T+3)/3 and d(T)>=1 imply ||E||->0.
This strengthens the previous 2/7 support endpoint to 1/3. For
0<=theta<=1/3 and every h<1-theta the full actual Gram is eventually
bounded below by h*||f||^2. At theta=1/3 every h<2/3 holds in the
explicit actual-row form ||Cf||^2-||Sf||^2, retaining the negative
sinh square, analytic multiplicity, original complex convention and
all integer/composite coordinates. The leading-budget theorem proves residual convergence under
d(T)^3/((T+3)*log(T+3))->0, including the checked logarithmic extension
d=O((T+3)^(1/3)*log(T+3)^b) for every b<1/3. Its exact iff characterizes
the nonnegative normalized envelope, not necessity for the signed residual.

**Established exact scalar cutoff; conditional actual-density reduction.**
Analysis/NonlinearZeroDensityRate.lean proves countCutoff(M,S)=3*S/(4*M+2*S),
M*inghamRate(countCutoff)=S and the least-cutoff equivalence for t<=1/2.
Its 1/32 range is equivalent to 47*S<=2*M. With A>0, S=log A+omega>=0,
A*exp(-M*inghamRate(countCutoff))=exp(-omega) exactly.
Analysis/ActualHyperbolicDensityBudget.lean transports an explicit inclusive
right-count hypothesis K*exp(-M*v(delta))+E through actual reflection and the
complete harmonic cap W_d. For A=2*K*W_d/N(T), it proves

    ||signedBadHyperbolic(T,d,delta)|| <= exp(-omega)+2*E*W_d/N(T).

This is a checked consumer, not an analytic zero-density provider.
**Open:** formalize the published uniform actual count estimate with its
initial count and additive remainder; prove the actual shrinking signed-tail
budget where needed; discharge the separate physical Pareto transfer.

**Established finite Schur transport; paper actual Cauchy specialization.**
Analysis/CorrelationSchurFrameBounds.lean proves that a PSD matrix S with
diagonal one transports both PSD frame bounds under Schur multiplication,
with unchanged constants. The actual Cauchy correlation, its positive
continuous displacement law, the sharp full arithmetic norm
||B_d||=4*log(log d)+O(1), and its exact inverse amplification
(d+1)/(2*sqrt(d)) are self-contained paper proofs, not Lean declarations.
Combining those paper results with the checked actual residual gives a
smoothed ordinary phase Gram tending to identity at d=O(T^(1/3)).
**Open:** the Lean Cauchy/Fourier/arithmetic specializations and the distinct
unsmoothed discrete-phase and physical transfers. No RH conclusion follows.

Reports: RH/LandauHilbertSchmidt20261005.md,
RH/ActualZeroOptimizedDensity20261005.md,
RH/CauchySmoothedActualZeroFrames20261005.md,
RH/SmoothedPrimePowerArithmetic20261005.md.

### Verified provider-gap continuation (2026-10-05)

**Established actual good-copy refinement.** The exact positive domination
delta^(2k)*B0-Bk proves ||Bk||<=delta^(2k)*||B0|| and ||B0||<=||phaseGram||.
The actual centered logarithmic commutator series, its complete signed good
correction, and its explicit finite-head remainder now use ||B0||/2.
These results extend HorizontalEuclideanMoments, ActualZeroPhaseMoments,
ActualZeroLogDiagonal and ActualZeroPhaseOperators without analytic premises.

**Established full leading-budget Landau convergence.**
LandauGrowingSupport proves that the normalized nonnegative three-term
envelope tends to zero iff exp(7*ell/2-L)/L does. This iff concerns the
envelope, not necessity for a signed residual. ActualLandauOperatorResidual
proves residual norm convergence if d^(7/2)/((T+3)*log(T+3))->0, including
d=O((T+3)^(2/7)*log(T+3)^b) for every fixed b<2/7. The complete signed
prime-power covariance main is retained.

**Established two-sided harmonic actual tail bound.**
FiniteHyperbolicHarmonicCap proves W_d=(d+sqrt(d*(d+1)*H_d/2))/2 and
W_d<=d*(1+sqrt(1+log d))/2 for d>=1. ActualHyperbolicHarmonicTail proves
||signedBadHyperbolic||<=actualSignedTailBudget<=(strictTail/N(T))*W_d,
Hermiticity, the corresponding masked-good norm bound, and the imported
two-thirds proportion consumers. Both row channels and the full normalizer
remain unchanged. With r=strictTail/N(T), the sharper spectral interval is
[-r*(W_d-d), r*W_d]; the centered norm is bounded by
||signedBadHyperbolic-(r*d/2)*I||<=r*sqrt(d*(d+1)*H_d/2)/2.

**Open actual analytic input.** The imported cumulative proportion only
gives strictTail/N<=1/3+epsilon. It supplies no shrinking-cutoff decay.
(strictTail(T,delta(T))/N(T))*W_(d(T))->0 is a sufficient one-point input;
the exact signed-surplus provider can be weaker. The sharp Landau--Gonek
estimate, the displacement-sensitive actual density provider, and the
separate physical Pareto transfer remain formalization obligations. See
RH/LeanProviderGapContinuation20261005.md for proofs, scope and sources.

### Actual hyperbolic lower bounds and signed-tail frames (2026-10-05)

**Established full actual form.**
Analysis/ActualHyperbolicGramLowerBounds.lean traces the normalized conjugate
phase rows over every actual zero copy with the transpose of the actual Landau
Gram. The exact quadratic identity is ||Cf||^2-||Sf||^2=Re<f,Hf>; analytic
multiplicities, the original complex convention, every integer frequency and
all composite interactions are retained. The explicit Ioc(0,d)/Fin d reindex
transfers the existing full arithmetic Schur estimate. For T>=0 it proves

    H[f] >= [1-T*(log d+log 4+4)/(2*pi*N(T))-||E||]*||f||^2,

where E=H-I+T*A/(2*pi*N(T)) is the original signed residual.
The stronger ground-state formula keeps the complete positive arithmetic
graph square and estimates only the signed residual. Its general finite
identity is in Analysis/WeightedGroundStateForm.lean.
For 0<=theta<=2/7, eventual log d<=a+theta*log(T+3), and h<1-theta,
eventually H[f]>=h*||f||^2 uniformly in all coefficient vectors.
In particular every h<5/7 holds at the existing 2/7 support endpoint.
No zero-density or RH premise is used. The concrete all-row centered transfer
now uses this computed form coefficient rather than an arbitrary form input.

**Established finite signed-tail budget; conditional masked-frame reduction.**
Analysis/HyperbolicRowNumericalRange.lean proves the sharp signed rank-two
upper coefficient (||u||*||v||+Re<u,v>)/2 by balanced sum/difference channels.
Analysis/ActualHyperbolicTailFrames.lean specializes it to the actual
normalized exponential rows and sums every strict-bad zero copy.
The original negative sinh square is retained in the exact bad form.
The good operator is exactly H-H_bad, using the full N(T) normalization.
Its zeroed good-row realization has the exact masked hyperbolic form.
goodHyperbolic_lower_iff_signed_surplus states the weakest exact directional
provider; SignedBadHyperbolicUpper is a useful one-sided sufficient provider.
actual_good_centered_frame_lower_of_signedBad feeds that explicit provider
directly into the finite centered-frame theorem with the shrinking delta.

**Open application input.**
The smallness of the actual signed bad-tail budget at the improved centered
support constant remains Open in Lean. A sufficient count-only budget is
strictTail(T,delta)*[d+sqrt(d*(d+1)*H_d/2)]/(2*N(T)); its harmonic reduction
and the published uniform-density specialization are paper consequences in
RH/ActualHyperbolicLowerBounds20261005.md. The report distinguishes these
from the checked finite declarations. Actual Ingham/Selberg density and
fully screened physical Pareto transfer remain separate Open obligations.
The Hilbert--Schmidt continuation above now formalizes the 1/3 strengthening
and its logarithmic support gain in Analysis/LandauHilbertSchmidtResidual.lean.

### Endpoint Landau support and centered hyperbolic frames (2026-10-05)

**Unconditional actual signed residual endpoint.**
Analysis/ActualLandauOperatorResidual.lean adds
actualLandauResidual_norm_tendsto_zero_critical_power_support:
for any fixed real a and eventually positive integer support d(T),
log d(T) <= a + (2/7)*log(T+3) implies the full signed residual tends
to zero in Euclidean operator norm. The actual zero count retains its
logarithmic gain; no density or RH premise is used. Every original integer,
composite interaction, analytic multiplicity and the arithmetic main matrix
remain in the exact residual. This is not a physical Pareto inverse bound.

Analysis/LandauGrowingSupport.lean proves the exact critical envelope
divided by L, its three-term limit, and strict polynomial support envelopes.
Analysis/NonlinearZeroDensityRate.lean proves the exact source power-to-exp
identity retaining log(log T), plus uniform scalar exponent cutoffs.

**Established finite centered identities and conditional frame transfer.**
Analysis/CenteredHyperbolicFrames.lean proves the exact cosh kernel and
quadratic C/S factorization, scalar centered row series, sharp even diagonal
half-centering, absolute operator-series summability, dimension-free
half-factor remainder bound, and lower norm/injectivity transfer.
The negative sinh square is retained. The finite transfer lists its form
bound explicitly. Analysis/CenteredHyperbolicRows.lean realizes rectangular
Euclidean analysis operators, proves their exact centered decomposition,
identifies the concrete remainder with the full operator series, and supplies
its half-factor norm bound from finite coordinate bounds. Its concrete lower
frame theorem leaves only the hyperbolic form lower bound as an application
input beyond the listed finite bounds.
The improved z < 7/5 certificate is algebraic. The exact positive constant
centeredSupportConstant=sqrt((8/3)*arcosh(7/5)) and its equivalence to
cosh(3*c^2/8)<7/5 for nonnegative c are proved without decimal assumptions.

**Open analytic/application obligations.**
The actual Ingham/Selberg zero-density theorem is still Open in Lean.
A cited theorem and Wolfram computations do not discharge this premise.
The unconditional actual-zero growing-support frame specialization and
the fully screened physical Pareto transfer remain Open.
See RH/LandauEndpointCenteredFrames20261005.md for exact scope and sources.

### Signed Landau residual and nonlinear density consumers (2026-10-05)

**Unconditional Landau residual assembly.**
Analysis/ActualLandauOperatorResidual.lean realizes the complete prime-power
covariance on the same Fin d Euclidean space as the actual Landau Gram.
The signed residual is exactly H-I+T*C_d/(2*pi*N(T)); every integer and
composite-frequency interaction is retained, the diagonal is zero, and
reflection gives its exact Hermitian entry identity.
`exists_actualLandauResidual_norm_bound` gives
`C*d*(d^(5/2)+d^(3/2)*log(T+3)^2+d*log(T+3))/N(T)`
without a density or RH premise.
`actualLandauResidual_norm_tendsto_zero_sqrt_support` proves its norm tends
to zero whenever log d(T)<=c*sqrt(log(T+3)) eventually, for every fixed real c
and eventually positive d(T). The arithmetic main matrix remains explicit.

Analysis/LandauGrowingSupport.lean proves the exact three-term exponential
envelope, polynomial-times-exponential decay, and the square-root-log
support majorant. EuclideanOperatorCoordinates.lean now supplies the full
d*R Euclidean norm bound from a uniform entry bound, including empty spaces.

**Conditional nonlinear density and frame consumers.**
Analysis/ActualZeroNonlinearDensityTransfer.lean transfers
`strictTail T s <= K*exp(-M*inghamRate s)+E` to the exact finite cosh budget.
Both exponential endpoints and the negative companion term remain, and
the additive remainder is exactly weighted by cosh(ell/2)-1.
`badCorrection_norm_le_of_nonlinearTail` retains d/(2*N(T));
`phaseGram_isUnit_of_nonlinearTail` gives the finite frame test from the
explicit actual density estimate, Landau-to-identity norm and scalar gap.
These are conditional research reductions. The actual Ingham/Selberg
density estimate, sharper classical Landau rate, and unconditional frame
specialization remain Open.

NonlinearZeroDensityRate.lean also proves the sharp physical cutoff test
`stableCutoff <= 1/2 iff R <= M-ell/2`, automatic denominator safety,
automatic positive weighted tangent slope for R>0, and exact exponential
cancellation before any estimate. No analytic density hypothesis is
discharged by these scalar identities.

### Full Landau and actual density work (2026-10-05)

**Established complete uniform rational Landau provider.**
ActualUniformRationalLandau.lean proves, for all T>=9 and 1<=m<n<=X,
the actual multiplicity-weighted residual bound
`C*(X^(5/2)+X^(3/2)*log(T+3)^2+X*log(T+3))`.
`exists_uniform_rational_landau_rpow_bound` has no analytic estimate premise;
`rationalLandauMain_eq_vonMangoldt_div_sqrt` proves the exact classical main
coefficient. All four contour sides, the low sum, nonresonant series, arbitrary
cutoff window and `(A+T-B)*main` correction are retained before taking norms.
This sufficient uniform provider closes the fixed-c=2 Landau obligation.
The sharper classical scalar and matrix rates below remain unformalized.

ActualZetaGoodLandauHorizontals.lean proves
the actual functional equation for logarithmic derivatives, Gamma growth on
[-1,2], and full weighted horizontal bounds at actual good heights.
ActualZeroHeightTransfer.lean proves the complete signed window increment,
its reflected cosh form, and the actual arbitrary short-height bound
`cosh(|u|/2)*Ncount T R`, then `2A*log(T+4)*cosh(|u|/2)`.
ComplexLogIntegralBounds.lean retains the exact horizontal complex-log FTC
and oscillatory logarithm integration-by-parts endpoints. ActualLandauLeftLine.lean
proves the actual chi model with full complex error <=6/t, its finite
oscillatory integral bound, the complete reflected von Mangoldt series and
finite interval interchange, and the entire signed left contour split/bound.
No analytic bound hypothesis occurs in these actual providers.

ActualZeroCriticalLineTailFraction.lean transfers the existing unconditional
`Zeta23.thmA₀_cumulative` to an exact on-line/off-line partition and the
uniform eventual strict-tail fraction `(1/3+epsilon)*Ncount`, together with
the actual bad-operator consequence. This constant fraction does not close
shrinking-window exponential density. NonlinearZeroDensityRate.lean proves
the exact common Ingham rate, positive tangent remainder, stable cutoff
quadratic and support-budget equivalence; it asserts no actual density theorem.

**Rigorous source deductions; analytic Lean obligations remain Open.**
RH/FullLandauDensityProof20261005.md links complete proofs of rational
Landau error `O(X*log(2XT))`, the stronger all-integer matrix remainder
`C0*(27*d^(3/2)+5*d*H_d*log(2T))/N(T)`, and actual strict density
`44*T*log(T)^3*exp(-(4/3)*(log T+log(log T))*s)`, uniformly on the full strip.
The shrinking interval s<=1/32 admits constant 10.14 and exact nonlinear
rate `4s/(3-2s)`. The finite count `N(3*10^12)` is retained and absorbed
uniformly; no finite RH certificate is imported. These are mathematical
deductions from unconditional published theorems, not Lean providers of the
source analytic theorem. The sharper Landau–Gonek rates and actual Ingham/Selberg
mean-value/zero-counting arguments remain Open in Lean. The leading sufficient
support coefficient is unchanged; the nonlinear rate improves the next-order
cutoff. Neither this phase Gram nor the source deductions supplies the
screened physical Pareto inverse or proves RH.

### Actual zeta central provider progress (2026-10-05)

**Established actual providers.**
Analysis/ActualZeroHorizontalExpansion.lean proves the complete convergent
scalar even expansion for actual multiplicity sums. Generic Euclidean operator
coordinates and diagonal commutators are in EuclideanOperatorCoordinates.lean;
ActualZeroLogDiagonal.lean proves the actual centered diagonal norm is exactly
log(d)/2 for d>=1. ActualZeroPhaseOperators.lean proves
`landauGram_sub_phaseGram`: the full actual H-G is exactly its even commutator
series plus the entire signed bad correction. Every integer frequency and
analytic multiplicity is retained, with the original Ncount normalizer.
The actual correction norm has the sharp factor one-half.

ActualZeroBadPhaseTail.lean identifies the complete bad operator with its
finite copy sum and proves d/(2N) times the bad cosh-minus-one sum, then d/(4N)
times the bad exponential sum. ActualZeroTailLayerCake.lean proves strict
finite layer cake with both endpoints; ActualZeroTailReflection.lean identifies
the absolute strict tail as twice the right strict tail and dominates it by
the inclusive density count. ActualZeroTailDensityTransfer.lean proves the
exact closed finite cosh bound from an explicit actual scalar tail estimate.
ActualZeroBadTailDensity.lean composes it with the actual bad operator, preserving
the complete strict mask, both endpoint terms and the original normalizer.

ActualZeroCountAsymptotics.lean strengthens the eventual normalization to every
coefficient c<1/(2*pi), concretely 7/(16*pi), from the existing actual
Riemann-von Mangoldt theorem. PrimePowerCovarianceEuclideanNorm.lean realizes
the full integer-frequency arithmetic covariance in the Euclidean operator
norm and proves log(d)-2 <= norm <= log(d)+log(4)+4 for d>=1.
Composite divisibility interactions are retained; no density or RH premise
occurs in either provider.

ActualRationalLandauRightLine.lean proves the actual zeta Dirichlet-series
identity on Re(s)=2, finite-interval interchange, complete rational integer
resonance split and the uniform nonresonant norm bound. The exact completed-zeta
and direct-zeta weighted contours remain in RvM/CountByIntegral.lean and
ActualZeroLandauContour.lean. Ordinary boundary and analyticity conditions are
explicit. ActualZeroPhaseBootstrap.lean specializes norm absorption and
invertibility to the actual finite Gram; only explicit Landau/bad norm estimates
and scalar gap premises remain.

**Conditional research reduction remains Open.** Actual uniform exponential
zero density, the sharper Landau rates, microscopic square budget and asymptotic
spectral assembly remain separate obligations. The sufficient full rational
Landau provider is established in the follow-up above. The weighted-tail
consumer is proved, but its actual density input remains Open. The precise
ledger is RH/ActualZetaAnalyticProviderAudit20261005.md.

### Horizontal phase-Gram bootstrap and strengthened conditional support

HorizontalPhaseBootstrap.lean proves exact scalar centering of commutators,
absolute even-series convergence, sharp half-factor bounds, finite truncation,
norm absorption and Banach-algebra invertibility. HorizontalEuclideanMoments.lean
and ActualZeroPhaseMoments.lean discharge actual positive moment centering;
the actual centered diagonal and full operator identity are now also
Established as described above.

RH/GrowingPhaseGramBootstrapAudit20261005.md derives the conditionally sufficient
support threshold
`log X / sqrt(log T) -> c < sqrt((4/3)*arcosh 2) = 1.325120320033778...`.
Its limiting lower and upper spectral bounds are 2*(2-q)/(3-q) and 2/(3-q),
q=cosh(3*c^2/4). The asymptotic statement still needs the checked actual density provider
and asymptotic operator assembly; its sufficient scalar Landau input is now proved. The sharper normalization and exact finite
cosh transfer improve constants and endpoints; only near-line density on
0<=s<=1/32 is sufficient at this support scale.

Primary analytic sources: Ford--Zaharescu, Lemma 1
(https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf), and
Chourasiya--Simonic, Theorem 1, Corollary 1 and Table 1
(https://arxiv.org/html/2507.15184v2). Literature and Wolfram checks are not Lean
providers. This zero-ordinate phase Gram does not replace the screened physical
Pareto inverse. RH-equivalent cofinal screened arithmetic, signed inverse
saturation and bounded-frequency signed marked cancellation remain unproved.


### Strengthened exact normalization and literal marked tails (2026-10-04)

**Established natural-error decomposition.**
RH/BaezDuarteNaturalApproximation.lean proves `lintegral_sq_div_Ioi` for
arbitrary positive cutoff, `natural_tailError_eq_charge_sq`, and
`naturalError_eq_head_add_charge_sq`. The complete natural error is exactly
its head error plus the signed charge squared. `charge_sq_le_naturalError`
and `naturalHeadError_le_naturalError` precede the sharpened
`centeredError_le_two_naturalError` and `corrected_naturalError_le_two`.
`corrected_naturalCharge_eq_zero` retains the exact coefficient charge.
The obsolete factor-four/factor-ten declarations have been removed and their
in-repository documentation updated. Open: a checked provider of the classical
`RiemannHypothesis -> NaturalApproximation`; the translation theorem does not
supply that direction.

**Established exact marked Fourier and occurrence assembly.**
Analysis/MarkedIntegralCauchy.lean proves actual Bochner integral Cauchy--Schwarz
from MemLp, not an assumed scalar Cauchy premise.
Analysis/MarkedLaplaceKernel.lean identifies the complete original pair weight
`4/(4+(gamma_i-gamma_j)^2)` with its actual Laplace integral;
`kernelForm_zero_eq_energy` identifies the unmarked positive energy.
Analysis/TentFourierIntegral.lean preserves both affine-primitive endpoints and
proves the literal compact tent's Mathlib Fourier transform.
Analysis/TentFourierInversion.lean proves absolute integrability of that transform
and inversion at every point, including the support endpoints.

Analysis/GaussianCellGeometry.lean proves the complete finite Gaussian pair mass
is at most six times the full cell-occupancy square sum. Equal ordinates,
separate analytic multiplicity copies and diagonal terms are all retained.
Analysis/CellOccupancyOverlap.lean identifies the occupancy-square budget with
ordered same-cell pairs and proves the overlap comparison.
Analysis/GaussianSpectralWindows.lean supplies the genuine Gaussian finite
transform and unit-window L2 bounds. Analysis/GaussianAbsoluteWindowMass.lean
passes to the integral of the marked norm. Analysis/RationalGaussianWindows.lean
applies these bounds to the exact original rational pair weight, proving
`unit_window_absolute_marked_Ico_mass_le` uniformly in both marked centres.
RH/ActualZeroGaussianCells.lean specializes to every copy of every actual zero
in (T,2T] and proves the exact copy count equals `Ncount T (2*T)` for T>=0.
RH/ActualZeroSpectralWindows.lean specializes the genuine L2 and absolute
spectral windows; RH/ActualMarkedRationalWindows.lean specializes the original
rational form and its literal normalized window mass.

Analysis/MarkedContinuousTail.lean partitions the actual frequency integral into
disjoint half-open unit windows, proves absolute tail integrability and proves
`two_sided_tail_integrable_and_le`: tail <= `4*C/(pi^2*B)` for B>=1.
RH/ActualMarkedRationalTail.lean consumes the actual finite-copy window bounds.
`normalizedRationalForm_absolute_tail_integrable_and_le` is unconditional for
each finite shell, with exact bound `24*Q/(c0*M*pi^2*B)`, where Q is the actual
square occupancy at `scale*gamma/sqrt(2)`, M is the full copy count, and
`c0=exp(-1/8)/sqrt(2*pi)`. Empty-shell division is totalized. The signed complex
tail is absolutely integrable and has the same norm bound.
`normalizedRationalForm_absolute_tail_le_of_squareBudget` gives the uniform
bound `24*C/(c0*pi^2*B)` from the explicit premise Q<=C*M, M>0, C>=0.

**Conditional research reduction and remaining providers.** The latter uniform
budget is Open as an actual Lean provider. It is the known unconditional
Tsang/Selberg/Fujii microscopic second-moment input, not an RH-equivalent new
conjecture. Primary paper sources: https://arxiv.org/abs/2010.10675, Theorem 2;
https://arxiv.org/abs/2503.15449, Propositions 1--2 and (5.4)--(5.6).
Ordinary unit-height O(log T) zero counting does not discharge it.
Bounded-frequency signed marked cancellation, the cofinal arithmetic
O(log N) estimate and signed inverse saturation remain unproved.
The scope ledger `RH/PrimePhasesFormalizationScope20261004.md` distinguishes
all established identities, consumers, classical formalization gaps and the
RH-equivalent targets.

### Full integer-frequency phase covariance and conditional Gram assembly (2026-10-04)

Source: user-provided `Prime_Phases_Agenda_Proof_Attempts.tex`, Theorem
`growing-phase-gram`. The original quadratic-pairing statements below now
have a checked Euclidean arithmetic operator realization in
PrimePowerCovarianceEuclideanNorm.lean, with log(d)-2 <= norm <=
log(d)+log(4)+4 for d>=1. Identifying the complete analytic main term of the
actual zero-phase sample still requires the uniform Landau provider.
Unless otherwise specified, declaration names have namespace
`RiemannResearch.Fourier`.

**Established actual arithmetic covariance.** All frequencies in
`Finset.Ioc 0 N` are retained, including every composite integer frequency.
`Analysis/PrimePowerCovarianceRowBudget.lean` defines the genuine directed
prime-power covariance and proves:

- `sum_primePowerCovarianceDirectedEntry_eq`: its complete row is exactly
  `sum_(q<=N/n) Lambda(q)/q + sum_(q|n) Lambda(q)`.
- `primePowerCovarianceRowBudget_eq`: the divisor part is exactly `log n`.
- `primePowerCovarianceRowBudget_le`: for `1<=n<=N`, the full row is at most
  `log N + log 4 + 4`. Its provider is the already-proved unconditional
  `Mertens.E₁Λ.le` in `RH/WeilExplicitFormula/FromPNTPlus/Mertens.lean`;
  no PNT, RH, zero-density, or phase-cancellation assumption is supplied.

`Analysis/FiniteWeightedSchurPairing.lean` proves
`finiteGramErrorPairing_norm_le_weighted_schur` from positive weights,
symmetric absolute entries, and the explicit weighted-row bound.
`Analysis/PrimePowerCovarianceConjugation.lean` supplies these hypotheses
for the actual arithmetic kernel. Its theorems
`primePowerCovarianceDirectedEntry_balance`,
`primePowerCovarianceSymmetricEntry_mul_weight`,
`primePowerCovarianceSymmetricEntry_symm`, and
`primePowerCovarianceSymmetricEntry_weighted_row` prove the square-root
conjugation and the complete row identity exactly.
`primePowerCovarianceSymmetricEntry_eq_of_lt_of_dvd` identifies an integer
ratio `q=m/n>1` with `Lambda(q)/sqrt(q)`; the diagonal is zero and
nondivisible pairs have zero entries. Thus the main covariance is the
manuscript's exact signed matrix, including every prime-power resonance.

`primePowerCovariance_normalized_pairing_bound` proves

    |a* C_N a| <= [(log N + log 4 + 4)/(2*pi)] sum_(n<=N) |a_n|^2,

where `C_N` has the exact negative coefficient `-1/(2*pi)`.
This is an actual arithmetic specialization, rather than a theorem assuming
the desired covariance bound.

**Established consumer with an explicit analytic premise.**
`Analysis/GrowingPhaseCovarianceAssembly.lean` defines the exact complex
`primePowerCovarianceSignedEntry`. Its theorem
`fullIntegerGramErrorPairing_bound_of_entrywise_remainder` assumes only the
entrywise analytic provider

    |G(n,m) - delta_(n,m) - t*C_N(n,m)| <= eta
    for every n,m in Ioc 0 N, with eta : NNReal,

and proves

    |a* (G-I) a|
      <= [N*eta + |t|*(log N + log 4 + 4)/(2*pi)] sum_(n<=N) |a_n|^2.

The coefficient `t` is a real parameter; the theorem does not identify it
with `T/N(T)` or identify `G` with the actual zero-phase Gram. All arithmetic
covariance obligations are discharged. The actual uniform rational-character
Landau/Ford–Meng–Zaharescu remainder is still a missing formalization provider.
Consequently the unconditional actual-zero assertion at growing support
`X=(log T)^(2-epsilon)` is not claimed as proved by this consumer.

**Established Fourier and measure-class reductions; actual sampling premises remain.**
The earlier verified `GrowingFourierGramBounds.lean` gives the exact
Wiener-square and cardinality losses in
`finiteGramErrorPairing_norm_le_wiener_sq` and
`finiteGramErrorPairing_norm_le_card_l2`.
`finite_fourier_error_le_wiener_budget` transfers an assumed uniform character
bound to a finite Fourier polynomial with its precise Wiener budget.

`DistinctPhaseMeasureClass.lean` proves the finite normalized sampling
inequalities from `sum H(gamma)^2 <= C*sum H(gamma)` and `H(gamma)>=1`.
`MeasureTheory.Measure.mutual_absoluteContinuity_of_set_sandwich` proves the
actual Mathlib relations `(ν ≪ μ) ∧ (μ ≪ ν)` from upper and quadratic
lower Borel-set domination. `ContinuousSamplingMeasureClass.lean` closes
regular approximation and the passage through continuous-test weak limits:
`MeasureTheory.Measure.mutual_absoluteContinuity_of_weak_test_limits` applies
to finite regular Borel measures with a finite domination constant on the stated
Hausdorff space with closed-set outer approximation. Its conclusion is a common measure class, not equality
of measures.

Still required for the distinct-ordinate/Haar specialization: construction
and identification of the two actual empirical measures, the actual
multiplicity-weighted Haar convergence provider, the uniform ordinate-cluster
square budget, and the corresponding subsequential weak-limit identification.
The square-budget statement is a known unconditional paper-level consequence
of Selberg/Fujii mean-square bounds, not a new arithmetic conjecture; no actual
Lean provider was found in this audit. None of these inputs is discharged
merely by the generic measure-class theorem.

The proved logarithmic estimate concerns the phase-covariance matrix,
not the fully screened legal-residue inverse Gram. The decisive cofinal
arithmetic O(log N) bound for that different matrix and signed inverse
saturation remain unresolved. The proposed stronger support
`X=exp(o(sqrt(log T)))` is recorded in
`RH/UnverifiedHorizontalBootstrapRoute20261004.md` as an unverified research
route. It is not a Lean theorem or an established provider.

### Complete inverse defects and actual physical-dual support transfer (2026-10-04)

**Established physical Hilbert identities and support approximation.**
Source: user-provided `Prime_Phases_Agenda_Proof_Attempts.tex`, section
"Full inverse bounds and an exact controlled-transfer test". Stage `n`
contains every legal conductor `2,...,n+1`, including every composite.

RH/ParetoPhysicalDualTransfer.lean proves the quadratic equality
`physicalInverseDefect_eq_residual_sq`, its nonnegativity, and the corresponding
`physicalPrefixInverseDefect_eq_residual_sq` for a small principal block taken
AFTER the full stage inverse. Thus the physical-dual Gram dominates the actual
full inverse Gram. `residueInverseEntry_diagonal_nonneg` and
`residueInverseEntry_diagonal_le_physical` give unconditional diagonal bounds.
`physicalPrefixInverseDefect_support_transfer` is the exact reverse-norm
sandwich; `physicalPrefixInverseDefect_finite_certificate` gives its finite
error certificate. `physicalSignedCharge_exact` retains the complete signed
coefficient charge and residual pairing before the Cauchy bound.

RH/ParetoDualSupportError.lean proves the elementary harmonic budget:
`A_K=H_(K+1)-1`, `0<=A_K<=K/2`, `A_K<=log(K+1)`, and
`supportErrorSq K <= (2*log(K+1)^2+1)/K` for `K>=1`.

RH/ParetoPhysicalDualProjection.lean constructs the ACTUAL orthogonal projection
onto `span(u_2,...,u_K)`, not an assumed approximation-provider structure.
Finite Möbius inversion proves its head coordinates, and finite support proves
its zero tail. `physicalDualProjection_explicit` identifies it with the
manuscript's anchored vector `q_K(n)=1-A_K*n/(K-A_K)` for `1<=n<=K`.
`physicalDualProjectionResidual_norm_sq` proves the complete squared error
`A_K^2/(K-A_K)+1/(K+1)` exactly. The support error is therefore a proved physical
Hilbert quantity. RH/ParetoPhysicalDualCoefficients.lean defines actual dual coefficients by
inner products and proves their finite-inner, floor, multiples, and closed
harmonic-multiples formulas. The latter is exactly the manuscript formula for
every conductor, including every composite, and feeds the moving criterion.

RH/ParetoPhysicalDualSupportLimit.lean proves the actual support error tends
to zero. RH/ParetoPhysicalDualSupportRate.lean gives the explicit eventual
bound `||1-q_K|| <= 2*log(K+1)/sqrt(K)` and its `IsBigO` declaration.

**Exact closure criterion and conditional RH consumer.**
RH/ParetoPhysicalDualSequenceCriterion.lean proves
`physicalDualProjection_inverse_criterion`: along EVERY support sequence
`k_j->infinity` with full stages `n_j>=k_j`, the actual complete principal
inverse defect tends to zero if and only if `hilbertOne` belongs to the closed
legal residue span. The support-error provider is discharged by the preceding
modules. `riemannHypothesis_of_physicalDualProjection_inverse_defect` concludes
Mathlib's actual `RiemannHypothesis` from the remaining vanishing-defect input.

Open: a proved provider making that moving complete inverse defect tend to
zero, or making the corresponding signed charge saturate. Positivity and
boundedness of the inverse defect do not discharge this obligation.

Formalization gap: the published RH-to-legal-density direction of the
Nyman--Beurling/Baez-Duarte theorem is not proved in the current project.
The new unconditional equivalence is therefore to CLOSED-SPAN MEMBERSHIP;
the RH implication is checked in the sufficient direction. An unconditional
Lean `RH iff vanishing defect` claim additionally requires the classical
RH-to-density provider. This gap is a missing formalization of a classical
theorem, not a newly proposed arithmetic assumption or an unconditional RH
proof. See RH/MellinDeficitRHTest.lean and
RH/BaezDuarteNaturalApproximation.lean for the existing explicit boundary.

### Inverse conditioning, prime-only budgets, Fourier measure classes and zero kernels (2026-10-04)

**Established finite estimates and actual zeta convergence.**
RH/ParetoInversePolynomial.lean proves
`completeResidue_inverse_quadratic_bound`: the ACTUAL complete inverse
quadratic form is at most `4*R^2*H_R^2*sum(a_i^2)`, with `R=n+1`.
Its subdictionary and composite-only corollaries retain the complete dictionary
bound. The exact `normalizedDifference_energy_completion` preserves every
interior square and the terminal boundary. RH/ParetoInverseMobiusHarmonic.lean
sharpens all three bounds to `4*R^2*M_R^2*sum(a_i^2)`, where
`M_R=sum_(1<=q<=R) abs(mu(q))/q <= H_R`; this removes no conductors. This is an explicit Euclidean quadratic-form statement, not the default
Pi/sup-norm operator norm.

Analysis/SignedIncidenceEnergy.lean preserves the exact finite signed energy
and every diagonal/off-diagonal term. RH/PrimeOnlyDyadicEnergy.lean applies it
to actual finite von Mangoldt and prime-only sums, retaining the square-root
prime-power correction. Analysis/FixedEnergyPerturbation.lean proves the
norm perturbation estimates. RH/ActualPrimePowerErrorSummability.lean consumes the existing unconditional
MediumPNT theorem and the pinned Mathlib Costa-Pereira inequalities.
RH/ActualPrimePowerParetoEnergy.lean proves the actual square-root compensated
prime-power error is Pareto-square-summable. RH/PrimeOnlyArithmeticBridge.lean
identifies these exact Chebyshev providers with the finite psi/theta sums.
RH/PrimeOnlyDyadicErrorBudget.lean proves the exact paired factor 1/2,
the uniform dyadic difference budget 3E, both-direction finite energy comparison,
and the sharper signed difference bound
`abs(E_psi-E_prime)<=2*sqrt(3*E*E_prime)+3*E`.
The decisive cofinal arithmetic energy bound is not inferred.

RH/ActualIntegratedZeroSeries.lean proves `absolutely_summable` for the ACTUAL
multiplicity-weighted kernel
`-m(rho)*exp(rho*log x)*(1-exp(-rho*log 2))/rho^2`, for `x>=1`.
It uses the existing unconditional zeta seam and proved reciprocal-square
zero summability. Analysis/IntegratedZeroSeriesBounds.lean supplies the generic
absolute-majorant truncation inequality.
RH/IntegratedZeroScalarTail.lean proves a logarithmic reciprocal-square
telescope, retaining its terminal term.
RH/ActualIntegratedZeroTruncation.lean applies the ACTUAL proved local zero
count with multiplicities and both signs of the ordinate: the weight tail is
at most `32*A0*log(K+3)/K`, and the integrated kernel tail is at most
`192*A0*x*log(K+3)/K`, for `K>=5`, `x>=1`.
RH/ActualIntegratedZeroRealTruncation.lean gives the literal real-height
bound `768*A0*x*log(Y)/Y` for `Y>=10`, plus its IsBigO declaration. Both boundary endpoints belong to the finite
head; the exact complete-minus-head remainder is proved before its norm bound.
A0 is the proved unit-window count constant; no numerical decimal A0 is claimed.
Analysis/DilogarithmSeries.lean, RH/TrivialZeroLogIntegral.lean and
RH/IntegratedTrivialZeroTerm.lean now prove the exact trivial-zero/dilogarithm
evaluation and its logarithmic integral, retaining both endpoints.
`correction_eq_log_integral` identifies the actual correction with the dyadic
logarithmic integral, and `correction_isBigO` proves its O(x^-2) decay.
Open: the arithmetic logarithmic Perron/integrated explicit-formula identity
joining the convergent zero sum and correction to the Chebyshev error.

**Conditional analytic assembly; explicit providers remain Open.**
Analysis/GrowingFourierGramBounds.lean proves the finite Wiener and
support-cardinality/ell2 error estimates from the displayed uniform entry bound.
Analysis/DistinctPhaseMeasureClass.lean proves the finite weighted/distinct
sampling inequalities and the Borel set sandwich.
Analysis/ContinuousSamplingMeasureClass.lean passes the continuous-test
sandwich through weak limits on compact regular spaces and proves mutual
absolute continuity. Open for ACTUAL zeta phases: growing-support quantitative
Landau/Fourier cancellation and the bounded normalized multiplicity-square
cluster budget. No exact Haar equality is claimed for distinct sampling.

Analysis/MarkedFourierTail.lean proves the tent inverse-square envelope,
the symmetric positive-kernel quadratic row bound, the marked Cauchy bound,
and the finite tail with its retained endpoint remainder. The two-sided
infinite tail is at most `4*C/B` from a uniform window-mass provider.
The new original-kernel/window/integral assembly is described below.
Open for a bound uniform in actual shell height: the checked microscopic
ordinate-square provider. The generic scalar theorem cannot supply it. Bounded-frequency signed cancellation and the
cofinal `O(log N)` arithmetic bound/signed inverse saturation remain open.

### Unconditional prime pivots, raw-model obstruction and norm-saving transfer (2026-10-01)

**Established arithmetic and analytic results; coherent kernel checks passed.**
RH/ParetoPrimePivotCertificates.lean proves exact two-site source observations,
capacity and four-site inverse-pivot norm-square completions for the COMPLETE
tail dictionary, including older composite conductors. Formal Bertrand gives
prime_schur_inverse_le_ten_sq and prime_schurSigma_ge_tenth:
1/sigma_p <= 10*p^2 and sigma_p >= 1/(10*p^2), unconditionally.
prime_schur_inverse_le_capacity preserves the signed credit
4*p^2+2*C_<=p-4*C_<p. The physical dictionary is not truncated.

RH/ParetoPrimeRawChargeModels.lean proves primeRawCharge_energy_summable,
primeRawModelRow_energy_summable and primeRawModelAmplitude_square_summable
for Q/p^2 plus any fixed Hilbert-vector pairing, with the ACTUAL prime Schur
weights and arbitrary dyadic block tests. Exact mixed-square and source-shift
identities remain. coprimePrimeRawCharge_eq connects the genuine coprime-two
charge. primeMovingCRT_rawModel_error_summable_iff equates summability of the
complete discrepancy to summability of the actual amplitude because the raw
model is square summable. This raw family cannot provide model divergence.

Analysis/WeightedNormDefectTransfer.lean proves
actual_square_not_summable_of_cofinal_norm_defect: divergent model energy
and a fixed positive cofinal saving in PREFIX NORMS force actual energy
divergence. The full signed cross term is retained before the bound.
All five critical audits use only propext, Classical.choice and Quot.sound.

**Conditional research reduction; arithmetic providers remain Open.**
RH/ParetoMovingRemainderTransfer.riemannHypothesis_of_moving_norm_defect uses
the actual normalized signed CRT amplitude, including zero-energy cases.
Open: an independently defined divergent arithmetic model outside the raw
summable family; a positive cofinal prefix-norm saving for the COMPLETE signed
error with that model. Relative error energy may tend to one. Unbounded saving
in energies alone is insufficient. The earlier moving-Hilbert theorem's
representation, orthonormality, model divergence and variation inputs remain
Open as an alternative route.

RH/PrimePivotAndRawModelContinuation20261001.md records exact ordinary
arguments, precise formal status, primary-source comparisons and the next
arithmetic obligation. RH/PrimePivotAndRawModelDiagnostics20261001.md records
successful Wolfram full-tail and exact finite-support checks plus reproduction.
This supersedes the earlier conditional raw-charge pivot estimate below;
historical audit receipts remain intact. No unconditional RH proof or
mathematical priority claim is asserted.

### Moving-remainder verification and signed CRT transfer (2026-10-01)

**Established generic analysis; independent source and axiom checks passed.**
The pinned b306d93 audit recompiled both new files and their combined proof
bodies; all six foundation audits use only propext, Classical.choice and
Quot.sound. See RH/MovingRemaindersIndependentAudit20261001.md for receipts,
the complete assumption trace, zero-energy handling and Wolfram reproduction.
Analysis/MovingOrthogonalEnergy.lean proves maskedPairingVector_norm_le,
finite_masked_moving_bound, moving_pairing_prefix_bound and
moving_pairing_summable. Complete signed increments remain, with absolute
total variation and orthonormality explicit. Standard foundations only:
propext, Classical.choice and Quot.sound.

RH/ParetoMovingRemainderTransfer.lean defines primeMovingCRTAmplitude and proves
primeMovingCRTAmplitude_sq for the actual signed pairing and actual energy,
including zero denominators. No raw rows or proxy weights are substituted.

**Conditional research reduction.**
riemannHypothesis_of_moving_remainder_model assembles the generic summability
theorem and the existing exact CRT contrast contradiction. Open: a genuinely
square-nonsummable arithmetic model; an exact complete remainder representation;
orthonormal tests for that representation; summable total Hilbert variation.
The axiom audit does not establish these hypotheses.

**Ordinary deductions, not newly formalized arithmetic providers.**
RH/MovingRemaindersVerificationAndResearch20261001.md proves the stronger full
block/centered-energy consequence and corrects the prior agenda's paired-only
limitation. Under negated RH, the prime coefficient dual and canonical
interpolant give 1/sigma_p <= 4*p^2+4+2*C, hence the natural raw-charge
comparison has finite gap energy with the ACTUAL weights. An exact abstract
Hilbert countermodel has growing sources and finite screened energy.
RH/MovingRemaindersDiagnostics20261001.md supplies reproducible full-tail
digamma Gram, signed screening and exact countermodel computations.
The report reviews primary preprints and retains the complete inverse-Gram
provider as Open. No priority claim or unconditional RH proof is asserted.


### Failure agenda: Li witnesses and complete model-error transfer (2026-10-01)

**Established generic transfer and negated-RH consequence; candidate kernel checks passed.**
Analysis/WeightedScalarEnergy.lean adds model_square_completion, the exact
nonnegative square identity; model_square_summable and
actual_square_not_summable_of_model transfer divergence of a weighted model
through a summable bound on the COMPLETE signed discrepancy.
RH/LiFailureWitness.lean proves not_RH_exists_negative_li from the unconditional
LiCriterion.li_criterion_rh_iff. Taylor index n represents lambda_(n+1).
Their axiom audits contain only propext, Classical.choice and Quot.sound.

**Conditional research reductions; substantive providers remain Open.**
The new report RH/NotRHConditionsAndContradictionAgenda20261001.md separates
ordinary proofs from formal declarations. It records centered screened-model
transfer, moving-vector variation, DPP truncated maximum-hole moments,
directional inverse saturation, Mellin-window nonvanishing, exponential
negative Li subsequences, screw weighted-energy/cofinal positivity, confluent
Hilbert-kernel obstructions, complete Weil positivity, and Connes generator
approximation/error floors. These ordinary deductions do not supply RH.

Open: arithmetic model with divergent actual-weight signed gap energy together
with summable complete centered screening errors; exact moving-remainder
representation and bounded Hilbert variation; synchronized bounded DPP range
moment or bounded full inverse-direction deficit; vanishing unscaled actual
Mellin deficit on a fixed positive-measure window; one-sided subexponential
Li lower bound; complete arithmetic screw identification in Lean and
cofinal weighted-energy bounds or full-window positivity; locally uniform
arithmetic jet-Gram matching to the target kernel; cofinal full Weil lower
bounds including tails and mixed blocks; Connes simple-even generators at
the same cofinal scales plus projection-tail/spectral-excess approximation.
No priority claim or RH contradiction is asserted.

### Failure intersection: signed raw growth and screened survivor rigidity (2026-10-01)

**Established consequences of hypothetical zeros or negated RH; isolated kernel checks passed.**
RH/RHFalseRawCorrelationGrowth.lean proves the same-zero polynomial lower bounds
for the complete signed raw off-diagonal Gram sum, inverse-source quadratic form,
and exact-head residual energy. Both pair orientations, signs and physical tails
remain. RH/RHFalseScreenedSurvivorRigidity.lean proves harmonic-weighted actual
prime-survivor summability, uniform arbitrary-window bounds, exact prime-plus-
nonprime capacity and certificate-error accounting, and finite exceptional-row
bounds by the SAME canonical remaining error. RHFalseJointObstruction adds
not_RH_signed_growth_and_screened_rigidity with sole premise negated Mathlib RH,
combining the shared zero, raw/inverse growth, screened summability and normalized
residual-tail divergence.

**Ordinary mathematical deductions, not new kernel-verified analytic providers:**
the exact Euler-tail calculation with classical prime estimates strengthens
failure to sum_prime(log p)*s_p^2 finite, and sum_j 2^j*G_j^2 finite for the actual
pooled screened gap. It also yields the discrete height-sensitive zero floor
D >= (2 beta - 1)*|rho|^(2 beta - 3)/6, retaining the full tail and correlated
multi-zero Gram optimization. No priority claim is made.
See RH/NotRHSignedIntersection20261001.md for proofs and source applicability.

**Conditional research reductions. Open:** actual signed survivor/contrast
nonsummability, a subpower signed raw Gram upper bound, or another arithmetic
estimate incompatible with this conjunction. No contradiction, RH proof,
screening lower bound or unconditional capacity divergence is asserted.


### Exact adjacent-weight regression and screened odd-charge contrasts (2026-10-01)

**Unconditional finite identities and bounds; coherent kernel candidate passed.**
Analysis/WeightedScalarEnergy.lean adds zero-source regression completion and
regression_weight_remainder, retaining both change-of-weight squares.
RH/ParetoFirstSiteAdjacentRegression.lean proves the explicit full-tail
adjacent weight, harmonic<=adjacent<=actual Schur weights, the corresponding
centered-scatter hierarchy, complete adjacent-weight split tree, actual signed
moment formula and capacity_eq_adjacentPrimeSurvivor_budget.
Every physical residue remainder, comparison square, historical drift,
mean mismatch, initial capacity and nonprime gain remains.
harmonicPrimeBlockSourceFloor_le_adjacent_source and
adjacentPrimeSurvivorVariance_ge_floor_gap keep the NEW model's actual signed
pooled slopes; prime density supplies no gap lower bound.

RH/ParetoFirstSiteAdjacentContrasts.lean proves fixed-vector contrast-energy
summability for changing tests with these explicit weights; the complete signed
base cross term; moving/full-row equality after diagonal source cancellation;
and adjacentPrimeMovingCRTContrastPairing_eq_screened_charge.
The charge is the explicit odd reciprocal-square source, screened against
EVERY old inverse-Gram row, including composite moduli.

**Conditional research reductions. Open:** nonsummability of the actual new
adjacent survivor scatter or moving CRT contrast series. The explicit finite
provider in riemannHypothesis_of_adjacentMovingCRTContrast_unbounded requires
unbounded nonnegative certificate prefixes. No signed arithmetic provider,
capacity divergence or unconditional RH is established. The source-only
harmonic rate assembly is still ordinary mathematics.
See RH/ScreenedAdjacentRegression20261001.md for exact formulas, the remaining
original G_j inequality, primary-source applicability and verification scope.

### Adjacent harmonic bounds for actual Schur gains (2026-09-30)

**Formalized finite certificates; isolated kernel checks passed.**
RH/ParetoAdjacentSchurBound.lean connects the existing complete adjacent raw
residue energy to the actual finite inverse-Gram completion. For conductor
q=n+3, v=t_q-((q-1)/q)t_(q-1) equals a scaled adjacentMomentPacket. Its exact
whole-tail norm is [H_(q-1)-(q-1)/q+adjacentResidueRemainder(q-1)]/q^2.
The literal infinite remainder is nonnegative and at most (q-1)/q.
Hence sigma_q<=H_(q-1)/q^2, eta_q=-<v,tailMinimum>, and
actual gain_q>=q^2*eta_q^2/H_(q-1), at both prime and nonprime conductors.
adjacentInnovationLower_sum_le_capacity retains the initial capacity and
all actual gain contributions. factorialPrimeSourceEnergy_ge_adjacent_harmonic
gives the pointwise lower 1/(4*H_(q-1)); it concerns the positive source,
not reciprocal-prime energy nonsummability or actual signed gain divergence.

**Conditional research reduction. Open:** a positive lower bound for enough
actual dyadic moments sum q^2*eta_q^2, or another divergent weighted moment.
The paper PNT/Burnol assembly improves U_N's lower scale to linear order and
C/U to O(log N/N); those analytic providers remain unformalized.
RH/AdjacentSchurResearch20260930.md records the exact proof, finite numerical
screening, open moment estimate, and exclusions from the source audit.
No RH or mathematical-priority claim is made.

### Vanishing slope, two gain channels and balanced nonprime trials (2026-09-30)

**Formalized conditional research reductions; isolated kernel checks passed.**
Analysis/VanishingRegressionSlope.lean proves the fixed finite-head implication
from bounded centered-prefix energy and slopes tending to zero to bounded
uncentered prefixes and summability. RH/ParetoFirstSiteAngularTwoChannels.lean
uses the actual survivor slope tau=(U+X)/U and retains the full centered square.
Under tau->0, Summable Gamma iff Summable factorialPrimeGain, their finite
totals agree, and R_N<=sum' Gamma-sum_(n<N) Gamma. Both gain series summable
give C_(N+1)<=C_1+sum' Gamma+sum' factorialCompositeGain. The separate
mean-channel alternative is consequently redundant under tau->0.

**Analytic inputs explicit.** C_(N+1)/U_N->0 implies tau->0 and the resulting
two-channel capacity equivalence. RH_iff_two_gain_channels_of_sublinear_source
also retains hBaezDuarte. Burnol/PNT give the source-scale premise classically
as detailed in RH/FirstSiteTwoChannels20260930.md; their complete analytic
rate assembly is not supplied as a Lean theorem or installed as an axiom.

RH/ParetoBalancedSchurTrial.lean retains the entire norm completion for a
balanced old-row direction v=t_new-a*t_old. The exact reciprocal constraint
gives eta=-<v,tailMinimum>, and sigma<=||v||^2 only after its projection
remainder is retained. A positive trial-norm upper bound K yields the actual
lower certificate <v,tailMinimum>^2/K<=eta^2/sigma, including composite gains.
The paper doubling application has v_p=t_(2p)-(1/2)t_p=(1/p)D_p g_2 and
||v_p||^2=log(2)/(4p). Its specialized Lean norm and prime-subset series
transfer are still pending. No arithmetic divergence is asserted.

**Open:** a divergent signed lower energy for the full prime block scatter,
or the actual nonprime bucket pairings, or the repository's complete
reciprocal Abel charge lower bound. The note records primary-source
applicability, exploratory full-tail numerics through N=256, and six
sequenced research stages. Verification timeouts without diagnostics are
recorded separately from the mathematical proofs.

### Source floors, complete split trees and moving CRT contrast transfer (2026-10-01)

**Established without RH.** Analysis/WeightedScalarEnergy.lean proves
reduced_weight_mono and the exact zero-denominator signed determinant form.
RH/ParetoFirstSitePrimeBlockContrast.lean generalizes primeBlockVariance_split
and its angular consequences to empty-source children.

RH/ParetoFirstSitePrimeMultiscale.lean proves
primeBlockVariance_eq_dyadicSplitBudget, capacity_eq_dyadicSplitBudget,
primeAngularInnovation_summable_iff_dyadicSplitBudget and the full four-channel
alternative. Every internal binary split, historical drift, mean mismatch,
initial capacity and nonprime gain is retained.

RH/ParetoFirstSitePrimeSourceFloors.lean proves reciprocalPrimeSourceFloor_le,
reciprocalPrimeBlockSourceFloor_le, the finite prime-count bridge and both
dyadicSplitSourceFloor source comparisons. The harmonic reduced floor keeps
unequal child mass and gives reciprocalPrimeSplitEnergy_le_variance.
The newer adjacent-conductor source bound also gives harmonicPrimeSourceFloor_le,
harmonicPrimeBlockSourceFloor_ge_count and a stronger harmonic split energy.
reciprocalPrimeSplitEnergy_le_harmonic proves pointwise domination with the
same actual screened slope gap. No asymptotic PNT/Dusart rate is assumed.
The harmonic endpoint retains its explicit actual-energy nonsummability hypothesis.

Analysis/DyadicWeightedContrast.lean proves exact dyadic grouping and finite
weighted-energy transfer. RH/ParetoFirstSitePrimeContrastPerturbations.lean
proves primeBlockFixedPairingCertificate_dyadic_summable for arbitrary varying
tests, primeBlockAdjustedContrastCertificate_dyadic_summable_iff,
primeBlockContrast_finite_columns_dyadic_summable_iff, and
primeBlockMovingCRTContrastCertificate_dyadic_summable_iff.
The exact primeBlockContrastCertificate_eq_movingCRT_split retains the signed
base cross term; only the summability question permits base removal.
primeBlockContrast_row_perturbation_dyadic_summable_iff explicitly requires
the signed correction's weighted square summability.

**Conditional research reductions. Open:** nonsummability of the actual
complete tree budget, reciprocal-prime weighted screened split energies, or
moving CRT contrast certificates. The corresponding endpoints are
riemannHypothesis_of_dyadicSplitBudget_not_summable,
riemannHypothesis_of_reciprocalPrimeSplitEnergy_not_summable,
riemannHypothesis_of_harmonicPrimeSplitEnergy_not_summable and
riemannHypothesis_of_movingCRTContrast_not_summable.
No actual screened-gap or moving-row growth provider is established.

**Ordinary mathematical consequence, not a new Lean import:** Dusart's
unconditional prime-count bounds give both child source floors at least
1/[80(j+3)log 2] for j>=17, reducing a sufficient provider to divergence of
the actual screened slope-gap squares divided by j+3. The existing pi_alt'
PNT declaration has standard axioms. Combining the newer harmonic floor
with the same ordinary count proof strengthens the sufficient gap-series
weight to 2^j/(j+3)^2. Interval-rate formalization and actual divergence
remain separate obligations.
See RH/FirstSiteMultiscaleSourceAudit20261001.md for the reproduced audit,
full proofs, primary literature screening and concrete research sequence.



### Source-balanced full-angular block contrasts (2026-09-30)

**Established without RH.** RH/ParetoFirstSitePrimeBlockContrast.lean proves
primeAngularBlock_eq_contrast_remainder_drift: an arbitrary automatically
source-balanced finite test supplies Q=L^2/D, with exact equality
sum Gamma=Q+contrastRemainder+historicalMeanDrift. The full screened CRT row
and every Schur/factorial weight remain in L; its survivor formula cancels
the aligned source exactly. primeBlockContrastCertificate_le_angular is the
all-row lower certificate, and primeBlockContrastCertificate_eq_variance_at_error
proves sharpness without growth. capacity_eq_dyadic_prime_contrast_budget
retains C_1, R, every contrast remainder, historical drift and nonprime gain.
primeBlockVariance_split retains both child scatters and pooled mean
separation. primeAngularBlock_ge_split_gap proves the finite bound
sum Gamma >= (v/2)*(x_R/u_R-x_L/u_L)^2 when 0<=v<=u_L,u_R, also at v=0.
Analysis/WeightedScalarEnergy.lean supplies exact balanced_contrast_completion,
centered_product_zero and signed finite product_sub_right.

**Conditional research reductions. Open:** nonsummability of the actual
dyadic contrast energies, or explicit lower source and pooled signed-gap
bounds with nonsummable (v_j/2)*d_j^2. These are the hypotheses of
riemannHypothesis_of_dyadic_prime_contrast and
riemannHypothesis_of_dyadic_split_gap. No positive divergent arithmetic
lower sequence or unconditional capacity divergence is supplied. E
nonsummability is not pursued; Burnol/PNT rates are not imported here.
See RH/FirstSitePrimeBlockContrast20260930.md.

### Exact weighted prime-block variance and pair certificates (2026-09-30)

**Established without RH.** RH/ParetoFirstSitePrimeBlocks.lean proves
primeAngularBlock_eq_variance_add_drift: the complete sum of Gamma on
[N,N+k), N>0, equals its internal weighted variance S plus the exact
head--block mean drift H. This retains the full Schur/factorial weights and
signed screened errors, including at empty block source. The ordered-pair
formula primeBlockVariance_eq_pair and the concrete lower bound
primeBlockVariance_ge_two_rows give a fully weighted two-row certificate
B(a,b)<=S<=sum Gamma. primeBlockVariance_eq_survivor_scatter cancels the
aligned negative source exactly, exposing the actual Schur survivor scatter.

primeAngularInnovation_summable_iff_dyadic_blocks is the exact equivalence
Summable Gamma iff Summable S_j and Summable H_j on [2^j,2^(j+1)).
capacity_eq_dyadic_prime_block_budget retains C_1, R, both block sums and
all nonprime gains. tailCapacity_tendsto_iff_dyadic_prime_block_channels
keeps all four channel alternatives; scatter divergence alone is not
asserted necessary. Analysis/WeightedScalarEnergy.lean supplies the exact
two-budget merge and two-row regression completion with their square
remainders.

**Conditional research reductions. Open:** nonsummability of actual
dyadic block scatter, or a nonsummable nonnegative lower sequence b_j<=S_j.
riemannHypothesis_of_dyadic_prime_pair_separation reduces a sufficient
provider to nonsummability of the complete two-row determinant energies
for explicitly distinct rows in [2^(j+1),2^(j+2)). No lower-series growth
provider is established. These use full Gamma weights, not the coarse
reciprocal-prime E target. See RH/FirstSitePrimeBlockVariance20260930.md
for the preceding three-series audit, exact identities and remaining task.

### Kolmogorov truncation of the exact angular variance (2026-09-30)

**Established without RH.** Analysis/NonnegativeSeriesTruncation.lean proves
clipped_eq_large_add_small, summable_clipped_iff,
summable_iff_tail_indicator_and_truncated_energy, and
not_summable_iff_clipped_prefix_unbounded for nonnegative real energies at
every fixed positive cutoff. RH/ParetoFirstSitePrimeThreeSeries.lean proves
primeAngularInnovation_summable_iff_three_series and
primeAngularInnovation_not_summable_iff_clipped_unbounded.
tailCapacity_tendsto_iff_prime_clipped_angular_channels retains the mean
channel and the complete nonprime gain series.

**Conditional research reduction. Open:** unbounded prefixes of
sum min(Gamma_n,1), supplied explicitly to
riemannHypothesis_of_clipped_prime_angular_unbounded. This is equivalent to
the existing angular nonsummability provider, not a proof of the provider.
The full weakest inequality remains unbounded R_N+sum Gamma_n+J_N.

**Classical interpretation, not kernel-formalized probability here:**
independent auxiliary fair signs times the complete signed angular
amplitudes give Var(M_N)=W_N. Kolmogorov three-series says this series
converges a.s. exactly when Gamma is summable. Arithmetic row independence
is not assumed or proved. Summability concerns increments Gamma, not
cumulative W_N or raw V_N. See
RH/FirstSiteKolmogorovThreeSeries20260930.md for the exact truncation,
rare-spike caveat, and the still-open screened prime-block lower bound.

### RH consequences and the monotone prime angular channel (2026-09-30)

**Established without RH.** RH/ParetoFirstSitePrimeAngular.lean proves
primeCancellationVariance_succ and primeCancellationVariance_eq_sum:
W_(n+1)=W_n+Gamma_n, where
Gamma_n=w_n*(U_n*kappa_n-X_n*delta_n)^2/[U_n*(U_n+w_n*delta_n^2)].
primeCancellationVariance_monotone and capacity_eq_prime_angular_budget
give C_(N+1)=C_1+R_N+sum_(n<N) Gamma_n+J_N.
primeMeanMismatchBudget_step preserves the complete mean/angular/gain balance.
The existing actual Schur source lower bound proves
primeRelativeAngularEnergy_le: E_n<=16*Gamma_n, where E_n is
(kappa_n/delta_n-X_n/U_n)^2/(n+3) at positive prime stages and zero otherwise.
primeRelativeAngularEnergy_eq_screened_rows retains every signed screened
CRT entry, the fixed base pairing, and the historical running slope.
Analysis/WeightedScalarEnergy.lean adds exact regression completion,
centered_energy_update, and the reduced-weight lower bound.

tailCapacity_tendsto_iff_prime_angular_channels is the exact alternative:
capacity divergence iff R_n does not tend to zero, or Gamma is not summable,
or the complete nonprime gain is not summable. No individual channel is
asserted necessary by itself. Failure of RH forces Gamma and E to be summable.

**Conditional research reductions. Open:** nonsummability of the actual
full weighted angular energy Gamma supplies capacity divergence and the
existing RH endpoint. The weakest exact inequality remains
forall B exists N>=1, R_N+sum_(n<N) Gamma_n+J_N>B.
RH/ParetoFirstSiteRHConsequences.lean connects this to RH while explicitly
retaining hBaezDuarte : RH -> NaturalApproximation. The analytic provider is
a classical published theorem, but is not yet Lean-provided.
primeSignedBudget_ratio_tendsto_of_capacity_sublinear_source proves
C_(N+1)/U_N -> 0 implies A_N/U_N -> -1, with that rate hypothesis explicit.

**Classical scale deduction, not kernel-verified here:** Burnol's lower bound,
the exact centered norm transfer, and dyadic denominator enlargement give
C_N=O(log N); PNT with the exact factorial Euler product gives
U_N>=(1/4-o(1))*(log N)^2. Consequently the fixed-fraction A-saving and
V-saving hypotheses from ParetoFirstSitePrimeBudget are incompatible with
these classical growth scales. Their conditional Lean implications remain
valid; these hypotheses are not suitable arithmetic targets.
The sharper fresh-prime weight gives E_n << Gamma_n/(log(n+3))^2.
Since W_N=sum Gamma_n<=C_(N+1)=O(log N), summation by parts proves that
E is summable classically without RH. This rate deduction is not yet
kernel-imported; the conditional E-nonsummability endpoints remain valid
but their hypotheses are not suitable arithmetic targets. The actual Gamma
nonsummability provider remains Open. See
RH/FirstSiteRHAngularContinuation20260930.md and
RH/FirstSiteKolmogorovThreeSeries20260930.md for the deductions,
verification distinctions, and the remaining full angular inequality.

### First-site prime alignment and fluctuation-scale providers (2026-09-30)

**Established without RH.** RH/ParetoFirstSitePrimeAlignment.lean proves
capacity_eq_prime_alignment_budget:
C_(N+1)=C_1+R_N+W_N+J_N, where R_N=(U_N+X_N)^2/U_N and W_N is the
complete centered signed-error square. primeCancellationVariance_eq_pair_budget
identifies W_N as the full ordered-pair determinant sum divided by 2U_N.
Every prime correlation, actual Schur pivot, physical tail, nonprime gain,
and initial capacity term is retained.
Analysis/WeightedScalarEnergy.lean proves exact finite square completion,
the weighted Lagrange identity, and normalized_product_tendsto_zero by a
finite-head/tail argument.
Bounded capacity forces R_N -> 0 and (V_N-U_N)^2/U_N -> 0, formalized by
primeMeanMismatchBudget_tendsto_of_capacity_bounded and
primeErrorMismatchBudget_tendsto_of_capacity_bounded.
primeErrorMismatchBudget_completion retains the full extra square before
the subsequent comparison drops it.
prime_source_add_cross_eq_screened_rows records the exact signed CRT pairing.

**Conditional research reductions. Open:** a cofinal R_N >= epsilon>0, or
(V_N-U_N)^2/U_N >= epsilon>0, supplies the first-site capacity provider.
The weaker square-root saving V_N <= U_N-c*sqrt(U_N)+K, for fixed c>0
and finite real K, also suffices via
tailCapacity_tendsto_of_prime_error_sqrt_gap_additive and its RH endpoint.
None of these arithmetic providers is established. Nonvanishing R_N is
sufficient, not asserted equivalent to RH. The weakest exact remaining
condition is unbounded R_N+W_N+J_N, by
tailCapacity_tendsto_iff_prime_alignment_unbounded.
The imported large-sieve upper bounds still lack a verified signed transfer
through adaptive inverse-Gram screening. See RH/FirstSitePrimeAlignment20260930.md.


### First-site capacity and signed prime budgets (2026-09-30)

**Established without RH.** RH/ParetoFirstSitePrimeBudget.lean proves
capacity_eq_prime_signed_budget:
C_(N+1)=C_1+U_N+V_N+2X_N+J_N.
U_N is the already divergent factorial fresh-prime source energy, V_N is
the full signed-error square energy, X_N is the signed mixed pairing,
and J_N retains every nonprime Schur increment. All physical tails and
old-block Gram correlations remain in the underlying vectors.
primeSourceBudget_young_completion retains the exact nonnegative square:
U_N+R_N(t)=(1+t)G_N+(1+1/t)V_N for every t>0.
primeSignedBudget_ratio_tendsto_of_capacity_bounded proves that bounded
capacity forces (V_N+2X_N+J_N)/U_N -> -1; no converse is asserted.
tailCapacity_tendsto_iff_prime_budget_unbounded identifies the exact
unbounded combined-signed-budget provider.

**Conditional research reductions:** a cofinal estimate
V_N+2X_N+J_N >= -theta*U_N-K for fixed theta<1 and finite K.
tailCapacity_tendsto_of_prime_signed_fraction then proves C_n -> +infinity;
riemannHypothesis_of_prime_signed_fraction gives the existing RH endpoint.
Alternatively a cofinal V_N <= theta*U_N+K with 0<=theta<1 suffices,
by tailCapacity_tendsto_of_prime_error_strict_fraction. Neither arithmetic
provider is established in Lean. The classical scale comparison in the new
RH angular continuation rules out these fixed-fraction hypotheses; the
conditional implications remain valid. The weakest exact remaining condition is
forall B exists N, B<U_N+V_N+2X_N+J_N.
See RH/FirstSitePrimeBudget20260930.md.

### Finite-rank offsite vacancy control (2026-09-30)

**Established without RH.** RH/IntegerDPPOffsiteTrialBounds.lean proves
offsiteWeightedVacancyCutoff_eq_gram_trace:
O_(N,M)+1/(M+2)=1/2-tr(D_off B_off G_N^(-1) B_off^T).
The Gram matrix is complete; every mixed entry and physical tail is retained.
weightedVacancyTerm_eq_fullGram_trial and
weightedVacancyTerm_eq_dilation_energy record the signed energies and the
full nonnegative trial-to-projection square before estimates are taken.
Analysis/ProjectionTrialEnergy.lean provides the underlying general identity.

Reusing the existing PointTargetDilationSynthesis and finite dilation
membership, offsiteWeightedVacancyPrefix_le_rank_trial_budget gives
O_(N,M) <= A_M(q^(K+1)+a_(K+1)*sqrt(Delta_n))^2 whenever
N+1 >= (M+2)*2^K*(n+1), where q=1/sqrt(2),
a_(K+1)=(1-q^(K+1))/(1-q),
A_M=sum_(j=2)^(M+1)(1/sqrt(j)+1/sqrt(j+1))^2,
and Delta_n=E/(S^2+2E)-finiteTrialVacancySlack n c=vacancy n/2.
weightedVacancyCutoff_le_rank_trial_budget adds Delta_n and the exact
1/(M+2) physical tail. Assumptions are finite rank enlargement and E>0.
offsiteDilationFactor_le_reciprocal_sum supplies the harmonic upper bound.
No new dilation operator or duplicate geometric synthesis is introduced.

**Conditional research reduction. Open:** arbitrarily small Delta_n,
equivalently the existing unbounded-capacity/large finite-trial-ratio provider.
Once provided, the new bound controls all offsite terms after explicit
conductor enlargement. No rate or uniform Gram inverse bound is required
for existential cutoff certificates. Same-rank vanishing is not asserted.
See RH/DPPOffsiteRankTrialBounds20260930.md.

### Old DPP certificates and weighted cutoff bridge (2026-09-30)

**Established without RH.** `RH/IntegerDPPCertificateCutoffBridge.lean`
proves `weightedVacancyCutoffCertificates_iff_finiteTrial_certificates`
and `weightedVacancyCutoffCertificates_iff_no_tailCertificate`.
The old large-ratio finite trial provider and the new cutoff provider are
equivalent; genuine infinite dual certificates instead obstruct both.
`weightedVacancyCutoff_eq_trial_split` retains the full Gram trial energy,
the nonnegative square slack, every offsite term, and the physical tail
allowance. `weightedVacancyCutoff_lt_iff_trial_budget` gives the exact
necessary-and-sufficient budget for an individual trial.
`finiteTailCertificate_weightedVacancyCutoff_exact` retains the finite
observation certificate's energy-completion square.
`tailCertificate_weightedVacancyCutoff_lower` gives
`C(N,q) >= 1/(||z||^2+2) + 1/(q+1)` for positive physical cutoff q.
`weightedVacancyCutoff_eq_canonical_split` retains the finite-to-closed
projection square in the obstruction case.
The damped window minimum and infinite prefix benchmark equality are
equivalent to the cutoff provider; a dual certificate gives the quantitative
lower bound `p_*/(||z||^2+2) <= dampedPrefixLimit-p_*`.

**Conditional research reduction. Open:** construct arbitrarily large
source-to-full-energy ratios, equivalently arbitrarily small cutoffs, or
exclude all genuine infinite dual certificates. A single finite trial
controls only the first site until its offsite budget is controlled.
Damped minimum equality does not discharge this provider.
See `RH/DPPCertificateCutoffComparison20260930.md`.

### Pareto DPP vacancy cutoffs and quantitative determinant separation (2026-09-30)

**Established without RH.** `RH/IntegerDPPWeightedVacancy.lean` proves
`finiteWeightedVacancyMass_exact`, retaining the complete infinite tail,
and `weightedVacancyTail_bounds` with cutoff error at most `1/(M+1)`.
The actual weighted masses are strictly positive at finite rank, antitone,
and converge to the existing `HistoricalTargets.weightedVacancyMass`.
`weightedVacancyPrefix_eq_gram_trace` gives the exact finite formula using
the full arithmetic Gram matrix. `weightedVacancyMass_zero_iff_top` and
`finiteWeightedVacancyMass_tendsto_zero_iff_top` identify zero mass with
density of the actual residue span; not RH gives strictly positive mass.

`Analysis/ContractiveProducts.lean` retains the exact two-product insert
recurrence and proves two-sided factor-difference bounds.
`Probability/MultiplicativeOccupancy.lean` proves the exact weighted-hole
expectation and its quantitative product comparison without independence
or negative association.
`RH/IntegerDPPWeightedDeterminant.lean` retains the exact finite product
expectation and proves `dampedPrefixLimit_defect_bounds`:
`p_* * mu_infty <= dampedPrefixLimit - p_* <= mu_infty`.
Zero weighted vacancy is equivalent to exact equality at the benchmark.

**Conditional research reduction.**
`weightedVacancyCutoffCertificates_iff_top` identifies arbitrarily small
finite certificates `weightedVacancyPrefix N M + 1/(M+1)` with density.
`riemannHypothesis_of_weightedVacancyCutoffCertificates` keeps this provider
explicit. **Open:** supply those certificates for every positive epsilon.
The logarithmic comparison, operator Fredholm identification, full negative
association, and spatial transport provider are not discharged here.
See `RH/DPPWeightedVacancyCutoffs20260930.md`.

### Abel endpoint decay and sharp signed-charge comparison (2026-09-30)

**Established without RH.** RH/MobiusPrimitiveCharge.lean proves
mobiusCharge_prefix_identity and primitiveChargeRiesz_inner with conductor
one retained. primitiveChargeRiesz_norm_le bounds the normalized complete
primitive kernel by 14; primitiveChargeRiesz_weak_zero and
primitiveChargeRiesz_inner_moving_tendsto_zero allow arbitrary divergent
test cutoffs and strongly convergent moving Hilbert vectors.

RH/DerivativeAbelChargeBounds.lean proves the exact first-site-corrected
endpoint formula correctionPrimitive_normalized_exact, its full square and
a dimension-independent centered-square bound, and the unconditional
correctionPrimitive_endpoint_tendsto_zero. The divisor primitive is identified
using the existing correctionPrimitive_eq_divisor_sum.
reciprocalCorrectionAbel_eq_divisor_endpoint_sum retains the entire endpoint
and harmonic signed sum at every finite stage.
signedDivisorPrimitiveSum_tendsto_full_square identifies the harmonic sum's
limit with minus the complete residual dyadic square.
reciprocalCorrectionAbel_doubleStage_full_squares retains the residual and
increment squares, the scalar Mobius sum, and both energy endpoints.
reciprocalCorrectionAbel_centered_two_gap_sq and
reciprocalCorrectionAbel_doubleStage_lower give a direct finite lower estimate
with the product of adjacent energy drops and no auxiliary raw-test error.
finiteDyadicSquare_tendsto_firstCoordinate and
reciprocalCorrectionAbel_centered_tendsto_zero establish the exact
coefficient-one comparison boundary.

**Conditional research reductions.**
signedDivisorPrimitiveSum_cofinal_iff_residual_zero leaves only cofinal
one-sided lower control of the signed divisor-primitive harmonic sum.
riemannHypothesis_of_signedDivisorPrimitiveSum_cofinal keeps that provider
explicit. reciprocalCorrectionAbel_strict_fraction_cofinal_iff_residual_zero
shows that any fixed strict improvement theta<1 in the complete comparison
A_n + theta*Q_n is also equivalent to residual zero.
**Open:** either signed arithmetic provider. Vanishing of the endpoint and
the previously established complete CRT cancellation do not prove that
provider. See RH/DerivativeAbelChargeEstimate20260930.md.


### Signed aggregate lower bounds and complete Möbius CRT cancellation (2026-09-30)

**Established without RH.** RH/DerivativeMobiusCRT.lean includes conductor one
in completeMobiusCRTIntersection_eq_lcm_sum and retains every actual lcm
intersection and progression tail. completeMobiusCRTIntersection_exact
identifies that sum as M_(m+1)*D_n minus the complete raw-derivative pairing
against the divisor correction synthesis. completeMobiusCRTIntersection_bound
and completeMobiusCRTIntersection_uniform_approximation prove uniform
cancellation over ALL optimization stages, without inverse-Gram l1 norms.
completeMobiusCRTIntersection_tendsto_zero even permits a fixed or oscillating
optimization sequence. The reciprocal charge remains in
mobiusRowAggregate_complete_crt.

RH/DerivativeMobiusAggregate.lean now retains the full finite signed balance
in mobiusRowAggregate_doubleStage_full_remainders: scalar Mobius sum,
residual dyadic square, increment square, both energy endpoints, and the
full raw-pairing remainder. mobiusRowAggregate_doubleStage_lower_bound gives
a finite one-sided estimate about the surviving negative residual square.
mobiusRowAggregate_centered_dyadic_budget bounds only the complete centered
signed expression, not the uncentered negative part.
reciprocalCorrectionAbel_eq_moment identifies the scalar correction with
its exact endpoint plus harmonic-weighted signed primitive sum.

**Conditional research reduction.**
reciprocalCorrectionAbel_cofinal_iff_residual_zero proves that cofinal
lower control of this COMBINED Abel charge is exactly residual vanishing.
riemannHypothesis_of_cofinal_reciprocalCorrectionAbel retains that provider
as an explicit hypothesis. **Open:** the zero-threshold one-sided bound
on this harmonic Abel charge, equivalently on T_(n,n).
Uniform cancellation of the complete CRT intersections does not remove
the reciprocal charge. See RH/DerivativeMobiusLowerBound20260930.md.


### Imported research libraries: large sieve, Li/Hadamard, operator core (2026-09-30)

**Established abstract results, with RH applications still open.**
Pinned external developments add 42 focused Lean modules. Original namespaces
and licenses are retained; source pins, scope, target adaptations, and verified
endpoints are recorded in RH/ResearchImports20260930.md and the adjacent
provenance documents.

- **Exact arithmetic identities and estimates.**
  Analysis/LargeSieve/Additive.lean supplies Erdos768LS.parseval_expsum and
  Erdos768LS.additive_large_sieve, with constant delta^(-1) + 4*pi*N.
  Analysis/LargeSieve/Multiplicative.lean supplies
  Erdos768LS.plancherel_dft, Erdos768LS.orthogonality_sum,
  Erdos768LS.farey_sum_bound, and Erdos768LS.mult_large_sieve_final.
  The exact identities precede the estimates; the positive universal
  multiplicative constant is witnessed by 4*pi.
  **Open:** duality, exact CRT Fourier identification, and weighted-tail
  transfer for RH/RawMobiusFarTailLargeSieve20260924.md. Its sharper displayed
  constant is not certified by this import.
- **Actual Li criterion and multiplicity-weighted zero identity.**
  Analysis/LiCriterionImport/Lc/LiCriterion/XiOrderBridge.lean supplies
  LiCriterion.li_criterion_rh_iff using Mathlib's RiemannHypothesis and
  riemannXi. XiGrowth proves the finite-order and order-at-most-one inputs.
  Fidelity.lean supplies LiCriterion.taylorCoeff_eq_li_symmetrized and
  LiCriterion.summable_li_symmetrized, retaining the factor one-half,
  both signed exponents, and analytic multiplicities. The 33-module
  Hadamard/complex-analysis dependency closure is included.
  **Open:** positivity of every actual coefficient, or a checked provider
  relating the signed CRT/Weil forms to these coefficients.
- **Canonical partial-operator closure and self-adjointness.**
  Analysis/UnboundedOperatorImport supplies closability/adjoint/core
  identities, shifted-range self-adjointness criteria, and deficiency-space
  identities in Mathlib's LinearPMap domains.
  Spectra.Operator.isEssentiallySelfAdjoint_of_denseRange_addSub retains
  symmetry, a dense domain, and density of both shifted ranges.
  **Open:** prove these hypotheses for the actual operator in
  RH/MellinJacobiOperator20260928.md and identify its spectrum with zeta zeros.

These imports discharge no signed CRT cancellation, Li positivity, or
Mellin/Jacobi domain/range obligation merely by being available.

### Uniform Möbius aggregation of derivative correction rows (2026-09-29)

**Established without RH.** RH/DerivativeMobiusAggregate.lean defines
T_(m,n) as the negative Mobius-weighted sum of the complete signed derivative
correction rows. mobiusRowAggregate_exact reconstructs half the reciprocal
correction with the full Hilbert-pairing remainder.
mobiusRowAggregate_square retains the signed cross term and remainder square;
mobiusRowRemainder_bound and mobiusRowAggregate_uniform_bound give a constant
independent of both finite dimensions, and
mobiusRowAggregate_uniform_approximation proves uniform approximation over
all optimization stages. The Abel endpoint and all signed kernel differences
and CRT lcm intersections remain explicit in mobiusRowAggregate_eq_abel and
mobiusRowAggregate_eq_crt.

mobiusRowAggregate_tendsto identifies the limit for any test cutoff m(n)
tending to infinity, without a relative growth condition.
mobiusRowAggregate_tendsto_full_remainder retains the complete dyadic
norm square and identifies the limit as -r(1)/2.
limiting_derivative_test_sq_le_firstCoordinate bounds every limiting
derivative pairing by (4+2*sqrt(2))*norm(f)^2*r(1).

**Conditional research reduction.** cofinal_mobius_gram_iff_fixedMismatch
and mobiusRowAggregate_cofinal_iff_residual_zero show that the single
one-sided estimate T_(n,n)>-epsilon at cofinally many stages for each
epsilon>0 is equivalent to all fixed mismatches vanishing and to residual
zero. riemannHypothesis_of_cofinal_mobiusRowAggregate supplies the RH
implication with that hypothesis explicit.
**Open:** an arithmetic provider of this cofinal lower bound.
Neither the existing reciprocal limit nor raw Mobius derivative convergence
supplies it. See RH/DerivativeMobiusAggregate20260929.md.


### Exact Abel–CRT–Weil transfer (2026-09-29)

**Established without RH.** RH/DerivativeCRT.lean proves the complete lcm
derivative kernel, explicit Abel kernel differences and endpoint, and the
finite Mobius-divisor primitive. Its combined CRT row has precisely the
existing cofinal residual-zero criterion.

RH/GeometricDerivativeMoments.lean constructs the actual tail multiplier of
norm at most 2^(-M), retains the first physical site and full signed/square
remainders, and proves an unconditional uniform correction norm bound.
RH/DerivativeCRTPowerMoments.lean evaluates its moments by actual integer
zeta values and lcm data. RH/DerivativeZetaGeometricBridge.lean proves
signedCorrectionRow_eq_zetaCRT and its dimension-independent geometric
error bound. The diagonal finite arithmetic criterion
correctionZetaCRT_cofinal_iff_residual_zero is equivalent to residual zero;
the diagonal limit is justified by uniform control, not coordinatewise limits.

RH/DerivativeCorrectionWeilBridge.lean uses the SAME correction primitive
in actual finite Weil zero sums, retaining the reflected-difference square.
Actual mixed Weil entries recover its Mellin samples at every actual zero
with multiplicity. The full finite Mellin proxy discrepancy has its own Abel
endpoint and complete square identity. mellinProxy_cofinal_iff_residual_zero
retains cancellation between proxy and discrepancy.

**Conditional research reductions:** the cofinal zeta/CRT-core and jointly
cofinal mixed-Weil/discrepancy budget implications to RH.
**Open:** provider of either complete signed arithmetic cancellation estimate.
No positivity, null-Weil/Gram identification, or growing-sum interchange is
assumed. See RH/AbelCRTWeilBridge20260929.md for exact formulas and scope.


### Three-route quantitative bridge (2026-09-29)

**Established without RH.** Analysis/ContractiveProductDefect.lean proves
exact multiplication and finite interaction telescopes for f(p)=p+1/p-2,
plus the complete multiplicity-weighted finite-product inequality.
RH/BurnolQuadraticZeroDefect.lean identifies its term with the actual
reflected-zero geometric defect, proves summability over actual right-hand
zeros, and bounds its total by f(productSq). The certificate version keeps
q>0 and q<=productSq explicit; it does not supply the analytic Pareto
projection comparison.

RH/ResidualCorrectionCertificate.lean proves the exact augmented covariance
identity for the optimal residual and the missing coefficient-dual Gram.
Every signed contraction obeys (z.e)^2<=E*z^T(U-Ginv)z, retaining all
cross terms and avoiding the potentially large raw Mobius residual norm.

NumberTheory/WeightedDivisorTransform.lean and RH/WeightedDivisorCorrection.lean
prove finite weighted convolution and complete Pareto Cauchy--Schwarz
budgets. RH/WeightedDivisorCorrectionLimit.lean supplies the actual Hilbert
weighted-l1 bound and correction_weightedMass_tendsto_zero with no extra
provider hypothesis. This is convergence about the identified residual
limit, not a claim that this limit vanishes.

**Rigorous paper deductions, not fully Lean-formalized endpoints:**
ThreeRouteQuantitativeBridge20260929.md proves the finite Weil negative-mass
bound tr(W_-)<=2*M^2*(1-Q)^2/[sqrt(Q)*(1+sqrt(Q))^2], using Burnol's classical
continuous projection identity, the full positive defect decomposition,
and a retained projection gap. It also proves weighted-array convergence
for every exponent s>3/2 and the exact CRT row separation into a reciprocal
charge and uniformly O(d^-2) remainder.
CorrectionDirichletZeroBridge20260929.md proves local uniform convergence
of the actual signed coefficient polynomials on Re(s)>1/2 and identifies
the correction continuation as 1/zeta(s)+P(s), with P holomorphic. All
off-line poles retain the full reciprocal-zeta principal part, including
multiplicity and the d=1 boundary term. This supplies a paper proof of
ClosedSpaceMellinMultiplicityTarget; its checked provider remains Open.

**Open mathematical RH obligation:** prove the limiting signed correction
vanishes, or an independent full Weil positivity/removability theorem.
**Open formalization obligations:** the complete analytic projection
provider, sharp conjugate-pair spectral transfer, general-s convergence,
and the correction continuation/principal-parts bridge. No literature
priority or RH proof is claimed. See RH/ThreeRouteQuantitativeBridge20260929.md.


### Fixed signed derivative correction and cofinal Abel criterion (2026-09-29)

**Established without RH.** RH/DerivativeSignedCorrection.lean defines
signedCorrectionRow as the entire derivative Gram row applied to the
original inverse-Gram correction. signedCorrectionRow_eq_pairing and
fixedMismatch_eq_raw_sub_signedCorrectionRow preserve the exact sign.
signedCorrectionRow_tendsto identifies its limit as the negative adjoint
pairing; signedCorrectionRow_first_tendsto retains D plus the weighted
parity remainder at conductor two.

correction_limit_error_exact and correction_limit_error_energy_exact retain
the full vector difference, signed cross term, and both square remainders.
correction_limit_test_bound and correction_limit_test_sq_bound give
dimension-independent estimates for every Hilbert test. The budget tends
to zero, and correction_limit_moving_test_tendsto_zero permits arbitrary
uniformly bounded moving tests. These establish convergence about the
identified limit, not vanishing of that limit.

signedCorrectionRow_eq_abel and signedCorrectionRow_eq_secondAbel give exact
finite Abel formulas with all boundary terms. The equivalences
signedCorrectionRow_cofinal_iff_residual_zero and
correctionAbel_cofinal_iff_residual_zero require only cofinal smallness
separately for each fixed test and accuracy.

**Conditional research reduction:** riemannHypothesis_of_cofinal_signedCorrectionRow.
**Open:** prove this signed cofinal smallness for the actual correction
coefficients. No rate, common cofinal set, or inverse-Gram norm bound is
assumed. See RH/DerivativeSignedCorrection20260929.md.

### Strong natural-cutoff Mobius derivative convergence (2026-09-29)

**Established without RH.** NumberTheory/DivisorCountSquareSummability.lean
proves square divisor-count summability using elementary divisor pairing
and the existing Dirichlet series at exponent 3/2.
RH/NaturalMobiusDerivativeConvergence.lean proves
rawMobiusDerivativeResidual_tendsto_zero: the complete raw derivative
converges strongly to zero as the natural cutoff N tends to infinity.
Every fixed Hilbert test is now allowed, without physical boundedness.

derivative_correction_exact and raw_derivative_complete_correction_energy
retain the entire correction and signed cross term.
derivative_correction_tendsto identifies the strong correction limit as
-Delta(limitResidual). Its energy tends to q = ||Delta(limitResidual)||^2;
derivative_correction_cross_tendsto gives cross-term limit -q.
The exact raw-energy identity therefore has limiting cancellation q-2q+q=0.

**Open:** the requested canonical optimal-coefficient vanishing, equivalently
limitResidual = 0, is not supplied by this stronger raw convergence.
All audited endpoints use only propext, Classical.choice, and Quot.sound.
See RH/DerivativeVanishingAttempt20260929.md, Section 2.

### Derivative vanishing attempt: raw source cancellation and canonical nonlinear coercivity (2026-09-29)

**Established without RH.** RH/NaturalMobiusDerivativeTests.lean proves
rawMobiusDerivativeResidual_inner_tendsto_of_bounded and
raw_derivative_signed_row_tendsto_zero: the complete derivative source
d_N+D_N*mu_N tends to zero in each fixed row. The proof uses the exact
truncated divisor jump, PNT, and a summable divisor-count majorant.
mismatchSource_eq_raw_sub_correction preserves the entire correction
D_N*G_N^{-1}(b_N+G_N*mu_N). This is not asserted to vanish.

RH/DerivativeAdjointRows.lean proves the exact weighted adjoint row and
fixedMismatch_first_limit_exact = -D - the full signed weighted parity
correlation. Ordinary legal orthogonality does not delete that correlation.

RH/ResidualDerivativeCoercivity.lean proves derivative_limit_exact_four_terms:
the limiting derivative energy equals (3-2*sqrt(2))*D^2 plus the complete
nonnegative dyadic cross term, dyadic remainder square, and derivative tail.
canonical_energy_sq_le_derivative_energy gives nonlinear coercivity specific
to the canonical residual. canonical_energy_sq_le_finite_compatibility gives
a finite certificate retaining the mismatch cost and full projection gap.

RH/PrimeSievePrimitiveEscape.lean proves exact primitive head-plus-tail
identities and derivativeSieveHilbert_primitive_error_tendsto_atTop:
the actual derivative sieve has diverging primitive error, despite its
vanishing derivative error. Its primitive norm also diverges.

**Requested optimal-coefficient vanishing remains Open.** The new raw
cancellation theorem does not discharge the signed canonical correction.
See RH/DerivativeVanishingAttempt20260929.md for the precise attempt and
the distinction between raw coefficients and optimal coefficients.
Endpoint axiom audits use only propext, Classical.choice, and Quot.sound.

### Formalized derivative compatibility, exact sieve scale, and fixed-coordinate reduction (2026-09-29)

**Established without RH.** RH/ThresholdHilbertDifference.lean constructs
the actual continuous injective anchored difference operator, its norm bound
2, its first-site boundary, and the complete primitive energy identity for
every Hilbert vector. Analysis/FiniteGramCompatibility.lean proves the exact
inverse-Gram mismatch cost and its attained dual formula with full square.

RH/PrimeSieveDerivativeApproximation.lean proves the complete factorial-sieve
derivative error C_Y^2 - 2*C_Y*J_Y + J_Y, its vanishing, and the stronger
derivativeSieveError_ratio_tendsto_one. The explicit absolute relative error
is bounded by 1/((Y+1)*C_Y^2). RH/PrimeSieveDerivativeClosure.lean proves actual
finite Hilbert sieve membership and derivative_target_mem_dictionaryClosure.

RH/ResidueDerivativeCompatibility.lean specializes the matrix theorem to the
actual legal projection coefficients. derivative_error_exact_split retains
h_N^T D_N^{-1} h_N with h_N=d_N-D_N G_N^{-1}b_N. Independence proves actual
derivative Gram determinant positivity, and derivativeSource_apply gives
1/(2*j). derivativeBestError_tendsto_zero is unconditional.
mismatchEnergy_tendsto identifies the full limit as the squared norm of the
derivative of limitResidual. The complete limiting primitive identity is kept.

Analysis/ClosedSpanCompatibility.lean and the application theorem
fixedMismatch_limits_iff_projection_norm_zero prove that, for these actual
strongly convergent projections, vanishing of every fixed signed derivative
pairing is equivalent to vanishing of the original full norm error.
No uniform inverse estimate is assumed.

**Conditional research reduction. Open:** the fixed signed derivative
compatibility limits (equivalently, vanishing of the complete mismatch cost)
are not established. riemannHypothesis_of_fixedMismatch_limits and
riemannHypothesis_of_mismatchEnergy_tendsto_zero retain those hypotheses.
This closes the paper-to-Lean gap in the audit, not the RH arithmetic gap.
See RH/CRTPrimitiveTransferAudit20260929.md, Section 6.
Endpoint axiom audits use only propext, Classical.choice, and Quot.sound.

### Exact failure of uniform CRT primitive transfer and optimizer incompatibility (2026-09-29)

**Established without RH.** RH/ParetoPrimitiveEnergy.lean proves
PrimitiveEnergy.energy_sub_backwardShift and full_primitive_energy_identity:
the complete shift defect and symmetric primitive square are retained.

RH/CRTPrimitiveEscape.lean proves binaryPrimitive_energy = m*log(2),
binaryPrimitive_mean = log(2), and binaryJump_energy_add_remainder = zetaTwoSeries.
The endpoint binaryPrimitive_full_remainder combines the whole primitive
identity with the positive sparse remainder. no_uniform_primitive_bound
refutes a conductor-independent upper primitive bound using two legal atoms
with zero reciprocal charge. The normalized_binary_approximate_kernel theorem
gives fixed positive primitive energy and arbitrarily small derivative energy.

The stronger centeredPrimitive_mean and centeredPrimitive_energy give an
actual Pareto-mean-zero three-atom family with full energy m*pi/2.
centeredJump_energy_le bounds its complete derivative energy by 4*zetaTwoSeries;
no_uniform_centered_primitive_bound refutes uniform transfer even on this family.

RH/ResidueDerivativeOptimization.lean proves the complete derivative objective
for the first legal residue is 1/4+(t-1/2)^2, whereas binaryPrimitive_scale_error
gives legal objective 1-log(2)+log(2)*(t-1)^2. The checked signed derivative
normal-equation mismatch at the legal optimizer is -1/2. Projection and
differentiation therefore do not commute automatically.

**RH closure remains Open.** These results do not refute convergence of the
actual optimal projections or the screened prime-power route.
RH/CRTPrimitiveTransferAudit20260929.md records the now-formalized identity
derivative_error^2 = derivative_optimal_error^2 + h_N^T D_N^{-1} h_N,
where h_N=d_N-D_N G_N^{-1}b_N. The compatibility energy tending to zero remains
an unresolved RH-strength obligation, not a checked arithmetic estimate.
Endpoint axiom audits report only propext, Classical.choice, and Quot.sound.

### Exact CRT Gram comparison, global prime-power Schur elimination, and actual Weil translations (2026-09-29)

**Established identities, without assuming RH.** In namespace
RiemannResearch.RH.Pareto.CRTSparseEnergy, the new modules
RH/CRTSparseEnergy.lean and RH/CRTGCDGram.lean prove the complete identity
E_M + R_M = E_infinity, with a full nonnegative square remainder.
The declarations sparseEnergy_add_remainder, positiveRemainder_bounds,
full_physical_energy_eq_sparseEnergy, gcdReferenceKernel_gcd,
referenceEnergy_incidenceProfile, and incidence_sparseEnergy_gcd_relative_bounds
give exact physical support reindexing and the full signed GCD quadratic form.
For every finite incidence profile, summability is proved and the relative
factor M/(M+1) is independent of dimension and conductor.

RH/PrimePowerRamanujanSchur.lean proves exact projection against the entire
non-prime-power Ramanujan packet space. The endpoint
PrimePowerSchur.exists_exact_global_elimination provides screened normal
equations with von Mangoldt source and the original minimum with BOTH full
square remainders. It assumes neither a Gram inverse nor unique coefficients.
It builds on the already established packet means and finite-span bridge.

Analysis/SuperexponentialTranslation.lean proves translation closure of every
derivative in the smooth superexponential test class.
RH/WeilPrimeTranslationKernel.lean uses the actual imported Weil formula and
proved single-zero tests. SignedWeilCorrelation.exists_smooth_translated_reflection_kernel
constructs the full translated arithmetic pairing from an explicitly supplied
actual off-line zero. The theorem does not assert such a zero exists.
Combined endpoint axiom audits report only propext, Classical.choice, Quot.sound.

**Conditional research reduction.** See
RH/CRTGramAndWeilTranslation20260929.md for precise equations, provenance,
and paper proofs of squarefree tensor inversion, the full legal primitive
identity, and the prime-log Weil matrix spectrum. Those paper matrix/primitive
consequences are not additional Lean declarations.

- **Open:** Vanishing of the exhaustive legal screened minima (equivalently the
  appropriate von Mangoldt inverse quadratic tending to one where defined).
- **Open:** Control of the complete primitive-energy and signed covariance terms
  needed to transfer sparse CRT information to legal optimization.
- **Open:** For the Weil route, positivity of the full actual arithmetic form
  on a sufficient test class.

No RH conclusion, uniform legal-Gram inverse, or mathematical novelty is claimed.
The sparse positive Gram and the conditional indefinite Weil matrix are distinct.

### Exact dyadic balance, complete remainders, and cumulative slope (2026-09-29)

**Established without RH.** `RH/FiniteDyadicDefect.lean` now keeps the exact
identities as the primary results. The declarations
`finiteDyadicSquare_eq_energy_add_remainder` and
`finiteDyadicDefect_eq_energy_drop_sub_remainder` restore the two norm-square
remainders. `finiteDyadicDefect_sum_eq_boundary_sub_remainders` telescopes the
signed defect exactly. `reciprocalCorrection_dyadic_sum_eq_full_remainders`
retains both square sums, the signed Mobius sum, and all four boundary energies.
No absolute-value replacement or unspecified error term occurs in that equality.

`firstCoordinate_eq_energy_add_dyadicRemainder` identifies the limiting first
coordinate as (2-sqrt(2))*limitEnergy plus the full normalized-dilation square
with coefficient 1/sqrt(2). `reciprocalCorrection_tendsto_full_remainder` and
`reciprocalCorrection_dyadic_average_tendsto` establish the exact correction
limit and cumulative slope. `dyadicStage_tendsto` supplies cofinal sampling.
`reciprocalCorrection_dyadic_average_zero_iff_residual_zero` proves zero slope
is equivalent to residual vanishing. Endpoint axiom audits report only the
standard foundations `propext`, `Classical.choice`, and `Quot.sound`.

**Conditional research reduction.**
`riemannHypothesis_of_reciprocalCorrection_dyadic_average_zero` derives RH
from zero slope. **Open:** an arithmetic proof that this slope is zero. The
existing logarithmic growth bound does not discharge this obligation. The
reverse RH-to-residual implication still uses the explicit analytic provider
`RiemannHypothesis → BaezDuarte.NaturalApproximation`; it is not a hidden
assumption of the new results. See `RH/DyadicSignedCorrectionResearch20260929.md`,
Section 1a, for the exact formulas and verification boundary.

### Summable dyadic signed defect and reciprocal correction budget (2026-09-29)

**Established without RH.** `RH/FiniteDyadicDefect.lean` proves the exact
finite first-coordinate square-minus-defect identity for the actual optimal
projections. `finiteDyadicDefect_two_gap_sq` bounds the squared defect by
twice the product of consecutive dyadic projection-energy decreases.
`finiteDyadicDefect_sum_abs_le` telescopes a complete finite l1 budget;
`finiteDyadicDefect_tsum_abs_gap_bound` bounds the infinite absolute sum by
sqrt(2) times the remaining projection gap. The actual full reciprocal
inverse-Gram statistic satisfies
`reciprocalCorrection_centered_dyadic_abs_summable`,
`reciprocalCorrection_dyadic_sum_le`, and
`reciprocalCorrection_dyadic_positive_sum_le`. No arithmetic sign or RH
hypothesis occurs in these declarations.

**Established exact Weil block.** `exists_smooth_weil_reflection_block` in
`RH/WeilConverse.lean` constructs the full arithmetic two-test matrix
[[0,m],[m,0]] for an actual off-line reflected zero pair. Analytic multiplicity
is retained; simplicity is not assumed. The full converse was already proved
in the preceding commit and is not counted as new here.

**Paper consequence with explicit external analytic inputs.** Combining the
finite budget with Burnol's NB distance lower bound and Johnston--Leong--Tudzi
Theorem A.2 gives summable positive parts of the dyadic reciprocal corrections
and negative cumulative drift at least 0.03903688411*log K asymptotically.
These cited analytic inputs and their assembled numerical consequence are NOT
kernel-formalized here and are not introduced as axioms. The statistic includes
the terminal conductor; no cumulative claim for the truncated divisor
statistic follows merely from a pointwise approximation. See
`RH/DyadicSignedCorrectionResearch20260929.md` for the full proof.

**Open.** Vanishing of the nonnegative main residual energy, fixed correction
limits zero, and universal arithmetic Weil positivity remain Open. Divergent
negative sums are compatible with RH and do not prove its failure.

### Full smooth Weil converse and quantitative arithmetic zero exclusion (2026-09-29)

**Established without RH.** `Analysis/FiniteTransformZeroRemoval.lean` proves
finite-order integral zero removal in the full smooth-superexponential class.
`RH/WeilSingleZeroTest.lean` constructs, for every actual nontrivial zero,
an admissible test with transform one there and zero at every other actual zero.
No simplicity or spectral-interpolation hypothesis is assumed.
`RH/WeilConverse.lean` proves
`exists_smooth_negative_weil_of_off_line`: an actual off-line zero produces
a smooth test of exact arithmetic Weil value minus twice its actual multiplicity.
The full converse is discharged:
`riemannHypothesis_iff_arithmeticWeilPairing_nonneg`,
`riemannHypothesis_iff_smoothWeilMatrix_two_nonneg`, and
`riemannHypothesis_iff_smoothWeilMatrix_nonneg`.
These are proved equivalences, not proofs of their positivity side or RH.

**Established quantitative obstruction.** `RH/ResidueDivisorZeroExclusion.lean`
makes the signed statistic's limiting deficit explicit in any hypothetical
right-half-plane zero: r(1) >= (2-sqrt(2))(2 Re(rho)-1)/norm(rho)^2.
It proves eventual negativity with an explicit positive margin and a bounded
zero-exclusion region from a cofinal arithmetic lower budget.
`RH/ResidualDyadicFactor.lean` strengthens this with the exact factorization
r(1)=(1+sqrt(2)/2)*norm(r-(1-sqrt(2)/2)*D_2(r))^2, and the sharper multiplier
(1+sqrt(2)/2)*norm(1-(1-sqrt(2)/2)*2^(1-rho))^2.
`dyadic_zero_multiplier_lower` proves this multiplier dominates 2-sqrt(2).

**Open positivity / conditional research reduction.** Arithmetic Weil
nonnegativity for every smooth test remains Open. Cofinal lower budgets for
the actual divisor statistic remain Open; the zero-exclusion theorems retain
these hypotheses. No effective residual convergence rate or RH-to-Pareto
density provider is asserted. The former open negative-witness construction
is now discharged. See `RH/StrongRHConsequences20260929.md`.

### Signed reciprocal divisor limit and admissible zero removal (2026-09-29)

**Established without RH.** `RH/MovingReciprocalCharge.lean` justifies growing
reciprocal heads against strongly convergent vectors using the proved Balazard
Riesz bound. It also proves `correction_terminal_div_tendsto_zero` and
`coefficient_terminal_div_tendsto_zero`: the actual last correction and
optimal coefficient are o(n). `RH/ResidueDivisorReciprocalLimit.lean` proves
`divisorReciprocalStatistic_error_le` with error `harmonic n / sqrt(n+1)`
and `divisorReciprocalStatistic_tendsto` with exact limit minus the first
residual coordinate. The existing energy interval transfers to this finite
signed progression statistic; positive defect forces eventual negative drift.
`Analysis/FiniteHarmonicBounds.lean` supplies the vanishing error envelope.

**Established analytic provider.** `Analysis/SuperexponentialPrimitive.lean`
and `Analysis/SmoothZeroRemoval.lean` construct the actual twisted primitive
at a transform zero. It preserves the smooth-superexponential Weil test class
and proves `F(s)=(s-z)G(s)`, preserves other zeros, and gives `G(z)=F'(z)`.
This is an admissible way to remove one order of a transform zero.

**Conditional research reduction; Open arithmetic lower estimate.**
`riemannHypothesis_of_divisorReciprocalStatistic_cofinal_lower` requires
that for each positive epsilon the statistic exceed minus epsilon cofinally.
No arithmetic lower-bound provider is asserted. The negative Weil witness
has now been formalized in `RH/WeilConverse.lean`; arithmetic positivity
remains Open.
See `RH/DivisorReciprocalAndZeroRemoval20260929.md` for proofs and exact scope.

### Signed Abel and common-period divisor bridge (2026-09-29)

**Verified Lean formalization.** The six modules
`Analysis/SignedAbel`, `RH/ResidueCorrectionAbel`, `RH/ResidueCorrectionAbelLimits`,
`RH/ResidueDualDifferences`, `RH/ResidueCorrectionDivisorAbel`, and
`RH/SmoothWeilMatrix` reconstruct the attached Anthropic bridge and extend it
with common-period cancellation. Principal endpoints include
`correction_sub_period_divisor_sq_le`, `correctionPeriodDivisor_tendsto`,
`projectedDualReciprocalCharge_sq_le`, and `smoothWeilMatrix_quadratic_zero_sum`.
The arithmetic identities and finite error certificate require no RH premise.
Weil positivity explicitly assumes RH; completed-Nyman matrices are zero.

**Conditional research reduction; Open signed cancellation provider.**
`riemannHypothesis_of_cofinal_period_divisor` retains separate cofinal
smallness of each actual signed inverse-column/progression pairing. No
provider of that hypothesis is asserted. See
`RH/ResidueDivisorAbelAudit20260929.md` for the paper argument and verification
boundary. All 16 principal declarations named in the supplied markdown are
available. The combined Lean check passes, and the 11 audited endpoints use
only `propext`, `Classical.choice`, and `Quot.sound`. The cofinal cancellation
and RH premises remain explicit hypotheses; the axiom audit does not discharge them.

### Complete Anthropic RH proof-library import (2026-09-28)

**Imported upstream mathematics; no new RH proof.** The pinned
`anthropics/formal-math` source at `fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`
now contributes 311 proof modules (171 newly added) under
`RH/WeilExplicitFormula/`, with the existing Lean/Mathlib pins unchanged.
The new entry points cover xi' zeros and Hardy-Z stationary points
(`Zeta23.XiPrime.xiDeriv_simple_on_line_quartic_std`,
`hardyZ_simple_stationary_points_quartic`), primitive Dirichlet zero counts
and optimized proportions (`Zeta23.ThmE.thmE_B₀_mult`,
`Zeta23.ThmDE.thmE_D₀_simple_mult`), Gevrey tapers, and rank-trace sharpness
(`Zeta23.ZeroSide.TightMult.lemmaR_tight`). Upstream proofs and namespaces
are preserved. These results supply analytic infrastructure; no application
to the actual Pareto inverse-Gram correction is asserted without a bridge.

**Conditional research reduction; Open numerical provider.**
`Zeta23.PairCeiling.ceiling_law256_signed` retains the form-factor enclosure
premise `EnclOK` and certificate validity `hvalid`, as well as regularity
conditions. The import does not discharge the law's enclosure premise.
The general `ceiling_stability` and Abel/discrepancy lemmas are available
under their explicit mathematical conditions. Standard foundation-only axiom
reports must not be interpreted as discharging hypotheses in theorem types.

See `RH/AnthropicRHImport20260928.md` for consumers, exact endpoints,
research-reading links, and verification boundaries, and
`RH/WeilExplicitFormula/SOURCE_MANIFEST.json` for all upstream blob identities.

### CRT orbit signed transport (2026-09-28)

**Established without RH.** `RH/DyadicCarrySignedTransport.lean` proves
`dyadicMultipleIndicator_scaled_moving_pairing_tendsto_zero`: for
d_k=2^k+1, b_k=1_{d_k divides n}, and every norm-convergent family f_k,
d_k*inner(f_k,b_k) tends to zero. The complete tail estimate is
d_k^2*inner(f,b_k)^2 <= 2*norm(tail_(2^k) f)^2.
`dyadicRepairEnergy_zero_head_scaled_difference_tendsto_zero` gives
d_k*(dyadicRepairEnergy k 0 (2^k)-energy(2^k)) -> 0.
This improves the comparison of actual finite optima; it does not prove their
common limit is zero. Exact signed covariance and residual-observation
identities retain the complete infinite Pareto norm.

**Conditional research reduction; Open.**
`dyadic_residual_pairing_cofinally_nonpos_iff` identifies constant membership
with cofinally nonpositive inner(limitResidual,dyadicSampledResidue k).
`riemannHypothesis_of_dyadic_residual_pairing_cofinally_nonpos` derives
Mathlib RH from that explicit condition. A checked arithmetic provider for
the cofinal sign assertion is **Open**. No infinite-DPP assumption or
RH-to-density provider is introduced.
See `RH/CRTOrbitSignedTransport20260928.md` for the source audit and proof.

### Exact dyadic Dyson connection and Mellin operator audit (2026-09-28)

**Established without RH, Lean-checked algebra.**
`Analysis/PowerDifferenceDeterminant.lean` proves the power-difference
Vandermonde determinant identity and its nondegeneracy criterion.
`RH/MellinDyadicVandermonde.lean` specializes it to actual dyadic residue
symbols and actual Mellin transforms. In particular,
`dyadicMellinMatrix_det_ne_zero_iff` says that the actual dyadic minor is
nonsingular exactly when all sampled critical-line zeta values are nonzero
and the dyadic phases are pairwise distinct. The result has no RH premise.

**On-paper results, not claimed Lean-verified.**
`RH/DyadicDysonConnection20260928.md` proves exact folding to a circular
beta=2 ensemble, a positive analytic weight between 1/528 and
(3+2*sqrt 2)/4, bulk sine-kernel universality, and a dimension-independent
inverse-Gram bound 528 for normalized dyadic differences. The dyadic
constant-function approximation defect is nevertheless at least 1/20;
its first-site vacancy is at least 1/10. General integer dilations have no
uniform Riesz lower bound. The canonical circle operator has continuous
spectrum; its occupied-space shift Cayley operator has unequal deficiency
indices and no selfadjoint extension on that same space.

`RH/MellinJacobiOperator20260928.md` proves a trivial ordinary Mellin
frequency domain, constructs the symmetric-cutoff Jacobi operator with
coefficients sqrt(n*(n+2))/2, and identifies its unique selfadjoint closure
with the Meixner-Pollaczek spectral measure
2*(t^2+1/4)/cosh(pi*t) dt. Its spectrum is purely absolutely continuous.
Its domain intersects each finite residue space in span(g_2), and its
leakage on g_2 is exactly one sixteenth of the constant-function defect.

**Conditional research reduction; Open.**
`RH/HilbertPolyaKernelTarget20260928.md` derives the renormalized
Lagarias-de Branges kernel associated with Xi+i*Xi'. Positivity of this
specific kernel is equivalent to RH; it has not been proved. An arithmetic
Gram representation converging to it is Open. The unmodified Mellin DPP
kernels cannot provide that pointwise limit at simple critical zeros,
because their diagonal values there are zero. Operator domains and zeta
multiplicity preservation would also need verification for an operator
construction. No Hilbert-Polya operator is claimed unconditionally.

### Actual continuous Mellin-window count law and concentration (2026-09-28)

**Established without RH, Lean-checked.** `RH/MellinWindowCount.lean`
proves the complete Poisson-binomial law of the number of sampled frequencies
in any measurable window under the actual finite `mellinLaw n`.
The eigenvalues come from the restricted Gram matrix of its actual Mellin modes
and lie in [0,1]. The count agrees almost surely with the unordered
configuration count.

The new continuous bridge is weighted Andréief in
`Probability/ContinuousProjectionDensity.lean`, followed by
`ContinuousProjectionCompression`, `ContinuousProjectionGenerating`,
and `ContinuousProjectionWindowEnergy`. `BoundedCountLaw` reuses the
existing finite Bernoulli and determinantal moment machinery to identify
the actual continuum count distribution. `BoundedCountGenerating` supplies
exact exponential-product upper and lower tails.

Main checked declarations:
- `mellinWindowCount_law`, `mellinWindowCount_moments`;
- `mellinWindowCount_expectation_kernel`: mean = integral of K(t,t);
- `mellinWindowCount_variance_kernel`: variance = trace minus kernel HS square;
- `mellinWindowCount_variance_boundary`: variance = integral over I x I-complement
  of |K(t,u)|²;
- `mellinWindowCount_variance_bounds`: variance <= min(mean, n-mean, n/4);
- `mellinWindowCount_upper_tail`, `mellinWindowCount_lower_tail`: exact
  spectral Chernoff products, for every nonnegative tilt;
- `mellinWindowCount_hole`, `mellinWindowCount_hole_le_exp`;
- `mellinWindowCount_hole_first_mode`: an explicit zeta/conductor-two
  integral in the hole exponent, independent of larger positive rank.

`RH/MellinCoordinateDefect.lean` additionally proves
`first_window_deficit_ge_zero_floor`: a hypothetical off-critical zero
forces a quantitative positive first-coordinate window deficit, using the
existing site Mellin vacancy floor without a zero-profile provider.

**Conditional research reduction; arithmetic provider Open.**
`RH/MellinWindowCountArithmetic20260928.md` gives a rigorous paper localization:
for the unit first-coordinate Mellin image h, a_R = ||1_[-R,R] h||² and
c_d = integral_[-R,R] conjugate(phi_d) h,
the limiting vacancy is at most
(sqrt(a_R - c* G^-1 c) + sqrt((3+2sqrt(2))/(pi R)))².
Finding ranks and expanding windows for which a_R - c* G^-1 c tends to zero
would imply RH. This estimate is not proved. The full frequency-L² localization
bridge is explained on paper, not claimed Lean-formalized here.
Count concentration and leading sine scaling do not supply the missing
orientation-sensitive signed inverse-Gram saturation. Physical-coordinate
cutoff M and arithmetic rank n remain distinct. No infinite DPP is assumed.

### DPP critical zeros, uniform intensity, and conductor obstruction (2026-09-28)

**Established without RH.** `RH/MellinDPPIntensity.lean` proves
`first_atom_intensity_uniform_bound`: for every positive rank and every real
frequency, the actual Mellin kernel diagonal is at least
`((3-2*sqrt 2)/log 2) * |zeta(1/2+it)/(1/2+it)|^2`.
`mellin_diagonal_zero_iff` identifies its zero set exactly with the actual
critical-line zeta zeros. There is no inverse-Gram growth premise.

`RH/IntegerDPPConductorCutoff.lean` proves coefficient-free control
`|hilbertSequence f k| <= L*norm f` on every finite legal space whose
conductors divide positive L. With the imported critical-zero provider,
`exists_uniform_conductor_vacancy_obstruction` proves, with no premises,
that some a>0 satisfies for all ranks and positive common conductors:

    a^2 <= 4 * vacancy(n) * log(4*(L+1+a)/a).

This is a lower bound on vacancy, not a saturation theorem.

**On-paper results, not claimed Lean-verified:** the companion notes
`CriticalZeroConductorCertificate20260928.md` and
`MellinDPPArithmeticBounds20260928.md` give sharper explicit finite-conductor
certificates, multizero Gram limits, infinite mean first-site entrance time,
global fixed-dyadic-subspace correlation and probability lower bounds,
exact zero-window exponents, and two-prime interpolation nondegeneracy.
The first-site threshold coupling suffices for the entrance theorem;
no new full spatial coupling is claimed. The conductor scale is weaker
than the classical Burnol logarithmic-cutoff benchmark.

**Open:** vacancy tends to zero, equivalently the relevant arithmetic
saturation endpoint. Critical-line intensity zeros and lower bounds do not
exclude off-line zeta zeros or supply the signed-correction cancellation.

### Signed correction covariance and two-gap stabilization (2026-09-28)

**Established without RH.** `Analysis/NestedProjectionPairing.lean` proves
residual and nested-gap pairing inequalities using orthogonal projections.
Its RH consumer `RH/ResidueCorrectionCovariance.lean` proves:

- `correction_quadratic_le_residual_covariance`: for every signed test vector,
  the squared inverse-Gram correction pairing is at most the optimal residual
  energy times the full dual-residual Gram quadratic form, with constant 1.
- `correction_sq_le_inverse_diagonal_defect`: the scalar bound uses the
  uncaptured dual energy, not the full dual norm.
- `correction_error_sq_le_two_gaps` and
  `correction_error_sq_isLittleO_energy_excess`: the squared error to the
  actual correction limit is bounded by the product of primal and dual
  projection gaps and is little-o of the remaining primal energy.
- `dualProjectionGap_eq_inverse_excess`: the dual gap is the difference
  between the limiting captured dual norm squared and the finite inverse
  diagonal.
- `correction_limit_sq_le_dual_defect`: the surviving limit is bounded by
  limiting residual energy times limiting uncaptured dual energy.
- `correction_two_three_ellipse`: the explicit simultaneous bound is
  `20*k₂² + 4*k₂*k₃ + 14*k₃² ≤ 276*energy`, uniformly in the cutoff.

**Open:** the actual limiting corrections vanish for all conductors, or
equivalently the full inverse-Gram captured energy tends to one. No estimate
above supplies this saturation. Fixed-coordinate convergence and finite total
variation were already established and are not new contributions here.
These are direct Hilbert-space estimates, with no claim of mathematical novelty.
See `RH/InverseGramCorrectionCovariance20260928.md` for notation and proof.

### Both-column endpoint obstruction and subcritical coercivity (2026-09-28)

**Established without RH.** `RH/SmallDualCriticalZeros.lean` proves that the
critical-line Mellin zeros of each individual column h_2 and h_3 form at most
one conjugate pair. With the imported actual simple critical zeros, it gives
arbitrarily high nonzero witnesses for each column and a common witness for
both. `ArithmeticConductorCommonZeros.two_three_cpow_neg_injective` supplies
the underlying injectivity of the pair (2^(-s),3^(-s)).

`RH/ProjectedDualMassEndpoint.lean` proves
`exists_coefficient_mass_endpoint_lower_bound_both`, with no premises:
there exist a>0 and kappa>0 such that eventually, simultaneously for d=2,3,

    kappa <= Phi(n)^2 exp(-a Phi(n)) B_(n,d)^2.

Its conditional interface preserves any positive arithmetic exponent a
satisfying the displayed canonical-energy estimate. Consequences are strict
exponent divergence for BOTH columns and exclusion of endpoint little-o
with the quadratic profile loss along every cofinal subsequence.
`exists_projectedDualError_log_mass_lower_bound` gives the all-n tradeoff
L^2/8 <= Q_(n,d)^2 log(4(12+B_(n,d)+L)/L), for some L>0 and each d=2,3.

`Analysis/CriticalCutoffEndpoint.lean` isolates the scalar inequalities.
`Analysis/CriticalCutoffSharpness.lean` proves an explicit scalar model
satisfying the hypotheses with endpoint normalized mass exactly one. This
establishes the limitation of those scalar assumptions, not an asymptotic
formula for actual projected duals. Bounded exp(-a Phi)B^2 and the direct
signed physical-tail estimate remain **Open**; RH is not proved.

`RH/SubcriticalShapeCoercivity.lean` removes the old critical-zero premise:
one C>0 satisfies alpha(1-alpha)|A(n,c)|^2 <= C E_alpha(n,c) for every
0<alpha<1 and every legal complex trial. It gives finite-capacity bounds
C/[alpha(1-alpha)] and positive normalized energy gaps. If normalized trials
have vanishing complete energy and shapes stay bounded away from zero,
their shapes must tend to one. Their energy cannot be little-o of 1-alpha.
These are necessary conditions, not constructions of endpoint approximants.
See `RH/Zeta23Consequences20260928.md` for exact scope and provenance.

### Critical-line zeros and imported zero-proportion results (2026-09-28)

**Established without RH.** The pinned Zeta23 import now contains 140
upstream modules (57 existing plus 83 added). It exports the full
Riemann--von Mangoldt provider, Montgomery--Vaughan weighted Hilbert
inequality, prime-side trace estimates, and the unconditional proportions
`Zeta23.thmA₀`, `Zeta23.thmB₀_mult`, `Zeta23.thmC₀_mult`:
at least 2/3 distinct on-line, 2/3 simple on-line, and 5/6 distinct zeros.
The optimized-window forms `Zeta23.ThmD.thmD₀_simple_mult` and
`Zeta23.ThmD.thmD₀_dist_mult` retain the exact Montgomery--Taylor constants.
These are upstream results, not new results attributed to this project.

`RH/CriticalLineZeros.lean` derives:

- `simpleCriticalZeroCount_dyadic_tendsto_atTop`;
- `eventually_exists_simple_critical_zero_dyadic`;
- `exists_simple_critical_zero_above`;
- `exists_critical_zero`.

The last theorem has type
`∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ.re = 1/2`, with no premises.
Growth of the full zero count makes the proportion theorem nonvacuous.
Lean/Mathlib versions are unchanged. Only the selected upstream proof
closure is imported; Challenge placeholders, Dirichlet, XiPrime, and
PairCeiling developments are excluded. Provenance and import adjustments
are recorded in `RH/WeilExplicitFormula/PROVENANCE.md`.
The signed-pairing estimate needed for the Pareto RH route remains Open;
none of these proportion results proves RH.

### Unconditional coefficient-mass obstruction (2026-09-28)

**Established analytic components.** `RH/ParetoCriticalMellinCutoff.lean`
checks the literal critical-line bound
|M_s(f)|<=||f|| sqrt(R)+2 C exp(-R/2) for bounded physical f and R>0.
`RH/ProjectedDualMellinWitness.lean` proves that h_2,h_3 cannot both
have zero Mellin value in Re(s)>0, that finite-space Mellin values vanish
at a zeta zero, and that |P_n h_d(j)|<=B_(n,d).

`Analysis/StretchedCutoffRescaling.lean` proves
Phi(n)<=Phi(n/8)+log 16 and preserves the arithmetic energy exponent a
under the required finite conductor rescaling.
`Analysis/CriticalCutoffGrowth.lean` gives the general scalar growth
barrier from a nonzero cutoff value and a fourth-power error envelope.

**Kernel-checked conditional obstruction.** In
`RH/ProjectedDualMassObstruction.lean`,
`exists_coefficient_mass_stretched_barrier_of_critical_zero` supplies
a>0 from the checked arithmetic provider and proves that one fixed
d in {2,3} satisfies exp(-b Phi(n)) B_(n,d)^2 -> infinity for every b<a.
The explicit domain-specific premises are Re(s)=1/2 and zeta(s)=0.
The zero premise is now discharged by `RH.exists_critical_zero` in
`RH/ProjectedDualMassObstructionUnconditional.lean`.
Its `exists_coefficient_mass_stretched_barrier` has no premises:
it supplies a>0 and one fixed d in {2,3} with the same divergence for
every b<a. No quantitative or zero-existence provider remains open
for this obstruction. No RH assumption or new axiom is used.

`not_cofinal_stretched_coefficient_mass_of_critical_zero` and
`not_cofinal_stretched_l2_concentration_of_critical_zero` refute the
global strict-margin providers under that same premise, even allowing
each column a separate cofinal set and separate exponent b_d<a.
The declarations without the `_of_critical_zero` suffix discharge that
premise, preserving the displayed arithmetic-energy exponent.
The new endpoint result above retains a quadratic profile factor. Bounded
endpoint mass without that factor and the direct signed physical-tail
criterion remain **Open**, as does RH. Earlier sufficient
implications remain valid. See `RH/ProjectedDualMassObstructionAudit20260928.md`.

### Sharp Pareto shape threshold and endpoint uniformity (2026-09-28)

**Established without RH.** `RH/ParetoShapeThreshold.lean` proves
summability of the actual Mellin cell energy iff alpha < 2 Re(s),
for alpha>0 and Re(s)>0, also for normalized certificates after every
finite deletion. At the boundary it supplies an explicit harmonic lower
bound. Positive shape weights admit one-sided domination exactly in
the reverse shape order, and two-sided comparison exactly when shapes agree.

`RH/ParetoShapeEnergyBlowup.lean` strengthens this to divergence of the
actual full and normalized energies as alpha approaches 2 Re(s) from
below, after every finite cutoff. It uses the arbitrary-filter extension
in `Analysis/PointwiseEnergyDivergence.lean`.

`RH/ParetoShapeEndpoint.lean` proves continuity of complete legal energies
and identifies shape one with the original complex tail norm. One
coefficient-uniform normalized coercivity constant in any left
neighborhood of one exists iff the original Pareto(1) capacities are
bounded. Failure of all such constants implies RH without a density premise.

`RH/ParetoComparableWeights.lean` proves that two-sided comparable
positive weights preserve raw finite-energy domains, actual legal
approximation, and the quantitative off-line-zero obstruction. It covers
all weights comparable to inverse squares. Approximation implies RH.

**Conditional research reductions.** The weighted approximation-to-RH
equivalence still takes RH -> BaezDuarte.NaturalApproximation (**Open
formalization dependency**). Uniform near-one coercivity iff not RH
still takes RH -> closedSpace=top (**Open formalization dependency**).
`RH/SubcriticalShapeCoercivity.lean` now discharges critical-zero existence
using the integrated and kernel-checked Zeta23 provider. Its uniform
shape-dependent bound and moving-shape necessity are unconditional.
Certificate-energy divergence does not establish capacity divergence.
See `RH/ParetoShapeBoundaryFormalization20260928.md`.

### Schur asymptotics and finite dual approximation (2026-09-28)

**Established without RH.** `RH/ProjectedDualSchurAsymptotics.lean`
proves B_(n,d)^2=o(S_n), S_n=sum_(j<n) A_j^2, by splitting off a
summable coefficient-mode tail. It also proves A_j^2>=(j+2)/2 and
S_n>=n(n+3)/4. The latter bounds concern the absolute Schur majorant,
not the actual signed column. No absolute sub-stretched bound follows.

`RH/ProjectedDualProjectionError.lean` proves exact conductor control
for dilated canonical approximants, the arbitrary-cutoff mass tail bound,
and |<h_d-P_nh_d,D_m 1>|^2<=m B_(n,d)^2 ||T_N||^2/(N+1)
for 0<d<=N and m(N+1)<=n+1. Exact syntheses of h_2 and h_3 give
||h_2-P_nh_2||^4<=270 B_(n,2)^2 ||T_N||^2/(N+1) and the
corresponding constant 530 for d=3, with the stated conductor cutoffs.

**Obstruction now unconditional.** See the preceding entries and
`RH/ProjectedDualMassObstructionAudit20260928.md`.
The cutoff, witness, profile comparison, asymptotic assembly, and
critical-zero provider are checked. The earlier sufficient implications remain valid.

**Conditional research reduction; provider Open.** Direct signed
physical-tail control still suffices for residual zero and RH. Neither
that provider nor RH is proved by this continuation.

`RH/ResidueProjectionCorrectionTail.lean` now records
`correction_signed_shell_split`: for every finite shell the correction is
the signed shell pairing plus its exact later-tail pairing. The theorem
`signed_pairing_cofinal_forces_limit` uses the unconditional existence of
each fixed correction limit. Consequently
`riemannHypothesis_of_cofinal_signed_pairings` needs only arbitrarily late
small signed pairings for each fixed d>1, with no common subsequence.
This hypothesis is Open and equivalent in strength to vanishing of all
limiting corrections; the shell split itself supplies no decay estimate.
### Projected inverse-column l2 concentration and Schur accumulation (2026-09-28)

**Established bounds.** `RH/ProjectedDualColumnConcentration.lean` identifies
the actual signed inverse column and proves B^2<=n L, L<=projected-dual
energy times the complete inverse trace, and B^2<=2 Q(I), where
Q(I)=|I| sum_I c_k^2+|I-complement| sum_(I-complement) c_k^2.
A relative l2 leakage bound gives
B^2<=2[|I|+|I-complement| rho] L. Exact sparsity and weighted variants
retain their hypotheses explicitly. A nonzero correction limit forces
exp(-b Phi(n)) B^2 to diverge for every b<a.

`RH/ProjectedDualSchurMass.lean` proves exact rank-one column updates,
B_(n,d)<=sum_(j<n)|modeCoefficient(d,j)| A_j, and
A_j=(1+||eliminated j||_1)/residueModeScale j.
The Bessel bound leaves the factor sum_(j<n) A_j^2, proved to be >=n.
This is a limitation of that majorant, not a lower bound on B itself.
The reusable finite concentration inequalities are in
`Analysis/FiniteCoefficientConcentration.lean`.

**Conditional research reductions.** The strict-margin global budgets
are now refuted unconditionally by the zero-existence specialization above;
endpoint providers remain Open.
`limitResidual_eq_zero_of_cofinal_stretched_l2_concentration` requires
the leakage estimate and the joint budget exp(-b Phi(n)) kappa L<=K_d
at the same cofinal indices, b<a, separately for each d>1. It calls the
existing coefficient-mass criterion through a split-energy bound.
At the endpoint a, `limitResidual_eq_zero_of_cofinally_small_split_energy`
requires only cofinal smallness. The checked arithmetic-provider assembly
`exists_stretched_l2_concentration_rh_criterion` conditionally concludes
zero residual and RH. No unconditional sub-stretched column-mass,
concentration, or accumulated-Schur rate is obtained.
See `RH/ProjectedDualColumnConcentrationAudit20260928.md`.

### Moving projected-dual stretched tail bridge (2026-09-28)

**Established bounds and identities.** In `RH/ProjectedDualStretchedTail.lean`,
`projectedDualTailEnergy_eq_inverse_diagonal_sub_head` gives the exact
inverse diagonal minus physical-head formula;
`inverse_diagonal_eq_modeCoefficient_sq_sum` identifies the diagonal with
the finite orthonormal coefficient sum.
`projectedDualTailEnergy_le_coefficient_mass` bounds the complete tail by
B_(n,d)^2/(n+1), and `projectedDualCoefficientMass_eq_inverse_column`
identifies B with the actual inverse-Gram column l1 norm.
`correction_eventual_stretched_coefficient_mass_bound` gives the uniform
eventual bound delta_(n,d)^2 <= [8/(n+1)+C exp(-a Phi(n))] B_(n,d)^2.
`exists_projectedDual_stretched_barrier` proves that any nonzero fixed
correction limit forces n exp(-b Phi(n)) E_(n,d) -> infinity for every
b<a, where a>0 comes from the checked arithmetic energy provider.

**Conditional research reductions; quantitative projection providers Open.**
`exists_projectedDual_stretched_shell_bridge` proves that cofinal
smallness of n exp(-a Phi(n)) E_(n,d), separately for each fixed d>1,
forces zero residual and zero cumulative signed shell gains for every
weight and dyadic orbit. At b<a, cofinal boundedness suffices.
`limitResidual_eq_zero_of_cofinal_stretched_coefficient_mass` gives the
stronger sufficient inverse-column condition
exp(-b Phi(n)) B_(n,d)^2 cofinally bounded, b<a.
The strict-margin global coefficient-mass provider is now refuted
unconditionally. No physical-tail rate provider is supplied by the existing qualitative projection,
mode-summability, diagonal, or Schur results. RH remains Open.
See `RH/ProjectedDualStretchedTailAudit20260928.md`.

### Dyadic signed-shell criterion at the stretched scale (2026-09-28)

**Established identities.** In `RH/ParetoDyadicShellCriterion.lean`,
`hilbert_weighted_dyadic_shell_telescope` gives exact finite telescoping
for every Hilbert vector and real weight.
`residualSignedShell_eq_energy` identifies the full signed expression
<r,A_N-P_V1>_shell - <r,A_(2N)-A_N>_tail with actual residual shell energy.
The local projection pairing cannot be discarded by global orthogonality.

**Conditional research reductions; signed-gain provider Open.**
`cofinally_small_dyadic_tail_iff_signed_gain` exactly expresses the
cofinal-small tail condition as one-sided cumulative shell gain.
`limitEnergy_eq_zero_of_cofinal_dyadic_signed_gain` assembles this with the
stretched complete-energy bound at its full exponent.
`exists_stretched_signed_shell_criterion` proves that, for every
0<b<a at a checked universal a>0, zero residual is equivalent to
cumulative weighted signed gains being bounded below on a cofinal set of
dyadic endpoints. Individual gains need not be nonnegative.
No unconditional upper bound on residual tails or these gains is proved.
RH remains Open. See `RH/DyadicSignedShellAudit20260928.md`.

### Stretched transfer to sources, corrections, and residual tails (2026-09-28)

**Established without a new arithmetic hypothesis.**
In `RH/CanonicalMobiusStretchedCorrection.lean`:

- `canonicalMobiusResidual_eventual_uniform_atom_pairing` gives the
  uniform squared source bound 8/(N+1)+C exp(-a Phi(N)) for every residue
  modulus, using complete physical tails.
- `correction_eventual_stretched_tail_bound` gives, for N<=M and m<=N,
  delta_(M,m)^2 <= (8+C N exp(-a Phi(N))) T_N(P_M u_m).
- `projection_error_eventual_stretched_tail_bound` gives the corresponding
  finite optimal-error bound E_M^2 <= (8+C N exp(-a Phi(N))) T_N(1-P_M 1).
- `residueInverseEntry_diagonal_le_dual` records that every fixed inverse
  diagonal is bounded by the squared norm of its finite-support dual.

In `RH/ParetoStretchedAnnihilatorTail.lean`,
`exists_annihilator_stretched_tail_barrier` proves that a nonzero constant
pairing of an actual annihilator forces
N exp(-b Phi(N)) T_N(z) -> infinity for every 0<b<a, for a universal a>0.

**Conditional research reductions; tail providers remain Open.**
`limitEnergy_eq_zero_of_cofinally_small_stretched_tail` proves that
cofinally arbitrarily small N exp(-a Phi(N)) T_N(r) suffices for zero
limiting defect at the provider's original exponent.
`exists_riemannHypothesis_of_cofinally_small_stretched_residual_tail`
assembles the checked arithmetic provider and the existing forward RH bridge.
At a smaller positive exponent, cofinal boundedness already suffices
(`exists_riemannHypothesis_of_frequently_bounded_stretched_residual_tail`).
No such tail bound is supplied. Fixed correction vanishing and RH remain Open.
See `RH/StretchedInverseGramTransfer20260928.md`.

### Unconditional stretched canonical Möbius energy (2026-09-28)

**Established without an unresolved arithmetic hypothesis.**
In `RH/CanonicalMobiusStretchedEnergy.lean`:

- `canonicalMobius_energy_of_uniform_mertens_square` proves that
  |M(y)|<=h^2*y for all y>=N, with N>=1 and 0<h<=1/2, gives
  |m_N|<=5h and ||A_N||^2/N<=3/N+260h.
- `canonicalMobius_eventual_stretched_bounds` instantiates the finite
  transfer using the checked `M_stretched_loglog_bound` provider. For some
  a>0 and C>=0, eventually |m_N|<=C exp(-a Phi(N)) and
  ||A_N||^2<=3+C*N*exp(-a Phi(N)), where
  Phi(N)=((6+log N)*log(6+log N))^(1/11).
- `canonicalMobiusResidual_eventual_stretched_energy` gives the complete
  exact-head error bound ||1-A_N||^2<=8+C*N*exp(-a Phi(N)).
  The full infinite physical tail is included.

This strengthens the previous logarithmic normalized energy ceiling.
The factor N remains: cofinal bounded error, zero optimal projection
error, and identification of the limiting coefficient corrections
remain **Open**. See `RH/CanonicalMobiusStretchedEnergy20260928.md`.

### Báez-Duarte natural-dilation to Pareto closure translation (2026-09-27)

**Established normalization, without an analytic approximation hypothesis:**

- `RH/BaezDuarteCenteredBridge.centeredError_eq_hilbert_norm_sq` identifies
  the full centered Lebesgue squared error exactly with the existing Pareto
  Hilbert norm. Conductor one is zero; coordinate zero has zero Pareto mass.
- `RH/BaezDuarteNaturalApproximation.centeredError_le_ten_naturalError`
  proves an explicit universal centering bound on the complete natural error.
  `corrected_naturalError_eq` proves the exact reverse coefficient correction.
- `BaezDuarte.naturalApproximation_iff_one_mem` proves the full correspondence
  between finite natural-dilation approximation on (0,infinity) and
  `hilbertOne ∈ CoefficientStabilization.closedSpace`.

**Conditional research reduction:** `BaezDuarte.one_mem_of_riemannHypothesis`
and the updated `ProjectionSchur.projection_norm_iff_riemannHypothesis_of_baez_duarte`
take `RiemannHypothesis → BaezDuarte.NaturalApproximation` explicitly.
This is the RH-to-approximation direction of Báez-Duarte (2002), Theorem 1.1,
in its real finite-coefficient form. Its analytic proof is **Open as a Lean
formalization dependency**. The direct residue-closure assumption is replaced
by this precise continuous input plus the checked normalization bridge;
the external analytic input itself is not eliminated or installed as an axiom.

See `RH/BaezDuarteNaturalDensityTranslation20260927.md` and the updated
`RH/RHToDensityDependencyAudit20260921.md`.


### Positive cutoff necessity and fixed-subhalf certificate obstruction (2026-09-27)

**Established analytic necessity under explicit proof-certificate assumptions:**

- `Analysis/PositiveCutoffObstruction.regular_trial_positive_cutoff_exponents_necessary`
  proves beta<=1/11 and beta=1/11 implies eta<=1/11 for p(T)=b*T^beta*(log T)^eta.
  It assumes b,beta>0; c>=0; a fixed H>0; and eventually L>=0, A=3L+K>=1,
  exp(p-c*L^(1/10))/T<=H and A*exp(p(T)-p(r))/T<=1, where r=T-L-log 2.
  The delayed argument must satisfy r>1 and 2*|eta|<=beta*log r.
  The corollary `regular_trial_positive_cutoff_exponents_of_delay_tendsto`
  obtains this region automatically from r(T)->infinity; no regularity of L is assumed.
- `positive_cutoff_certificate_exact_deficit` retains the complete finite budget
  kappa*p*(p-log(T*H))^10 <= c^10*T*log(T/A), with its explicit nonnegativity,
  forcing-absorption, contraction and lower-shift assumptions. The regular-profile
  lower shift itself is proved in `Analysis/PowerLogProfileObstruction`.
- `rpow_log_rpow_eventually_bounded_iff` classifies the scalar power/log budget
  exactly. Its converse is not a converse for arbitrary recurrence certificates.
- `Analysis/PositiveAbelObstruction` proves the terminal positive majorant tends
  to infinity for every fixed positive linear weight and positive amplitude when
  the supplied phase is sublinear. `RH/DampedMobiusPositiveAbelObstruction`
  specializes this to the actual endpoint profile, preserves its index shift,
  and proves every fixed epsilon<1/2 eventually leaves the supported moving band.

**Scope:** these hypotheses constrain a one-step positive certificate, not the
actual arithmetic envelope. The zero envelope satisfies the recurrence with
arbitrarily fast upper bounds. Signed cancellation before the triangle inequality,
stronger arithmetic inputs, and other proof mechanisms are not excluded.
No new fixed-subhalf finite-energy theorem or RH conclusion is asserted.
See Sections 5-6 of `RH/MertensStretchedContinuation20260927.md`.

### Direct MediumPNT: optimized stretched-exponential Mertens and endpoint rates (2026-09-27)

**Established without a new arithmetic hypothesis:** let Phi(L)=(L*log L)^(1/11).

- `NumberTheory/PrimeNumberTheorem/MertensStretchedDecay.M_stretched_loglog_bound`
  proves positive d and B>=0 with |M(x)|<=B*x*exp(-d*Phi(6+log x)) for all real x>=1.
- `RH/DampedMobiusHalfHilbertLoglogStretchedRate.dampedMobius_half_cutoffs_loglog_stretched_rate`
  proves positive a and C>=0 with ||F_(1/2),M-f_(1/2)||<=C*exp(-a*Phi(L_M)),
  L_M=6+log(M+1), for every natural M. This includes the complete physical head and tail.
- `RH/DampedMobiusLoglogStretchedMovingBand.dampedMobius_loglog_stretched_subhalf_band_package`
  supplies one shared a>0,C>=0 and, for every fixed 0<=c<a, quantitative,
  sequential and uniform full norm/energy convergence in delta*L_M<=c*Phi(L_M),
  delta=1/2-epsilon>=0. The width is c*L_M^(-10/11)*(log L_M)^(1/11).

The direct exponential prime provider feeds a genuine supremum of future
Mertens tails. A uniform delayed contraction with cutoff
L=((T+6)*log(T+6))^(10/11) closes the earlier exponent-uniformity gap.
Signed Abel transfer preserves the optimized profile in weighted prefixes,
density tails, complete endpoint norms, and the moving-band estimate.
The principal arithmetic, endpoint and band-package axiom audits report
only propext, Classical.choice and Quot.sound.

**Scope:** the exponent pair (1/11,1/11) reaches the verified necessity boundary
for the positive one-step certificates and regular-profile region stated above.
Absolute arithmetic optimality and numerical constants are not asserted.
No finite energy at any newly supplied fixed epsilon<1/2 is proved.
All supported moving dampings approach one half; the RH gap remains Open.

See `RH/MertensStretchedContinuation20260927.md` for the explicit recurrence,
cutoff optimization, full propagation, verification record, and limitations.

### Every fixed logarithmic Mertens/endpoint rate and all fixed moving-band coefficients (2026-09-27)

**Established without a new arithmetic hypothesis:**

- `NumberTheory/PrimeNumberTheorem/MertensAllLogPowers.M_shiftedLog_all_powers`
  proves, for every fixed real a, an exponent-dependent B_a>=0 with
  |M(x)|<=B_a*x*(6+log x)^(-a) for every real x>=1.
- `RH/DampedMobiusHalfHilbertAllLogRates.dampedMobius_half_cutoffs_all_log_rate`
  proves, for every fixed real a, C_a>=0 with
  ||F_(1/2),M-f_(1/2)||<=C_a*(6+log(M+1))^(-a) for every natural M.
  The complete finite physical head and the infinite physical tail are both included.
- `RH/DampedMobiusAllLogMovingBand` proves full Hilbert norm and energy
  convergence uniformly in every band delta=1/2-epsilon>=0 satisfying
  delta*log(M+1)<=c*log(6+log(M+1)), for every fixed c>=0.

The finite bootstrap has no fixed logarithmic-exponent ceiling. It uses
J=floor(exp(sqrt(log N)))+1 and the logarithmic harmonic bound, then
inducts on the Mertens exponent. Every prime-error inverse-log power has
a checked provider from Quantitative.MediumPNT. The moving-band proof
uses centered Abel error splitting, avoiding the old scalar multiplier's
restriction that its endpoint exponent be below one.

**Scope:** there is no largest fixed logarithmic endpoint exponent or
fixed log-logarithmic band coefficient in these families. Constants and
thresholds in this intermediate family depend on the exponent. The new
uniform stretched-exponential result above is stronger and closes that
uniformity gap. No new fixed-subhalf finite energy or positive damping
sequence tending to zero is proved; the RH gap remains Open.

See `RH/MertensAllLogPowersContinuation20260927.md` for the exact finite
inequality, cutoff induction, downstream transfers, and the historical
uniformity gap subsequently resolved by the direct exponential bootstrap.

### Earlier quarter-log endpoint and moving-band estimates (superseded in strength)

**Established without an arithmetic hypothesis:** with L(M)=6+log(M+1),
`RH/DampedMobiusHalfHilbertRate.dampedMobius_half_cutoffs_log_rate`
proves ||F_(1/2),M-f_(1/2)|| <= C L(M)^(-1/4), for every M.
The finite physical head has squared error <=D(6+log M)^(-3);
the infinite physical tail contributes <=12K^2(6+log M)^(-1/2).
The quarter-logarithmic norm rate is sharp for the existing envelope
argument, not asserted optimal for the actual arithmetic error.

`Analysis/IncreasingAbelConvergence` now retains the exact centered
signed-prefix error budget. `Analysis/IncreasingLogWeights` bounds its
power-weight/log-profile variation uniformly in the undamping exponent;
`Analysis/MovingBandAsymptotics` proves the exact amplification/margin test.
`RH/DampedMobiusMovingSubhalfBand.dampedMobius_subhalf_quantitative_bound`
therefore gives, for delta=1/2-epsilon>=0, a single constant C with
||F_epsilon,M-f_(1/2)|| <= C (M+1)^delta L(M)^(-1/4).

Consequences: full Hilbert and energy convergence when
delta*log(M+1)-(1/4)*log L(M) -> -infinity; uniform error <=C L(M)^(c-1/4)
throughout every band delta*log(M+1)<=c*log L(M); uniform convergence
for c<1/4 or any divergent subtractive slack at the critical coefficient.
At the critical coefficient with a bounded additive margin, the complete
cutoff norms, signed Gram off-diagonals, and every signed physical head
have a uniform upper bound. Fixed-subhalf cutoff growth gains one quarter
logarithm over its existing power scale.

**Still Open:** actual finite energy at any newly supplied fixed
0<epsilon<1/2, and finite energy at positive dampings tending to zero.
Every supported moving damping approaches one half. The critical-band
boundedness theorem is not a fixed-subhalf membership theorem.
See `RH/QuantitativeEndpointContinuation20260927.md` for the exact proof,
provider audit, declaration table, and scope of the sharpness claim.

### Stronger signed cancellation transfers and moving subhalf band (2026-09-27)

**Established without an arithmetic hypothesis:**
`RH/DampedMobiusMovingSubhalfBand` proves full Hilbert convergence uniformly
throughout every shrinking band
0 <= 1/2-epsilon <= A/log(M+1), for fixed A>=0. The limit is the actual
half-damped vector. Complete cutoff energies converge, and full signed Gram
off-diagonals and every physical signed head have a common band-dependent bound.
The general increasing triangular Abel theorem is in
`Analysis/IncreasingAbelConvergence`. This does not prove fixed subhalf
membership: the moving damping tends to one half, not zero.

**Established analytic implications / conditional research reductions:**

- `Analysis/ScalarPrefixDensityTail` derives the reciprocal density tail
  from one signed scalar prefix estimate. Consequently
  `RH/ArithmeticFloorSinglePrefixConvergence` requires only a<epsilon
  in the power case, or one critical prefix logarithm b>1. The independent
  density-tail estimate is discharged by Abel summation.
- `Analysis/SignedCriticalDamping` and
  `RH/DampedMobiusCriticalSignedGrowth` replace the strict raw Hilbert
  growth exponent gap by the eventual critical bound
  ||F_0,M|| <= C M^epsilon / log(2M)^q, q>1. This gives full natural-order
  convergence and canonical finite energy.
- `Analysis/SignedDiniBoundedSubsequence`,
  `Analysis/SignedAveragedSquareDamping`, and
  `RH/DampedMobiusSignedDiniEnergy` give actual finite energy from
  sum_M ||F_0,M|| / M^(1+epsilon) < infinity, without a boundary-limit
  hypothesis. A logarithmically weighted square-average is another
  sufficient input. Dini finiteness at positive dampings approaching zero
  implies RH; no common bound across damping stages is assumed.
- `RH/DampedMobiusNormGrowthZeroFree` proves that a full signed cutoff
  bound ||F_alpha,M|| <= C M^theta, alpha,theta>=0, excludes zeros with
  1/2+alpha+theta < Re(rho) < 1. Varying the extra damping removes the
  single-shift common-zero loophole. Its contrapositive forces failure
  of every such growth bound when an eligible zero exists.

**Open arithmetic providers:** no verified fixed 0<epsilon<1/2 instance
of the new scalar-prefix, critical signed-logarithmic, or signed Dini
hypotheses is supplied. The unconditional moving band does not discharge
them. No new unconditional zero-free region or RH proof is claimed.
See `RH/SignedCancellationContinuation20260927.md`.

### General truncation and sharp exponent criteria (2026-09-27)

**Established analytic implications:** the argument of
`DampedMobiusHalfHilbertConvergence` is abstracted in
`ArithmeticFloorProfileCriterion`, `ArithmeticFloorPowerConvergence`, and
`ArithmeticFloorLogConvergence`. The limit's finite energy is a conclusion,
not an assumed premise. All bounds are uniform in the conductor and include
the infinite physical tail.

For 0<epsilon<=1/2, a signed prefix bound B*t^a and density tail D*t^(-d)
give full natural-order convergence when a<epsilon and d>1-epsilon.
`dampedMobius_cutoffs_converge_of_prefix_density_powers` states the actual
arithmetic specialization with both estimates explicit.

At a=epsilon,d=1-epsilon, prefix/tail logarithmic savings b,e>1 suffice.
The proved integer cutoff gives a physical saving min(b,e)/2>1/2.
See `dampedMobius_cutoffs_converge_of_critical_log_bounds` and
`arithmeticFloorHilbertPartial_tendsto_of_critical_two_log_bounds`.

Generic support is in `Analysis/HyperbolaExponentOptimization`,
`Analysis/HyperbolaLogOptimization`, `Analysis/PowerLogProfiles`, and
`RH/ArithmeticFloorHyperbolaPowerBounds`. The general profile criterion
retains a replaceable signed residue-head estimate. Exact power/log
feasibility tests are sharp for the separate positive majorants, not
necessary conditions for actual convergence.

**Conditional research reduction / Open arithmetic providers:** no fixed
0<epsilon<1/2 is supplied by the audited estimates. The newer normalized
subhalf norm and head-energy limits do not give a fixed power saving or an
unnormalized bound. Relative to a=1-epsilon,d=epsilon, the exact strict power
gain needed in both inputs is delta>1-2*epsilon; equality needs the stated
logarithmic saving. Scalar prefix conditions become too strong at very small
damping, so signed residue-head or Hilbert cancellation is needed toward zero.
Finite energy at positive dampings approaching zero remains RH-strength and
Open; a fixed damping is not identified with RH.
See `RH/TruncationExponentCriterion20260927.md`.

### Actual centered head growth below half damping (2026-09-27)

**Established without an arithmetic hypothesis:**
`RH/DampedMobiusCenteredHeadGrowth` proves, for every fixed 0<epsilon<1/2,
E_epsilon(H)/(H+1)^(1-2*epsilon)->0, where E_epsilon(H) is the energy of
the actual centered arithmetic sequence on n<H. The conductor has
already been completed; this result transfers the prior normalized
finite-conductor Hilbert energy theorem to physical-head growth.

`dampedMobius_centered_head_energy_le` compares the actual head energy
with 2*||F_epsilon,M||^2 plus (2/epsilon^2)*H*M^(-2*epsilon).
`Analysis/TwoScaleEnergyTransfer.two_scale_energy_tendsto_zero` uses
M=k*(H+1)+H, first fixing k and taking H to infinity, then increasing k.
Its generic hypotheses need q>0, C>=0 and E>=0, but not q<1 or A>=0.

`dampedMobius_completed_head_diagonal_normalized_tendsto` and
`dampedMobius_signed_head_limit_normalized_tendsto` also give vanishing
normalized completed diagonal and absolute completed signed-head limit.
Absolute values are taken after the full signed sum.

**Open:** bounded unnormalized subhalf centered energy and the positive
damping providers approaching zero needed by the RH reductions.
The growing normalization does not establish finite energy or RH.
See `RH/CenteredHeadGrowth20260927.md`.

### Normalized signed cancellation below half damping (2026-09-27)

**Established without an arithmetic hypothesis:**
`RH/DampedMobiusSubhalfNormalization` proves, for every real epsilon<1/2,
that the full signed vector divided by (M+1)^(1/2-epsilon) tends to zero
in Hilbert norm. Its squared norm, actual finite diagonal, and full signed
off-diagonal, divided by (M+1)^(1-2*epsilon), each tend to zero.

`dampedMobius_subhalf_normalized_signed_heads_uniform` proves vanishing
absolute normalized signed heads uniformly in EVERY physical cutoff H.
The absolute value follows the complete signed sum. Arbitrary moving H_j
are allowed whenever M_j diverges; no relative-rate condition is needed.

At zero damping, `rawMobius_norm_div_sqrt_tendsto` proves
||F_0,M||/sqrt(M+1)->0 and `rawMobius_energy_div_cutoff_tendsto`
proves ||F_0,M||^2/(M+1)->0. Both control the entire infinite physical tail.

`Analysis/VectorKronecker` proves the general increasing-weight signed
prefix and tail estimates and the vector Kronecker lemma. The arithmetic
specialization uses the checked half-endpoint natural-order convergence
and an exact inverse-power atom factorization. It assumes no RH or
unproved cancellation estimate.

**Open:** bounded unnormalized subhalf energy and the positive-damping
bounds approaching zero. The growing normalization does not supply
finite energy or a fixed power saving below the raw exponent 1/2.
No new zero-free region or unconditional RH is claimed.
See `RH/SubhalfNormalization20260927.md`.

### Uniform damping range and endpoint norm continuity (2026-09-27)

**Established without an arithmetic hypothesis:**
`RH/DampedMobiusUniformHalfRange.dampedMobius_half_range_uniform_approximation`
proves one full Hilbert approximation modulus for every epsilon>=1/2:
for each eta>0 there is K such that ||F_epsilon,M-g_epsilon||<=eta
for all epsilon>=1/2 and M>=K. This includes the infinite physical tail.

`dampedMobius_half_range_uniform_energy_and_signed_bounds` supplies
one B for every epsilon>=1/2, bounding the actual energy, every full
signed Gram off-diagonal, and every signed physical head at all H,M.
The constant is independent of damping as well as both cutoffs.

`dampedMobius_joint_damping_cutoff_tendsto` permits epsilon_j>=1/2
to approach 1/2 and M_j to diverge at any independent rates.
`dampedMobius_limit_tendsto_half` and
`dampedMobius_energy_tendsto_half` prove norm and actual energy
continuity at the endpoint. No monotonicity of epsilon_j is required.
Even without a damping limit, `dampedMobius_varying_damping_error_tendsto`
proves vanishing approximation error whenever M_j diverges.

The generic positive decreasing-weight argument is in
`Analysis/MonotoneAbelConvergence`. It preserves signed prefix and
tail bounds by exact Abel summation and supplies uniform Cauchy and
approximation moduli; absolute summability is not required.

**Open:** subhalf arithmetic finite energy and positive-damping
bounds approaching zero. For epsilon<1/2 the extra conductor weights
increase, so this transfer does not give descent or prove RH.
See `RH/UniformHalfRange20260927.md`.

### Full natural-order Hilbert convergence at half damping (2026-09-27)

**Established without an arithmetic hypothesis:**
`RH/DampedMobiusHalfHilbertConvergence.dampedMobius_half_cutoffs_converge`
proves full Hilbert norm convergence at epsilon=1/2 to the canonical
centered arithmetic sequence. This includes the infinite physical tail.
`dampedMobius_cutoffs_converge_of_half_le` covers every epsilon>=1/2.

The decisive new provider is
`dampedMobius_half_partial_uniform_log_bound`: every conductor cutoff M
obeys a common K*sqrt(n)/(6+log n)^(3/4) envelope for log(n)>=200,
without a relation between n and M. Truncation preserves the signed
prefix and density-tail estimates; the existing hyperbola theorem and
full weighted dominated convergence discharge the missing tail control.

**Stronger signed results for epsilon>=1/2:**
`dampedMobius_full_offDiagonal_tendsto_of_half_le` proves that the full
Gram off-diagonal tends to E_epsilon-Delta_epsilon.
`dampedMobius_offDiagonal_unrestricted_joint_tendsto` proves the same
head limit for arbitrary diverging H(j),M(j), removing H(j)<=M(j).
`dampedMobius_signed_bounds_of_half_le` supplies one finite upper bound
for every full Gram cutoff and every pair of physical/conductor cutoffs.

Generic components are in `RH/ArithmeticFloorTruncationBounds` and
`RH/ParetoDominatedConvergence`; logarithmic-profile monotonicity extends
`Analysis/WeightedMertensTransfer`, and the signed prefix provider
extends `RH/DampedMobiusHalfEndpoint`.

**Open:** actual subhalf finite energy and signed bounds at positive
dampings approaching zero. Natural-order endpoint convergence does not
assert an unordered Hilbert `tsum` or absolute off-diagonal summability.
No unconditional RH or new zero-free region is claimed.
See `RH/HalfHilbertConvergence20260927.md`.

### Joint signed-head convergence through the half endpoint (2026-09-27)

**Established without an arithmetic hypothesis:** `RH/DampedMobiusJointHeadLimits`
proves, for every epsilon>=1/2, that the signed off-diagonal
O_epsilon(H(j),M(j)) tends to E_epsilon-Delta_epsilon whenever both
cutoffs diverge and H(j)<=M(j) eventually. Equal cutoffs are allowed.
`dampedMobius_equal_cutoff_signed_bound_of_half_le` supplies an actual
unconditional bound on O_epsilon(H,H) for every H.

The endpoint density tail has the proved saving
D*M^(-1/2)*(6+log M)^(-3/2). The exact signed head-error identity therefore
gives square error <=K*(6+log M)^(-3) for H<=M and M>=1, which tends to
zero at the formerly critical equal-cutoff scale. The strict half range
uses the elementary M^(1-2*epsilon)/epsilon^2 bound. The existing endpoint
and strict-range finite-energy providers discharge every domain premise.

`RH/DampedMobiusExactSignedHeadLimits.dampedMobius_headDiagonal_joint_tendsto`
also proves diagonal convergence for every epsilon>0 at arbitrary
diverging cutoffs, without a relative-rate condition.
`Analysis/FiniteWeightedEnergyComparison` now supplies weighted
Cauchy--Schwarz and moving-energy convergence from vanishing square error.

**Conditional transfer / Open arithmetic obligation:** the general
`dampedMobius_offDiagonal_joint_tendsto_of_head_error` retains actual
finite energy and vanishing head error as hypotheses. Subhalf membership
and the signed bounds at positive dampings approaching zero remain
**Open**. Full natural-order endpoint convergence is now established in
`RH/DampedMobiusHalfHilbertConvergence`, which also removes the cutoff-order
restriction. No subhalf membership or absolute signed summability is claimed.
See `RH/JointSignedHeadLimits20260927.md`.

### Actual diagonal and exact iterated signed-head limits (2026-09-27)

**Established for every epsilon>0:**
`RH/DampedMobiusExactSignedHeadLimits` constructs the summable actual
diagonal Delta_epsilon=sum_d ||u_{epsilon,d}||^2 and proves
Delta_epsilon <= 2*sum_d d^(-1-2*epsilon). On each finite physical head H,
the signed residue-cutoff limit exists and equals
E_epsilon(H)-Delta_epsilon(H). The completed head diagonal tends to
Delta_epsilon by dominated convergence for series.

**Exact energy identity:** under the explicit actual finite-energy
premise, lim_H lim_M O_epsilon(H,M)=E_epsilon-Delta_epsilon.
The residue cutoff M tends to infinity first. No reversed order or
absolute signed double-series summability is asserted. The endpoint
provider discharges the energy premise for every epsilon>=1/2.
For subhalf damping that premise remains **Open**.

The sparse moving-head theorem now has the sharper conclusion
E_epsilon <= Delta_epsilon+B, replacing the coarse p-series budget.
Its signed upper-bound hypothesis and all downstream RH obligations
remain explicit. No new unconditional subhalf membership is established.
See `RH/ExactSignedHeadLimits20260927.md` for the proofs and verification.

### Sparse signed-head transfer and damping accumulation (2026-09-27)

**Established transfer and divergence implications:**
`RH/DampedMobiusSparseHeadDichotomy` proves that at any epsilon>0 and
residue cutoff M(H) tending to infinity, a signed off-diagonal bound B
at arbitrarily large physical heads supplies actual centered finite
energy E_epsilon <= Delta_epsilon+B with the actual arithmetic diagonal. There is no factor-two
loss or head-error term. M need not be monotone, polynomial, or at least H.
The signed bound is an explicit hypothesis, not an arithmetic estimate.

Failure of finite energy forces the signed off-diagonal to tend to
positive infinity for every cofinal cutoff. For M(H)=(H+1)^k with
2*k*epsilon>=1, finite energy is equivalent to a signed upper bound at
arbitrarily large H, hence to the existing all-head condition.

**Conditional zero-free and RH reductions:** sparse signed bounds at
arbitrarily large damping indices epsilon_j>a tending to a>=0 exclude
zeros in 1/2+a<Re(s)<1, without uniform constants in j. At a=0 they imply RH.
`riemannHypothesis_of_sparse_reciprocal_polynomial_signed_heads` needs
only arbitrarily large j with a finite B_j bounding
O_{1/(j+3)}(H,(H+1)^(j+3)) at arbitrarily large H.
This signed hypothesis remains **Open** and RH-strength.
No new fixed subhalf finite-energy provider is established.

The verified not-RH implication forces divergence at every sufficiently
small positive damping and every cofinal residue cutoff. That divergence
has not been excluded. See `RH/SparseSignedHeadDichotomy20260927.md`
for complete proofs, provenance, and verification evidence.

### Explicit polynomial signed heads and ordered vector damping (2026-09-27)

**Established unconditional estimates:** `RH/DampedMobiusHeadApproximation`
proves the reciprocal-density tail bound M^(-epsilon)/epsilon for every
epsilon>0, then applies the existing exact signed-head identity to prove
head error <= H*M^(-2*epsilon)/epsilon^2. No absolute Hilbert-series
convergence is assumed. `Analysis/NaturalPowerCutoff` proves that
M=(H+1)^k, 2*k*epsilon>=1 makes H*M^(-2*epsilon)<=1.
`Analysis/FiniteWeightedEnergyComparison` supplies both finite energy
comparisons with twice the signed-error energy.

**Exact conditional research reduction:**
`RH/DampedMobiusPolynomialHeadCriterion` proves fixed-damping energy iff
exists B, forall H, signedHeadOffDiagonal(epsilon,H,(H+1)^k)<=B.
The approximation error and diagonal budget are discharged unconditionally.
The uniform signed off-diagonal bound remains **Open** at any specified
fixed 0<epsilon<1/2. The numerical hypothesis
forall j, exists B_j, forall H,
signedHeadOffDiagonal(1/(j+3),H,(H+1)^(j+3))<=B_j
implies RH via `riemannHypothesis_of_reciprocal_polynomial_signed_head_bound`.
No uniformity across j is required. This hypothesis is **Open** and
RH-strength; no unconditional RH theorem or new subhalf membership is claimed.

**Established analytic transfer, unresolved arithmetic provider:**
`Analysis/SignedPowerDampingAbel` proves a Banach-valued finite Abel identity
and ordered convergence from signed-prefix variation and boundary decay.
Signed prefix growth ||S_N||<=C*N^theta suffices for every positive
epsilon>theta. `RH/DampedMobiusSignedAbelGrowth` constructs the actual
damped Hilbert limit from that complete raw residue norm bound and
identifies canonical centered finite energy. The raw power-growth premise
needed for subhalf damping remains **Open**. Ordered convergence is not
asserted to be unconditional summability of the original vector series.

The literature audit in `RH/PolynomialSignedHeadResearch20260927.md` records
the separated-scale ranges of Maier--Rassias, the shrinking-boundary gap
in Conrey--Myerson, and the RH premise of Bettin--Conrey--Farmer. These
published results were not introduced as axioms. The half endpoint and
the already proved sharp power/log obstruction were not redone.

### Signed cancellation below the Burnol half endpoint (2026-09-27)

**Established in Lean:** `Analysis/PowerLogSquareObstruction` proves the
subcritical power/log majorant is nonsummable for every real fixed log
exponent, including the exact Pareto weight. At the power threshold the
logarithmic majorant is summable iff q > 1/2. This is a majorant obstruction,
not divergence of the actual arithmetic energy.

**Established unconditional bridge:** `RH/DampedMobiusSignedGram` proves
squared residue-atom norms have a summable majorant 2*d^(-1-2*epsilon)
for every epsilon > 0. The exact cutoff Gram identity retains all signed
distinct-pair terms. `RH/DampedMobiusSignedHeadClosure` proves scalar
coordinate convergence at every positive damping and an exact fixed-head
error identity: the entire omitted signed tail combines into one density
error before squaring.

**Conditional research reduction:**
`centered_damped_energy_iff_signed_head_bound` identifies actual centered
finite energy at one fixed positive epsilon with
exists B, forall H, eventually M, signedHeadOffDiagonal(epsilon,H,M) <= B.
The cutoff threshold may depend on H; B may not. The uniform diagonal
estimate is discharged. The common signed off-diagonal bound is **Open**
for any chosen fixed 0 < epsilon < 1/2.

**Strength audit:** `RH/BurnolFixedDampingObstruction` proves fixed-energy
zero propagation and that an off-line zero prevents finite energy at every
sufficiently small positive damping, for every center. One fixed damping
has no RH equivalence established here; a positive sequence tending to
zero is RH-strength. The stronger existing raw subpower, growing signed
covariance, and single fixed-head capacity criteria already imply RH.
No numerical descent below one half is claimed.

The combined new-source check returned exit_code=0, verified=true, without
warnings. Six principal axiom reports contain only propext,
Classical.choice, Quot.sound. See `RH/SignedCancellationAudit20260927.md`
for the source audit, exact definitions, and quantifier order.

### Burnol half-damping endpoint and quantitative arithmetic strengthening (2026-09-27)

**Established in Lean:** `RH/DampedMobiusHalfEndpoint` closes the actual
centered arithmetic/Pareto finite-energy obligation at epsilon=1/2.
Published in commit `d4e06595e09075250bc2c2c49399dcd0b3cd6767`.
`dampedMobius_half_endpoint` proves both full weighted square summability
and an unconditional bound
|A_{1/2}(N)-N*Re(1/zeta(3/2))| <= K*sqrt(N)/(6+log(N))^(3/4)
for positive N with log(N)>=200.
`centered_dampedMobius_square_summable_iff_of_half_le` characterizes the
unique center Re(1/zeta(1+epsilon)) throughout epsilon>=1/2.

**Established arithmetic provider:** `NumberTheory/PrimeNumberTheorem/
MertensShiftedGlobal.M_shiftedLog_threeHalves_bound` derives
|M(x)| <= B*x*(6+log(x))^(-3/2) for every real x>=1 from the existing
unconditional quantitative PNT. `MobiusLogBootstrapFinite` retains exact
signed Mobius-von-Mangoldt convolution terms and proves the finite estimate;
`MertensBootstrapCutoffs` and `MertensLogThreeHalvesAssembly` optimize it.
Their provider-facing bounds display all quantitative hypotheses.

**Generic strengthening:** `Analysis/WeightedMertensTransfer` and
`Analysis/WeightedMertensTail` prove signed-coefficient Abel bounds with
constants 3B and 5B. `RH/ArithmeticFloorHyperbola`,
`ArithmeticFloorHyperbolaBounds`, and `HyperbolaLogCutoff` retain the exact
centered decomposition and optimize the complete discrepancy, without
multiplicativity or positivity assumptions on the weights.
`RH/ParetoLogEnergyCriterion` proves energy summability from any eventual
sqrt(N)/(log N)^q bound with q>1/2.
`RH/DampedMobiusEnergyClosure` proves a coordinatewise Fatou transfer;
its common finite-head energy bound remains an explicit premise. The actual
half-endpoint proof does not assume that bound.

Statement source: Burnol, Acta Cientifica Venezolana 54 (2003), 210-215,
Lemma 4.1, https://arxiv.org/abs/math/0202166. This formalization uses an
arithmetic proof through the existing PNT+ compatibility port. The pointwise
bound strengthens the qualitative statement; no literature novelty is claimed.

**Open RH obligation:** actual finite energy at positive epsilon_j tending
to zero. The inclusive range epsilon>=1/2 does not discharge this obligation.
Further fixed logarithmic gains alone leave a divergent proposed majorant
below one half; that does not establish divergence of actual energy.
The conditional Burnol RH reduction remains conditional.

The combined kernel check passed with exit code 0, verified=true, and only
propext, Classical.choice, and Quot.sound in the three principal dependency
reports. See `RH/BurnolHalfEndpointFormalization20260927.md`.

### Published Burnol strict-range finite energy and quantitative synthesis (2026-09-27)

**Established in Lean:** `RH/ArithmeticFloorHilbertSeries` constructs the
actual centered floor prefix for arbitrary real weights w satisfying
sum |w(n)|/sqrt(n) < infinity (n >= 1). It proves scalar-density summability,
absolute Hilbert-series summability, exact coordinates
A_w(k)-k*C_w, a full norm bound, and exact signed truncation tails.
No sign condition, multiplicativity, or Mobius cancellation is assumed.
`square_summable_centering_unique` proves that finite energy fixes the
linear centering of any real sequence uniquely.

**Established in Lean:** `RH/DampedMobiusFiniteEnergy` discharges the
actual centered Mobius square-summability obligation for every epsilon>1/2.
`centered_dampedMobius_square_summable_iff` characterizes all centers:
the weighted squares are summable iff
C = Re(1/zeta(1+epsilon)). `dampedMobius_finiteEnergy_with_bound`
constructs the Hilbert vector with a full infinite norm bound.
`centered_dampedMobius_normalization` proves C*zeta(1+epsilon)=1
from actual finite energy at every epsilon>0, including the still-open
small-damping range; it does not assert existence there.

**Quantitative extension:** `dampedMobius_finiteEnergy_tail_bound`
proves the complete Hilbert truncation error is at most
sqrt(2)*N^(1/2-epsilon)/(epsilon-1/2), for N>=1.
The general integral-test bound is `Real.tsum_nat_rpow_tail_le` in
`Analysis/PSeriesTail`.

Source for the absolute-convergence strategy: J.-F. Burnol,
Acta Cientifica Venezolana 54 (2003), 210-215, Section 4,
Lemma 4.1 in https://arxiv.org/abs/math/0202166.
This is the discrete counterpart of the lemma's strict epsilon>1/2 part.
The published lemma also includes epsilon=1/2; that endpoint is now
**Established** by `dampedMobius_half_endpoint` in the half-damping development
above. `centered_dampedMobius_square_summable_iff_of_half_le` extends the
unique-centering characterization to every epsilon>=1/2; the explicit
truncation bound above still requires epsilon>1/2. The arbitrary-weight and explicit-tail
statements are standard generalizations/corollaries, with no novelty claim.

**Open RH obligation:** finite energy for the actual centered prefixes
at positive epsilon_j tending to zero. Even the completed inclusive
epsilon>=1/2 range does not supply such a sequence. The prior conditional Burnol RH
reduction remains conditional, and the reverse RH-to-membership
direction remains unformalized here.
The combined candidate passed with exit code 0, verified=true, and only
propext, Classical.choice, and Quot.sound in the principal axiom reports.
See `RH/BurnolStrictRangeFormalization20260927.md`.

### Actual damped Mellin identity and finite-energy continuation (2026-09-26)

**Established in Lean:** `RH/DampedDivisorLSeries` identifies the actual
damped divisor Dirichlet series with zeta(s)/zeta(s+epsilon) on its common
absolute-convergence domain. `RH/DampedMobiusMellinArithmetic` proves the
actual centered floor-prefix Mellin identity for Re(s)>1, with arbitrary
real centering. Neither statement assumes PNT or RH.

**Established in Lean:** `RH/ParetoMellinFiniteEnergy` proves
`paretoMellin_tendstoUniformlyOn_of_tendsto`,
`paretoMellin_differentiableAt`, and `paretoMellin_analyticOnNhd`.
Every actual Pareto Hilbert vector has a holomorphic Mellin transform on
Re(s)>1/2; the former bounded-coordinate assumption is removed.

**Established in Lean:** `RH/BurnolMellinContinuation` continues the
cross-multiplied identity through the former poles using entire conductor
factors. It proves forced normalization C*zeta(1+epsilon)=1 and propagation
of eligible actual zeta zeros. The analytic function and its initial
identity are explicit premises of these general analytic lemmas.
Source: Burnol, arXiv:math/0202166, Lemma 4.3 and Theorem 4.2.

**Conditional research reduction:** `RH/BurnolFiniteEnergyReduction`
assembles those premises from actual centered arithmetic Hilbert vectors.
`riemannHypothesis_of_centered_damped_square_summable` assumes only a
positive sequence epsilon_j tending to zero and, at each stage, some real
C_j for which the actual weighted square sequence
positiveWeight(n)*(dampedMobiusPrefix(epsilon_j,n)-n*C_j)^2 is summable.
It concludes Mathlib's `RiemannHypothesis`. No common norm bound is needed.
The scalar-to-Hilbert realization is proved, not assumed.

**Open:** this small-positive-damping arithmetic summability. The arithmetic
Mellin identity, finite-energy holomorphy, and continuation steps are now
formalized, but they do not prove the membership premise. The subsequent
`RH/DampedMobiusHalfEndpoint` development proves membership throughout
epsilon>=1/2, including the endpoint; it does not supply positive dampings
tending to zero. The reverse
RH-to-membership direction is not formalized here. No unconditional RH
proof is claimed. The combined candidate passed with `verified=true`,
exit code 0, and only standard foundational axioms in the five principal
dependency reports. See `RH/NymanBeurlingFiniteEnergyContinuation20260926.md`.

### Joint damping limits and Burnol zero-shift obstruction (2026-09-26)

**Established in Lean:** `Analysis/OrderedPrimitiveAbel` adds
`primitive_abel_diagonal_partialSum_tendsto`: dominated primitive variations
control arbitrary simultaneous cutoffs. `RH/DampedMobiusOrderedPairing`
adds `dampedPhysicalWeight_diagonal_primitive_boundary` and
`dampedPhysical_joint_ordered_pairing_tendsto`. The latter allows every
physical cutoff sequence tending to infinity as damping and centering tend
to zero, under the existing summable primitive majorant and sublinear
boundary assumptions. No coordination of convergence rates is required.

**Established in Lean:** `RH/BurnolDampingZeroShift` proves punctured
zero-free neighborhoods for Mathlib's actual zeta function away from its
pole, nonvanishing at all sufficiently small positive left shifts, and
the resulting right-half-strip zero-shift obstruction. Source for this
proof strategy: Burnol, arXiv:math/0202166, Corollary 4.1 and Theorem 4.2.

**Conditional research reductions:** cofinal zero propagation and
propagation along a positive damping sequence tending to zero imply
Mathlib's `RiemannHypothesis`. Both conclusions retain their explicit
`hprop` premise. The arithmetic Mellin continuation deriving propagation
from square-integrability is supplied by the new modules above. Small-damping
square-integrability for the actual arithmetic family remains **Open**.
The joint pairing theorem does not discharge the actual residual's
primitive regularity, critical Hilbert membership, or legal-series
interchange obligations; these remain **Open**.

The combined candidate passed with exit code 0 and `verified=true`;
the principal dependency checks contain only `propext`,
`Classical.choice`, and `Quot.sound`. Publication requires the project
checkpoint. No unconditional RH proof is claimed.
See `RH/JointDampingAndBurnolZeroShift20260926.md`.

### Ordered damping, finite certificates, and next-atom source prediction (2026-09-24)

**Established in Lean:** `Analysis/OrderedPrimitiveAbel` proves natural-order
Abel pairing limits without assuming absolute summability of the physical
series, including a variation-majorant and damping-limit theorem.
`RH/DampedMobiusOrderedPairing` supplies the actual power-damped physical
specialization, its endpoint bound, and the correctly ordered iterated
physical-cutoff/damping limits. No Hilbert membership of the damped
approximant is assumed.
`RH/FiniteDilationInnovationCertificates` proves finite signed certificate
orthogonality, exact pairing w_Q, Cauchy--Schwarz innovation bounds, and an
eventual lower bound with the actual arithmetic limiting energy retained.
`RH/DivisorBoxLocalEnergy` proves the exact local geometric polynomial and
prime-square specialization; the global Euler product is not formalized.
`RH/ScreeningSourcePrediction` identifies the actual source exactly:
E_M*s_M = (M+2)*inner(rho_(M+2),P_M e1)-1/2. Normalization recovers s_M.

**Conditional research reduction:** nonsummability of the actual normalized
prediction errors squared with harmonic weight implies RH. This arithmetic
nonsummability remains **Open**. The actual residual Dini envelope and
squarefree-divisor weighted primitive criterion also remain **Open**.

**Audited prose, not fully formalized:** a squarefree-divisor weighted
primitive criterion removes the monotone envelope and separate sublinear
primitive assumption. A consecutive-dilation certificate has exact limiting
energy 1 plus a truncated Mobius tail, tending to one by divisor-square
summability. Its global Gram-reversal/provider assembly is not yet in Lean.
The full fixed-damping legal-series interchange and zeta-mode identification
remain formalization tasks. These implications do not discharge an actual
RH-strength provider. Unconditional RH was not proved.
See `RH/OrderedDampingAndSourcePrediction20260924.md`.

### Power damping, finite dilations, and exact source masses (2026-09-24)

**Established in Lean:** `RH/DampedMobiusPrimitiveVariation` proves exact
increments and pointwise convergence of genuine damped Mobius physical sums,
a uniform weighted variation bound 2/((n+1)(n+2)), and convergence of the
primitive-side pairing series under its explicit summable majorant. It does
not assume Hilbert membership of an infinite damped approximant.
`RH/FiniteDilationMobiusKernel` and `RH/FiniteDilationReciprocalCharge` prove
unconditional quotient energy and physical norm limits for every finite
signed positive integer-dilation family, using an explicit common-multiple
reversal and proved PNT/size inputs.
`RH/ScreeningSourceMass` proves E_M^2*s_M^2/B_M=E_M-E_(M+1), the exact HasSum
E_1-E_infinity, and that nondensity forces sum s_M^2/H_(M+1) to converge.
Nonsummability of the latter is a verified **conditional RH reduction**;
its actual arithmetic provider remains **Open**.

**Mathematical proofs, not fully formalized:** preserving power-damped signed
Mobius cancellation lowers the centered primitive sufficient logarithmic
exponent from p>2 to p>1. The fixed-epsilon absolute interchange and constant
zeta-mode limit are proved in prose, not assumed in a Lean RH theorem.
Divisor-box Euler products complete the all-dilation innovation lower-limit
bound of 1 in prose; the generic finite physical limit is verified but that
Euler-product specialization is not yet formalized.
The actual residual Dini envelope and source divergence remain **Open**.
Unconditional RH was not proved.
See `RH/PowerDampingAndAllDilationContinuation20260924.md`.

### Exact screening bridge and centered primitives (2026-09-24)

**Established in Lean:** `RH/ReciprocalChargeGeometricInnovation` proves the
geometric dyadic charge energy limit (12+3*4^(-L))/pi^2, its exact unit pairing
with the full adjacent innovation, and eventual full innovation energy > c
for every c < pi^2/12.
`RH/CanonicalMobiusScreeningBridge` proves the actual identities
B_M = D_M + E_M*s_M^2 and D_M = B_M*E_(M+1)/E_M, with the full signed source
and complete tail retained. It transfers the dyadic bound to the actual tail
denominator with this error ratio. Nondensity implies the ratio tends to one
and the actual denominator is eventually > c for every c < pi^2/12.
`RH/NaturalMobiusCenteredPrimitiveTests` proves the exact physical-primitive
formula H_f(N)-L*N = 2*sum_(j<N)(tailAverage f j-L)-N*(tailAverage f N-L),
and extends the PNT pairing tests to centered physical primitives.

**Conditional RH reduction:** the centered physical primitive bound
|H_r(K)-L*K| <= C*(K+1)/log(2*(K+1))^p, p>2, for the actual residual remains
**Open**. Actual signed source accumulation sum s_M^2/D_M = infinity also
remains **Open**. The all-integer dilation extension to a full innovation
lower limit of 1 is an informal mathematical argument, not a new Lean result.
Unconditional RH was not proved.
See `RH/LateralScreeningContinuation20260924.md`.

### Lateral arithmetic synthesis: charges, projections, and logarithmic tests (2026-09-24)

**Established in Lean:** `RH/ReciprocalChargeDyadicAverages` proves the exact
limiting energy (3L+15)/(pi^2 (L+1)^2) of the mean of L+1 dyadic charge vectors,
retaining negative neighboring correlations.
`RH/ReciprocalChargeInnovations` proves exact charge/adjacent-step
biorthogonality, orthogonality to the preceding finite legal space, and the
full-space innovation energy bound >=1/42.
`RH/CanonicalMobiusSourceProjection` identifies the actual capacity normal
scaled by first-head error with the negative projection-residual tail.
`NumberTheory/DivisorCountLogSummability` proves the divisor-weighted
logarithmic series converges for p>2.
`RH/NaturalMobiusLogarithmicTests` extends the PNT test class to physical
primitive growth C(K+1)/log(2(K+1))^p.

**Conditional RH reduction:** the new logarithmic RH implication retains
this explicit bound for the actual limiting residual as an **Open** input.
Dual norm cancellation and full-space innovation positivity do not prove
capacity divergence. Unconditional RH was not established.
See `RH/LateralArithmeticSynthesis20260924.md`.


### Exact arithmetic gain cancellation and harmonic bound (2026-09-24)

**Established in Lean:** `RH/CanonicalMobiusWindowGainBounds` cancels the
nonzero reciprocal Mobius factor from both terms of the actual one-step
capacity quotient. The screened adjacent-step energy is positive and at most
`H_(M+1)`, giving gain >= signed-source^2 / H_(M+1) and an accumulated
finite lower bound on the actual window capacity.
`Analysis/FiniteGramScreeningCalculus` supplies the general screening algebra.
`RH/RawMobiusPrimitivePeriodMean` identifies the complete signed primitive
remainder's period mean exactly with the Jordan variance, including the
upper-half prime-count lower bound.
Source-sum divergence and the actual RH upper bounds remain **Open**.
See `RH/ArithmeticGainRepair20260924.md`.

### PNT and dichotomy compatibility audit (2026-09-24)

**Established in Lean:** `RH/ParetoTailRateCompatibility` realizes every
decreasing zero-limit sequence as an exact Hilbert tail energy and proves
sharp exact-head interpolation in an orthogonal hyperplane.
`exists_hyperplane_exact_head_sublinear_divergence` constructs constant-head
vectors in a hyperplane excluding `hilbertOne`, with full error energy
`c^2 * sqrt(N+1)` for `c > 0`. The energy diverges while its quotient by N
tends to zero. This refutes the inference from those analytic rates alone;
it does not identify the hyperplane with the arithmetic legal space.
The actual cofinal bounded normalized-tail provider remains **Open**.
See `RH/DichotomyPNTAttempt20260924.md`.

### Quantitative first-window energy and signed primitive identity (2026-09-24)

**Established in Lean:** `RH/RawMobiusFirstWindowQuantitative` proves
the unconditional eventual bound I_N <= 4*C^2*N/(log N)^2 and
`rawMobiusFirstWindowBudget_div_mul_log_tendsto_zero`, namely (W_N/N)*log N -> 0.
W_N includes the reciprocal head and the actual first middle window.
`RH/RawMobiusPrimitiveEnergy` proves an exact weighted interval energy identity
with all endpoint, mean, and signed cross terms retained. Only the diagonal
of the primitive-times-divisor-jump product vanishes.
`RH/ParetoUniformJordanIdentification` proves uniform variance is at least
one sixteenth of the number of upper-half primes.
The cofinal subpower bound on the full B_N remains **Open**.
See `RH/SecondMomentRHAttempt20260924.md`.

### Directed RH arithmetic: prefixes and first window (2026-09-24)

**Established in Lean:** `RH/CenteredResiduePrefixes` proves an exact
discrete primitive, uniform shifted Mobius prefix bounds, summability, and
an unconditional signed Pareto-tail bound. `RH/RawMobiusFirstWindow` proves
U_N(k)=k*m_N+M(k)-M(N) on N<k<=2N+1 and weighted increment energy <=2*B_N.
`RH/ParetoUniformJordanIdentification` identifies the top-half moving
divisor coordinates exactly as mu(q)/q and derives a uniform-variance lower bound.
The actual cofinal subpower bound for B_N remains **Open**. First-moment
cancellation is not a bound on the required weighted second moment.
See `RH/DirectedRHArithmeticAttempt20260924.md`.

### Exact centered Mobius Jordan variance (2026-09-24)

**Established in Lean:** `RH/ParetoUniformJordanIdentification` proves the
exact centered Mobius uniform variance as Jordan-weighted divisor squares.
`centeredMobius_uniform_variance_finite_cutoff` removes all coordinates q>N;
`centeredMobius_factorial_variance_eq_jordan` has no hypotheses. Only standard
foundational axioms occur. Uniform variance is not Pareto energy. The cofinal
subpower estimate for the actual RH budget remains **Open**.
See `RH/CenteredMobiusJordanVarianceAudit20260924.md`.

### Signed Gram moving exponents (2026-09-24)

**Conditional research reductions:** RH/RawMobiusSignedGramMovingExponent
proves zeta_ne_zero_of_frequently_raw_offDiagonal_power,
riemannHypothesis_of_raw_offDiagonal_exponents_tendsto_zero, and
riemannHypothesis_of_raw_offDiagonal_moving_exponent.
Each exponent may have its own constant and cofinal set.
The actual signed arithmetic bounds hC/hbound remain **Open**.
See RH/SignedGramMovingExponentAudit20260924.md for literature and limits.

### Signed raw Gram energy and far-tail continuation (2026-09-24)

**Established in Lean:** RH/RawMobiusSignedGramEnergy defines actual signed
atoms, the diagonal \(D_N\), and the complete ordered off-diagonal sum \(Q_N\).
It proves
\[
 \|U_N\|_P^2=1+2L_N+D_N+Q_N,\quad 0\le D_N\le2H_N,\quad
 Q_N-4\le B_N\le2Q_N+4H_N\ \text{eventually}.
\]
For every positive exponent,
frequently_power_rawMobiusBudget_iff_offDiagonal proves equivalence of the
cofinal upper power bounds for \(B_N\) and \(Q_N\).

**Conditional research reduction:**
riemannHypothesis_of_frequently_subpower_raw_offDiagonal proves Mathlib RH
from those upper estimates on \(Q_N\) at every positive exponent.
Its arithmetic hsub is **Open**. No bound on the growing mixed Gram block
is inferred from fixed-source convergence.

**Established in Lean:** NaturalMobiusSourceLimits adds
rawMobiusResidual_inner_rawMobius_tendsto_zero and
rawMobius_tail_inner_head_tendsto: unconditional cancellation of every
fixed-head/expanding-tail signed rectangle, with its explicit limit.

**Established in Lean:** RawMobiusBudgetQuantitative adds
rawMobiusSquareBudget_add_far_sub_norm_tendsto_zero, proving the exact
harmonic correction tends to zero while retaining the far tail.

**Established in Lean:** Analysis/ReciprocalEnergyFromPrefix proves finite
and infinite Abel energy transfers. RawMobiusFiniteWindowEnergy specializes
them as rawMobiusFarEnergy_le_of_prefix, with its finite-interval arithmetic
provider explicit.

**Mathematical proof, not yet fully Lean-formalized:** the classical dual
large sieve plus exact CRT covariance gives
\[
 T_N\le[2A_N^2+(N/6)H_N^2]/(N^2+2)\longrightarrow0.
\]
The Fourier/CRT and large-sieve provider implementation remains pending;
the middle-window subpower bound remains **Open**.
See [RawMobiusSignedGramAttempt20260924.md](RH/RawMobiusSignedGramAttempt20260924.md)
and [RawMobiusFarTailLargeSieve20260924.md](RH/RawMobiusFarTailLargeSieve20260924.md).

### Quantitative raw budget and fixed-power zero-free regions (2026-09-24)

**Established in Lean:** RH/RawMobiusBudgetQuantitative proves the exact
identity
\[
 B_N+T_N=\|U_N\|_P^2+m_N^2(H_{N+1}-1)
\]
and rawMobiusSquareBudget_le_two_raw_norm_sq: \(B_N\le2\|U_N\|_P^2\).
Together with the existing forward comparison, the finite budget and full
physical norm control each other with universal constants.

**Established in Lean:** rawMobiusSquareBudget_eventual_explicit_ceiling
has no new arithmetic hypothesis. There is \(C\ge0\) such that eventually
\[
 B_N/N\le16/N+(25+8(2+4C)^2)x_N+16(2+4C)^2x_N^2,\quad
 x_N=\frac{1+\log(\log N+3)}{\log N}.
\]
rawMobiusBudgetCeiling_tendsto_zero proves convergence of this explicit
ceiling. The providers are the actual quantitative PNT results in
CanonicalMobiusQuantitativeEnergy and MobiusQuantitativeRate.
This logarithmic improvement does not establish a positive power saving.

**Conditional research reductions:** RH/RawMobiusBudgetZeroFree proves:
- zeta_ne_zero_of_frequently_raw_square_budget_power: a frequent
  \(B_N\le C(N+1)^\alpha\), \(\alpha\ge0\), excludes zeros strictly right
  of \((1+\alpha)/2\).
- zeta_ne_zero_of_frequently_small_raw_square_budget_power: for
  \(\alpha>0\), arbitrarily small frequent coefficients also exclude
  the boundary.
- zeta_ne_zero_of_raw_square_budget_normalized_tendsto_zero supplies the
  boundary premise from normalized convergence.

The arithmetic power hypotheses remain **Open** at the exponents needed
for RH. The continuation also records a literature-based converse to the
subpower RH criterion, explicitly **not yet formalized in Lean**.
See [RawMobiusBudgetContinuation20260924.md](RH/RawMobiusBudgetContinuation20260924.md).

### Unconditional sublinear finite budget (2026-09-24)

**Established in Lean:** `RH/RawMobiusBudgetSublinear` proves
\[
 B_N\le4\|F_N\|_P^2+4+9Nm_N^2,\qquad B_N/N\longrightarrow0.
\]
The principal theorem `rawMobiusSquareBudget_sublinear` uses the
actual unconditional PNT providers from `CanonicalMobiusPNT`.
It has no new arithmetic premise and retains the full physical energy.

This is weaker than the cofinal subpower estimates below: sublinear
growth alone does not imply growth slower than every positive power.
The missing estimate `hsub` remains **Open**.

Source audit and exact formulas:
[NymanBeurlingSubpowerAudit20260924.md](RH/NymanBeurlingSubpowerAudit20260924.md).

### Subpower finite arithmetic budget criterion (2026-09-24)

**Established in Lean:** `RH/RawMobiusSubpowerCriterion` defines
`rawMobiusSquareBudget N = N*m_N^2 + M_{N,N^2}` and proves
`canonicalMobius_norm_sq_le_raw_square_budget`:
\\(\\|F_N\\|_P^2\\le12B_N+8\\) for every positive cutoff.
The actual continuous critical energy is identified with the Pareto norm.

**Established in Lean:** `rawMobiusSquareBudget_lower_of_zeta_zero`
shows that any zeta zero \\(\\rho\\ne1\\) with \\(\\beta=\\Re\\rho>1/2\\) forces
\\[
 \\frac{2\\beta-1}{4|\\rho|^2}(N+1)^{2\\beta-1}\\le12B_N+8
 \\qquad(N\\ge3).
\\]

**Conditional research reduction:**
`riemannHypothesis_of_frequently_subpower_raw_square_budget` proves
Mathlib's `RiemannHypothesis` if for every \\(\\varepsilon>0\\) there is a
constant \\(C_\\varepsilon\\) and cofinally many cutoffs with
\\(B_N\\le C_\\varepsilon(N+1)^\\varepsilon\\). The cofinal sets may depend
on the exponent. No sign-crossing hypothesis is required.
The actual arithmetic estimate `hsub` remains **Open**.

### Finite raw Möbius energy windows (2026-09-24)

**Established in Lean:** `RH/RawMobiusFiniteWindowEnergy` retains the exact
head, finite middle window, and complete infinite far tail of the raw
Möbius residual. It proves
\[
 \|U_N\|_P^2=m_N^2\sum_{k=1}^{N}\frac{k}{k+1}+M_{N,K}+F_{N,K},
 \qquad F_{N,K}\le N^2/(K+1).
\]
At the square cutoff this gives
\(\|U_N\|_P^2\le Nm_N^2+M_{N,N^2}+1\).
`rawMobiusMiddleEnergy_finite_arithmetic` expands the middle window entirely
into finite Möbius and residue sums.

**Established in Lean:** `RH/RawMobiusFiniteWindowCriterion` identifies the
raw cutoff \(N=n+1\) with `naturalResidual n` and proves the quantitative
actual-residual obstruction
\[
 E^2\le (B_{n+1}+1)\|r-Q_n r\|_P^2,\qquad
 B_N=Nm_N^2+M_{N,N^2}.
\]

**Conditional research reduction:**
`riemannHypothesis_of_frequently_bounded_raw_square_window` proves RH
from one cofinal upper bound on \(B_N\). Its explicit `hbudget` remains
**Open**. No provider for the middle-window estimate or the classical
cofinal reciprocal-Möbius sign-change cutoffs is supplied by these modules.

### Geometric residual correlation summability (2026-09-24)

**Established in Lean:** `Analysis/GeometricGramInnovations` constructs an
orthonormal innovation family from an exact geometric Gram kernel, proves
finite and infinite Bessel bounds, and proves an exact scalar energy identity.

**Established in Lean:** `RH/ResidualGeometricInnovations` discharges the
Gram hypotheses using actual Pareto dilations and specializes to the actual
limiting residual. With \(E=\|r\|_P^2\) and \(A_j=\langle r,D_{4^j}r\rangle_P\),
\[
 E^2+\frac13\sum_{j\ge0}4^{-j}(A_{j+1}-A_j)^2\le E,\qquad
 \sum_{j\ge0}4^{-j}A_j^2\le3E-E^2.
\]
Both series are explicitly proved summable. Principal declarations:
`residual_geometric_pairing_difference_summable`,
`residual_geometric_pairing_difference_bound`,
`residual_geometric_pairing_square_summable`,
`residual_geometric_pairing_square_tsum_bound`.

**Still Open:** signed cancellation strong enough to bound the ordinary
residual primitive sublinearly or to force the residual energy to vanish.
Geometric-scale summability alone does not provide that arithmetic estimate.

Details and source audit:
[FiniteWindowsAndGeometricCorrelations20260924.md](RH/FiniteWindowsAndGeometricCorrelations20260924.md).

### Physical signed harmonic masses (2026-09-24)

**Established in Lean:** `RH/ResidualPhysicalSignMass` proves that, for any
annihilator of all actual residue generators, summability of either
positive or negative physical first moment forces summability of the
absolute first moment. For the actual projection residual, the existing
raw-Mobius test convergence then forces residual vanishing.

The theorem `not_RH_physical_sign_masses_nonsummable` proves that failure
of RH makes both nonnegative series `sum r(k)^+/(k+1)` and
`sum r(k)^-/(k+1)` nonsummable. The formal statements use the equal
weights `positiveWeight k * k`, with the zero coordinate anchored at zero.
These are physical sign masses, not Möbius-charge sign masses.

The coherent check `job_gx4m_YwzFV0V7Qcc7-X67PF61Z8C5uzj` succeeded,
exit 0, verified true, in 4.750 seconds. Both principal axiom reports
contain only `propext`, `Classical.choice`, and `Quot.sound`.

**Open:** summability of either signed mass for the actual residual.
The proved conditional vanishing implications do not discharge that
arithmetic premise and do not prove unconditional RH.

### Residual dilation tail localization (2026-09-24)

**Established in Lean:** `RH/ParetoDilationTailLocalization` proves, for any
Pareto Hilbert vectors f,g, that
`inner(f,D_(N+1) g)^2 <= (N+1)*norm(g)^2*norm(tail_N f)^2`.
Consequently the squared correlation divided by N+1 tends to zero.

**Established in Lean:** `RH/ResidualDilationTailBounds` specializes this
bound and limit to the actual projection residual. It also proves the
finite partial-sum upper bound obtained by retaining the individual tail
energies in the signed dilation identity.

The coherent proof check `job_i-lCGXY-xMXctD5cpNL8d4dj0ktS4qz6` succeeded,
exit 0, verified true, in 4.225 seconds. Principal axiom reports contain
only `propext`, `Classical.choice`, and `Quot.sound`.
No unresolved arithmetic premise occurs in these declarations.
Publication additionally requires the affected-module checkpoint.

**Still Open:** an estimate for the actual residual strong enough to force
its energy to vanish. The new limits do not establish RH.

### Logarithmic Möbius mean, full fixed sources, and primitive criteria (2026-09-24)

**Established in Lean:** `NumberTheory/PrimeNumberTheorem/LogarithmicMobiusMean`
proves `logarithmicMobiusMean_tendsto_neg_one` for the actual ordered sum
`sum_{n=1}^N mu(n)*log(n)/n`, with no additional arithmetic hypotheses.
The proof uses the existing `Quantitative.MediumPNT`, its inverse-fourth-log
weakening, exact finite convolution and Abel identities, an explicit
inverse-cube-log harmonic-defect remainder, and fixed quotient-window
cancellation. The classical statement is NIST DLMF 27.11.15.

**Established providers:** `Analysis/ReciprocalAbel`,
`Analysis/LogarithmicAbelRemainder`, `NumberTheory/LogarithmicKernelConvolution`,
and `NumberTheory/PrimeNumberTheorem/{LogarithmicMobiusConvolution,
LogarithmicMobiusConvergence,PrimeErrorInverseLogFourth,MangoldtHarmonicAbel}`.
In particular `mangoldtHarmonicDefect_inverse_log_cube_bound` discharges the
explicit envelope of the intermediate conditional mean assembly. No
unsquared logarithmic Mertens estimate is assumed.

**Established in Lean:** `RH/NaturalMobiusSourceLimits` proves the exact
constant-source identity `inner U_N One = 1 + logarithmicMobiusMean N`,
its unconditional limit zero, and
`rawMobiusResidual_residue_inner_tendsto_zero` for every fixed actual
normalized residue generator. This closes the centered and constant source
obligations in Sections 7–8 of the reciprocal-charge research note.

**Established in Lean:** `Analysis/DominatedPrimitivePairing`,
`NumberTheory/DivisorCountSummability`, and
`RH/{NaturalMobiusVariation,NaturalMobiusPrimitiveTests,NaturalMobiusPeriodicTests}`
prove the exact weighted variation bound and pairing decay for tests whose
ordinary primitive is summable against
`(3 + tau(K+1))/((K+1)*(K+2))`. A fixed power bound
`|H(K)| <= C*(K+1)^alpha`, with `alpha < 1`, suffices. The divisor
Dirichlet series is established for every real exponent greater than one;
the actual raw-residual endpoint follows from its proved cutoff bound.

**Established equivalence; conditional research reduction:**
`RH/NaturalMobiusResidualCriterion` proves
`limitResidual_zero_iff_summable_primitive` and
`riemannHypothesis_of_residual_primitive_rpow_bound`.
**Open:** the displayed summability or a sufficient fixed sublinear power
bound for the actual orthogonal residual. No such provider is asserted.
The non-RH consequence only states that each proposed fixed bound is
exceeded at some cutoff.

**Established in Lean:** `RH/ResidualDilationPartialSums` proves the exact
signed formula `H_r(N)=2*sum_{m=1}^N inner r (D_m r)-N*inner r (D_(N+1) r)`
and the unconditional square-root dilation bound. Its resulting
order-three-halves primitive bound does not close the sublinear obligation.

**Verification:** the 16-module coherent check
`job_MRYX9KShwGKCY8LFBcQV0RrndaHpoE7z` succeeded, exit 0,
`verified:true`, 6.466 seconds, SHA-256
`69ba1fe754ce8cf70d2201819cb6085120d6d090d64dcaafed90a58dac37e05b`.
All 12 principal axiom reports contain only `propext`, `Classical.choice`,
and `Quot.sound`. Local hypotheses in the RH reduction remain explicit.
The repository checkpoint independently validates the published modules.

**Still Open:** growing inverse-Gram amplification, signed saturation, or
a sufficient actual-residual bound. RH remains unproved. The new research
ledger is `RH/PrimitiveAndLogarithmicContinuation20260924.md`;
`RH/Residual_Abel_Obstruction_20260924.md` contains separately labeled
paper derivations, including the Abel limit-interchange obstruction.

### Reciprocal-charge norm limit and signed dilation correlations (2026-09-24 continuation)

**Established in Lean:** `RH/ReciprocalChargeNormLimit` proves
`reciprocalChargeRiesz_norm_sq_tendsto`: the actual squared norms tend to
`15 / Real.pi ^ 2`. The proof uses exact low/isolated quotient-window
separation, PNT, summable domination, and the existing squarefree Euler series.
All signed mixed terms are retained. It also proves the limiting squared
distance from every fixed Hilbert vector is its squared norm plus `15/pi^2`,
and that no cofinal subsequence converges in norm.

**Established in Lean:** `NumberTheory/QuotientWindowEnergySplit`,
`NumberTheory/QuotientWindowEnergyLimit`, `Analysis/BoundedSquareEnergy`, and
`NumberTheory/QuotientKernelEnergyLimit` provide the reusable exact finite
identities, dominated limits, correction limits, and homogeneous kernel theorem.

**Established in Lean:** the `RH/ReciprocalChargeDilation*` chain constructs
actual two-cutoff kernels and proves their Hilbert norm identity, complete
coefficient-series expansion, and signed correlation limit
`(1/h) * sum_d mu(d)*mu(h*d)/d^2` for every positive integer h.
`RH/PrimeReciprocalChargeCorrelation` evaluates prime factors. The final
specializations are `-6/pi^2` for h=2 and `-9/(2*pi^2)` for h=3.

**Still Open:** these dual-vector limits do not prove the residual sign
r(1)<=0, inverse-Gram control, signed Schur saturation, or approximation at
weights tending to 1. RH remains unproved. The full rational-dilation formula,
two-seed rectangle averages and rescaled energy measures are recorded as
written research in `RH/ReciprocalCharge_DilationAndPeriodicSource_20260924.md`.
The fixed periodic Gram-source obligation is now discharged by the modules
in the continuation entry above.


### Agenda execution: signed Schur, weighted minima, reciprocal charges (2026-09-24)

**Established in Lean:** `RH/ReciprocalSchurVariation` proves the actual
signed W increment including the Mobius term, symmetric reciprocal numerator,
exact projection budgets, absolute mixed variation <=sqrt(2), and exact mixed
sum 1-r(1). Signed saturation remains Open.

**Established in Lean:** `RH/ParetoWeightedCells` and `RH/ParetoWeightedGram`
prove exact positive physical cell weights, complete infinite weighted energy,
the actual positive definite finite matrix and minimum 1/u-b^T G^(-1)b.
They prove cutoff monotonicity, finite/closure approximation transfer, and
unconditional optimized convergence for u>=2. The `riemannHypothesis_of_minima`
consumer is a **conditional research reduction**: the actual vanishing
minima for weights approaching 1 remain Open.

**Established in Lean:** `RH/ParetoResidualShell` and
`RH/ParetoTailAverageArithmetic` prove exact dyadic tail bookkeeping, signed
full-tail observations of legal exact heads, and a residue-jump Abel identity.
No cofinal normalized-tail upper bound or actual Noor regularity is proved.

**Established in Lean:** `RH/MobiusResidualOneSidedMass` proves uniform
reconstruction bounds from either norm-summable charge sign part. Under
not RH, both actual residual sign masses have partial sums tending to infinity.
The sufficient one-sided mass hypothesis remains an Open arithmetic input.

**Classical import completed in this physical realization:** Balazard
Propositions 5--7 are implemented by
`NumberTheory/QuotientWindowSquareBound`, `RH/MobiusQuotientEnergy`,
`RH/MobiusReciprocalChargeBridge`, and `RH/BalazardReciprocalCharge`.
The actual quotient-window bound is 10 and the Riesz squared norm bound is 42.
`mobiusDifference_reciprocal_tendsto_zero` proves the ordered reciprocal
charge sum tends to zero for every physical Hilbert vector, without any
unproved uniform-bound premise. The from-two sum tends to -f(1).
The representing vectors converge weakly to zero but provably not in norm.

**Established in Lean:** `RH/NaturalMobiusPhysicalTests` proves actual raw
Mobius exact heads, fixed-coordinate decay, |A_N(k)|<=min(N,k), and convergence
against an explicitly summable test class. Periodic residue atoms fail that
test condition; full fixed Gram-source decay is not claimed.

**Still Open:** the signed scalar saturation, approximation at weights near 1,
actual cofinal tail boundedness, one-sided mass control, and residual regularity.
**Remaining formal imports:** the local RH converse, Burnol projection
representation, and full BSY boundary passage.

**Completed by the continuation above:** the full norm-limit argument in
`RH/ReciprocalChargeNormLimit20260924.md` is now formalized in
`RH/ReciprocalChargeNormLimit`. No mathematical novelty is claimed.
Full execution report: `RH/RH_Agenda_Execution_2026-09-24.md`.
No unconditional RH proof is asserted.


### RH criteria, reciprocal correction, and sign oscillation (2026-09-24)

**Established in Lean:** `RH/ReciprocalGramCorrection` computes the growing
reciprocal-weighted inverse-Gram correction W_n exactly and proves
W_n -> -r(1). Its limit lies between -(2+sqrt(2))E and -(2-sqrt(2))E.
Zero limit is equivalent to actual residual zero. No limit is passed through
an inverse matrix.

**Established in Lean:** `RH/ParetoWeightedApproximationRH` proves the
positive error floor (2 Re(s)-u)/|s|^2 at an actual right-hand zeta zero,
for every legal closure member and 1<=u<2 Re(s). Independently small errors
on individual vertical lines approaching 1/2 suffice for RH.

**Established in Lean:** `RH/ParetoReciprocalDifference` proves
sum |f(n)/n|^2 <= 2||f||^2, physical sublinearity, exact finite Abel
summation, and convergence of ordered reciprocal first differences to
<f,1>. `hilbertPhysicalSublinear` now discharges the historical
`HilbertPhysicalSublinearTarget` in `RH/CanonicalTailHistoricalTargets`.
This imports the real s=1 difference-series result, not Balazard's separate
Mobius reciprocal sum rule.

**Established in Lean:** `RH/MobiusResidualSignOscillation` proves a general
order reversal for vectors with nonnegative Mobius charges, contractivity
of their ordered reconstructions, and both defect signs arbitrarily far
under not RH. Eventual one-sided charges of the actual residual force RH.

**Conditional research reductions / Open:** a nonnegative W_n limit;
independently small weighted errors with u tending to 1; or eventual
one-sided residual charges. None of these arithmetic providers is asserted.
The compact scalar obligation remains r(1)<=0. The proved internal
residual equivalences must not be called a Lean RH equivalence: the
classical RH-to-Nyman/Baez-Duarte converse remains unimported here.

Primary-source coverage, exact proof statements, missing criterion imports,
and explicit obstructions to an endpoint/interpolation or sign bootstrap:
`RH/RHCriteriaImportAudit20260924.md`. No unconditional RH or novelty claim.

### Residual tails and inverse source escape (2026-09-24)

**Established in Lean:** `RH/ResidualTailPNT` connects the existing
sublinear-energy reduction to `canonicalMobiusHilbert_sublinear`, whose
classical PNT premise is already discharged. Positive limiting energy E
forces positive residual tails T_N at every cutoff and N T_N -> infinity.
The actual residual is zero exactly when N T_N has a bounded cofinal
subsequence. With the existing explicit PNT ceiling q_C(N), one unconditional
constant C gives eventually (N+1) T_N >= E^2/q_C(N), with q_C(N)>0 and q_C(N)->0.

**Historical target resolved:** `residualTailLinearFloor` in
`RH/ResidualEnergyHistoricalTargets` proves `ResidualTailLinearFloorTarget`. The stronger divergence result
makes the proposed linear exact-head upper witness unnecessary for this target.

**Established in Lean:** `RH/NaturalMobiusResidualEscape` proves
<A_N,r-Q_N r>=E for the raw Mobius residual A_N and the total finite-dual
projections Q_N. It proves the exact full-norm identity
||A_N||^2 = energy N + s_N^T G_N^(-1) s_N, where s_N=b_N+G_N mu_N.
Positive E forces both ||A_N|| and this inverse quadratic form to infinity.
Every fixed correction still has its previously proved finite limit.

**Conditional research reductions / Open:** a bounded cofinal subsequence
of N T_N, of ||A_N||, or of s_N^T G_N^(-1) s_N suffices for RH.
None of these boundedness providers is proved. Fixed source decay, relative
Gram-inverse bounds, and sublinear energy do not supply them.
The qualitative tail argument was already present conditionally; this update
discharges its arithmetic inputs and adds the quantitative and raw-source results.
No unconditional RH proof or claim of mathematical novelty is made.

Proofs, exact declarations, and remaining obligations:
`RH/ResidualEscapePNT20260924.md`.

### Gram–Mobius quantitative bridge (2026-09-24)

**Established in Lean:** `RH/UniformTrigammaMeanPoint` combines the cubic
mean-point estimate with the midpoint sandwich:
(L alpha(r,L)-sqrt(r(r+1)))^4 <= trigamma(1)/(512 L^3)
for every real r>=1 and L>0, uniformly in growing residues.

**Established in Lean:** `RH/MidpointTailEnergy` identifies the actual complete
midpoint physical energy, proves its relative zero-head error bound with
factor 1-(2N+3)^(-2), and transfers the canonical full-tail Hardy schedule
to any certified midpoint competitor. No inverse-norm bound or minimizer
existence is assumed. The comparator premise is explicit.

**Established in Lean:** `RH/CanonicalMobiusCapacityHardy` transfers the
unconditional quantitative PNT ceiling to the attained signed-covariance
optimizer, including singular covariance matrices. For every finite positive
index family with k_i>=N containing N, one eventual arithmetic constant gives
1 <= (N B_C(N)-N/(N+1))*capacity. The optimizer satisfies the exact weighted
identity head + (N+1)^(1-u)/capacity - weightDefect and the same explicit
uniform moving-Hardy residual bound as the canonical competitor.

**Open:** a capacity improvement or signed weight-defect estimate sufficient
for the RH-strength moving boundary. The proved boundary still tends to 1,
not 1/2. Relative midpoint stability does not supply the missing arithmetic rate.
The literature obstruction to full critical convergence of the classical
canonical family is explained, but not formalized, in the audit.

Comparison, literature, exact constants, assumptions, and verification scope:
`RH/GramMobiusBridgeAudit20260924.md`.

### Quantitative Mobius energy and moving Hardy boundaries (2026-09-24)

**Established in Lean:** `RH/CanonicalMobiusQuantitativeEnergy` proves a
simultaneous full-energy bound for every pair of finite cutoffs K>=2, J>=1:
E_1(F_N)/N <= 3/N + 2K D(N,K,J)^2 + 4/K, with
D=1/J+1/(NJ)+C(H_K+H_J+2)/log N and one unconditional C.
Optimization gives the explicit ceiling B_C(N) with logarithmic ratio
x_N=(1+log(log N+3))/log N. Both B_C(N) and the residual ceiling
q_C(N)=2B_C(N)+3/N tend to zero.

**Established in Lean:** `Analysis/WeightedMellinHeadTail` and
`RH/ExactHeadWeightedEnergy` prove the exact head-tail energy identity,
including its nonnegative weight defect, and the complete zero-head
suppression factor (N+1)^(1-u). Actual Hardy line integrals are identified.

**Established in Lean:** `RH/CanonicalMobiusMovingBoundary` assembles an
unconditional explicit moving-half-plane theorem:
beta_N=1+log(q_C(N))/(4 log(N+1)) tends to 1 from below and every residual
line integral on sigma>beta_N is at most sqrt(q_C(N)), tending to zero.
The module also gives an unconditional intermediate-exponent upper bound
for the approximants themselves and the full finite theta scheduling family.

**Open:** boundaries tending to 1/2 with a common approximant bound.
The new logarithmic full-energy saving does not discharge this RH-strength
obligation. No unconditional RH proof is claimed.

Proof details, exact constants, declarations, and verification scope:
`RH/QuantitativeMobiusMovingBoundary20260924.md`.
Integration also renames the operator in `OptimalProjectionDilationGaps`
to `optimalProjectionDilationCorrection`, resolving a pre-existing root
import collision with the different `TailCapacityDilationCorrection` definition.

### Hardy endpoint and moving-bound RH reduction (2026-09-24)

**Established in Lean:** `RH/HardyMobiusEndpoint.rawHardyMobiusSum_endpoint`
and `correctedHardyMobiusSum_endpoint` prove unconditional convergence of the
actual raw and boundary-corrected Möbius sums in H²(Re(s)>1).
`RH/ParetoMellinHardyEndpoint` proves actual Hardy membership and the exact
least-upper-bound identity for line integrals with cell weight
(2n+1)/[2n²(n+1)²]. The analytic identification is fully formalized.

**Established arithmetic providers:** `NumberTheory/PrimeNumberTheorem/Quantitative`
adapts the pinned PNT+ Mellin calculus, zeta conjugation, and MediumPNT proofs.
`PrimeErrorInverseLogSq`, `MobiusLogarithmicRateBridge`,
`MobiusFloorTailReindex`, `RH/MobiusReciprocalCutoff`,
`RH/MobiusReciprocalLogRate`, and `RH/MobiusQuantitativeRate` prove the
unconditional decay m_N²(H_N+1) → 0. Thus the scalar premise in
`rawHardyMobiusSum_endpoint_of_headRate` is discharged; no Ramaré bound is assumed.
`RH/EndpointResidueCorrection` includes the entire infinite correction tail.

**Established general criteria:** `RH/DampedDiagonalCompactness` retains the
bounded finite-coordinate and damping-diagonal closed-span criteria.
`RH/ExactHeadMovingHardyRH` proves the actual Mellin tail bound, the
polynomial energy cost of a zero, and the moving-energy/Hardy-bound RH implications.
The canonical specialization discharges legality and exact heads.

**Conditional research reduction / Open:** the common bound in
`canonicalMobius_riemannHypothesis_of_movingHardy_bound` remains unproved:
alpha_N ≥ 0, alpha_N → 0 and one C bounding every actual line integral on
sigma > 1/2 + alpha_N. No unconditional RH theorem is claimed.
The earlier diagonal criterion's bounded-approximant provider remains open.

**Established finite improvement:** `RH/MobiusSignCrossingBridge` proves
the reciprocal-sum and critical correction bounds at a finite sign crossing.
Cofinality of crossings and control of the full critical residual tail are not supplied.

Proof, provenance, and verification boundaries:
`RH/HardyEndpointFormalization20260924.md`.
Earlier analytic argument, Wolfram checks, and finite computations:
`RH/HardyEndpointCompactness20260924.md`.

### Complete mixed arithmetic Gram and exact shift defect (2026-09-24)

**Established in Lean:** `RH/NoorMixedGramArithmetic` proves the harmonic
coefficient formula and the full signed mixed Gram series, including the
skew part. `Analysis/NoorLogarithmGram.summable_log_multiples` verifies
the general summability input. For fixed e, d B(d,e)/log d tends to
log(e)/e, while d B(e,d)/log d tends to zero. These are fixed-column
limits, not bounds uniform over growing arrays.

**Established in Lean:** `Analysis/ShiftedLiftDefect` proves an exact
square completion, specialized by `RH/NoorShiftedDefect` to the actual
canonical minimizer. For 0<s<1 and t=(1-s^2)/s,
J_N(t)/t = s E_N + ||S v_N-s^2(v_N-a_N)||^2/[s(1-s^2)].
The complete arithmetic inverse gain obeys the matched-parameter bound.
No conditional arithmetic premise is used in these identities.

**Open:** the existing cofinal divided-gap provider `hrate`, source-zero
provider `hsource`, and vanishing limiting residual remain unresolved.
Neither the full mixed-entry formula nor its asymmetric fixed-column limits
discharge the growing inverse-matrix obligation. Details and primary-source
audit: `RH/NoorMixedGramDefect20260924.md`.

### Actual shifted source moments and Schur control (2026-09-24)

**Established in Lean:** `RH/NoorShiftedSource` identifies the actual source:
d h_N(d) = E_N log d + M_N(1) - M_N(d), where
M_N(d) is the full logarithmic moment of the actual finite residual.
`Analysis/NoorLogarithmGram.inner_logVector_eq_tsum_multiples` expresses
the moment as the exact sum of a_N(dm)/m over positive m.

**Established in Lean:** for cofinal cutoffs and legal indices d_j tending
to infinity, M_(N_j)(d_j) tends to zero and d_j h_(N_j)(d_j)/log d_j
tends to the actual limiting residual energy. The zero value of this
normalized source limit is equivalent to zero limiting residual.
No zero-energy conclusion is claimed.

**Established in Lean:** with the full mixed matrix
B_N(d,e)=<Du_d,u_e>, h_N=b_N-B_N c_N and B_N+B_N^T=K_N.
The source obeys the complete Schur quadratic bound
(x^T h_N)^2 <= E_N [x^T K_N x - (B_N^T x)^T G_N^(-1)(B_N^T x)].
Only the original independent family's Gram inverse is used.

**Conditional research reduction:**
`riemannHypothesis_of_finiteShiftedSource_log_scaled_zero` concludes
Mathlib RH from the explicit source-zero premise `hsource`.
**Open:** this source-zero provider and the original divided inverse-Gram
gap provider `hrate`. Source limits and the Schur bound do not discharge
either obligation. Details: `RH/NoorShiftedSource20260924.md`.
### Exact shifted arithmetic Gram and canonical minimizers (2026-09-24)

**Established in Lean:** `Analysis/NoorLogarithmGram` computes the exact
lcm inner product of logarithmic vectors. `RH/NoorRegularizedGram`
transfers it to every entry of the actual shifted residue Gram K.
`Analysis/ShiftedLiftGram` proves positivity of K+t^2 G for an independent
dictionary and t>0, constructs the actual inverse-matrix normal solution,
and proves the full-norm minimum E-h^T(K+t^2 G)^(-1)h.

**Established in Lean:** the arithmetic application constructs the unique
canonical finite minimizer, proves its normal equations and exact energy,
and derives unscaled convergence for every positive vanishing parameter
schedule. The finite inverse gain is at most E/(1+t). All signed terms and
the complete infinite Hilbert norm are retained.

**Conditional research reduction:** `riemannHypothesis_of_inverseGram_gap`
concludes Mathlib RH from vanishing of the actual inverse-matrix gap
divided by t along cofinal cutoffs and positive parameters tending to zero.
**Open:** the divided-gap provider `hrate`. Explicit inversion and the
lcm kernel do not discharge this estimate.
Details: `RH/NoorRegularizedGram20260924.md`.

### Exact remaining normalized-tail obligation (2026-09-23)

**Established in Lean:** `RH/ParetoResidualTailDichotomy` now exposes
`frequently_bounded_actual_tail_iff_residual_zero`: existence of one finite
bound on N times the actual residual tail energy at arbitrarily large N is
equivalent to the actual limiting projection residual being zero.
The forward proof uses the existing checked PNT provider and tail dichotomy.
No RH-to-density converse is required.

**Conditional research reduction:** the existing
`riemannHypothesis_of_frequently_bounded_actual_tail` concludes Mathlib RH
from that bound. **Open:** a provider of the bound. The equivalence does not
assert either side. The current coefficient, CRT, tail-regularity, and
Mellin-window obligations are audited in `RH/UnconditionalRHObligations20260923.md`.

### Exact Pareto CRT transfer and growing-family Green bounds (2026-09-23)

**Established in Lean:** `RH/ParetoCRTGramTransfer` transfers the closed
uniform CRT covariance formula to the actual Pareto inner product. The result
is an exact identity: the gcd covariance is the main term and a finite signed
`uniformDefect` sum is retained as the complete correction. Its absolute
value is bounded explicitly by the L1 defect of the genuine residue weights.

**Established in Lean:** the same module defines a visible coefficient
envelope for arbitrary finite Ramanujan-packet combinations and proves that
the complete tail beyond N has absolute value at most the product of the two
envelopes divided by N+1. Consequently the anchored-Green finite Gram has that
same error bound. The support, conductors, dimension, and coefficients may all
depend on N; convergence follows constructively whenever the displayed
envelope product divided by N+1 tends to zero.

**Important limitation:** no asymptotic replacement of the Pareto weights by
uniform weights is asserted. In fact `RH/ParetoCRTWeightLimits` proves that
the residue-one defect tends to one half. The exact correction must therefore
remain unless separate cancellation is proved. These results control the
transfer and Green tail; they do not prove density of the legal span or RH.


### Exact inverse-Gram correction pairings (2026-09-23)

**Established in Lean:** `RH/ResidueGramCorrectionPairing` proves exact
pairings for the actual Pareto Hilbert space. The natural Mobius residual
annihilates the full finite-support coefficient dual. Its pairing with the
projected dual equals the inverse-Gram correction, hence also the negative
pairing with the missed dual component. An exact norm-square identity
retains the entire signed interaction. `fixed_matrix_correction_tendsto`
identifies the limit of each actual inverse-Gram correction coordinate as
`-inner limitResidual (coefficientDual i)`, with only finitely many
zero-padded stages. This is unconditional; the limit may be nonzero.

**Mathematical proof, not yet formalized:** each fixed coordinate of
`b_N + G_N * mu_N` tends to zero, using classical PNT limits, exact periodic
summation by parts, and a summable divisor bound. Full proof and normalization:
`RH/InverseGramCorrectionAttempt20260923.md`.

**Open:** proving that every identified inverse-Gram correction limit is zero.
Source convergence alone does not prove this vanishing.

### Continuous Nyman space and Burnol analytic prerequisites (2026-09-23)

**Established:** `RH/NymanContinuousSpace` constructs the actual complex L²
generators, their closed span, the norm-one constant, and dilation membership.
`RH/NymanCommonZeros` proves the exact common-zero statement for the scalar
numerators and, away from 0 and 1, their zeta Mellin symbols.

**Established:** `RH/BurnolCriticalLine` proves local logarithmic and weighted
integrability, evenness, finite-cutoff additivity, finiteness of bounded
critical zero sets, and almost-everywhere nonvanishing.
`RH/BurnolCayleyJensen` constructs the analytic pole-removed Cayley zeta
function and proves its exact finite-radius Jensen formula.
`RH/BurnolBoundaryCoordinates` proves its actual critical-line boundary
modulus identity. `RH/BurnolRealAxis` proves zeta and normalized real-axis
limits from the Dirichlet series. These six modules add 68 proved theorems.

**Open:** the global weighted integrability and boundary passage needed for
BSY; transport of divisor multiplicities to the canonical zero sum; the
Mellin--Hardy surjection, inner factorization and invariant-subspace
identification needed for the full Nyman--Beurling projection theorem.
Neither full requested identity is claimed by these prerequisites.
The continuous-to-Pareto transport and its exact projection gap also remain
separate obligations. Detailed acceptance gates and research priorities:
`RH/BurnolCompletionResearchAgenda.md`.


### Burnol zero product with actual multiplicities (2026-09-23)

**Established:** `RH/BurnolZeroFactors` and `RH/BurnolProductCalculus` prove
the exact one-zero, multiplicity, cutoff, and logarithmic identities.
`Analysis/ContractiveProducts` supplies the finite and infinite weighted
defect telescopes and the contractive-product limit calculus.

**Established:** `RH/BurnolZeroProduct` uses actual nontrivial zeta zeros
strictly right of the critical line and their analytic multiplicities.
It proves finite-subset net convergence, agreement with Mathlib `HasProd`,
single-zero quantitative obstructions, and `productSq_eq_one_iff_rh`.
`RH/BurnolZeroProductConvergence` proves unconditional strict positivity,
absolute summability of logarithms, `productSq = exp (-2 * logarithmicZeroSum)`,
the unsquared infinite product, and `product_eq_one_iff_rh`.
The positivity proof uses the checked multiplicity-weighted inverse-square
zero sum with `Zeta23.zetaSeam`; it assumes neither RH nor a projection identity.

**Established:** `Analysis/NestedProjectionEnergy` retains the exact squared
norm of the difference between nested projections.
`Analysis/InnerMultiplierProjection` proves the abstract isometric-multiplier
projection computation from its explicitly stated reproducing relation.

**Conditional research reductions:** `RH/BurnolProjectionConsequences` assumes
the projection norm/product identity for the larger space. It derives the
RH membership equivalence and the exact smaller-space error, including the
full projection-difference remainder. No equality of discrete and continuous
projections follows from inclusion alone.

**Open formalization obligations:** the continuous Nyman--Beurling/Hardy
identification and analytic inner-factor/evaluation providers for Burnol
Theorem 1.2; the BSY critical-line integral identity and integrability; and
the actual continuous-to-Pareto transport for the intended application.
The equivalent assertion `product = 1` remains RH-strength and is not proved.
Sources, theorem map, and details: `RH/BurnolZeroProductNotes.md`.

### Inverse Gram dual identities and the Pareto tail-average criterion (2026-09-23)

**Established:** `Analysis/FiniteHilbertGramDual` identifies entries of the actual
inverse Gram endomorphism with pairings of projected biorthogonal vectors.
It proves the diagonal and bilinear residual identities, retaining the full
orthogonal complement.

**Established:** `RH/ParetoInverseGramDual` specializes these identities to
`coefficientDual i = -mobiusRieszHilbert (i+2)`. It proves every fixed-entry
limit, the explicit finite divisor formula for each dual norm, and
`one_mem_iff_inverse_diagonals`. Thus simultaneous saturation of all inverse
diagonals is equivalent to membership of the constant in the full closed
residue span; an individual diagonal is only a single dual membership test.
The exact small-index targets are 14, 20, and the cross pairing -2.

**Established:** `RH/ParetoTailAverages` constructs `fullTailBasis` from the
existing wavelets plus the negative constant. It proves the absolute
summability of the weighted physical mean, the full infinite-tail formula,
the coordinate difference and finite telescoping formulas, Parseval, and
`localDirichlet_iff_tailRegular`. In this API `tailAverage f n` is the
markdown's T_(n+1), not T_n.

**Established:** `Analysis/CoefficientShift` constructs the forward/backward
coefficient differences and their adjoint pairing, and proves the abstract
dense-span annihilation lemma. `RH/ParetoTailAverageCriterion` proves the
unconditional residual identities T_1(r)=D and
sum_m |T_m(r)-T_(m+1)(r)|^2 = D-D^2.

**Established:** `Analysis/NoorLogarithmDensity` proves convergence of finite
factorial-divisor Möbius combinations of logarithmic vectors to each positive
coordinate vector. `RH/NoorShiftedResidueDensity` proves the exact normalization
of the actual shifted residue coordinates and their dense span
(`Noor.shiftedResidue_density`). The density proof uses finite divisor
cancellation and dominated convergence, without PNT or RH.

**Established:** `eq_zero_of_orthogonal_tailRegular` now proves Noor's
regularity theorem in the real Pareto model with no density hypothesis:
a tail-regular vector orthogonal to the complete residue span is zero.
Via `localDirichlet_iff_tailRegular`, this is the real coefficient form of
Noor's Theorem 12. Both `limitResidual_zero_iff_tailRegular` and
`limitResidual_zero_iff_tail_average_summable` are unconditional equivalences.
The former `ShiftedResidueDensity` obligation has been discharged and its
unused proposition wrapper removed.

**Conditional research reduction:** `riemannHypothesis_of_tailRegular`
now assumes only `TailRegular limitResidual`. The shifted density,
regular-annihilator theorem, and resulting RH implication have only the
standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
Details: `RH/NoorRegularityCompletion20260923.md`.

**Open RH-strength arithmetic assertion:** `TailRegular limitResidual`.
Square-summability of successive differences, already proved, does not
supply square-summability of the centered averages. No RH converse or
unconditional zero-residual theorem is claimed.


**Established:** Analysis/ShiftedLift verifies the exact isometric
shifted-lift identity, a scaled regularized bound, and the exact
completion/minimum formula on every lift subspace when its normal equations
are supplied. These are unconditional Hilbert-space lemmas.
**Established (2026-09-24):** `Analysis/ShiftedLiftApproximation` proves
finite-dimensional attainment for positive regularization without a
normal-equation hypothesis, and convergence of unscaled finite infima
from shifted density. `RH/NoorRegularizedApproximation` applies this to
the actual arithmetic residue spans and finite projection residuals:
`Noor.finiteMinimum_tendsto_zero` proves `J_N(t_N) -> 0` for every
parameter schedule `t_N -> 0`, along all cutoffs. For `t_N > 0`,
`Noor.exists_finite_minimizing_lifts` supplies finite arithmetic minimizers
with the same vanishing complete regularized energy. No RH-strength
arithmetic hypothesis enters either theorem.

**Established rate obstruction:** `Noor.energy_div_le_finiteMinimum_div`
proves `E_N / (1+t) <= J_N(t) / t` for `t > 0`. The infimum is also
identified with the previous exact normal-solution formula when that
solution is supplied. Axiom inspection reports only `propext`,
`Classical.choice`, and `Quot.sound`.

**Conditional research reduction:**
`Noor.riemannHypothesis_of_finiteMinimum_div_parameter_tendsto_zero`
deduces residual vanishing and RH from divided-energy convergence on a
cofinal sequence. **Open:** a cofinal arithmetic provider with positive
`t_j -> 0` and `J_{N_j}(t_j) / t_j -> 0`. The proved unscaled convergence
does not discharge this rate hypothesis. No unconditional RH or RH
converse is claimed. Details: `RH/NoorRegularizedApproximation20260924.md`.

### Exact limit of the inverse-Gram Mobius correction (2026-09-22)

**Established:** `RH/ResidueGramMobiusCorrection` now identifies the actual
arithmetic correction at each finite stage as the Mobius difference
functional applied to the full projection residual
(`correction_eq_residual_coordinate`).
`correction_tendsto_residual` and `correction_tendsto_divisor_sum` prove
its unconditional limit, explicitly as a finite divisor sum of
`limitResidual`. These statements assume only a positive conductor.

The existing captured-energy/coefficient/norm convergence equivalences
were rechecked with the new limit theorem. Axiom inspection reports only
`propext`, `Classical.choice`, and `Quot.sound`.
**Open:** vanishing of the displayed divisor sums for every conductor
at least two; this is equivalent to zero full projection defect.
Existence of their limits, the Schur recurrence, and the algebraic
Mobius decomposition do not establish this vanishing.

### Captured energy and coefficient convergence equivalences (2026-09-22)

**Established:** `RH/ResidueSchurLimits` now proves:

- `ProjectionSchur.captured_tendsto_one_iff_limitEnergy_zero`;
- `captured_tendsto_one_iff_norm`;
- `captured_tendsto_one_iff_coefficients_tendsto_mobius`;
- `captured_tendsto_one_iff_correction_tendsto_zero`.

These are unconditional equivalences of propositions, not unconditional
assertions that Q tends to one or that the fixed coefficient limits have
their Mobius values. The existing `coefficient_tendsto` proves existence of
every fixed limit. The exact Schur recurrence and inverse-Gram Mobius
decomposition remain unchanged.

**Conditional research reduction:** `riemannHypothesis_of_captured_tendsto_one`.
**Open arithmetic assertion:** Q tends to one, equivalently the full
Pareto error tends to zero or all fixed Mobius corrections vanish.

**Separate formalization gap:** the current project has approximation => RH;
its classical reverse direction RH => membership of one in the closed
residue span is not yet supplied by a checked provider. This gap is exposed
explicitly in `MellinDeficitRHTest` and `FirstCoordinateTailGap`.
The new theorems do not assert a provider-free equivalence with RH.
Representative snippet checks pass and report only standard Lean axioms.

### Coefficient limits imply zero defect and the full RH chain (2026-09-22)

**Conditional research reductions:** `RH/ResidueProjectionL1` now includes
`CoefficientStabilization.limitEnergy_zero_of_coefficients_tendsto_mobius`
and `ProjectionSchur.convergence_chain_of_coefficients_tendsto_mobius`.

Assuming the actual fixed-conductor coefficients tend to -moebius(d) for
every d>=2, the checked chain proves D=0, convergence of the actual
projections to one in L2 and L1 Pareto, convergence of the first and second
moments to one, convergence of the expanded squared error to zero, target
membership in the closed span of all residue generators, and Mathlib RH.

**Open hypothesis:** simultaneous coefficient convergence to -moebius(d).
The unconditional coefficient-stabilization theorem proves existence of
the coefficient limits; it does not identify them as the Mobius values.
The new theorem proves the requested implication and retains this premise.
Snippet verification succeeded; axiom inspection reports only
`propext`, `Classical.choice`, and `Quot.sound`.

### Pareto L1 convergence and the actual projection defect (2026-09-22)

**Established:** `RH/ThresholdHilbertL1` defines the complete weighted
`hilbertL1Norm`, proves its summability, and proves
`inner_one_le_hilbertL1Norm` and `hilbertL1Norm_le_norm`.
Thus convergence in the actual Hilbert norm implies Pareto L1 convergence.

**Established:** `RH/ResidueProjectionL1` applies these bounds to the actual
inverse-Gram projections, retaining the limiting defect D = limitEnergy.

- `ProjectionSchur.energy_le_l1_error` and `l1_error_le_l2_error` prove
  E_n <= L1_error_n <= sqrt(E_n) at every finite stage.
- `inner_one_projection_tendsto` and `projection_norm_sq_tendsto` give
  the unconditional first and second moment limits 1-D.
- `energy_expansion` and `expanded_energy_tendsto` show that the expanded
  squared error tends to 1-2(1-D)+(1-D)=D.
- `projection_l1_tendsto_limit` gives unconditional L1 convergence to
  the closed-span projection of one.
- `l1_error_tendsto_zero_iff_limitEnergy_zero`,
  `l1_error_tendsto_zero_iff_l2`, and
  `l1_error_tendsto_zero_iff_closed_span` give the precise equivalences.
- `projection_tendsto_one_of_limitEnergy_zero` retains D=0 explicitly.

**Conditional research reduction:**
`ProjectionSchur.riemannHypothesis_of_projection_l1_tendsto_zero`.
**Open:** L1 convergence of these projections to one, equivalently D=0.
The convergence audit does not establish this assertion. The L1 and L2
equivalences do not provide an unconditional RH proof.
Representative snippet axiom audits report only `propext`,
`Classical.choice`, and `Quot.sound`; the RH theorem retains its
explicit convergence hypothesis.

### Infinite Schur tails and relative-gain saturation (2026-09-22)

**Established:** `RH/ResidueSchurLimits` continues the full-Pareto Schur
recursion into exact infinite sums, retaining the limiting defect.

- `ProjectionSchur.schur_gain_hasSum`, `schur_gain_tail_hasSum`, and
  `energy_eq_limit_add_schur_tail` prove that the total Schur gain is
  1 - limitEnergy and its tail is energy n - limitEnergy.
- `schur_gain_after_two_hasSum` removes the exact first gain log 2.
- `schur_gain_tail_eq_projection_distance` and
  `coefficient_error_bound_schur_tail` identify what the tail controls.
- `captured_tendsto` proves the unconditional captured-energy limit.
- `finite_energy_factorial_floor` and `finite_energy_pos` prove a
  positive finite-stage error using the common multiple (n+1)!.
- `projectionRelativeGain_eq_schur`, `relativeGain_lt_one`, and
  `energy_relativeGain_product` give the exact normalized Schur gains
  and survival product without a not-RH assumption.
- `energy_zero_iff_relativeGain_not_summable` and
  `schur_saturation_iff_relativeGain_not_summable` prove the exact
  infinite-product criterion for this actual residue chain.
- `coefficient_total_variation_summable` proves unconditional finite
  total variation of every fixed canonical coefficient.

**Conditional research reductions:**
`riemannHypothesis_of_schur_saturation` and
`riemannHypothesis_of_relativeGain_not_summable`.
**Open:** total Schur gain equals 1, equivalently the actual relative
gains are not summable. These are explicit hypotheses, not providers.
No unconditional RH conclusion is asserted.
Representative axiom audits return only `propext`, `Classical.choice`,
and `Quot.sound`; the RH theorem still has its open hypothesis.


### Full-Pareto minimizer and exact Schur recursion (2026-09-22)

**Established:** `RH/ResidueProjectionSchur` proves the unique full-norm
inverse-Gram minimizer, exact error identity, positive innovation Schur
complement, and adjoining-generator coefficient and energy recursions.
It reuses `ResidueGramMobiusCorrection` and `ResidueGramDigamma`.
See `RH/ResidueProjectionSchur.md` for formulas and the numerical table.

- `ProjectionSchur.canonical_completion`, `canonical_minimizes`, and
  `canonical_unique` give the exact variational characterization.
- `error_eq_one_sub_captured` and `captured_eq_norm_sq` identify
  the error and b-transpose-G-inverse-b with the actual projection.
- `sigma_eq_gram_schur`, `eta_eq_gram_schur`, and `sigma_pos`
  identify the matrix Schur data and prove strict positivity.
- `projection_schur_step`, `canonicalVector_schur_new`,
  `canonicalVector_schur_old`, and `captured_schur_step` prove
  the exact projection, coefficient, and captured-energy recursions.
- `canonicalVector_one`, `projection_one`, `captured_one`, and
  `energy_one` give the exact manuscript N=2 values.

Project stage n is manuscript cutoff N=n+1. Schur index n adjoins
conductor n+2. All statements use the complete infinite Pareto norm.
The rounded N=2,...,5 table is numerically checked documentation, not
Lean-certified decimal enclosures. No convergence-to-zero is asserted.
Axiom checks report only `propext`, `Classical.choice`, and `Quot.sound`.

### Exact inverse-Gram Möbius correction and convergence (2026-09-22)

**Established:** `RH/ResidueGramMobiusCorrection` formalizes the actual full
Pareto inverse-Gram coefficients and their exact Möbius correction.
Project stage n corresponds to manuscript cutoff N=n+1.

- `source_apply` gives the source entry log(i+2)/(i+2).
- `canonicalVector_apply` and `projection_eq_inverseGram_synthesis`
  identify the inverse-Gram vector with the actual projection coefficients.
- `canonical_decomposition` holds for every reference vector;
  `canonical_mobius_decomposition` specializes it to the Möbius vector.
- `correctionVector_apply` identifies the matrix correction with c+mu.
- `correction_tendsto` proves that fixed correction limits exist.
- `correction_tendsto_zero_iff` and `correction_limits_iff_norm` prove
  correction decay iff Möbius coefficient convergence, and simultaneous
  correction decay iff full unsquared Pareto norm convergence.

**Conditional research reduction:**
`GramMobiusCorrection.riemannHypothesis_of_correction_limits` concludes Mathlib RH.
**Open:** every fixed correction tends to zero for conductors m>=2.
The exact decomposition adds no estimate proving that limit.
Axiom checks of the decomposition, norm equivalence, and conditional RH
theorem report only `propext`, `Classical.choice`, and `Quot.sound`.
The convergence hypothesis remains explicit in the RH theorem's type.

### Canonical Pareto norm convergence and closure (2026-09-22)

**Established:** `RH/ParetoNormClosure` formalizes the supplied
`Pareto_Norm_Convergence_and_Closure_Equivalence(1).md` for the actual
complete Pareto Hilbert space and the existing canonical residue projections.
The project stage n corresponds to manuscript N = n + 1.

- `projection_norm_error_tendsto`: the full unsquared error converges
  unconditionally to the norm of the actual limiting residual.
- `projection_norm_tendsto_zero_iff_mem`: error tends to zero exactly when
  the constant target belongs to the closed residue span.
- `projection_norm_tendsto_zero_iff_fixed_point`: equivalently, the closed-span
  projection fixes the target.
- `limitResidual_norm_le_projection_error`: the limiting residual norm is
  a lower bound at every finite stage.
- `projection_error_uniform_floor_of_not_rh`: if Mathlib RH fails, that
  same residual norm is strictly positive and bounds all finite errors below.

**Conditional research reduction:**
`riemannHypothesis_of_projection_norm_tendsto_zero` concludes actual Mathlib
RH from the displayed norm limit. **Open:** a proof of that limit, or an
independent proof of target membership. The equivalences do not provide it.
Axiom inspection of the equivalence, conditional RH theorem, and positive-floor
theorem reports only `propext`, `Classical.choice`, and `Quot.sound`;
the convergence hypothesis remains visible in the RH theorem's type.

### Classical Möbius cancellation and actual residual-tail dichotomy (2026-09-22)

**Established:** `RH/CanonicalMobiusPNT` supplies the previously missing
unconditional theorem `mobiusReciprocalSum_tendsto_zero` and
`canonicalMobiusHilbert_sublinear`. The formal proof uses the local PNT+ compatibility port
`NumberTheory/PrimeNumberTheorem/{Fourier,Defs,Wiener,Consequences}`,
adapted from commit `a5154676af9aa3095150ee410cdda80555aa0642`.
It preserves the project's Lean/Mathlib version and reuses the existing
Fourier, Sobolev, and logarithm ports plus pinned upstream smooth-function
and asymptotic support. Three unused alternative decay declarations with
incomplete upstream proofs are omitted. The adapter converts
`mu_pnt_alt`'s real cutoff to the project's inclusive positive Möbius sum. The ordinary normalized
Möbius limit follows from the existing Cesàro identity.

Mathematical reference: Terence Tao, *A remark on partial sums involving
the Möbius function*, arXiv:0908.4323, introduction, equation (1).
Tao records the classical PNT-equivalent limit, attributed to Landau;
the elementary bound alone does not imply it.

**Established:** `RH/ParetoResidualTailDichotomy` proves
`actual_normalized_residual_tail_dichotomy`: the actual projection
residual is zero and all normalized tail energies are zero, or the residual
is nonzero and `N * residualTailEnergy N -> atTop`.
It also proves `not_RH_normalized_residual_tail_tendsto_atTop`.

**Verification:** the combined Lean proof check reports only `propext`,
`Classical.choice`, and `Quot.sound` for `mu_pnt_alt`, the concrete reciprocal
limit, the actual-residual dichotomy, and the bounded-tail-to-RH implication.

**Conditional research reductions:**
`limitResidual_zero_of_frequently_bounded_actual_tail` and
`riemannHypothesis_of_frequently_bounded_actual_tail` need only a bounded
cofinal subsequence of the normalized actual residual tails.
**Open:** that tail upper-bound provider. RH-to-zero-residual is not claimed
by this module; the separate RH-to-density formalization obligation remains.

### Two optimal coefficients and the full Pareto error (2026-09-22)

**Established:** `RH/OptimalTwoCoefficientCriterion` proves the exact identity
`4 - 3 * limitCoefficient 2 - limitCoefficient 3 =
(1/12) * norm(6r - (13/2)Dr + 3D^2r)^2 + (23/24) * limitEnergy`,
where r is the actual limiting projection residual and D is the project's
scaled dilation, Df(j)=2f(floor(j/2)). Consequently the single scalar
limit `3 * coefficient n 2 + coefficient n 3 -> 4` is equivalent to
vanishing full Pareto error. The project index n uses g_2 through g_(n+1).

**Conditional research reductions:** `riemannHypothesis_of_twoThreeCoefficients`
and `riemannHypothesis_of_second_and_third_coefficients` conclude actual
Mathlib RH from this scalar limit, or from the two separate coefficient
limits to 1. **Open:** a provider for those limits. The exact Gram formulas
and positivity of Schur gains do not discharge that obligation.
The checked identity, equivalence, and RH implication use only ordinary
Mathlib foundational axioms; the scalar limit is a local hypothesis.

**Established distinction:** `RH/ExactHeadCoefficientCounterexample` proves
that growing exact heads force every fixed coefficient to its Mobius target,
and constructs finite legal vectors with all those limits but full squared
error at least N^2. Thus the optimal-projection hypothesis in the preceding
criterion matters. Its counterexample has no PNT or RH assumptions.

**Further established finite estimate:** `RH/OptimalProjectionDilationGaps`
proves `dilationCorrection_norm_identity`, the exact sum-of-squares
bound for W=-4I-13D+3D^2 with squared constant 5425/12, and
`dilationCorrection_two_gap_sq_bound`. At stages m, n=4m+3,
k=4n+3, the square of the residual pairing is at most
(5425/12)(energy n-energy k)(energy m-energy n).
These are the same unconstrained optimal projections as above.
**Still open:** proving that their total Schur gain equals the initial
error; this finite estimate does not establish zero limiting error.

### Exact signed Schur gains and fixed-head capacity density (2026-09-22)

**Established:** 47 declarations in six modules. `RH/CanonicalMobiusTailIndependence`
proves complete-tail injectivity, new canonical directions, and positive definite
full-tail covariance for every finite set of distinct positive indices.
`Analysis/FiniteGramOneStepCapacity` constructs screening for singular Gram systems
and proves the exact one-vector gain. `RH/CanonicalMobiusOneStepCapacity` specializes
this to actual infinite tails: eta = 1 - sum a, sigma = C_mm - a^T b, C a = b,
capacity increment = eta^2/sigma. Every higher new index has sigma > 0.
`RH/CanonicalMobiusWindowRecursion` proves the actual window recursion, diagonal
initial value, and exact telescope of all signed gains.

`RH/CanonicalMobiusHeadRepair` constructs continuous triangular legal head repair.
It proves that finite legal exact-head vectors approximate every target in the
corresponding closed affine slice, with fixed head length.
`RH/CanonicalMobiusCapacityDensity` proves density iff conductor-capacity divergence
at every fixed positive head, iff every such head admits capacity at least one.

**Conditional research reductions:** divergence of the actual signed-gain sums at
every fixed positive head implies actual Mathlib RH. **Open research provider:**
that divergence, or the weaker positive cofinal capacity lower bound.
No cumulative arithmetic numerator lower bound is supplied.
**Open formalization provider:** the previously recorded RH-to-density converse.
Classical reciprocal Möbius cancellation is now supplied by
`RH/CanonicalMobiusPNT`. Neither is assumed by these finite identities or
geometric equivalences. No RH proof is claimed.
See `RH/ParetoExactSchurContinuation20260922.md`.


### One fixed head and the attained infinite capacity dual (2026-09-22)

**Established:** 34 declarations in three modules.
`RH/ParetoFiniteHeadDilation` proves the exact finite-head dilation identity,
the two-sided residual pairing bound
`(1 - 1/sqrt(N+1))*delta <= h_N <= (1 + 1/sqrt(N+1))*delta`,
positive residual pairing at EVERY positive head, and the uniform all-family
capacity bound `capacity <= T_N / (delta^2*(1-1/sqrt(N+1))^2)` when delta>0.
Membership of any one positive head indicator is equivalent to full legal density.

`RH/CanonicalMobiusWindowDuality` identifies bounded fixed-head capacities
with existence of a common infinite normal witness. The actual finite normals
converge strongly; their limiting energy equals the capacity supremum.
The infinite minimum is attained and unique, with exact finite and infinite
Pythagorean remainders. A nonzero actual residual supplies an explicit common
normal at every positive head; not RH therefore gives finite normal limits.

`RH/CanonicalMobiusFixedHeadLimit` identifies inverse capacity with the
optimizer's squared distance to the finite head indicator. It proves that,
for ANY ONE fixed N>=1, density is equivalent to capacity divergence and to
divergence of that single exact signed Schur-gain series.
Bounded capacity at any one head is equivalent to failure of legal density;
mixed bounded/divergent behavior between positive heads is impossible.
Under not RH, every fixed-head gain series has an exact finite normal-energy limit.

**Conditional research reduction:** divergence of the single gain series at
N=1 implies actual Mathlib RH. **Open research provider:** this divergence,
equivalently exclusion of the corresponding infinite common normal.
No such exclusion, residual vanishing, or RH proof is supplied.
The separate RH-to-density converse remains a formalization provider.
The concurrent `RH/CanonicalMobiusPNT` now supplies unconditional reciprocal
Mobius cancellation; neither input is assumed by these new results.
See `RH/ParetoSingleHeadDualityContinuation20260922.md`.


### First-head projection identity and all-annihilator heavy tails (2026-09-22)

**Established:** 42 declarations in four modules.
`Analysis/SingleObservationProjection` proves the attained one-observation
projection minimum, its exact completion, and optimizer uniqueness.
`RH/CanonicalMobiusSingleHeadCapacity` identifies the actual first-point
projection error `t_M = 1 / (windowCapacity 1 M + 2)`, proves its conductor
limit, and expresses its exact one-step decrease through the signed Schur gain.
In the nondense case, the capacity limit is `1/t - 2`, the energy of the
actual limiting normal, where `t = ||e_1 - P_S e_1||^2`.

`RH/ParetoAnnihilatorTail` proves that EVERY nonzero vector in the actual
legal annihilator satisfies `N * ||tail_N z||^2 -> atTop`, without a
nonzero-mean hypothesis. It uses the unconditional canonical sublinear energy,
integer dilation invariance, and totality of the integer threshold family.
Any annihilator with a bounded cofinal normalized-tail subsequence is zero.

`RH/ParetoFirstHeadDefect` constructs `rho = e_1 - P_S e_1`, proves its
positive constant pairing when the original residual energy delta is positive,
and verifies `(6 - 4*sqrt(2))*||rho||^2 <= delta <=
(6 + 4*sqrt(2))*||rho||^2`. Hence in the nondense case
`6 - 4*sqrt(2) <= delta*(||Z_1^*||^2 + 2) <= 6 + 4*sqrt(2)`.

**Conditional research reduction:** a bounded cofinal normalized-tail
subsequence for this one first-point projection defect implies Mathlib RH.
**Open research provider:** that upper bound, or equivalently at the geometric
level vanishing first-point error/divergence of the single-head capacity.
The heavy-tail theorem does not exclude all possible nonzero annihilators.
No RH proof is supplied; the separate RH-to-density converse remains unformalized.
See `RH/ParetoSingleHeadProjectionContinuation20260922.md`.

### Compressed-dilation reconstruction and a single cyclic obstruction (2026-09-22)

**Established:** 19 theorem declarations in two modules.
`Analysis/ContractiveNeumannReconstruction` proves the exact finite Neumann
remainder, its geometric squared-norm bound, and strong convergence under an
explicit global squared-contraction hypothesis.
`RH/ParetoResidualDilation` discharges that hypothesis for the actual
compressed unscaled integer dilations A_B = P_(S^perp) U_B. It proves
A_B A_C = A_(BC), A_B P_(S^perp) = A_B, and
||A_B x||^2 <= ||x||^2/B.

For the actual first-head defect rho and canonical residual r it proves
rho = r - A_2 r, the exact finite remainder
r - sum_(j<M) A_2^j rho = A_2^M r, the error bound
||r - sum_(j<M) A_2^j rho||^2 <= 2^(-M) limitEnergy, and strong convergence.
The theorem `annihilator_eq_zero_of_inner_firstHead_orbit_zero` proves that
z in S^perp orthogonal to every A_B rho must vanish. Thus the orbit separates
the whole annihilator space; the checked statement is this exact separation
criterion.

All actual RH-module results are unconditional. The reconstruction terms
belong to S^perp and converge to the possible obstruction r.
**Open research provider:** an estimate forcing rho = 0, such as the already
recorded bounded cofinal normalized-tail condition or first-head capacity
divergence. The contraction equation contains the forcing term rho and does
not prove RH. No missing arithmetic estimate is marked established.

The combined source check `job_geHw5Bsra-F-98k2VqZheRjR7QZBZvto` passed with
exit code 0, verified true, and no warnings. Principal axiom audits report only
`propext`, `Classical.choice`, and `Quot.sound`.
See `RH/ParetoResidualDilationContinuation20260922.md`.

### Canonical finite affine exhaustion and exact capacity increments (2026-09-22)

**Established:** `NumberTheory/IsolatedPrimeReciprocalSum` and
`RH/MobiusReciprocalNonvanishing` prove finite nonvanishing m_N ≠ 0 for N>0
by Bertrand and integer denominator clearing, without PNT or RH.
`RH/CanonicalMobiusTriangular` proves the adjacent-step identities,
canonical span = full finite legal span, finite head injectivity, and an
actual mass-one canonical-window expansion of every finite legal exact-head
vector. At diagonal budget the canonical vector is the unique candidate.

`RH/CanonicalMobiusWindowMinimum` proves the attained minimum over ALL
finite legal vectors at budget M+1 with head 1..N equal to one:
full norm squared = N/(N+1) + inverse window capacity.
`Analysis/FiniteGramCapacityIncrement` and
`RH/CanonicalMobiusCapacityIncrement` identify capacity gain with the
squared change of synthesized normal vectors, characterize saturation,
and bound signed new-equation defects by screened energy times gain.
Singular Gram systems and noninjective family maps remain allowed.

**Open research provider:** a positive cofinal lower bound for window
capacity, equivalently sufficient bounded cofinal exact-head energies.
The classical limit m_N → 0 is now supplied by `RH/CanonicalMobiusPNT`.
Finite nonvanishing and spanning are discharged; no RH proof is claimed.
See `RH/ParetoAffineExhaustionContinuation20260922.md`.


### Quantitative signed capacity and uniform residual obstruction (2026-09-22)

**Established:** `RH/CanonicalMobiusCapacityBounds` proves the exact residual
head pairing and `capacity * residualHeadPairing^2 <= residualTailEnergy`.
For positive residual energy, all admissible finite families simultaneously
satisfy `capacity <= 4 * residualTailEnergy / limitEnergy^2` eventually.
Under not RH, decay is uniform over all finite index types and conductor
horizons. Each member gives the strict lower bound `capacity > 1/(4*k_i)`.

`Analysis/FiniteGramAffineMinimum` proves monotonicity under affine transfer
or a possibly noninjective family map. `RH/CanonicalMobiusCovarianceMinimum`
applies it to family enlargement and proves the exact fixed-family cutoff law
`cap(N)^-1 = cap(K)^-1 + K/(K+1) - N/(N+1)`.

**Established arithmetic implication with explicit classical premise:**
`normalized_capacity_tendsto_atTop_of_reciprocal_cancellation` proves
`N * capacity_N -> atTop` when the family eventually contains index N and
`mobiusReciprocalSum -> 0`.
The classical premise is now supplied by `RH/CanonicalMobiusPNT` through
`mobiusReciprocalSum_tendsto_zero`.
**Open research provider:** a fixed positive cofinal capacity lower bound.
These bounds permit capacity to tend to zero; RH is not proved.
See `RH/ParetoCapacityBoundsContinuation20260922.md` for exact coverage.


### Signed covariance minimum and one-input arithmetic bridge (2026-09-22)

**Established:** `Analysis/FiniteGramRange` proves singular Gram solvability
from synthesis-kernel compatibility. `Analysis/FiniteGramAffineMinimum` proves
the attained mass-one minimum, exact signed completion, uniqueness of the
synthesized minimizer, and independence of the scalar normal mass.
`RH/CanonicalMobiusCovarianceMinimum` discharges compatibility for actual
canonical infinite tails using finite periodicity. It constructs `C z = 1`,
proves `capacity = sum z > 0`, and attains minimum tail energy `1/capacity`.
The exact full energy is `N/(N+1) + 1/capacity` when every index is at least N.
Failure of RH forces these capacities to tend to zero for every growing
nonempty finite family satisfying that index condition.

**Established arithmetic implication:** `RH/CanonicalMobiusCesaro` proves
`M(N) = N m_N - sum_(k<N) m_k`; convergence of m_N to any finite limit implies
M(N)/N tends to zero. The sublinear-energy theorem thus needs only m_N -> 0.

**Conditional research reductions:** a fixed positive capacity lower bound
along arbitrarily large cutoffs implies Mathlib RH, without a PNT premise.
`RH/ParetoResidualTailDichotomy` now supplies the corresponding RH reduction
from bounded cofinal normalized residual tails alone, using the classical
limit proved in `RH/CanonicalMobiusPNT`.
**Open:** the positive cofinal capacity lower bound or residual-tail upper
bound.
No RH proof or vanishing projection residual is asserted. Exact declarations
and verification are recorded in `RH/ParetoCovarianceMinimumContinuation20260922.md`.

### Canonical Mobius full energy and sublinear residual tails (2026-09-22)

**Established:** `RH/CanonicalMobiusFullEnergy` realizes the manuscript's
canonical family in the actual Pareto Hilbert space, proves its finite-span
membership and exact head, its all-coordinate floor formula, the full
infinite head/tail norm identity, and
`canonicalMobiusHilbert_norm_sq_le`:
`||u_N||^2 <= N(4N+1)/(N+1) < 4N` for positive N.

**Established analytic implications:** `Analysis/SublinearEnergyLimits`
proves the fixed-cutoff limiting step and positive-product divergence.
`RH/ParetoSublinearResidualTail` proves that sublinear exact-head full
energy forces `N * residualTailEnergy N -> atTop` when `limitEnergy > 0`.
The concrete canonical specialization supplies verified head and legality
providers. Failure of RH forces every exact-head family's full energy to
diverge.

**Conditional research reductions:** a bounded cofinal subsequence of
exact-head full energies implies actual Mathlib RH, without a sublinear
premise. Sublinear energy together with a bounded cofinal subsequence of
normalized residual-tail energies also implies RH.

**Established arithmetic-to-energy implication:**
`NumberTheory/FiniteFloorTail` proves finite floor-tail double counting.
`RH/CanonicalMobiusWindowCancellation` proves the exact Möbius tail
identity and fixed-window estimate. `RH/CanonicalMobiusSublinearEnergy`
proves the full head/window/infinite-tail cutoff bound and
`canonicalMobiusHilbert_sublinear_of_mobius_cancellation`.
Its precise hypotheses are M(N)/N→0 and m_N=Σ(d≤N)μ(d)/d→0.
`canonical_normalized_tail_tendsto_atTop_of_mobius_cancellation`
uses this result for the actual residual, without an extra energy premise.

The two classical cancellation inputs are now supplied by
`RH/CanonicalMobiusPNT` and the Cesàro theorem in `RH/CanonicalMobiusCesaro`.
The older implication theorems retain their explicit hypotheses for reuse.
**Open research providers:** bounded cofinal candidate energy or normalized
residual-tail estimates. The new
`canonical_limitEnergy_zero_of_frequently_bounded_tail` is a conditional
research reduction with these obligations explicit. No vanishing actual
residual, approximation convergence, or RH is asserted.
See `RH/ParetoSublinearEnergyFormalization20260922.md` for exact coverage.

### Signed canonical averages and tail nondegeneracy (2026-09-22)

**Established:** `RH/CanonicalMobiusSignedAverages` proves finite legality,
exact heads, the dyadic average, the complete infinite tail-covariance
identity, and its signed quadratic expansion and nonnegativity.
`RH/CanonicalMobiusTailNondegeneracy` proves that every covariance-null
direction over positive candidate indices has coefficient sum zero.
Every admissible finite average at a positive cutoff therefore has strictly
positive tail energy; no uniform lower bound is asserted.

**Conditional research reductions:** frequently bounded actual signed
tail-covariance energies imply Mathlib RH. This criterion needs no PNT
premise. `riemannHypothesis_of_mobius_cancellation_and_bounded_tail`
also assembles the published arithmetic-to-energy chain into actual RH
from the two explicit PNT limits and frequently bounded normalized
residual tails.

**Open:** the bounded signed-covariance or residual-tail provider.
The classical PNT inputs now have checked providers in
`RH/CanonicalMobiusPNT` and `RH/CanonicalMobiusCesaro`. No unconditional
residual vanishing or RH is claimed. See
`RH/ParetoSignedAverageContinuation20260922.md`.

### Exact Ramanujan coordinates, periodic Green inverse, and qN (2026-09-22)

**Established:** `RH/IntegratedRamanujanMarkedArithmetic` proves the head
value `-mu(q)`, nonsquarefree head vanishing, prime-power floor formulas,
full Pareto norm scaling, and common-prime-power correlation scaling.
`RH/ParetoPeriodicPacketGreen` proves the complete finite-period Green
identity, including the zero-boundary version on `1,...,L-1`.
`LinearAlgebra/WeightedGreenInverse` proves the Green action, inverse flux
formula, tridiagonal rows, and exact weighted Dirichlet identity.

**Established:** `Analysis/FiniteGramBasisInvariance` and
`RH/RamanujanFiniteSpanBridge` prove equality of the actual finite residue
and packet spans and capacities. `qN_eq_packetInverseGram` identifies the
existing DPP probability with `W_L(1) * mu^T Xi^(-1) mu`.
`residue_inverseGram_eq_packetInverseGram` proves the corresponding exact
identity for `b^T G^(-1) b`. The actual Gram inverse follows from independence.

**Established algebra:** `LinearAlgebra/RankTwoWoodbury` proves the explicit
two-variable elimination from an actual symmetric rank-two matrix identity.
`RH/IntegerDPPPacketRankTwo` defines the finite cotangent sum and its double
Mobius-divisor core, and proves the core's symmetry.

**Conditional research reductions:** `RH/IntegratedRamanujanRankTwo` and
`RH/IntegerDPPPacketRankTwo` apply that algebra to the actual arithmetic
Gram and the canonical `qN`. **Open providers:** the proposed cotangent
identification of the full Gram, a symmetric inverse for that core at each
relevant finite stage, and nonvanishing of the small Schur denominator.
These are explicit hypotheses; the desired marked quadratic is derived.
**Open:** `qN N -> 1` and RH. Neither is asserted by this addition.
The complete informal calculation and formal coverage ledger are recorded
in `RH/RamanujanGreenSchurFormalization20260922.md`.

### Exact residue-class DPP probabilities (2026-09-21)

**Established:** `RH/IntegerDPPResidueProbability` proves that the actual
probability of occupying physical class 1 modulo any positive common
conductor equals its full Pareto progression weight times `fullCapacity`.
It defines the canonical lcm modulus and `qN`, then proves the exact
inverse-Gram, orthonormal-sum, determinant-ratio, and successor identities.
The proof uses almost-sure arithmetic exclusion and countable additivity.

**Established:** `RH/IntegerDPPResidueSmallValues` computes `qN 1 = 1` and
the exact closed expression for `qN 2` in log(2), log(3), and pi/sqrt(3).
`RH/ResidueSmallGram.progressionWeight_six_one` supplies the exact full
class weight. These are unconditional statements about the actual DPP.

**Established (2026-09-22):** `RH/IntegerDPPResidueAccounting` gives the
actual DPP kernel-increment recurrence, and exact telescoping from `qN 1=1`.
The nonnegative entry and retention-loss series are summable, with total
entry at most total loss and total loss at most `log(2*log 2)<log 2<1`.
`qN_liminf_eq_entry_loss` computes the actual limit/liminf as one plus total
entry minus total loss, using direct recurrence accounting.

**Established:** `RH/IntegerDPPResiduePrimePowers` proves the canonical
modulus is unchanged exactly when `vonMangoldt (N+2)=0`; at a prime power
`N+2=p^(k+1)` it is multiplied by p. Non-prime-power steps have retention
factor one, zero loss, and nondecreasing qN. All losses are prime-power
losses. The infinite prime-power entry sum is less than one, and the
infinite prime-power loss sum is less than log two. These sums start at N=1.

**Established limitation:** `retentionOnly_liminf_lt_one` verifies a scalar
comparison sequence with the same actual arithmetic weights, initial value
one, retention recurrence, and values in (0,1], whose limit is
`1/(2*log 2)<1`. It is not asserted to be the arithmetic DPP.
**Open:** equality of the actual total entry and total loss. By
`qN_liminf_eq_one_iff_entry_eq_loss`, this is exactly the remaining assertion
for liminf qN equal to one. No unconditional saturation or RH proof is supplied.

**Established (2026-09-22):** `RH/IntegerDPPResidueSymbolic` proves the
nonrecursive prime-product formula for the canonical modulus and its prime
valuations. It expresses every progression weight and full Gram entry as
finite remainder sums with exact rational-argument digamma constants, whose
Gamma logarithmic-derivative definition is also recorded.

`qN_eq_symbolic_determinant_ratio` gives the actual probability as
`1 - det(M - Delta_1 J)/det(M)`, for the explicitly defined finite matrix
M. `qN_eq_finite_symbolic_formula` expands both determinants into finite
signed permutation sums. `residueDeterminantPolynomial_zero_pos` proves
the denominator is positive for every N. These formulas are unconditional,
contain no entry/loss or unknown capacity inputs, and retain all Pareto tails.

**Open:** the limiting assertion `qN N → 1`; none of these identities
asserts saturation or proves RH.


### Invariant defect under independent even correction (2026-09-21)

**Established:** `RH/ParetoIndependentEvenDefect` proves that every legal
first-point lift has defect exactly minus its head times the first-point
defect. For the actual independently corrected normalized sieves it proves
the exact identity: block-mean energy plus half the complete contrast energy
equals kappa squared times limiting vacancy divided by four, plus half the
full legal projection energy.

**Conditional obstruction:** under not-RH, the block-mean energy is eventually
at least kappa squared times the positive limiting vacancy divided by eight,
uniformly over EVERY finite even-dictionary size. Its not-RH hypothesis is
explicit; no off-line-zero existence, vacancy positivity, or RH conclusion
is asserted unconditionally.
**Open:** vanishing limiting vacancy and full independently corrected energy.
The accompanying analytic candidate failures are ordinary proofs, not
declarations in this module.

### Explicit exhaustive legal residue families (2026-09-21)

**Established:** `RH/ResidueExhaustiveFamilies` supplies ordinary, dyadic,
and factorial cutoffs, and the adjacent-difference dictionary. Every residue
generator appears at a finite stage; the adjacent-difference finite spans
equal the original finite spans exactly. The full-norm projections converge
strongly to `closedSpace.starProjection`, and converge to each vector already
in `closedSpace`. The exact error decomposition retains the entire limiting
defect. The first-point defect lower bound is uniform across all cutoffs.

**Established equivalence:** `tendsto_identity_iff_top` identifies convergence
to the ambient identity with `closedSpace = top`; `tendsto_identity_iff_one`
identifies it with convergence to the constant target alone.
**Conditional research reduction:** `riemannHypothesis_of_identity` proves
actual Mathlib RH from the full strong-convergence premise.
**Open:** ambient identity convergence / residue density. No unconditional
RH proof or formal RH-to-density converse is supplied.

### Exact diagonal cardinal residues (2026-09-21)

**Established:** `RH/ParetoDiagonalCardinal` defines a concrete
three-residue vector `diagonalCardinalResidue` and proves its actual
finite-dictionary membership, exact floor identity, upper-half head
interpolation, and top-third doubled-coordinate matrix formula
`C(M,j)(2*i) = indicator(i=j) - (M+1)/(j*(j+1))`.
No RH, density, or norm estimate is assumed.

The separate Cauchy-Binet/exponential determinant obstruction is an ordinary
mathematical derivation, not a Lean theorem in this module. It does not
settle any unrestricted energy, weighted-vacancy, or saturation endpoint.

### Positive finite arithmetic windows (2026-09-21)

**Established:** `RH/IntegerDPPWindowPositivity` constructs exact finite
head interpolation in the actual residue closure using integer dilations.
`limitingWindow_projected_basis_independent` and
`limitingKernel_window_posDef` prove strict positive definiteness of
every finite limiting compression. `limitingLaw_window_occupation_pos`
proves every prescribed finite occupation event has positive probability.
`positiveFiniteHead` is a checked provider for the formerly open
`HistoricalTargets.PositiveFiniteHead` proposition.

These declarations have no RH, zero-existence, density, or energy hypotheses.
**Open:** saturation at one; any uniform or subpower lower bound as the
window grows. Finite positive definiteness alone does not supply these.

### First-point subpower witnesses (2026-09-21)

**Established:** `RH/ParetoFirstPointSubpower.firstPoint_power_obstruction_of_not_RH`
quantifies the complete-energy obstruction uniformly over every exact
first-point head: if RH fails and a is nonzero, some fixed p,c>0 satisfy
`a^2/2 + c*(N+1)^p <= ||f||^2` for all N>=1 and every f in the actual
residue closure with the prescribed head.

**Conditional research reductions:** `riemannHypothesis_of_firstPoint_head_small_power_witnesses`
needs only one genuine witness below `c*(N+1)^p` for each p,c>0;
`riemannHypothesis_of_firstPoint_head_subpower` specializes to a family
whose complete squared norms divided by every positive power tend to zero.
**Open:** construction and the full-energy estimate. No upper bound,
vanishing weighted vacancy, spectral saturation, or RH is asserted.
All three declarations use only ordinary Mathlib foundations.

### Independent even corrections, full block energy, and bounded first-point heads (2026-09-21)

**Established:** `Analysis/FiniteHilbertHeadConstraint` proves exact
one-observation finite Gram minimization and the nested-dictionary identity
old energy = new energy + squared change in the optimizer.
`RH/ParetoIndependentEvenCorrection` applies this with an independent even
dictionary, preserving every odd contrast of normalized candidates.

**Established:** `RH/ParetoFullContrastEnergy` proves summability and the full
norm bound for the complete contrast series of every actual Hilbert vector.
`RH/ParetoParityBlockEnergy` identifies the entire remaining energy as
f(1)^2/2 + twice the norm squared of the dyadic half-adjoint. For the genuine
corrected factorial sieve, full-energy decay is equivalent to decay of its
actual block-mean norm; the exact arithmetic contrast term is retained.

**Established:** `RH/ParetoBoundedCoordinateClosure` proves that a uniformly
bounded coordinatewise-convergent family in a submodule has its limit in
that submodule's norm closure. `RH/ParetoFirstPointHeadObstruction` proves
the explicit polynomial complete-energy lower bound for exact first-point
heads at any hypothetical right-half-plane zeta zero, including the full
factor |1-2^(-s)|^2/|s|^2.

**Conditional research reduction:** a uniformly full-norm-bounded genuine
legal family with growing first-point heads implies Mathlib RH, without an
RH-to-density provider. **Open:** the uniform bound or corrected-sieve
block-mean decay. Monotonicity under even refinement and vanishing parity
contrast do not discharge those arithmetic obligations.
**Conditional research reduction:** `RH/ParetoIndependentEvenRH` proves
that the actual corrected sieve plus its fixed first-point head is legal,
and derives Mathlib RH from the displayed block-mean decay for any schedule.
The complete block-mean estimate remains **Open**.
No unconditional RH or off-line-zero existence is asserted.

### Normalized even optimization, harmonic corrections, and solved parity contrasts (2026-09-21)

**Established:** `RH/ParetoOddMomentNormalizedSchur` constructs the unique
optimal even correction for fixed signed odd coefficients with h=kappa*J.
Its exact energy is ||x_b||^2+r_b^2/K_n, with positive K_n, an affine
completion, uniqueness, and a dictionary-independent multiplicative bound.
`RH/ParetoNormalizedOddOptimizer` gives the exact nonnegative energy cost
of normalizing the existing global odd-moment inverse-Gram optimizer.

**Established:** `RH/AdjacentResidueHarmonic` and
`RH/ParetoAdjacentMomentCorrection` construct adjacent odd/even packets,
preserve the physical head and reciprocal head, normalize the odd moment,
and retain full signed correction energy. Their full packet energy lies
between d^2*(H_d-d/(d+1)) and d^2*H_d; the literal infinite remainder is bounded.

**Established:** `RH/ParetoParityContrast` proves exact finite arithmetic
contrast extraction with the complete orthogonal remainder retained.
`RH/ParetoParitySieveMass`, `RH/ParetoSieveMobiusBridge`, and
`RH/ParetoSieveContrastClosure` construct actual finite all-divisor Mobius
vectors with normalized odd moment, prove the exact coprimality mask and
mass identity, and establish that their entire odd-pair contrast energy
tends to zero along factorial stages. This is unconditional, with no
prime-rate, RH, density, or zero-existence premise.
`RH/ParetoSieveFullEnergy` retains the separate actual site-two lower
bound (2*head-a)^2/6 on the full norm.

**Conditional research reduction:** the normalized-even small-tail condition
implies RH and is equivalent to the original small-tail condition.
**Open:** prove the complete optimized energy small, including the
block-mean remainder. The solved contrast component is not the full norm;
no small-tail witness family or unconditional RH is asserted.
Ordinary infinite-space geometry and additional Euler-product specializations
are distinguished from Lean results in the accompanying research notes.

### Dyadic repair obstruction and admissible reciprocal head (2026-09-21)

**Established:** `RH/ParetoOddMomentDyadicRepair` identifies the three-scale
repair with R=I-2T_2. It proves its exact signed energy and the bound
||Rf|| >= (2sqrt(2)-1)||f||. Repaired odd-moment-one mixtures have a
positive full-energy floor, and repeated repairs give a geometric lower
bound. Vanishing Mellin value at s=2 is compatible with norm expansion.

**Established:** `RH/ParetoOddMomentHeadNormalization` proves
<F_c,z_2>=h(c)-kappa*J(c), where kappa=pi^2/(pi^2-8).
Thus J=1 and h=0 force energy at least kappa^2/||z_2||^2>0 for arbitrary
signed full-dictionary coefficients. Changing only the modulus-two
coefficient by 2(kappa*J-h) preserves J and sets h=kappa*J exactly.
The full correction energy and a dictionary-independent norm bound
are proved. Small-tail existence with J=1 is equivalent to small-tail
existence with J=1 and h=kappa.

**Open:** construct these signed witnesses, equivalently prove Q_n
unbounded. Their existence remains the premise of the existing RH
endpoint. No RH, not-RH, density or zero provider is added.
DPP sampling is not used; no new arithmetic benefit was established.

### Odd-moment matched dyadic obstruction and repair (2026-09-21)

**Established:** `RH/ParetoOddMomentDyadicObstruction` constructs the actual
signed packets g_d-2g_(2d), verifies their full-dictionary synthesis and
odd reciprocal-square moment, and proves exact initial head cancellation.
Their Mellin transform at s=2 is -zeta(2)/(4d^2). Every signed mixture with
odd moment one has full tail energy at least 81*|zeta(2)|^2/16 > 0.
When all active odd moduli exceed N, the bound is
3*(N+1)^3*|zeta(2)|^2/16. Independent Hilbert corrections must cancel the
fixed Mellin value; the quantitative energy obstruction is explicit.

**Established:** The three-scale packet g_d-6g_(2d)+8g_(4d) retains
initial head cancellation and the odd coefficient moment while its actual
Mellin transform at s=2 is exactly zero. This repairs one bounded
functional obstruction; no small-norm theorem is asserted.

**Resolved negatively:** the normalized three-scale repaired combinations
cannot have vanishing energy; see the dyadic repair continuation above.
**Open:** small-energy witnesses for the unrestricted odd Schur optimizer.
The restricted packet bounds do not apply to that full Schur problem.
No RH, density, or zeta-zero existence premise is used in the new results.

### Odd-moment parity elimination and sign obstruction (2026-09-21)

**Established:** `RH/ParetoOddMomentParity` proves independence of the
odd atoms after projection off all even atoms, the exact full Schur
Gram entries, and the unique optimal even coefficients. Its energy
completion retains the entire even correction. The original defect
minimum and capacity equal those of the screened odd system exactly.

**Established:** `RH/ParetoOddMomentSignObstruction` proves that every
nonnegative odd-moment-one coefficient vector has physical value at
least six at site two and full tail energy at least six. Thus energy
below six requires a negative coefficient.

**Conditional research reduction:**
`riemannHypothesis_of_screenedOdd_small_tail` proves RH from normalized
screened odd combinations of arbitrarily small energy. This condition
is equivalent to the original full-dictionary small-tail condition.
**Open:** constructing those signed vectors or proving the equivalent
capacity unboundedness. No RH, not-RH, density or zero provider was added.

### Odd-moment variational problem (2026-09-21)

**Established:** `Analysis/FiniteGramSourceTranslation` proves the exact
minimum-vector translation and signed capacity identity for subtracting
the observations of a fixed Hilbert vector, with two-sided finite bounds.

**Established:** `RH/ParetoCoprimeDefectVariational` defines the actual
odd-source interpolation minimum and inverse-Gram energy Q_n. Its nested
energies are monotone; Q_n=C_n-2<tailMinimum_n,z_2>+||P_n z_2||^2 exactly.
Uniform boundedness of Q_n, boundedness of C_n, existence of a single
Hilbert interpolant for all odd-source observations, and summability of
the existing full signed row energy are equivalent without an RH premise.

**Established:** For n>=2, Q_n>0. With kappa=pi^2/(pi^2-8), the actual
coefficients (kappa/Q_n)G_n^{-1}H_n have odd reciprocal-square moment one
and exact minimum full tail energy kappa^2/Q_n. The completion retains
the squared distance from this optimizer. Even and composite dictionary
vectors remain. Unbounded Q_n is equivalent to existence, for every
epsilon>0, of a finite legal combination with odd moment one and tail
squared norm less than epsilon.

**Conditional research reduction:**
`riemannHypothesis_of_oddMoment_small_tail` proves RH from these witnesses.
**Open:** construction of the small-energy witness family, equivalently
unbounded Q_n or nonsummable screened row energy. No unconditional RH,
not-RH, or new density/zero provider is asserted.

### All-modulus observations and odd-source screening (2026-09-21)

**Established:** `RH/ParetoCoprimeCompositeObservation` proves the actual
certificate observation 1/d - F_P(d) for every d >= 2, where
F_P(d)=M_P/[d^2(M_P-1)] when gcd(d,P)=1 and zero otherwise.
It reindexes the convergent divisor mass without a primality premise.

**Established:** `RH/ParetoCoprimeDefectScreening` evaluates every raw
refinement entry as a difference of F values. For P=2 the source H(d)
is zero at even moduli and pi^2/[(pi^2-8)d^2] at odd moduli, with exact
HasSum pi^2/8 over d >= 2. The full signed row is exactly
L_n=H(n+3)-sum_(i<=n) c_(n,i) H(i+2), using the actual full inverse-Gram
projection coefficients. Its normalized square is the existing row energy.
All thirteen new theorems are unconditional. Composite dictionary vectors
remain in the Gram matrix and Schur denominator.

**Open:** nonsummability of this screened energy, the arithmetic premise
of the existing conditional RH reduction. The summable raw source does
not control the growing inverse Gram matrices or Schur denominators.

### Prime-only refinements and raw arithmetic cancellation (2026-09-21)

**Established:** `RH/ParetoFactorialRefinementArithmetic` proves that the
factorial refinement d_n is nonzero exactly when n+3 is prime. Composite
columns of the screened cross-Gram matrix vanish, giving an exact prime-only
column sum without removing composite dictionary rows.

The exact refinement energy is D_n = E_(n+1) - E_n; at prime stages
D_n = delta_n * E_(n+1). For raw tail-atom pairings B(n,m), every prime row
has B(n,m)=0 above the diagonal, B(n,n)=delta_n, and
B(n,m)=-D_m/[2(n+3)^2] below the diagonal. Earlier prime entries are negative.
The complete raw row is (1+E_0/2)/(n+3)^2, and its ratio to the positive
diagonal is exactly (E_0+2)/(E_n+2), tending to zero along prime stages.
All thirteen new theorems are unconditional.

**Open:** nonsummability of the actual screened row energy. The raw matrix
already has strong arithmetic cancellation; its identities and convergence
do not establish the screened matrix's row-energy limit or RH. The next
arithmetic question is the effect of full-dictionary orthogonal screening.

### Full signed cross-Gram row energy (2026-09-21)

**Established:** `Analysis/OrthogonalPairingEnergy` proves normalized
orthonormality, summability and Bessel bounds for fixed-vector pairings,
and invariance of weighted square summability under a finite-energy addition.
The cross-stage Schur row identity now holds without a primality premise.

`RH/ParetoCrossGramRowEnergy` defines the actual signed row
`L_n = sum_(j<=n) A(n,j)` and `E_n = L_n^2 / sigma_(n+1)`.
It proves the exact capacity telescope, summability of each fixed column,
and the equivalence between summability of E and of the complete Schur
gain series. Deleting or modifying any fixed finite signed combination
of columns preserves this summability question.

**Conditional research reduction:** nonsummability of the actual full
row energy implies RH, with no density or zeta-zero provider.
**Open:** prove that nonsummability. Positive prime diagonal source
divergence does not exclude signed off-diagonal cancellation. The
necessary implication from not RH retains its explicit not-RH premise;
no RH converse is asserted here.

### Exact cross-stage prime cancellation (2026-09-21)

**Established:** `RH/ParetoPrimeCrossStageCancellation` proves that the
Schur innovations and factorial refinements are each pairwise orthogonal.
The cross-Gram entries `A(n,m) = inner(r_(n+1),d_m)` vanish for `n < m`,
and `A(n,n) = delta_n` at prime stages. Exact telescoping gives
`kappa_n = inner(r_(n+1),z_2) + sum_(j<n) A(n,j)` and
`eta_(n+1) = inner(r_(n+1),z_2) + sum_(j<=n) A(n,j)` at every stage.
All signed terms are retained.

**Scope:** these structural equalities are unconditional. A lower bound
excluding cancellation in the finite row sums remains **Open**. Pairwise
orthogonality does not identify the moving certificate errors with one
fixed vector and does not by itself prove RH.

### Normalized prime cancellation and refinement budget (2026-09-21)

**Established:** `RH/ParetoPrimeNormalizedCancellation` defines the positive
fresh-prime source delta and the dimensionless survivor energy
`1/q * (1 + kappa/delta)^2`. It proves the pointwise bound by eight times
the actual Schur gain. Consequently, not RH forces these relative survivors
to be summable with reciprocal-prime weight. Equivalently, failure of this
weighted-L2 cancellation condition implies RH.

**Established:** `RH/ParetoPrimeRefinementCancellation` constructs the actual
factorial refinement vector `d_n = z_((n+3)!) - z_((n+2)!)`. It is invisible
to every old observation, pairs with the new innovation by exactly delta,
and is orthogonal to the old feasible error. The reusable two-direction
Bessel lemma in `LinearAlgebra/OrthogonalFarSupportBound` then proves
`kappa^2*norm(d)^2 + delta^2*norm(w)^2 <=
sigma*norm(w)^2*norm(d)^2`.

**Scope:** these are unconditional necessary constraints and sharpen the
remaining cancellation channel. The normalized nonsummability premise is
**Open**. The two-vector estimate is sharp in abstract Hilbert geometry, so
an arithmetic lower bound for the signed Schur numerator on a prime set of
divergent reciprocal mass is still required. Neither module proves RH.

### Divergent fresh-prime source and necessary cancellation (2026-09-21)

**Established:** `RH/ParetoPrimeSourceDivergence` proves the actual
Pareto bound norm(g_d)^2 <= 2/d, full Schur bound sigma_n <= 2/(n+2),
and exact defect identity delta = (1 + norm(z_P)^2/2)/q^2.
For P=(n+1)! and n>=1, support escape gives delta>=1/(2q) and
delta^2/sigma>=1/(8q). Mathlib's checked prime reciprocal divergence
therefore proves nonsummability and divergence of partial sums of the
explicit positive prime-source energy.

**Established implications:** `RH/ParetoPrimeCancellation` retains
eta=delta+kappa with the actual changing certificate and full innovation.
Under not RH the actual Schur gains are summable, while the signed prime
error energy is nonsummable. For each epsilon>0 the primes where
abs(delta+kappa)>=epsilon*delta have summable reciprocal-prime mass.
This is a weighted exceptional-set condition, not pointwise convergence
at every prime. No RH-to-density or critical-zero provider is used.

**Conditional research reductions:** RH follows from summability of the
signed prime error energy, or from nonsummable reciprocal mass of primes
with fixed-fraction noncancellation. Uniform relative noncancellation is
a sufficient specialization. Each of these arithmetic premises is **Open**;
they are not asserted equivalent to RH. Divergence of the actual signed
gain sum, the unrestricted capacity limit, and RH remain **Open**.
Twenty proved theorems and four definitions are added across both modules.

### Fresh-prime observations and growing-dictionary corrections (2026-09-21)

**Established:** `RH/ParetoCoprimePrimeObservation` evaluates the actual
infinite certificate's prime observation as 1/q minus
(M_P - M_(Pq))/(M_P - 1). For a fresh prime q, the exact Euler-factor
update makes this defect delta = M_P/(q^2*(M_P - 1)) > 0.

**Established:** `RH/ParetoCoprimePrimeUpdates` proves
eta = delta + inner(innovation, z_P - tailMinimum(n)) and the full
signed capacity increment (delta + inner(...))^2/sigma.
The concrete vector y = z_P + (delta/sigma)*innovation satisfies every
next-stage observation. Its energy is E_P + (2*delta*eta - delta^2)/sigma,
and its next-stage squared-distance gap equals the old gap minus
(eta - delta)^2/sigma. Factorial specializations discharge the common
modulus and fresh-prime conditions when n > 0 and n+2 is prime.

**Scope:** nineteen public proved theorems, two definitions, and one
private summation lemma. No RH, zeta-zero, or density premise is used.
This is a one-step correction from z_P, not an iterated certificate
construction. Controlling the signed error pairing sufficiently to
prove divergence of the actual gain sum remains Open.

### Coprime modulus refinement and divergent fixed-dictionary excess (2026-09-21)

**Established:** `RH/ParetoCoprimeModulusRefinement` proves that P dividing Q
gives inner(z_P,z_Q) = norm(z_P)^2 and the exact orthogonal energy increment
norm(z_Q)^2 = norm(z_P)^2 + norm(z_Q-z_P)^2. For a dictionary already
supported by P, the refinement increment has zero observations and its
whole energy is added to the gap from the unrestricted minimum.

The same module proves exact energy completion and the unique equality
case for every Hilbert-convergent signed mixture of certificates from
nonzero multiples of P, with scalar coefficient HasSum one. The refined
moduli need not form a chain. Such mixtures cannot lower the base energy.

**Established:** `RH/ParetoCoprimeCertificateEscape` instantiates support
escape for the actual infinite averages at (m+2)!. The physical head
through m+1 vanishes and the exact g2 pairing is 1/2, giving squared norm
at least m+2 and divergence. For fixed dictionary size n and modulus
(m+n+2)!, it proves the exact gap G = E - tailCapacity(n), G tending to
infinity, and G/E tending to one.

**Scope:** these new statements require no RH, zeta-zero, or density
provider. The factorial limits hold with the dictionary fixed. They do
not decide the growing-dictionary capacity limit, which remains Open.

### Infinite coprime tail certificate and exact capacity gap (2026-09-21)

**Established:** `Analysis/OrthogonalAffineSeries` constructs the actual
reciprocal-energy Hilbert sum for a nonzero orthogonal family with summable
reciprocal squared norms. It proves its unit pairings, exact norm,
normalization and attainment, scalar coefficient summability for every
convergent signed vector series, and the exact affine energy completion
with unique equality case.

**Established arithmetic specialization:**
`RH/ParetoInfiniteRoughTailCertificates` constructs the whole infinite
odd-coprime two-point average in the original Pareto Hilbert space.
For a nonzero even common multiple P of the stage-n dictionary, it proves
the actual finite observations, zero first-coordinate component,
and exact energy 2/S_P, where S_P is the full coprime reciprocal-square
sum. Every convergent signed affine combination in this family has
energy 2/S_P plus its squared distance from the constructed average.

`infiniteCoprimeCertificate_capacity_gap` and
`infiniteCoprimeCertificate_eulerProduct_capacity_gap` identify the
complete excess over the unrestricted capacity:
2/S_P = tailCapacity(n) + norm(z_P - tailMinimum(n))^2.
All Euler factors are retained. No RH, not-RH, zero-existence, or
RH-to-density hypothesis is used by these additions.

**Open:** boundedness/divergence of the unrestricted stage capacities.
Optimality within the infinite coprime family does not discharge this
limit, because the exact squared-distance excess can vary with the stage.
The separate critical-line-zero and Bagchi-density providers remain open.

### Stringent conditions under failure of RH: exact additions and open coverage (2026-09-21)

Full ledger: [all 35 groups](RH/NOT_RH_STRINGENT_CONDITIONS.md).
The historical source is preserved alongside it; its earlier claims do not
override the exact Lean status recorded here. This update adds 17 modules
and 49 public proved declarations, and strengthens the existing joint theorem.
It does **not** complete the proofs of all 35 groups.

**Established consequences on the actual common arithmetic projection:**

- `RH/ResidualGainObstruction`: actual relative-gain summability, exact
  logarithmic `HasSum` budget, comparison for its total sum, finite harmonic
  mass of large-gain scales, and exact capacity-increment `HasSum`.
- `RH/MeanOneResidualFloor`: the sharp lower bound `E/(1-E)` for every
  exactly mean-one vector in the actual closed legal space, with `E<1`;
  cofinally large repairs at every strict threshold below
  `(1-q)*sqrt(E/(1-E))`, and positivity under not RH.
  `Analysis/ContractiveRepairFloor` supplies the general finite-descent
  proof without assuming bounded repairs. Finite-legal infimum attainment
  and approximation remain separate.
- `RH/IntegerDPPPowerWeightedHoles`: the physical weight `(n+1)^alpha`
  times limiting site vacancy is nonsummable for every
  `alpha >= 2*Re(rho)-1`, including equality, for each applicable actual
  zero. One common zero gives all these exponents under not RH.
  This is not an almost-sure infinitely-many-holes assertion.
- `RH/IntegerDPPDampedConvergence`: unconditional convergence of actual
  finite occupied determinants; `B >= p0*(1+limitingVacancy)`; and
  `p0 < B` under not RH. The stronger logarithmic comparison remains Open.
- `RH/ResidualMellinZeroConditions`: the same limiting residual has Mellin
  value `1/rho` at every applicable actual zero, while its projection
  has value zero.
- `RH/ChebyshevZeroObstruction`: actual simple-pole and Hardy-half-plane
  obstructions. This does not discharge the weighted-energy endpoint.
- `RH/ReflectionFailureConditions`: the exact disjunction that signed
  calibration or normalized reflection variance fails to tend to zero,
  retaining all legal-packet, mean, periodicity, and reflection hypotheses.
- `RH/RHFalseJointObstruction`: strengthened `not_RH_joint_arithmetic_obstruction`
  assembles the common zero, sharp weighted exponents, positive limiting
  energy, exact-head residual-tail product, wrong coefficients, reconstruction
  divergence, canonical excursions, exact logarithmic gain budget, and
  strict occupied-determinant separation under sole `not RH`.

**Established supporting geometry and analysis:**
`LinearAlgebra/SourceSpectralObstruction` proves persistent omitted mass and
divergent inverse first moment from positive limiting defect and vanishing
polarization. Its arithmetic compression/spectral-measure assembly remains
Open. `RH/ClassicalArithmeticObstructions` proves Chebyshev damping monotonicity.
`RH/LiCoefficientObstructions` proves the actual transformed-zero radius
identity `R(rho)^2*norm(rho)^2 = norm(rho)^2-(2*Re(rho)-1)` and `0<R(rho)<1`
at an applicable actual zero, using correctly regularized xi.

**Conditional research reductions:**
`RH/WeilFailureConditions` derives late polynomial and reference-energy
lower-bound failures from `TwoHatWeilIdentity h` and
`FixedWidthLandauDetection h`. Both providers remain **Open**.
The provider-alternative theorem asserts a disjunction, not the failure of
each provider. Nested support/moment-constrained window test sets are proved.

**Open, concrete proposition definitions (not axioms or theorem providers):**
`RH/CanonicalTailHistoricalTargets`, `RH/CanonicalSieveAbelTargets`,
`RH/ResidualEnergyHistoricalTargets`, `RH/IntegerDPPHistoricalTargets`,
`RH/DeBruijnNewmanObstructions`, and target sections in the Mellin, Chebyshev,
Weil, classical, and Li modules record the unresolved numerical, tail,
multiplicity, normalized escape, Abel/sieve, DPP pair-hole, Fredholm,
profinite, endpoint energy, Weil spectral/Sobolev, prime/Mertens, Li-sign,
Robin/Lagarias, and Newman claims. Series convergence and bounded-extremum
conditions are kept explicit where totalized values would be misleading.
The sieve statement retains the order of both limits; it does not assert
that every fixed-sieve Abel limit is zero.

**Further specification gaps:** the ledger explicitly retains family-specific
Schur-minimizer covariance growth, some simultaneous higher-jet Gram
constructions, and several historical analytic proof packages whose actual
objects and providers are not supplied by this update. There is no opaque
assumed proposition standing in for these proofs.

### Pareto shape threshold and concrete full-tail capacity certificates (2026-09-21)

Modules: `RH/ParetoRoughTailCertificates`, `RH/ParetoShapeMellinEnergy`,
`RH/ParetoShapeCapacity`, `RH/ParetoTailCertificateEscape`; extensions to `RH/ParetoTailCapacityDuality`
and `RH/FirstCoordinateTailGap`.
Source and coverage: `RH/ParetoCapacityFormalization20260921.md`.

**Established:** actual two-point Hilbert certificates have exact squared
norm 2p^2 and residue pairing 1/d minus the divisibility indicator.
Finite orthogonal averaging, passage to the complete coprime
reciprocal-square sum, and the existing proved Euler product give
`tailCapacity_le_factorial_eulerProduct`. This is a finite-stage upper
bound for the actual full-tail Gram capacity, not a uniform bound as the
dictionary grows. `finiteTailCertificate_energy_completion` retains
the exact nonnegative distance from the finite minimum.
`roughCertificate_affine_energy_completion` proves optimality of the
inverse-square average within each finite separated family, including
signed reweightings. Independently, actual certificates supported on
physical sites j>=M with g_2 pairing 1/2 have squared norm at least M;
escaping support therefore forces their energy to tend to infinity.

**Established:** actual Pareto shape-cell Mellin energy is summable for
0<alpha<2 Re(s), with the explicit complete-tail constant.
`criticalNormalizedTailEnergy_not_summable` proves genuine divergence of
the literal normalized critical-line certificate at alpha=1, using a
harmonic lower bound. These analytic statements require no zeta-zero input.

**Established theorem with an explicit zero hypothesis:**
`critical_shapeFiniteCapacities_bddAbove` bounds all actual finite
coefficient-supremum capacities for 0<alpha<1, given
`riemannZeta (criticalPoint t)=0`. All legal-combination summability and
arithmetic pairing steps are proved. **Not supplied here:** a formal
critical-line-zero existence provider. This classical existence input
is not an RH assumption, but it remains visible in the theorem type.

**Conditional research reduction:**
`tailCapacity_bounded_iff_not_RH` directly states the original Pareto(1)
criterion with the explicit classical Bagchi argument
`hDensity : RiemannHypothesis → closedSpace = ⊤`.
**Open:** formal provider for that density direction; independently,
whether the original capacities are uniformly bounded or diverge.
No new axiom or conclusion proving or disproving RH is introduced.

### Exact Cauchy-annihilator criterion and signed capacity barriers (2026-09-21)

Modules: `RH/CauchyAnnihilatorRH`, `RH/MellinCapacityBarrier`.

**Established equivalence:** `not_RH_iff_exists_finite_energy_cauchy_annihilator`
identifies failure of actual Mathlib RH with existence of one positive-scale
Cauchy mixture, with scale less than one half, that is nonzero, has genuinely
summable positive Pareto energy, and annihilates every normalized residue.
`riemannHypothesis_iff_cauchy_generator_detected` identifies RH with
nonvanishing of the single modulus-two pairing throughout this two-parameter
Cauchy family. Neither theorem assumes RH, Bagchi's theorem, a density
provider, or a new analytic provider. These are reformulations, not a proof
of either side.

**Established conditional obstruction:** write `v(s)=mellinVacancyFloor s`
and `B(s)=2/v(s)-2`. A right-half-plane zeta zero away from the pole forces
`B(s)>0`, `tailCapacity n <= B(s)` at every stage, and
`1/B(s) <= firstCoordinateTailGap`. The same bound controls every finite
signed coefficient family, with all mixed terms retained.
`not_RH_common_signed_tail_barrier` selects one zero for all these bounds.
`zeta_ne_zero_of_capacity_exceeds_mellin_bound` turns a finite capacity
exceeding the explicit threshold into a zero exclusion. The previously
proved cell-integral bound in `MellinZeroQuantitativeGap` remains available;
no optimality claim is made for either estimate.

**Conditional research reduction:**
`riemannHypothesis_of_arbitrarily_small_signed_tails` requires, for every
positive epsilon, a finite real coefficient family with reciprocal source
one and full tail norm squared below epsilon.
**Open:** construction or an arithmetic estimate providing those trials.
The Cauchy equivalence does not discharge that input, and the existing
compact-frequency/first-moment exclusions do not cover its Cauchy witnesses.

### Cauchy frequency mixtures and explicit zero-to-gap bounds (2026-09-21)

Modules: `RH/CauchyFourierTransform`, `RH/CauchyFrequencyMoments`,
`RH/CauchyMellinMixture`, `RH/CauchyMixtureEscape`,
`RH/PowerCellMassSummation`, `RH/MellinModeEnergyBounds`,
`RH/MellinModeTailCauchy`, and `RH/MellinZeroQuantitativeGap`.

**Established:** `cauchyMellinMixture_eq_mellinMode` identifies the actual
coordinate mixture against `cauchyMeasure gamma delta` with the Mellin mode
at `verticalPoint (1/2 + delta) gamma`, for positive scale. The more general
identity `cauchyMeasure_integral_mellinMode` shifts any real part `sigma`
to `sigma + delta`. Every displayed coordinate integral is absolutely
integrable; the corresponding ordinary Cauchy-density/Lebesgue identity is
also proved. No Hilbert-valued integral of the individual critical modes is
asserted.

**Established:** `cauchyMeasure_noAtoms` and `cauchyMeasure_countable_null`
show that positive-scale Cauchy measures are atomless and give every countable
frequency set measure zero. Their support is the entire real line and no
bounded frequency band has full measure.
`cauchyMeasure_integrable_abs_rpow` proves finiteness of every absolute
moment of order `0 <= alpha < 1`, for arbitrary location and positive scale.
The first absolute moment and the critical-amplitude first moment are
infinite. This identifies precisely why this continuous construction lies
outside both the compact-frequency and countable pure-point hypotheses.
`cauchyMellinMixture_frequency_obstructions` packages failure of the actual
compact-data predicate, countable almost-everywhere support, and the critical
first-moment condition for this same Cauchy mixture.

**Established:** for `beta > 1/2` and `a > 0`,
`powerCellMass_hasSum` proves genuine summability of the actual integrals
over `[n+a,n+a+1]`, with exact sum
`a^(1-2*beta)/(2*beta-1)`. Weighted cell Cauchy--Schwarz then proves
absolute Pareto square summability of each Mellin mode with
`Re(s)>1/2` and the bounds

```text
sum_n paretoWeight n * norm(mellinMode s n)^2
  <= norm(s)^2 / (2*Re(s)-1),
sum_k paretoWeight (k+1) * norm(mellinMode s (k+1))^2
  <= norm(s)^2 * 2^(1-2*Re(s)) / (2*Re(s)-1).
```

The sums include the complete sequence and complete first-coordinate tail,
respectively. `cauchyMellinMixture_energy_summable`,
`cauchyMellinMixture_energy_le`, and `cauchyMellinMixture_energy_pos` give
positive finite energy with upper bound `norm(s)^2/(2*delta)` for every
positive-scale Cauchy mixture. `cauchyMellinMixture_energy_contrast` proves
this simultaneously with infinite energy for every constituent critical
mode. These are coordinate integrals, so no Hilbert-valued integrability
of the constituent modes is used.

**Established:** `cauchyMellinMixture_residuePairing` computes each actual
pairing as `(1/d - d^(-s))*zeta(s)`. For `0 < delta < 1/2`,
`cauchyMellinMixture_annihilates_iff` proves simultaneous vanishing of every
normalized residue pairing if and only if `zeta(s)=0`, where
`s=1/2+delta+i*gamma`.

**Established conditional implication:**
`TailCapacity.firstCoordinateTailGap_lower_bound_of_zeta_zero` assumes
only an actual zero `riemannZeta s = 0` and `1/2 < Re(s) < 1`. It proves

```text
(2*Re(s)-1) * 2^(2*Re(s)-1) * norm(1 - (2:Complex)^(-s))^2 / norm(s)^2
  <= firstCoordinateTailGap.
```

`firstCoordinateTailGap_pos_of_zeta_zero` proves strict positivity under
the same hypotheses. The argument uses the actual complex tail pairing,
retains every signed coefficient direction, and supplies all norm and
convergence estimates; it assumes no separate analytic provider or
hypothetical certificate. This is a quantitative bound obtained from exact
cell integrals, not a claim that the displayed bound is optimal.

**Open formalization:** `RiemannHypothesis -> closedSpace = top` remains
explicit in the converse gap/RH equivalences. The present zero-to-gap
theorems neither assume nor discharge that provider. Its classical analytic
dependencies are recorded in `RH/RHToDensityDependencyAudit20260921.md`.

**Open mathematical endpoint:** no off-line zeta zero is constructed, and
the unrestricted gap is not shown positive or zero. No RH proof or disproof
is claimed. The Cauchy coordinate identity alone does not supply the
arithmetic annihilation equations.

### Sharp tail gap and Mellin mixture obstructions (2026-09-21)

Core modules: `RH/FirstCoordinateTailGap`, `RH/TailMinimumConvergence`,
`RH/ComplexTailCoercivity`, `RH/CompactFrequencyRigidity`,
`RH/CriticalMellinCountableEnergy`, `RH/FiniteCriticalMellinMixtureEnergy`,
and `RH/CompactCriticalMixtureTriviality`. The supporting Mellin summation,
Fourier, sampling, cell asymptotic, harmonic mean, Gram, and atomic modules
are listed in `RH/RHDisproofObstructionFormalization20260921.md`.
Ordinary argument: `RH/RHDisproofObstructionDraft20260921.md`.

**Established:** the actual first-coordinate tail gap is the sharp constant
for all real and complex signed finite tail combinations, with the complex
space realized in genuine complex `lp` at exponent two. Positivity is
equivalent to bounded capacity and existence of a residue tail certificate.
Not RH forces a positive gap; a zero gap implies actual Mathlib RH.
Finite minimum vectors converge iff capacities are bounded, with the
canonical limit and exact squared-error bound.

**Established:** `SpectralObstruction.compactFrequencyRigidity_proved`
assumes only `CompactFrequencyData`. It proves the equivalence between
annihilation of all normalized residues and almost-everywhere vanishing
of the actual zeta-weighted density. The Mellin/Fubini identity, absolute
summability, entire exponential-type bound, Jensen logarithmic sampling,
and weighted Fourier injectivity all have checked proofs.

**Established:** `criticalPurePointEnergyProvider_proved` supplies the actual
countable logarithmic-energy law under injective ordinates and absolute
coefficient first-moment control. `nonzero_criticalMixture_not_summable`
excludes every such nonzero critical mixture from finite Pareto energy.
The finite-family law is proved separately. Actual Gram limits and a
uniform bound of `4 * norm(s_t) * norm(s_u)` justify every mixed-series
interchange, without frequency separation or bounded ordinates.

**Established:** `compactCriticalMixtureTriviality_proved` shows that a
compact critical-line mixture with finite Pareto energy and every residue
pairing zero has zero density almost everywhere and is the zero mixture.
The reduction uses the actual finite set of critical-line zeta zeros and
the measure's actual atom coefficients. No analytic provider is assumed.

**Conditional research reductions:** the full gap/RH equivalences still
expose `hDensity : RiemannHypothesis → closedSpace = ⊤`.
**Open formalization:** this classical RH-to-density implication; its exact
missing analytic inputs are documented in
`RH/RHToDensityDependencyAudit20260921.md`. The completed mixture theorems
do not discharge it. This is a missing formalization of known ordinary
mathematics, not a new mathematical conjecture.

**Open mathematical endpoint:** neither positivity nor vanishing of the
unrestricted gap is proved. No disproof or proof of RH is claimed.
The audited completed declarations use only `propext`, `Classical.choice`,
and `Quot.sound`; explicit local hypotheses are tracked separately.

### Joint arithmetic obstruction under failure of RH (2026-09-21)

Module: `RH/RHFalseJointObstruction.lean`.

**Established:** `Pareto.not_RH_joint_arithmetic_obstruction` assumes only
`¬ RiemannHypothesis`. One actual right-half-strip zeta zero simultaneously
forces a Chebyshev-Mellin pole, strictly positive vacancy floors at every
integer site and every finite projection stage, an exact oscillatory
exact-head energy lower bound, and the canonical certificate's Mellin identity.
The same canonical certificate satisfies every residue observation, is the
unique minimum-energy certificate, is the finite tail-capacity limit in energy,
has square-summable but nonsummable signed tails, lacks the stated additive
partial-sum summability, and has both signs arbitrarily far out.
Weighted limiting holes are nonsummable, exact-head energy eventually exceeds
every constant multiple of one positive power, and the full uniform signed
Schur target fails.

The isolated combined theorem passed Lean with only `propext`,
`Classical.choice`, and `Quot.sound`. No RH-to-density provider is assumed.
**Open:** excluding this simultaneous obstruction; the constraints have not
been shown contradictory. This synthesis does not claim a maximal theorem
inventory or an RH proof.

### Coordinate Mellin defects and the unscaled RH test (2026-09-21)

Modules: `Analysis/NonnegativeDeficit`, `RH/MellinCoordinateDefect`,
`RH/MellinZeroProfile`, `RH/MellinDeficitRHTest`, and
`RH/MellinCoordinateScaling`. Detailed coverage and remaining obligations:
`RH/ArithmeticProjectionDPPFormalization20260921.md`. The complete ordinary
mathematics draft is archived as `RH/ArithmeticProjectionDPPDraft20260921.md`.

**Established:** explicit coordinate features equal the actual Mellin
integrals on the critical line; exact intensity/defect decomposition;
nonnegative extended window integrals; the first-cutoff factorization
`d_1(I) = ofReal(limitingVacancy) * firstModeMass(I)`; and
`first_window_zero_iff_density` on any positive-measure window.
`riemannHypothesis_of_first_window_zero` proves actual Mathlib RH from
that zero-deficit premise without an additional analytic provider.
It does not prove the premise.

The exact finite zero profile equals a combination of the actual Mellin
functionals of the cutoff heads. `zeroProfilePartial_cauchy_bound` proves
`((2 Re(rho)-1)/2) * norm(F_rho,M(t))^2 <= E_M(t,t)` from an actual
off-critical zeta zero. This weaker-than-sharp bound is fully supplied.
Fatou then proves `zeroWindowMass_le_liminf` from explicit profile
convergence. The general ENNReal criterion is exactly equivalent to
cofinally arbitrarily small deficits, including the potentially unbounded
case.

**Established scaling distinction:** the omitted-first-coordinate
correction tends to zero after logarithmic normalization; compensating
by that logarithm recovers a nonzero limit. The filled comparison and its
proper subprojection share any existing leading kernel limit.

**Conditional research reduction:** `riemannHypothesis_iff_windowTest`
exposes the classical RH-to-density converse and `ZeroModeWindowProvider`
as explicit hypotheses. **Open formalization:** profile convergence,
positive limiting profile mass on a bounded positive-measure window, and
the classical RH-to-density converse. The two profile fields concern
all points in the right half-plane, not only zeta zeros; domination is
proved separately. Absence of nonstandard axioms does not discharge
these local hypotheses.

**Open formalization:** `CoordinateSineLimitTarget`,
`CoordinateSecondOrderTarget`, the full process/Fredholm convergence,
the meromorphic profile and higher-order refinements, and the infinite
local trace-class obstruction. They remain ordinary proofs in the draft,
not fully formalized theorems.

**Open mathematical estimate:** unconditional zero unscaled deficit (or
signed-capacity divergence). No RH proof, Montgomery matching, or
Hilbert--Polya spectrum is claimed.

### Decisive vacancy endpoint: exact finite and dual certificates (2026-09-20)

Modules: `RH/IntegerDPPVacancyCertificates` and
`RH/IntegerDPPVacancyDuality`.

**Established:** for a finite conductor trial `c`, define its reciprocal
source `A = finiteTrialSource n c` and full Hilbert-tail energy
`E = finiteTrialEnergy n c`. The energy's Gram expansion retains every
signed mixed term. For `E > 0`, the actual finite vacancy satisfies
`vacancy n <= 2 E / (A^2 + 2 E)`. Moreover,
`limitingVacancy = 0` is equivalent to
`forall B : Real, exists n c, 0 < E and B * E < A^2`.
The forward direction uses actual finite inverse-Gram optimizers; the
reverse direction uses the source-energy inequality and monotone capacity.

Every genuine tail certificate `z` forces
`2 / (norm(z)^2 + 2) <= limitingVacancy`. Positive limiting vacancy is
equivalent to the existence of such a certificate, and zero limiting
vacancy is equivalent to their exclusion. In the positive-vacancy case,
the canonical certificate has energy `2 / limitingVacancy - 2), attains
the sharp vacancy bound, and is its unique equality case.

**Conditional research reduction:**
`riemannHypothesis_of_finiteTrial_certificates` consumes the explicitly
quantified finite-witness family. It proves Mathlib's RH only under that
hypothesis.

**Open:** produce trials with arbitrarily large source-squared-to-energy
ratio, or equivalently exclude every genuine Hilbert tail certificate.
Zero limiting vacancy, closure saturation, tail-capacity divergence,
full-capacity saturation at 2, and the damped benchmark endpoint remain
unproved. Finite inverse-Gram existence and the finite-rank Mellin DPP
construction do not discharge this arithmetic obligation. No RH-to-density
converse is asserted.

### Trigamma mean points and midpoint inverse comparisons (2026-09-24)

**Established:** `RH/CRTTrigammaMeanValue` defines the unique mean point
for the actual digamma derivative and proves strict increase in the residue,
strict decrease in the conductor, geometric/arithmetic bounds, and the
fixed-residue limit `L * alpha(r,L) -> sqrt(r*(r+1))` along every positive
conductor sequence that tends to infinity.

The interval-width cancellation estimate
`trigammaMean_sq_sub_mul_le_width` sharpens the scaled squared error:
`progressionAlpha_scaled_sq_error_cubic` bounds it by
`trigamma(1) * r * (r+1)^3 / L^3`.
`progressionAlpha_scaled_error_cubic` also gives the nonnegative absolute
difference from `sqrt(r*(r+1))`, bounded by that quantity divided by
`2*sqrt(r*(r+1))`. Both hold for every real `r > 0` and `L > 0`, with no
new analytic hypothesis. The previous squared-error bound with `L^2`
also remains available; the cubic bound is stronger for `L > 1`.

`LinearAlgebra/FiniteMatrixInverseComparison` proves antitonicity and
relative comparison for actual positive finite Gram inverses, reusing
`FiniteConstrainedMatrixInverse` for literal inverse identification.
`RH/ProgressionMidpointInverse` proves midpoint Gram positivity and
`progressionMidpoint_occupation_error`: the exact and midpoint occupations
differ by at most `1/(2*L+3)^2`, independently of the dimension.
`progressionMidpoint_occupation_tendsto_iff` transfers convergence to every
real limit for arbitrary growing finite dictionaries. Limit one gives the
saturation equivalence. Positive definiteness of the exact finite Gram is
explicit; no condition-number or saturation hypothesis is hidden.

`RH/NonnegativeResidueObstruction` proves the two-site tail lower bound
`2/27` and occupation cap `27/31` for normalized nonnegative-coefficient
trials. It does not bound unrestricted signed optimizers.

**Verification:** commit `090bf0ca128df7ca1c9e892577f50cf93ad1cdd2`
published all four recovered modules after affected-module builds on both
the recovery base and the newer main. The cubic extension is validated by
its publication checkpoint. These results use the existing
`CRTPolygammaSigns` and `ParetoProgressionMidpoint` ingredients. Verification
of these modules is not a claim of whole-repository or unconditional RH
verification. A subsequent 16-theorem axiom audit, including both cubic
bounds, reported only `propext`, `Classical.choice`, and `Quot.sound`;
explicit theorem hypotheses remain as stated.

**Open:** exact/midpoint saturation, physical-tail capacity divergence,
strict decrease of the scaled mean point `L*alpha` in `L`, and the signed
Mobius candidate's weighted infinite-tail estimate. The comparison theorems
do not discharge these arithmetic obligations. See
`RH/TrigammaMidpointSaturationResearch20260921.md` and
`RH/RHContinuation20260924.md` for normalization and continuation.

### Finite-rank Mellin DPP construction (2026-09-20)

Main module: `RH/MellinProjectionDPP`.

**Established for every rank n, without an RH hypothesis:** an actual
probability measure `mellinLaw n` on n labeled real frequencies, invariant
under relabeling and almost surely consisting of n distinct points. Its
joint density relative to the product of `frequencyMeasure = dt/(2*pi)`
is `det (kernel n (x i) (x j)) / n!`, where `kernel` is the existing
arithmetic inverse-Gram Mellin kernel. The kernel reproducing integral
and trace n are also proved.

The analytic input is proved for the actual Pareto realization:
`RH/ParetoMellinIsometry` constructs the logarithmic real-linear isometry
and proves complex cross-Plancherel;
`RH/MellinModeOrthonormality` identifies the actual Mellin integrals with
the Fourier transform and proves orthonormality;
`RH/MellinFrequencyMeasure` gives the exact angular measure and L2 bounds.
`RH/ParetoBoundedMellinLinearity`, `RH/ResidueModeGramInverse`, and
`RH/MellinProjectionKernel` identify the actual finite mode sum with the
arithmetic inverse-Gram kernel.

Reusable probability modules: `Probability/ContinuousProjectionLaw`,
`Probability/ContinuousProjectionDensity`,
`Probability/ContinuousProjectionSymmetry`, and
`Probability/ContinuousProjectionKernel`. Normalization follows by
integrating the squared determinant using the proved cross-Gram identities;
neither a probability-law provider nor a Mellin isometry is assumed.

**Scope:** this constructs the finite-rank family by its full n-point
joint density. Separate formulas for every lower-order factorial marginal
and an infinite-rank locally finite continuum process are not asserted.
The infinite local-trace obstruction and scaling limits remain separate
formalization/research obligations.


### Route 4 Möbius coefficient defect (2026-09-20)

Module: `RH/MobiusCoefficientDefect`.
Detailed status and exact notation: `RH/RH_Mobius_Coefficient_Option4_2026-09-20.md`.

**Established:** totality of the Möbius Riesz tests; coefficient uniqueness and
reconstruction under summability; weak convergence from bounded coefficient
tests; and divergence of residue-coordinate truncations of every nonzero
orthogonal vector. In particular, not RH forces coefficient defects beyond
every conductor bound and full-sequence divergence of the norms of
`defectPartialSum`. The exact Gram identity retains all signed mixed terms.
The complete atom norm satisfies `norm(g_d)^2 <= log(d)/d`.

**Conditional research reductions:** `riemannHypothesis_of_eventual_mobius`
(and its mode-series version) tolerates finitely many exceptional conductors.
`riemannHypothesis_of_cofinal_defect_gram_bound` requires only a cofinal
bound on the actual signed defect Gram energy.
`riemannHypothesis_of_summable_weighted_defect` consumes the scalar condition
`sum |c_infinity,d + mu(d)| * sqrt(log(d)/d) < infinity`.

**Open:** arithmetic providers for eventual identification, the cofinal Gram
bound, or weighted defect summability. Fixed-conductor absolute convergence
of the mode series supplies none of these uniform conditions. RH remains
unproved; no RH-to-density converse is used.

### Route 6 covariance absorption (2026-09-20)

Module: `Analysis/CovarianceAbsorption`.

**Established abstract inequalities:** `finite_absorption_bound` telescopes
the exact square balance while retaining the endpoint term;
`partial_energy_bound` bounds partial energy given a positive margin and
bounded diagonal/error sums; `cofinal_nonpositive_covariance_bound` bounds
monotone energy from a cofinal covariance-sign hypothesis.

**Conditional research reduction:** the Chebyshev application requires its
actual integral/jump square identity and matching sequence definitions.
**Open:** the strict arithmetic covariance bound with summable errors, or
cofinal nonpositive covariance for exponents approaching one. Neither these
inputs nor RH is proved here. The exact-divisor and operator-obstruction
arguments in the companion continuation remain outside Lean.

### Orthonormal/DPP/Mellin chat additions and remaining obligations (2026-09-20)

See `RH/OrthonormalDPPMellinChatCoverage20260920.md` for the complete itemized
comparison against the supplied conversation and exact indexing conventions.

**Established additions:** normalized Gram cofactor formulas and positive
leading coefficients; exact finite digamma Gram evaluation and the first
binary/ternary constants; finite inverse-Gram/mode identities; actual
finite-window independent-Bernoulli count-law representation; weighted
multiplicative Gram determinants; the maximum-point distribution on an
infinite-tail event; symmetric finite damping; the positive scalar benchmark
`sin (pi * (sqrt 5 - 1)/2) / pi`; finite minimum rigidity and an infinite-prefix
damped determinant criterion equivalent to zero limiting vacancy; a nested
rank-growth DPP counterexample with a permanent hole; actual Mellin
inverse-Gram kernel factorization, Hermitian symmetry and normalized pair
cancellation; convergent Hermitian cutoff matrices with real spectrum;
finite and infinite nonnegative spectral products with real zeros; and the
logarithmic step-space frequency-multiplication domain obstruction.

**Conditional research reductions:** the damped benchmark must actually be
attained to invoke its RH implication. The new sine-kernel and upper-edge
scaling properties are precise targets, not supplied limits. The positive
spectral representation of the completed zeta function on the strip has no
provider; the theorem deriving Mathlib RH from that identity is conditional.
None of these hypotheses is hidden in a project axiom.

**Open formalization obligations for known mathematics:** the Bagchi
RH-to-density converse; full DPP negative association and the finite spatial
transport provider; separate lower-order continuum correlation marginals;
the infinite continuum local-trace obstruction; the operator trace-class
Fredholm identification; and the cutoff eigenvalue interval bound.

**Open arithmetic/research obligations:** zero vacancy/weighted vacancy
estimates, capacity divergence, the arithmetic spectral determinant identity,
sine/Airy scaling existence and its connection to zero ordinates, and KPZ
joint dynamics. No unconditional RH theorem has been added.


### Spatial arithmetic DPP coupling: finite-window reduction (2026-09-20)

Modules: `Probability/CompactProbabilityConstraints`,
`Probability/DeterminantalLimit`, `RH/IntegerDPPSpatialCoupling`,
and `RH/IntegerDPPSpatialVacancy`.

**Established:** `exists_probabilityMeasure_clopen_constraints` assembles
finitely satisfiable clopen probability constraints by compactness, with no
compatibility assumption on finite witnesses. `isDPP_pastUnion` converts
almost-sure nested paths to pointwise nested paths without changing any DPP
marginal. `spatialWindowFeasible_iff_exists_spatialCoupling` proves the exact
equivalence between finite rectangular transport feasibility and a canonical
countable spatial coupling. `exists_spatialCoupling_of_windows` is its
noncomputable forward implication.

**Conditional research reduction:** `SpatialWindowFeasible` has no checked
provider. The full spatial coupling is still an open formalization obligation;
ordered kernels alone are not treated as a coupling. The remaining finite
domination/supported-transport proof follows the route of Lyons,
https://arxiv.org/abs/math/0204325, Theorems 6.2 and 7.1, and Strassen.
See `RH/SpatialCouplingStatus.md` for the concrete signed-minor/Hall route.

**Established identification for every supplied coupling:**
`never_enter_site_probability` gives P(k never enters) = 1 - K_infinity(k,k).
`weighted_never_entry_summable_iff` identifies the weighted sum exactly with
`Summable weightedLimitingHole`; `limitingLaw_weighted_hole_summable_iff`
gives the same identification for the already constructed limiting law.
`riemannHypothesis_of_weighted_never_entry_summable` retains this explicit
arithmetic hypothesis. `weighted_never_entry_harmonic_lower` and
`weighted_never_entry_not_summable_of_not_RH` transfer the existing obstruction.

**Open arithmetic provider:** weighted summability, and in particular
zero vacancy, is not proved. No RH-to-residue-density converse is assumed.

### Orthonormal coordinates, arithmetic DPP structure, and RH reductions (2026-09-20)

Modules: `Analysis/FiniteHilbertGramProjection`, `Analysis/FiniteHilbertGramMatrix`,
`Probability/FiniteDeterminantalGenerating`, `Probability/DeterminantalWindow`,
`Probability/DeterminantalMoments`, `Probability/DeterminantalCardinality`,
`RH/ResidueOrthonormalCoordinates`, `RH/IntegerDPPTrace`,
`RH/IntegerDPPCardinality`, `RH/IntegerDPPArithmeticExclusion`,
`RH/IntegerDPPWindow`, `RH/IntegerDPPGramDeterminant`,
`RH/RiemannHypothesisRightHalfStrip`, `RH/IntegerDPPAllSiteObstruction`,
`RH/IntegerDPPWeightedHoles`, `RH/IntegerDPPWeightedWindow`,
`Probability/DeterminantalWindowGenerating`, `RH/IntegerDPPWindowGenerating`,
`Probability/DeterminantalConfiguration`, `RH/IntegerDPPLiftFactorization`,
`Probability/CountableProductConditioning`, and `RH/IntegerDPPConditionalLifts`.

Source: the user-provided orthonormal/DPP/Fredholm argument; finite DPP
generating and cardinality statements also follow the terminology of
Hough--Krishnapur--Peres--Virag, https://arxiv.org/abs/math/0503110.
The formal proofs use actual Hilbert projections and constructed probability
laws. No RH, density, coupling, or pointwise saturation assumption is used
for the structural results below.

**Established orthonormal structure:** `residueMode_orthonormal` and the
finite/full span identities identify Gram--Schmidt modes with the residue
dictionary. `projection_eq_mode_sum`, `modeAlpha_sq_tsum`,
`mode_coefficient_series_norm_summable`, and
`mode_coefficient_series_hasSum` prove actual vector and coefficient
expansions, including unconditional absolute convergence.
`modeCoefficient_eq_zero_of_lt` gives triangularity;
`residueAtom_inner_one` and `modeAlpha_eq_log_sum` give the logarithmic means.
The Parseval equality is equivalent to constant membership, completeness,
vanishing vacancy, and all limiting coefficients being negative Moebius
values. The limiting residual belongs to the mode closure if and only if
it is zero; merely choosing Gram--Schmidt modes does not supply that membership.

**Established matrix identities:** actual Gram matrices are positive definite
and invertible. `gramMatrix_inverseSource` identifies the matrix inverse with
the already defined source. `projection_kernel_matrix` proves the
observation-matrix inverse-Gram formula. `gram_det_ratio_eq_vacancy` proves
det(tailGram)/det(fullGram) = vacancy, and the latter equals 2/(tailCapacity+2)
by the existing capacity theorem. `headDeterminant_eq` gives the full
real-parameter first-site determinant polynomial.
`window_determinant_eq_gram_ratio` and
`integerLaw_window_gram_determinant` prove finite-window determinant and
actual gap-probability ratios, with every tail/mixed Gram contribution retained.

**Established probability structure:** finite PMF generating polynomials,
the actual finite restriction law, and finite-window gap determinants.
`IsDPP.expected_windowCount` and `IsDPP.variance_windowCount` prove
expectation = trace and variance = trace minus the sum of Q(i,j)Q(j,i).
`integerKernel_diagonal_tsum` proves trace N, and the order N+1 minors vanish.
Tonelli plus the rank bound proves `integerLaw_cardinality`: exactly N
points almost surely under the constructed stage-N law.
Common conductor residue classes contain at most one occupied site almost
surely, multiples are absent, and occupation probability divided by Pareto
weight is constant on each residue class.

**Established actual generating functions and joint lift weights:**
`IsDPP.window_generating` and `IsDPP.window_count_generating` are Bochner
expectations under the DPP measure, with determinant formulas. The finite and
limiting arithmetic specializations discharge all matrix-positivity inputs.
`IsDPP.full_configuration_of_setCount` identifies a full N-point inclusion
minor with the exact configuration probability.
`integerKernel_principal_det_weight_factorization` and
`integerLaw_full_configuration_weight_factorization` factor probabilities
into the product of Pareto weights times a determinant depending only on
residue features. `integerLaw_full_configuration_common_conductor` proves
that the full-configuration probability divided by that product is invariant
under every residue-preserving choice of all N integer lifts. These are joint
factorization identities, beyond the earlier singleton marginal identities.
`conditional_product_partition` normalizes actual countable disjoint
configuration events. `integerLaw_conditional_residue_lifts` gives every
conditional joint atom as the product of the individually normalized Pareto
lift weights, conditional on distinct selected classes of positive probability.
`residueClassWeight_pos` and `residueLiftWeight_tsum_one` discharge positivity
and normalization of the individual factors. This characterizes the conditional
independent lift distribution on the countable tuple space; it does not assert
cross-stage independence or establish the missing class-selection asymptotics.

**Established analytic RH iff:**
`riemannHypothesis_iff_right_half_strip_zero_free` is an unconditional
equivalence with Mathlib's actual `RiemannHypothesis`, using functional-equation
reflection. It is an analytic right-half-strip equivalence, not the missing
RH-to-residue-density converse.

**Established conditional research reductions:** the supplied hypotheses in
`riemannHypothesis_of_mode_parseval`,
`riemannHypothesis_of_determinant_ratio_zero`,
`riemannHypothesis_of_limitingKernel_site_one`, and
`riemannHypothesis_of_site_vacancy_tendsto_zero` each imply actual RH.
An off-line zero in the right half strip forces the explicit positive
`siteMellinVacancyFloor` at every site, simultaneously for all finite stages
and for the closed-space projection. `weightedLimitingHole_harmonic_lower`
then implies divergence of the weighted expected hole sum under not-RH.
`riemannHypothesis_of_weightedLimitingHole_summable` proves the summability
criterion; `riemannHypothesis_of_summable_weighted_hole_probabilities`
identifies its actual probability interpretation.
`riemannHypothesis_of_bounded_weighted_hole_windows` needs only a fixed real
C such that every window [0,M) has some stage N with
sum (n+1)*(1-integerKernel N n n) <= C. N may depend arbitrarily on M.

**Open providers:** no proof of Parseval saturation, determinant-ratio decay,
single-site saturation, weighted-hole summability, or the uniform weighted
finite-window bound is supplied. The DPP identities alone do not discharge
these arithmetic obligations.

**Open classical formalization:** RH implies residue density (Bagchi,
https://arxiv.org/abs/math/0607733, Theorem 2). Missing providers include
RH-dependent Moebius Dirichlet partial-sum bounds, a uniform spectral L2
majorant, and transport of the two norm limits to this residue Hilbert space.
`GeneralHardyConverse` is also an unproved proposition in the existing
analytic library; it must not be treated as an established provider.
The full spatial monotone coupling, continuous Mellin-space DPP, infinite
trace-class Fredholm theory, and claimed scaling limits are not established
by this finite/countable development.

### Arithmetic DPP existence and the remaining spatial coupling (2026-09-20)

Modules: `LinearAlgebra/AccretiveDeterminant`,
`Probability/FiniteDeterminantalLaw`, `Probability/FiniteSubsetLaw`,
`Probability/BooleanProjectiveLimit`, `Probability/DeterminantalExistence`,
`Probability/DeterminantalLimit`, `Probability/ScalarVacancyCoupling`,
`Analysis/ProjectionDPPKernel`, `RH/IntegerDPPExistence`, and
`RH/IntegerDPPCoupling`.

Source: Lyons, *Determinantal Probability Measures*,
https://arxiv.org/abs/math/0204325, Sections 5, 7, and 8, for the existence
statement and DPP terminology. The formal construction uses explicit mixed-row
determinant weights, row multilinearity, finite inclusion-law uniqueness, and
compact Boolean cylinders. Its Caratheodory step follows Mathlib's projective
content and Ionescu--Tulcea implementation. No general existence theorem is
assumed as an axiom.

**Established:** `Matrix.det_nonneg_of_quadratic_nonneg` needs only a
nonnegative real quadratic form, not matrix symmetry. This proves
`exactWeight_nonneg` for every real positive contraction; `sum_exactWeight`
and `sum_exactWeight_supersets` give normalization and every inclusion minor.
`finiteLaw_isDPP` checks all finite correlations. Finite Boolean laws are
projectively consistent by `isProjectiveFamily_of_isDPP`.
`contractionDPP_isDPP` constructs the full probability law for an arbitrary
ground set from positive-contraction finite principal matrices.

The arithmetic proofs discharge both matrix hypotheses using the actual
orthogonal projections and counting basis. `integerLaw_isDPP` gives every
finite-rank arithmetic DPP on the full countable set, and
`limitingLaw_isDPP` gives the closed-space DPP. Their first-site vacancies
are exactly `vacancy n` and `limitingVacancy`. These existence theorems
have no RH, density, carry-membership, or vacancy-decay hypothesis.

**Coupling results established:** every principal kernel increment is positive
semidefinite, with the exact projection-difference Gram identity.
`isDPP_increasingUnion` identifies the union of any supplied pointwise nested
DPP sequence with its limiting kernel. The arithmetic specialization gives the
exact never-entry probability, but still assumes that spatial coupling.
Separately, `firstSiteOccupied` constructs a genuine monotone process on a
single uniform probability space with the arithmetic first-site marginals.
`firstSite_entry_ratio` proves its conditional entry ratio equals the actual
`hazard n`, unconditionally. This scalar process is not a construction of
joint spatial DPP correlations.

**Open formalization obligation:** a monotone coupling of the full arithmetic
random subsets. The finite rank-one projection-extension transport problem is
the next concrete step: construct nonnegative joint masses supported on
S subset T whose marginals are the two explicit determinant laws. Kernel
order alone is not a formal proof of the required stochastic domination and
transport. The mathematical existence is established by Lyons, Theorems 6.2
and 7.1 together with Strassen's theorem; it is not an open RH conjecture.

**Conditional research reduction:** `riemannHypothesis_of_limitingLaw_first_site_ae`
uses the now-constructed law but retains almost-sure first-site occupation.
**Open mathematical obligation:** prove zero limiting vacancy, or an existing
equivalent density/carry/divergence criterion. DPP existence and either scalar
or full spatial coupling do not by themselves discharge that obligation.

### Reciprocal Mellin reflection and symmetric completion (2026-09-20)

Modules: `Analysis/ReciprocalMellinSymmetry`, `Analysis/ReflectedProjection`,
`Analysis/ReflectedHilbertRank`, `Analysis/DoubleHilbertReflection`,
`Analysis/ReflectedKernel`,
`RH/IntegerDPPReflection`.

Source: user-provided reciprocal Mellin construction. Mathlib's actual Mellin
change-of-variable theorems support the analytic identities; the DPP
correlation terminology follows Hough--Krishnapur--Peres--Virag,
https://arxiv.org/abs/math/0503110.

**Established:** reciprocal reflection and conjugation
are commuting involutions on the positive axis; they act on the actual Mellin
transform by s -> 1-s and conjugation. Both weighted energy and its integrability
are preserved. The original and reflected positive-side functions are
orthogonal, including treatment of the measure-zero endpoint at 1.

The algebraic completion P+JPJ is self-adjoint, idempotent, and commutes with J
under the explicit involution and orthogonality conditions. A concrete
Hilbert direct-sum implementation proves these conditions for the actual
Submodule.starProjection, and is specialized to the arithmetic finite spaces.
Hilbert projection
orthogonality supplies PJP=0, and finite dimensions double. For real physical
features the reflected Mellin kernel equals the complex conjugate kernel;
the completed kernel is twice its real part, and every finite correlation
determinant is reflection-invariant.

The actual arithmetic doubled-space condition is equivalent to the original
closedSpace=top, limitingVacancy=0, and vacancy tending to zero.
**Conditional research reduction:** riemannHypothesis_of_reflectedClosedSpace_eq_top
uses the existing checked implication to RH. **Open:** proving that the actual
reflectedClosedSpace is top, equivalently the original arithmetic density.
Symmetry does not discharge that obligation.

Formalization boundary: these modules prove analytic, projection, dimension,
and correlation-kernel statements. They do not construct a general continuous
DPP probability law or identify random particles with zeta zeros.

### Exact dyadic CRT optimization and the remaining convergence estimate (2026-09-20)

Modules: `RH/DyadicCarryCRT`, `RH/MobiusJointHeadProjection`,
`RH/MobiusJointHeadCorrections`, `RH/DyadicCarryOptimization`,
`RH/DyadicCarryOptimizationCRT`, `RH/DyadicCarryOptimizationLimit`,
and `RH/ParetoProgressionMidpoint`.

Source: the user-provided
`RH_Dyadic_Block_CRT_Energy_and_Mobius_Obstruction_2026-09-20.md`,
especially Sections 2--8. This entry records the formalized finite argument;
the paper's external analytic nonconvergence and hypothetical-zero discussion
are not asserted as Lean results here.

**Established:** `dyadicCarryBlock_sequence` identifies the actual Hilbert
block at d = 2^k+1 with r_d minus the indicator of nonmultiples of d.
The exact-head interpolant reproduces every vector with conductors at most
N+1 and is uniquely determined by that head. `headNullResidueSpan_iff`
identifies every finite legal head-zero correction with a finite combination
of r_m-r_(N+1), m>N+1. The natural diagonal error is exactly the corrected
constant Möbius approximant minus the nonmultiple indicator.

`headNullHilbert_independent` proves independence of the actual Hilbert
correction vectors using their Möbius charges. `headCorrectionCoefficients`
constructs their inverse-Gram minimizer without an inverse hypothesis.
`dyadicRepairEnergy_eq_norm` and `dyadicRepairEnergy_minimizes` identify the
complete signed Schur remainder with the true optimum for the finite
correction dictionary. `dyadicRepairEnergy_crt` identifies that optimized
energy with its full positive-period CRT sum. Summability, periodicity,
all mixed terms, and the vanishing repaired head are included.

`progressionMidpointWeight_relative_bounds` proves
(1 - 1/(2P+3)^2) W <= W_mid <= W for every positive P and r.
The global factor is at least 24/25. The comparison holds for arbitrary
signed finite quadratic forms; their exact and midpoint energies tend to
zero along exactly the same parameter limits, with no coefficient-growth
restriction. The minimum-comparison theorem takes minimizing points and
their minimizing properties explicitly; it does not construct a separate
midpoint optimizer.

**Concrete limit:** `dyadicRepairEnergy_zero_head_tendsto` proves, without
a convergence hypothesis, that the completely specified schedule N=0, L=2^k
converges to `limitEnergy`, the constant target's squared projection defect.
`headCorrection_zero_eq_projection` identifies the actual inverse-Gram
correction with the established finite residue projection. Removing the legal
terminal residue and the uniform contraction bound control the moving target.
`dyadicRepairEnergy_zero_head_tendsto_zero_iff` proves that this limit is zero
exactly when the constant belongs to the closed legal space. Exhaustion has
therefore supplied the limit, but not the missing assertion `limitEnergy = 0`.

**Conditional endpoint:** `riemannHypothesis_of_dyadicRepairEnergy_tendsto`
derives Mathlib's RH from vanishing of the constructed Schur energies along
unbounded dyadic stages. Legal vectors, exact heads, inverse coefficients,
and CRT identities are discharged. The vanishing-energy hypothesis is not.

**Open:** choose stage, head, and correction schedules and prove that their
full signed Schur remainder tends to zero. `dyadicRepairEnergy_limit_lower_bound`
shows that any such energy limit is at least the constant target's squared
distance to the closed legal space. Finite interpolation, invertibility,
and uniform midpoint approximation do not prove that distance is zero.
Odd-carry membership remains unproved. Arithmetic DPP existence is supplied
by the later `RH/IntegerDPPExistence` development; the full spatial monotone
coupling remains unformalized. No unconditional RH is asserted.

### Quantitative dyadic carry transport (2026-09-20)

Module: `RH/DyadicCarryQuantitative`.

Source: the user-provided odd-carry continuation and its exact finite residue
identities. No novelty claim is made.

**Established:** reusing `residueFraction_reverse_all` from `RH/DyadicCarryCRT`,
`dyadicMultipleIndicator_sequence` identifies the remaining error exactly
with the positive-multiple indicator. `dyadicMultipleIndicator_norm_sq`
retains its entire infinite sparse energy, and
`dyadicMultipleIndicator_norm_sq_le` bounds it by 2/(2^k+1)^2.
The existing `positiveWeight_mul_bound` in `RH/DilationWaveletOffScale` is
exported and reused, without a persisted duplicate proof.

`dyadicCarryBlock_projection_sparse` gives the exact projected discrepancy.
`dyadicCarryGap_error_le` bounds the difference between the block optimum
and the constant's distance by sqrt(2)/(2^k+1).
`dyadicCarryBlock_transport_mem` and `dyadicCarryBlock_transport_error`
convert each legal block candidate v to the legal constant candidate
(2^k+1) g_(2^k+1)-v with that same additive error bound.
The unprojected sampled-residue squared error is also bounded by 2/(2^k+1).

**Finite signed comparison:** in `RH/DyadicCarryOptimizationLimit`,
`dyadicRepairEnergy_zero_head_eq_sparse` writes the actual optimum as the
squared norm of the constant residual minus the projected multiple indicator.
`dyadicRepairEnergy_zero_head_signed` retains the exact negative twice-inner
product term and the complete remaining square.
`dyadicRepairEnergy_zero_head_sqrt_error_le` bounds the difference of the
two finite error norms by sqrt(2)/(2^k+1), using
`dyadicFiniteSparseResidual_norm_le`. This is a comparison with the original
finite constant error, not an upper bound tending to zero for either error.

**Open:** the constant's distance has not been proved zero; neither a vanishing
block approximation nor unconditional RH follows from the quantitative
convergence-to-that-distance theorem. Later-modulus head-preserving
optimization still needs an all-scale tail-energy estimate.

### Joint carry heads, dyadic carry blocks, and canonical Schur tails (2026-09-20)

Modules: `RH/OddCarryJointHead`, `RH/DyadicCarryBlocks`,
`RH/IntegerDPPSchurCanonicalEnergy`.

Source: the user-provided odd-carry/DPP continuation, particularly its exact
signed residual and simultaneous boundary-repair task; the existing finite
Mobius inversion, argument-doubling, and canonical tail-capacity modules.

**Established:** the actual carry Mobius coefficients are the positive
progression convolution minus the single period atom. `mobiusJointHead` gives
an explicit finite legal interpolation of every anchored sequence on its
entire prescribed head. Its complete signed floor residual and its summable
carry energy are retained in `doublingCarry_joint_energy_eq_tail`.

The whole dyadic carry block is an exact weighted finite sum of sampled
carries. The sampled residue at modulus 2^k+1 converges to the constant in the
actual norm. `dyadicCarryBlock_projection_residual` removes its legal residue
term exactly, and `dyadicCarryGap_tendsto` identifies the limiting optimum with
the constant's distance to the closed legal space. The formerly private
`reverseResidue_head` is now public and reused, without a duplicate proof.

Under the explicit hypothesis `pointDualResidual != 0`,
`schur_hasSum_canonical_energy` and `schur_tail_hasSum_error` give the exact
infinite Schur sum and every remaining tail as canonical certificate energies.
The same hypothesis gives uniform normalized vanishing of all reciprocal
source discrepancies. This describes the obstruction case; it does not
exclude it.

**Conditional research reduction:**
`riemannHypothesis_of_dyadicCarryBlock_approx` implies Mathlib's RH from legal
approximation of whole dyadic blocks with norm error tending to zero along
an unbounded sequence of stages. It does not require a Hurwitz-series provider.

**Open:** construct that block approximation, or bound the complete signed
tails of the explicit joint head interpolants uniformly across the growing
stages. Individual carries tending to zero and finite head interpolation do
not discharge this obligation. The original odd-carry approximation bound,
capacity/Schur divergence, and unconditional RH remain unproved.

### Odd-carry arithmetic and a concrete legal approximation (2026-09-20)

Module: `RH/OddCarryArithmetic`.

Source: the user-provided DPP/odd-carry and argument-doubling handoffs,
especially Sections 2 and 4 of the doubling/Hurwitz note, support the carry
definition, modular identities, and finite Mellin proof strategy.

**Established:** `doublingCarry_succ_sub` proves the exact positive and
negative jumps for every modulus at least two. The finite complex-weight
telescope and its cpow specialization retain the terminal boundary term.
`doublingCarryHilbert_tendsto_zero` proves unconditional norm decay of the
actual carries, which is not a closed-span membership assertion.

`oddCarryAdjacentApprox` is an explicit finite legal combination for modulus
2*m+1. Its exact signed error is the argument-doubling image of
g_(2*m+2)-g_(2*m+1), with the corresponding norm upper bound. The error at
physical coordinate 2*m+1 is m/(m+1). The resulting full-norm square lower
bound concerns this particular approximation; it is not a bound on the
optimum over all legal vectors.

**Open:** the infinite paired progression/Hurwitz Mellin identification and
the parameter-derivative asymptotic are not formalized by this module.
Odd-carry membership, vanishing vacancy, and the actual capacity/Schur
divergence remain unresolved mathematical obligations. None of the new
declarations is an unconditional RH theorem.

### Determinantal laws, actual integer vacancy, and odd-carry RH reduction (2026-09-20)

Modules: `Probability/DeterminantalProcess`, `Probability/DeterminantalEntry`,
`Analysis/ProjectionDPPKernel`, `RH/IntegerDPPHazards`,
`RH/ResidueClosureDensity`, `RH/IntegerDPPClosure`, `RH/IntegerDPPSchur`,
`RH/IntegerDPPKernel`, `RH/IntegerDPPMellinObstruction`,
`RH/IntegerDPPReduction`.

Source: user-provided `RH_DPP_Proof_Attempt_and_Explicit_Zero_Hole_Obstruction_2026-09-20.md`,
`RH_CRT_Orbit_Exhaustion_and_Doubling_Invariance_2026-09-20.md`, and the
argument-doubling handoff. Hough--Krishnapur--Peres--Virag,
https://arxiv.org/abs/math/0503110, supports the DPP terminology and correlation
definition. The explicit singleton and single-hole constructions are proved
directly here; a general existence theorem is not imported as an axiom.

**Established:** `Probability.DPP.IsDPP` specifies all finite inclusion
determinants, not just marginals. Occupation, vacancy, almost-sure saturation,
two-point covariance and pairwise negative correlation for symmetric kernels
follow from that definition. `singleton_isDPP` and `singleHole_isDPP` construct
actual laws from any PMF and verify every correlation determinant.
The rank-one kernel is normalized, symmetric, idempotent, and has trace one.
`normalized_singleHole_vacancy` gives the exact normalized weight law with
explicit finite, nonzero total-mass hypotheses.

`ProjectionDPPKernel` proves Gram positivity and the complementary residual
kernel identity. `IntegerDPPKernel` defines the actual arithmetic kernels
using `lp.single` and the finite/closed residue projections. Counting coordinate
0 is physical integer 1. It proves q_N = 1-K_N(0,0), kernel convergence, and
q_infinity = 1-K_infinity(0,0). `IntegerDPPHazards` proves
q_N = 2/(C_N+2), q_0=1, positivity, monotonicity, the hazard product, exact log
accounting, and vacancy decay iff divergence of the actual hazard series.

`IntegerDPPSchur` constructs the actual tail innovation, proves sigma_N>0,
retains the signed eta_N, and establishes
C_(N+1)-C_N = eta_N^2/sigma_N and
h_N = eta_N^2/((C_N+2)sigma_N+eta_N^2), including the exact telescope.
No arbitrary capacity-increment identity is assumed.

`ResidueClosureDensity` expresses every point vector as a difference of scaled
floor dilations of the constant and proves 1 in S iff S is the entire Hilbert
space. `IntegerDPPClosure` and `IntegerDPPReduction` prove exact equivalences
between all odd carries belonging to S, q_infinity=0, q_N tending to zero,
C_N tending to infinity, and divergence of the actual hazard and Schur sums.

`IntegerDPPMellinObstruction` evaluates the first-point Mellin transform as
(1-2^(-s))/s and proves it is nonzero for Re(s)>1/2. A zeta zero s with
Re(s)>1/2 and s != 1 forces the explicit positive vacancy floor
2(2 Re(s)-1)|1-2^(-s)|^2/|s|^2, bounded actual capacity, and summable hazards.
These are implications from a hypothetical zero, not an assertion that one
exists or an exclusion of the resulting hole.

**Conditional research reductions:** the odd-carry, vacancy, capacity,
hazard-sum, and Schur-sum endpoints prove Mathlib's `RiemannHypothesis` under
their stated equivalent hypotheses. With a supplied arithmetic `IsDPP` law,
`odd_carry_iff_first_site_ae` and `odd_carry_iff_full_occupation_ae` identify
almost-sure saturation; `riemannHypothesis_of_dpp_first_site_ae` is the
probability endpoint. `dpp_entry_probability_eq_hazard` additionally requires
a given nested coupling and identifies the exact conditional entry probability.

**Open mathematical obligation:** prove membership in S of every odd carry,
equivalently any one of the actual divergence/vanishing criteria above.
**Existence formalization discharged:** the later `RH/IntegerDPPExistence`
module constructs the finite-rank and limiting arithmetic projection DPPs on
the full countable ground set, without a DPP-existence assumption.
**Open formalization obligations:** the full spatial nested coupling;
identification of the handoff's specific complex Mellin rank-one mode with a
constructed probability law; the RH-to-density converse; and supplementary
CRT-lift, arithmetic-progression occupation, first-moment, and Mellin-frequency
gap arguments. The scalar coupling and hazard interpretation are now proved
in `RH/IntegerDPPCoupling`; they do not assert spatial correlations.
The equivalent capacity formula remains fully proved. No unconditional RH
or general negative-association theorem is claimed.

### Argument-doubling operator and odd-generator criterion (2026-09-20)

Module: `RH/ArgumentDoublingGenerators`.

Source: user-provided
`RH_Doubling_Generators_and_Hurwitz_Obstruction_2026-09-20(1).md`,
Sections 1--4; Bagchi, Theorem 1, https://arxiv.org/abs/math/0607733
supports the weighted residue-space terminology.

**Established:** `argumentDoublingContinuous_norm` constructs the actual
operator A_2 f(n) = f(2n) and proves its exact operator norm is 2.
`doubling_weight_identity` keeps the exact weight ratio.
`hilbertArgumentDoubling_residue_even` proves A_2 g_(2q) = g_q.
`hilbertArgumentDoubling_residue` and `doublingCarry_odd` give
A_2 g_d = 2 g_d - b_d, with the exact odd half-residue indicator.
`CoefficientStabilization.argumentDoublingInvariant_iff_generators`
and `argumentDoublingInvariant_iff_odd_carry` identify the remaining
closed-span membership condition without assuming it.
`doubled_three_not_mem_finiteSpan` proves there is no finite residue identity
for A_2 g_3; it makes no assertion of nonmembership in the closure.
`closedSpace_mellin_distance_sq_lower_bound` proves, for a right-half-plane
zeta zero s and u in S,
(2 Re(s)-1) |L_s(f)|^2 <= ||f-u||^2 in the original full weighted norm.
`doubled_residue_not_mem_of_mellin_ne_zero` applies the actual Mellin separator.

**Conditional research reduction:**
`CoefficientStabilization.riemannHypothesis_of_odd_carry` proves Mathlib's
`RiemannHypothesis` from membership in S of b_d for every odd d >= 3.
The contrapositive `exists_odd_carry_not_mem_of_not_RH` is also proved.

**Open:** the odd-indicator membership hypothesis. Neither the norm bound
nor the finite modular formulas supplies it. The handoff's Hurwitz Taylor
estimate and nonvanishing, all-sufficiently-large-odd obstruction,
unbounded-index criterion, and RH-to-invariance converse are not yet
formalized here. No unconditional proof of RH is claimed.

### Argument-doubling closure reduction (2026-09-20)

Module: `RH/ArgumentDoublingClosure`.

Source: user-provided CRT/orbit research direction and the ensuing
argument-doubling construction.

**Established:** `hilbert_tendsto_one_of_bounded_coordinates` proves norm
convergence to the constant target from positive-coordinate convergence and
values in [0,1], using the actual summable Pareto weights.
`floorDilation_ne_argumentDoubling` proves that the already available
floor dilation differs from sampling even arguments.

**Conditional research reduction:**
`CoefficientStabilization.hilbertOne_mem_of_argumentDoubling` and
`CoefficientStabilization.riemannHypothesis_of_argumentDoubling` prove
that invariance of the actual closed residue span under f(n) ↦ f(2n)
implies target membership and Mathlib's Riemann hypothesis.
The proof iterates the assumed map on g_(2^k+1), uses
g_(2^k+1)(2^k n) = 1 - n/(2^k+1) for 0 < n < 2^k+1,
and applies dominated convergence and the verified Mellin bridge.

**Open:** `CoefficientStabilization.ArgumentDoublingInvariant`.
It is an explicit hypothesis, not a proved provider. CRT orbit exhaustion
and the existing floor-dilation theorem do not discharge it.
No unconditional proof of RH, or formal RH-to-invariance converse,
is claimed here.

### Signal-to-noise PDF audit (2026-09-19)

Source: Christian Noack, user-provided `signal_to_noise_RH_program (2)(1).pdf`,
Lemma 4.1, Theorem 4.2, Conjecture 8.2, and Section 10.
Explanation: `RH/SignalNoiseAudit20260919.md`.

**Established:** `RH/IntegratedRamanujanCovariance` proves strict centered
variance for actual finite packet combinations.
`LinearAlgebra/FiniteSignalNoise` proves finite covariance completion,
unique minimization, Rayleigh bounds and the scalar signal inequality under
its stated symmetric positive definite matrix and normal-equation hypotheses.
`RH/RamanujanSignalNoise` supplies the actual arithmetic solution, its
uniqueness, the exact error `1/(1+R)), and optimal coefficients, using the
full Pareto law and actual Gram inverse with no assumed inverse provider.

`RH/ConductorDegreeObstruction` proves the direct Hilbert version of
Conjecture 8.2 for all conductors of bounded distinct-prime count, with the
exact error remainder and centered signal/variance inequality.
`RH/ParetoOccurrenceGreen` proves the exact digamma block and Green sums.
`RH/MobiusFloorTail` proves the finite split and actual endpoint refutation
of the missing-constant residual; its general repair explicitly assumes the
coprime-count inclusion-exclusion equality.

**Open:** the main scalar variance rate, atom-reuse decay, and shell SNR
divergence. The accompanying audit gives an analytic occurrence-decay
argument via a squarefree transfer of Heath-Brown's gap method; it is not
Lean-verified and supplies no project axiom. The general coprime-count
identity, exact primorial subspace assembly, and RH-to-closure converse
remain formalization obligations. Finite inverse and positivity results
do not discharge these limiting estimates.

### Ramanujan inverse and von Mangoldt orthogonal scores (2026-09-19)

Modules: RH/IntegratedRamanujanInverse and RH/RamanujanOrthogonalScores.
Explanation: RH/RamanujanVonMangoldtRoute20260919.md.

**Established:** ramanujanPacket_prime_pow_mul_inverse gives the explicit
finite inverse from \(B_{p^{v+1}u}\) to prime-seed dilations, for a prime
\(p\), positive \(u\), and \(p\nmid u\). The full Pareto orthogonalization
constructs the old Gram fit, proves orthogonality, and identifies the
screened score as von Mangoldt minus the fitted von Mangoldt means
(score_vonMangoldt). The theorem pivot_schur retains every covariance.
The theorem pivot_pos proves a strictly positive pivot for an increasing
conductor enumeration from the Mobius coordinate innovation_mobiusDifference.
The theorem update_error proves the exact one-step squared-error gain;
gain_le_error bounds it by the previous full error; update_legal
preserves the two-seed space.

The prior paretoMean_ramanujanPacket identifies the mean with the actual
ArithmeticFunction.vonMangoldt. Mixed conductors stay in the Gram
dictionary even when this raw mean vanishes.

**Open:** exhaustion of the target norm by the sum of orthogonal gains,
or decay of the growing exact-head affine Schur errors. The finite inverse
and normal equations do not provide these all-scale estimates. The
orthogonal-sum and exact-head matrix displays in the explanation describe
the finite construction; no new Lean theorem asserts their limiting decay.


### CRT weights and two-seed regression limits (2026-09-19)

Modules: `Analysis/FiniteHilbertGramProjection`,
`RH/TwoSeedSchurConvergence`, and `RH/ParetoCRTWeightLimits`.
Explanation: `RH/CRTRegressionLimits20260919.md`.

**Established:** the exact inverse-Gram fit equals orthogonal projection.
Finite coefficients are unique. Nested finite tail dictionaries with the
same prescribed head obey the full Pythagorean error-drop identity.
`candidate_tendsto_fixed_head` proves norm convergence to the affine
projection onto the closed union of these tail spans. The literal intervals
`{N+1,...,N+M}` exhaust all balanced tail indices. The theorem
`candidate_tendsto_one_iff` identifies the precise target-membership condition.
No density hypothesis is needed to prove existence of the projection limit.

The genuine CRT progression mass at fixed residue `r` tends to its first
atom. In particular `uniformDefect_one_tendsto_half` and
`uniformDefect_one_not_tendsto_zero` rule out asymptotic uniformity of these
weights. This is not a positive error floor for exact-head candidates.

**Conditional research reduction:** `diagonal_limit_eq_one` identifies any
norm limit of the growing exact-head candidates with one.
`riemannHypothesis_of_diagonal_limit` concludes RH from the explicitly
supplied existence of that limit. Existence, all-scale Schur error decay,
and a uniform exact-head energy bound remain open. Finite uniqueness,
CRT regrouping, and a fixed-dictionary CLT do not discharge them.

### Full finite two-seed Schur candidates (2026-09-19)

Module: `RH/TwoSeedSchurCandidates`.

**Established:** `candidate` constructs the canonical exact head plus the
full inverse-Gram correction on any finite set of balanced indices greater
than the head length. Zero-target coefficients are allowed. Target zero
minimizes packet energy; target one minimizes squared error to one.
`correctedHead_feasible` also covers arbitrary fixed coefficients.
`candidate_feasible`, `candidate_error_sq`, `candidate_completion`, and
`candidate_minimizes` prove exact-head legality, the full signed Schur value,
the exact excess loss, and finite affine optimality. The existing Green
identity retains the negative finite boundary and the true infinite tail.

**Open:** all-scale error decay or a uniform bound on the energies of chosen
growing candidates. Fixed-dictionary CLT arguments concern coefficient
estimation only; no CLT or growing-dimension statistical theorem is
formalized in this module. Numerical rational candidates and integer
arithmetic certificates are separate from the Lean kernel proofs.

### Quantitative finite two-seed approximation (2026-09-19)

Module: `RH/TwoSeedHeadEnergyGeometry`.
Namespace: `RiemannResearch.RH.Pareto.TwoSeedExactHeadEnergy`.

**Conditional research reduction:** for the actual full-norm exact-head
infimum `energy N`, `BddAbove (Set.range energy)` produces finite legal
two-seed packets `F N` at finite dilation budgets `M N`, satisfying
`F N(k) = 1` for `1 <= k <= N`,
`norm (F N - hilbertOne)^2 < 4/(N+1)`, and norm convergence to
`hilbertOne`. No growth restriction on `M N` is imposed or proved.

Endpoints: `exists_finite_budget_approximation_of_energy_bddAbove` and
`exists_finite_budget_sequence_of_energy_bddAbove`.

The supporting checked identities keep their closure hypothesis explicit:
`closedMinimizer_error_sq_of_closure` gives
`norm (hilbertOne - closedMinimizer N)^2 = 1 - energy N`;
`feasible_error_sq_le` bounds the full error by twice the excess energy
plus twice `1 - energy N`.

**Open:** prove the uniform bound `BddAbove (Set.range energy)`.
The pre-existing `energy_bddAbove_iff_closure` shows that it is exactly
the two-seed approximation problem. The new rate constructs finite
witnesses from that hypothesis; it does not discharge it. No unconditional
two-seed approximation or RH proof is asserted.

Source: independently derived from the project's exact-head projection
geometry in response to the user's two-seed approximation request.

### Exact-head residual tails and RH-criterion failures (2026-09-19)

Modules: `RH/ExactHeadResidualTail` and `RH/RHCriterionFailures`.

**Established:** the actual canonical residual has vanishing weighted tail
energy `t_N`, and every exact-head vector in the closed legal residue span
satisfies `E^2 <= t_N * norm (one - f)^2`, where `E = norm r^2`.
The shift realization is proved equal to the physical infinite Pareto tail.
Simultaneous orthogonal repair preserves legality and the exact head, and
has the exact full-energy split; the remaining Schur error obeys the same
canonical lower bound.

**Established under explicit not RH:** every growing exact-head legal
family has squared errors tending to infinity. Positive-seed approximation,
mean-one variance, noise-to-signal and conditional-iid criteria have positive
uniform error floors; every legal walk has summable relative gains.
Conditional exact-head minima diverge. Dyadic boundary recovery, the
applicable repair-orbit criteria, balanced finite-deletion approximation,
and the literal uniform signed-Schur targets fail. The cofinal subpower
criterion fails with its exact quantified negation: some positive exponent
eventually beats every constant-multiple bound for the head minimum.

**Conditional research reductions:**
`riemannHypothesis_of_residual_tail_product`,
`riemannHypothesis_of_small_residual_tail_product`, and
`riemannHypothesis_of_bounded_exact_head_errors`.
Only arbitrarily small residual-tail/error products are needed; a prescribed
rate or convergence of the approximants is not assumed. General repair
operators retain their fixing and contraction hypotheses.

**Open:** construct genuine exact-head legal witnesses with these
product/energy upper bounds. The exact finite optimization identities and
their strict improvements do not establish an all-scale bound. No
unconditional RH proof, reverse density provider, or contradiction between
already-proved arithmetic estimates is asserted.

Verification and candidate-clash audit: `RH/RHContradictionAudit20260919.md`.


### Escape of the canonical defect reconstruction (2026-09-19)

**Established:** finite Möbius inversion makes the ordered reconstruction
error linear on the first N+1 coordinates. The coefficient Riesz dictionary
is total independently of residue density. Its finite projections converge
strongly to every vector. For the actual orthogonal residual r and its
ordered reconstruction R_N, the exact pairing is
`inner (r - R_N) (r - dualProjection_N r) = norm r ^ 2`.
Cauchy--Schwarz and Pythagoras give the corresponding squared norm bound.

**Established under explicit not RH:** `norm R_N` tends to infinity.
This strengthens the earlier exclusion of an ordinary norm limit and
excludes every bounded cofinal subsequence.

Module: `RH/MobiusResidualEscape`.
Principal endpoints: `coordinatePartialSum_prefix_linear`,
`dualCoordinateProjection_tendsto`,
`defect_reconstruction_dual_bound_sq`,
`not_RH_defect_norms_tendsto_atTop`.

**Conditional research reduction:**
`riemannHypothesis_of_cofinally_bounded_defect_reconstruction`.

**Open:** a cofinal norm bound for the actual stabilized defect reconstruction.
No boundedness, subpower signed Gram estimate, or contradiction is asserted.
Polynomial and multiplicity-sensitive Mellin lower bounds in the written
continuation are not new Lean declarations in this module.

### Canonical constraints under failure of RH (2026-09-19)

**Established under explicit ¬RH:** the actual canonical tail certificate
has finite limiting capacity, a square-summable but not absolutely summable
primitive, both signs arbitrarily far out, and cofinal violations of
power/logarithmic additive savings. One common right-half-strip zero gives
a genuine Mellin pole and polynomial growth of the unrestricted head energy.

**Established canonical geometry:** finite dual vectors converge strongly
to the canonical certificate; every competing certificate satisfies exact
Pythagoras. The point projection is orthogonal to every integer dilation
m≥2. Every off-line zero imposes exact canonical Mellin interpolation.

**Established coefficient obstruction:** the actual stabilized defect
reconstruction has no ordinary ordered Hilbert-norm limit under ¬RH, is not
unconditionally summable, and has divergent absolute norm sum. Wrong
stabilized coefficients occur at arbitrarily large moduli.

Modules: `RH/CanonicalTailCapacityGeometry`, `RH/RHFalseTailConstraints`,
`RH/MobiusResidualInfiniteDefects`. Verification details and exact scope:
`RH/RHFalseConstraintsVerification20260919.md`. All 18 audited endpoints
use only standard foundations; no density-from-RH provider is used.

**Open:** the constraints have not been proved contradictory. Canonical
primitive absolute summability, cofinal subpower head energy, convergent
actual defect reconstruction, or divergent actual screened gains still
needs a new arithmetic estimate. The explicit Mellin-kernel compatibility
model and sqrt-modulus weight comparison remain written arguments.


### Signed primitives, full sieve boundaries, and the canonical RH endpoint (2026-09-19)

Source: continuation handoff
`RH_First_Coordinate_and_Tail_Capacity_Continuation_2026-09-19.md`,
Sections 24–31. Detailed scope and verification:
`RH/TailCertificateSieveFormalization20260919.md`.

**Established:** weighted-H membership implies primitive ℓ² with constant
four and vanishing square-root boundary; primitive ℓ¹ excludes an actual
reciprocal tail certificate, reusing the existing summable-tail rigidity.
Actual additive cancellation, including explicit power/logarithmic saving,
implies this exclusion. The alternating α=0 and constant-one examples
certify the two distinct regularity gaps.

`RH/ParetoFiniteSieveBoundary` and
`RH/ParetoMobiusSieveBoundary` prove the exact finite signed
identity. `RH/ParetoSieveBoundaryNorm` and
`RH/ParetoSieveBoundaryGrowth` prove the full signed
functional norm and its divergence for cutoff floor(Y/2).
`Analysis/FinitePrimeProductBounds` supplies all prime-product
rates. `RH/PrimeSievePointEnergy` proves the actual legal
candidate's correct pointwise/coefficient limits and divergent full-tail
energy. `RH/TailCapacityJointCorrections` proves attained
joint optimization, complete signed covariance, reciprocal-defect sources,
capacity-gain bounds and the telescope, including dependent trial families.

**Conditional research reductions:** in
`RH/TailCertificateCancellationEndpoint`,
`riemannHypothesis_of_canonicalTailSummability` and
`riemannHypothesis_of_canonicalAdditiveCancellation`
retain their actual summability premise. In the joint module,
`riemannHypothesis_of_jointScreenedGainDivergence` retains
the actual divergent-gain premise.

**Open:** canonical primitive ℓ¹ under a nonzero residual; an arithmetic
power/logarithmic cancellation estimate that would supply it; or concrete
finite legal trial families with divergent cumulative screened gains.
`CanonicalTailSummability` is a proposition, not an axiom,
and its checked equivalence with vanishing of the canonical residual
makes its strength explicit. The unconditional attempt leaves precisely
the canonical summability goal unresolved. No unconditional RH proof.

### Exact conductor enlargement and cumulative gain (2026-09-19)

Source: user-provided argument, `RH_Controlled_Conductor_Schur_2026-09-10.md`, §§1–8.
The new development uses real Hilbert spaces and the actual complete Pareto weights.

**Established finite identities:** `LinearAlgebra/ConditionalSchurDecomposition.lean`
and `ConditionalSchurWoodbury.lean` prove the signed mean/fluctuation Gram split,
exact objective, attained enlarged-space projection, two-sided Woodbury inverse,
and marked spectral energy, including an actual symmetric eigensystem.
`FiniteHilbertSchur.lean` additionally gives normal-equation existence for singular
or redundant families, exact mixed residual covariance, and zero-gain criteria.
`WeightedFiniteCovariance.lean` and `WeightedQuotientHilbert.lean` prove the full
signed pairwise covariance and weighted averaging as orthogonal projection.

**Established arithmetic providers:** `RH/ParetoConductorFibers.lean`,
`ParetoConductorHilbert.lean`, and `ParetoConductorSchur.lean` construct the actual
weighted finite-period model and discharge its orthogonality assumptions.
`ParetoNewPacketPeriodicity.lean`, `ParetoNewPacketCovariance.lean`, and
`ParetoConductorInnovationCovariance.lean` prove independence modulo every old
periodic function and strict positivity of the actual full innovation covariance,
including repeated-prime enlargement. The proof uses divisor/Möbius arithmetic
rather than an assumed Fourier-support theorem.

**Established Green and obstruction statements:** `RH/ParetoPacketGreenGram.lean`
retains the exact finite boundary, complete tail, marked-score minus sign, full
means, and fixed-data limits for arbitrary finite combinations.
`IntegratedRamanujanHilbert.lean` and `OmittedPrimePacketObstruction.lean`
construct actual Hilbert packets and prove the prime functional, its Riesz
coordinates and exact norm, and the complete error identity throughout the
restricted packet closure for every omitted prime greater than two.
The norm theorem in `TwoSeedContrastObstruction.lean` now covers primes >2.

**Established all-scale equivalences:** `RH/ConductorProjectionChain.lean`
constructs actual divisor-packet projections, proves the full progression-mass
error floor, exact recurrence, gain bounds, and energy convergence iff actual
gains are nonsummable. Cofinality identifies the limiting packet closure.
`Analysis/ResidualGainProduct.lean` supplies additive, product, and logarithmic
accounting; `ResidualSpectralGain.lean` supplies the conditional marked-mass bound.

**Established exact assembly:** `RH/ParetoConductorEnergy.lean` identifies each
finite weighted minimum with the complete Hilbert conductor error.
`ParetoConductorSchurGain.lean` proves the complete old/new divisor partition,
the new-prime divisor enumeration, and equality of the full infinite gain with
the signed finite Schur value. `ParetoConductorInnovationBasis.lean` supplies
actual innovation synthesis injectivity. `ParetoConductorSpectrum.lean`
constructs both covariance and Schur inverse operators from that arithmetic
provider. `conductor_resolvent_energy` and `conductor_actual_spectral_formula`
prove equations (4.2), (4.3), and (7.3) for the actual conductor errors and gains.
The eigensystem is on the full finite ambient space; additional zero eigenvalues
preserve the exact marked residual weights. No rank or inverse provider is assumed.
`LinearAlgebra/ScalarSchurAddition.lean` proves the exact addition defect and
a strictly positive-block counterexample to Schur additivity.
`ConductorProjectionChain.lean` also specializes exact additive, product, and
logarithmic accounting directly to the actual conductor energies.
The existing complex `LinearMap.IsSymm.signed_change` in
`LinearAlgebra/SignedChannelUpdate.lean` supplies the signed-form audit in §8.

**Conditional research reduction:** `RH/ConductorProjectionRH.lean` proves
`riemannHypothesis_of_gain_not_summable` for actual nested conductor projections.
Its positive-seed closure is identified exactly with full packet closure.
**Open:** prove nonsummability of the actual arithmetic gains, or a sufficient
marked spectral-mass estimate. No such provider, unconditional RH theorem,
or formal RH-to-approximation converse is asserted here. Redundant designs
are handled by attained normal equations, not a named Moore–Penrose API.

### Tail-capacity literature audit and affine-head energy obstruction (2026-09-19)

**Established:** `Analysis/FiniteParetoAffineEnergy.lean` proves
`finite_pareto_affine_energy`, `finite_pareto_linear_energy`,
`pareto_affine_head_error_lower`, and
`pareto_affine_head_error_lower_linear`. A physical head 1-c*k forces
full squared error at least c^2*N/2, with an explicit summability hypothesis.

**Written mathematics:** `RH/TailCapacityLiteratureAudit20260919.md`
identifies the exact discrete residue space with Bagchi's Theorem 1.
It derives the primorial Mobius sieve head, proves its divergent energy,
and proves that a single exact-head repair still has divergent Pareto energy.
Those arithmetic specializations and asymptotic arguments are not claimed
as end-to-end Lean formalizations. The actual projection theorems are unaffected.

**Open:** actual tail-capacity divergence, or exclusion of every Hilbert tail
certificate. The audited literature gives equivalences, lower error bounds,
and RH-conditional upper estimates; no unconditional provider was added.


### Minimal-support finite-tail exhaustion and cofinal RH criterion (2026-09-19)

**Established:** `RH/BalancedFiniteTailGram.lean` now proves
`feasible_tail_representation`: every actual minimal-support exact-head packet
is the canonical head plus a finite supported tail.
`exists_schur_le_feasible`, `exists_schur_near_minimizer`, and
`energy_eq_sInf_schurValues` identify the unrestricted optimum exactly as
the infimum of the full signed finite inverse-Gram values. No finite-tail
ansatz, minimizer attainment, or prescribed budget growth is assumed.
`closure_iff_near_unit_schur` gives the exact target-synthesis criterion.
`twoSeed_energy_le` compares the full and retained dictionaries, and
`energy_power_lower_of_zeta` transfers the polynomial zero obstruction.

`cofinal_subpower_energy_iff_tail_gain` proves that the cofinal bound on
the infimum is exactly equivalent to the cofinal bound on actual finite
inverse-Gram witnesses; a near-minimizer changes C to C+1.
`cofinal_subpower_tail_gain_iff_unit_constant` removes the multiplicative
constant by halving the exponent and using cofinality. These are proved
equivalences of still-open arithmetic estimates, not providers of them.

**Conditional research reductions:**
`riemannHypothesis_of_cofinal_subpower_energy` and
`riemannHypothesis_of_cofinal_subpower_tail_gain` conclude Mathlib's actual
`RiemannHypothesis`. Each positive exponent may use its own cofinal head
sequence, with arbitrary finite tail budgets.

**Open:** the actual cofinal subpower energy/tail-gain upper estimate;
the stronger uniform bound; simultaneous deletion of all zero-target
coordinates under RH; RH itself. No provider for these estimates was added.
The infimum equality is unconditional; the RH conclusion retains its displayed
arithmetic upper-bound hypothesis.

### Dyadic gain endpoint and prime contrast obstruction (2026-09-19)

**Established:** `RH/DyadicGainEndpoint.lean` specializes the exact survival
product and zero-distance/nonsummable-relative-gain equivalence to the actual
two-seed Pareto budget residual. Summable gains have an explicit positive
surviving-energy limit. `normalized_dyadic_cost_iff` identifies the exact
reciprocal-cost condition for normalized legal screened corrections.

**Conditional research reductions:**
`riemannHypothesis_of_dyadic_gain_divergence`,
`riemannHypothesis_of_dyadic_gain_schedule`,
`riemannHypothesis_of_dyadic_cost_schedule`, and
`riemannHypothesis_of_dyadicLogarithmicGainBound`.
**Open:** nonsummability of the actual relative gains; an actual nonnegative
nonsummable gain minorant; normalized legal corrections with nonsummable
reciprocal costs; `DyadicLogarithmicGainBound`. No provider is asserted.
The dyadic-only logarithmic proposition has the precise handoff quantifiers;
it is not asserted RH-necessary or unconditionally RH-equivalent.

**Established:** `RH/TwoSeedContrastObstruction.lean` proves the prime Mobius
coordinate of every seed generator, its exact squared dual norm 2(q^2+1),
and annihilation of the closed span of a fixed old budget V_M plus all future
contrasts g_(3,m)-g_(2,m), including screened contrasts. For prime q>max(M,3),
every F in that closed span has the exact full-norm identity
||1-F||^2 = 1/[2(q^2+1)] + ||1-F+k_q/[2(q^2+1)]||^2.
This gives a positive obstruction for that restricted construction and the
same lower bound for the actual finite residual. Full prime generators escape
the kernel: their coordinate is q, and a pair of coefficients contributes
q(a+b). This does not prove or refute the full dyadic gain target.

### First-coordinate rigidity and the single-point RH target (2026-09-19)

**Established:** RH/MobiusResidualFirstCoordinate.lean proves the exact normalized
residue dilation formula and invariance of the actual coefficient dictionary
closure. For its actual limiting projection residual r and squared norm E,
the first physical coordinate satisfies
(1-sqrt(2)/2)*E <= r(1)/2 <= (1+sqrt(2)/2)*E.
It is nonnegative and vanishes exactly when the residual is zero. Membership
of the first point vector in the closed span is equivalent to membership of
the constant target. Point-error convergence and convergence of the first
constant-projection coordinate to one are equivalent to the existing
simultaneous Mobius coefficient target. Finite-stage first-coordinate
agreement is not asserted to imply zero error.

**Conditional research reductions:**
riemannHypothesis_of_firstCoordinate_zero and
riemannHypothesis_of_firstPoint_error_tendsto_zero.
**Open:** the actual limiting first residual coordinate equals zero;
equivalently, the full Pareto point approximation error tends to zero.
No provider for this equality or limit is asserted. The separate written
continuation derives the inverse-Gram scalar formulation and finite transfer
to multi-range conditional-mean witnesses; these extra written arguments
are not claimed as kernel-checked declarations in this module.

### Full Pareto tail capacity and the unresolved RH limit (2026-09-19)

**Established:** Analysis/FiniteGramCapacity and Analysis/FiniteGramScreenedCapacity
prove actual inverse-Gram capacities, normalized constrained minima, rank-one
identities, screened independence, exact additive Schur gains, and telescoping.
RH/ParetoTailCapacity specializes them to the actual residue dictionary and
removes only physical coordinate one. It proves finite tail independence,
delta_n = 1/(tau_n+2), kappa_n = 2*tau_n/(tau_n+2), and equivalence of
tau_n tending to infinity, kappa_n tending to 2, and point error tending to zero.
Stage n uses moduli 2 through n+1.

**Established:** RH/ParetoTailCapacityDuality constructs actual minimum-energy
tail vectors, proves exact squared-norm increments and capacity monotonicity,
and identifies bounded capacities with existence of an actual Hilbert tail
certificate. RH/ResidueTailCertificateRegularity excludes certificates with
finite absolute first moment and proves both signs occur arbitrarily far out.
Hilbert membership alone does not provide that moment condition.

**Established:** RH/ParetoFullTailCRT gives complete signed CRT/digamma tail
formulas. RH/TailCapacityDilationCorrection gives legal finite corrections and
exact energy gains. RH/PointTargetDilationSynthesis proves the finite
point-to-constant transfer with its exact largest-modulus budget.
RH/OmittedPrimeResidueBarrier proves permanent point and tail error lower
bounds when an odd prime modulus is omitted.

**Conditional research reductions:** riemannHypothesis_of_tailCapacity_tendsto,
riemannHypothesis_of_fullCapacity_tendsto, and
riemannHypothesis_of_no_tailCertificate. **Open:** TailCapacityDivergence,
equivalently excluding all actual tail certificates. No provider is asserted;
regularity exclusion and positive finite gains do not supply divergence.

**Conditional rate barrier:** RH/PointTargetLogarithmicBarrier rules out
eventual fixed fractional dyadic point-error improvement assuming
PointBurnolLogLowerEnvelope. Analysis/PointLogarithmicTransfer proves the
scalar transfer. **Open formalization input:** Burnol's analytic provider,
the continuous comparison, and logarithmic scale asymptotics.
See RH/TailCapacityFormalization20260919.md for exact coverage and limitations.
No unconditional RH theorem is asserted.

### Multi-range divisor corrections: exact construction and optimization (2026-09-19)

**Established:** the MultiRange modules prove the complete original primorial
correction characterization with reciprocal balance -alpha, anchored legality,
exact heads and coefficient uniqueness; actual finite Gram positivity and a
unique inverse-Gram optimizer; exact signed screened Schur gains with global
old/new reoptimization; and convergence of finite-range infima to the legal
infimum. Signed cross terms and overlapping supports are preserved.

**Established:** explicit finite-horizon positive definiteness, actual prefix
minimization, exact rational inverse coefficients, infinite-tail certificates,
and convergence of both rational endpoints to each fixed-family minimum.
The delayed-support obstruction includes the balance-anchor caveat. The
explicit polynomial zeta-zero obstruction applies to the remaining tail.
See RH/MultiRangeFormalization20260919.md for declaration/module coverage.

**Conditional research reduction:**
riemannHypothesis_of_multiRangeSubpolynomialTarget.
**Open:** MultiRangeSubpolynomialTarget, the actual legal family with
subpolynomial conditional-mean energy; a uniform fractional tail gain; RH.
No provider for these obligations is asserted. The existing canonical witness
has the stronger unconditional linear energy bound below 2Y.
The earlier documentation-only submission is superseded.

### Möbius coefficient stabilization and exact residual characterization (2026-09-19)

**Established:** RH/MobiusHilbertCoordinates.lean proves the actual finite
Möbius coordinates jointly separate points of the Pareto Hilbert space,
biorthogonality on normalized residues, the finite-support Riesz representation,
and the exact squared coordinate norm sum j(j+1)*dualCoeff(m,j)^2.

**Established:** Analysis/ExhaustiveProjectionWalk.lean now gives continuous
coordinate convergence, the exact limiting energy decomposition, and coordinate
error bounds. RH/MobiusCoefficientStabilization.lean proves the actual finite
projection expansion and uniqueness, unconditional coefficient stabilization,
the finite residual-correction formula, and equivalence of all Möbius target
limits with zero residual, zero limiting energy, target membership, and energy
convergence to zero. Stage n uses g_2,...,g_(n+1); all norms are the full Pareto norm.

**Conditional research reductions:** riemannHypothesis_of_limitCoefficients and
riemannHypothesis_of_coefficients_tendsto_mobius conclude Mathlib RH through
the existing actual Mellin bridge. **Open:** every stabilized coefficient equals
-mu(m), equivalently all Möbius coordinates of the actual limiting residual vanish.
riemannHypothesis_of_mobiusRiesz_mem supplies a second route. **Open:** every
finite-support Möbius Riesz vector for m>=2 belongs to the closed legal residue span.
Neither continuity, finite support, nor stabilization discharges these inputs.
See RH/RH_Coefficient_Lean_Integration_2026-09-19.md and the accompanying written proof.

### CRT–Pareto first-period reduction and exact coordinate legality (2026-09-18)

**Established:** RH/CRTFirstPeriodEnergy.lean proves that for every real
mean-zero sequence of positive integral period Q, the actual complete
conditional Cesaro energy lies between its first-period energy A_Q and
(9/8)*A_Q. The factor is independent of the conductor. The finite form
uses the actual signed cumulative defects; all mixed terms are retained.
The progression tail proof uses an elementary telescoping fourth-power
majorant. firstPeriod_subpolynomial_iff transfers growth for the same family.

**Established:** RH/CRTLegalCoordinates.lean proves the full exact-head
and zero-mean feasibility equivalence for normalized residue coefficients:
sum c_d/d=1, sum c_d=1, and low coefficients c_d=-mu(d). It also proves the
two exact high-range Mobius moments, low-prime divisibility of the support
conductor, and gcd-class compatibility of increments and defect second
differences.

**Established obstruction:** RH/CRTCoordinateLegality.lean gives a free
defect vector with first-period cost Y/(Y+2) and complete cost at most
(9/8)*Y/(Y+2), but proves it cannot be realized by a legal mean-zero witness
when Y>0 and Q>=Y+4. Legal reflection excludes this particular shortcut.

**Conditional research reductions:** riemannHypothesis_of_subpolynomial_firstPeriod
and riemannHypothesis_of_subpolynomial_residue_coordinates conclude Mathlib RH.
**Open:** construct legal coefficient families satisfying the explicit
moment/low-coefficient constraints with subpolynomial finite cost hcore/hcost.
Neither endpoint proves that input. See RH/CRTCoordinateReduction20260918.md.

### Strict improvement of all exact heads and conductor escape (2026-09-18)

**Established:** RH/ConditionalHeadStrictImprovement.lean extends the existing
mean-zero three-generator result to every finite legal nonempty exact head.
A nonzero period mean is detected by a late nonnegative pulse using the exact
bounded-period-defect formula. The actual unrestricted minimum is strictly
below every finite witness and is never attained by one.

**Established:** RH/ConditionalConductorStrictImprovement.lean proves every
finite inverse-matrix minimum has a strictly better larger conductor budget.
For each fixed old budget, a single new witness gives a positive additive
improvement over all feasible old-budget witnesses. Any minimizing family
must escape every fixed finite residue dictionary; its valid budgets tend
to infinity.

**Established limitation:** signed_gain_le_variational_excess bounds every
actual signed scalar gain by E(F)-conditionalHeadMinimum Y. Theorems
exists_head_with_all_signed_gains_small and
near_minimizer_signed_gains_tendsto_zero show that all directions have
simultaneously small gains at near-minimizers, including adaptively selected
directions. No positive additive gain floor can hold across all conductors.

**Open:** subpolynomial control of the unrestricted minima as the head length
grows. Strict improvement and conductor escape do not provide it. See
RH/StrictImprovementConductorEscape20260918.md for the exact argument,
formalization scope, and remaining RH obligation.

### Signed conditional projection and the dyadic-only obstruction (2026-09-18)

**Established:** RH/ConditionalMeanSignedProjection.lean defines the actual
infinite signed Cesaro pairing, proves summability and bilinearity, scalar
square completion, legal exact-head projection bounds, and the full signed
two-direction Schur gain. Covariance is retained in the screened source and
energy. Zero screened energy forces zero screened source; the optimum
identity includes that singular branch.

**Established:** RH/CRTDelayedProjection.lean proves
exists_delayed_pulse_projection: for every positive error allowance a
finite legal mean-zero pulse swap preserves the exact head and recovers
the entire one-direction projection gain up to that error. It also proves
the exact triadic dictionary identity and dyadic/triadic compatibility.

**Established:** RH/ConditionalSeedFactorObstruction.lean proves the
unconditional dyadic_pulse_head_linear_obstruction_eventually and
not_subpolynomial_dyadic_heads. A fixed nonreal conductor resonance on
Re(s)=1 annihilates the actual one-seed dyadic space and forces E(F) >= c*N
for sufficiently long exact heads, with a proved positive c. This applies
to witnesses entirely in that restricted space, not to the full legal
dictionary or an arbitrary affine family around a witness outside it.

**Conditional research reductions:** riemannHypothesis_of_signed_projection_subpolynomial
and riemannHypothesis_of_signed_schur_subpolynomial conclude mathlib RH.
Their actual signed cofinal remainder bound hbound remains **Open**.
No unconditional subpolynomial family or proof of RH is supplied.

**Established (delayed-gain continuation):** the same two modules now prove
conditionalMeanSquare_gain_eq_tail_difference and
conditionalMeanSquare_gain_le_original_tail: an arbitrary legal correction
preserving the head through M changes only the actual tail energy.
delayed_scalar_gain_le_original_tail bounds the exact signed scalar gain
by that tail. For period mean zero and actual defect bound B,
zeroMean_tail_energy_bound, delayed_correction_gain_bound, and
delayed_scalar_gain_bound give the explicit upper bound
2/(M+2) * (B/(M+1))^2. This is uniform over all delayed legal corrections
of a fixed witness, including combined finite directions. It is not
a bound uniform in growing head length: control of B remains unresolved.

**Established (three-generator strict improvement):**
RH/ThreeGeneratorStrictImprovement.lean proves
exists_threeGenerator_correlation_ne_zero and
exists_threeGenerator_strict_improvement: every finite legal zero-mean
exact head of positive length Y admits d > Y and an optimal correction
u*W_d, where W_d = 3*g_(2d) - g_d - 2*g_(4d), preserving its head and
zero period mean and strictly decreasing the actual infinite energy.
Nonzero correlation is proved, not assumed. Analysis/LatePulseDetection.lean
uses summable-multiples inversion and dyadic rigidity;
RH/ConditionalPulsePairing.lean proves the actual adjoint pairing,
second differences, and the first-moment/weighted-tail decay providers.
RH/ThreeGeneratorCorrection.lean proves the exact gain R_d^2/E(W_d)
and a corrected period Q*(4*d). No RH assumption is used.

**Written mathematics, not Lean-verified:** the explicit Dirichlet-inverse
coefficient formula and quantitative finite-scale detection estimates in
RH/UniformEnergyAttempt20260918.md remain informal. The qualitative
strict-improvement conclusion is now established as above. No uniform
gain or subpolynomial exact-head family has been proved; the RH-strength
energy bound remains **Open**.

Coverage and supplementary written arguments are in
RH/CRTProjectionContinuation20260918.md.


### Mean-zero infimum, cofinal growth, and conductor refinement (2026-09-18)

**Established:** RH/CRTMeanZeroInfimum.lean proves zeroMeanHeadMinimum_eq:
the actual mean-zero exact-head energy infimum equals the unrestricted
conditionalHeadMinimum. Period existence is discharged using the existing
legalSeedSpan_hasLegalReflectionPeriod theorem. The equivalence
subpolynomial_heads_zeroMean_iff preserves actual legal families along any
supplied cofinal sequence; it asserts no existence of a bounded family.

**Conditional research reduction:**
riemannHypothesis_of_positiveM_subpolynomial_heads concludes mathlib's
RiemannHypothesis from actual legal exact heads and a subpolynomial bound on
the concrete positive polygamma core. The domain-specific bound hcore remains
**Open**. No provider declaration for it is introduced.

**Established:** RH/CRTConductorRefinement.lean proves exact finite
refinements of both progressionL and progressionM under conductor multiplication.
The proof uses the actual residue-class reindexing of convergent arithmetic
series. Increasing the computational period does not itself improve energy.

### Exact positive quadratic CRT weight and delayed mean repair (2026-09-18)

**Established:** RH/CRTPositiveMExpansion.lean proves the exact finite expansion
of the actual progressionM weight with a strictly positive remainder, identifies
every term with actual polygamma derivatives, and bounds the remainder uniformly
in the conductor. The order-one positive core lies between E/2 and E. The
growing_zeroMean_positiveM_subpolynomial_iff theorem equates two growing-bound
obligations without asserting either.

**Established:** RH/CRTMeanRepair.lean constructs the legal pulse
H_A = 2 g_(2A) - g_A, proves its zero head, periodicity, mean 1/2, and conditional
energy at most 2/(A+1). The actual meanRepair is legal, preserves the head, and
has zero mean over an explicit common period. meanRepair_square_completion
retains the full second square and gives meanRepair_energy_le.
exists_zeroMean_head_near constructs a mean-zero periodic legal exact-head
witness with energy arbitrarily close from above to any supplied periodic legal
exact-head witness. meanPulse_difference_tailCorrection identifies the repair
inside the handoff's actual two-direction tail dictionary.

**Open:** an unconditional cofinal subpolynomial bound for the actual legal
exact-head energy, or a sufficient residual-specific signed Schur gain. None
of these declarations assumes or proves that arithmetic bound.

### CRT/coupled residual open declarations (2026-09-18)

Modules: `RH/CoupledResidualAnalyticTargets`,
`NumberTheory/GeneralizedCRTDescentTargets`.

**Open declarations, not providers:** `LaplaceFiniteOrder`,
`FarPeriodIntegralIdentity`, `FarPeriodGainLowerBound`,
`BurnolDistanceLowerEnvelope`, `FreshMoorePenroseFormula`,
`InverseHeadSpectralFormula`, `ReconstructionCostLimsupBarrier`, and
`LogarithmicGainBound` are collected by `CoupledResidualOpenPackage`.
The Moore--Penrose target retains the complete signed screened Gram matrix;
the limsup target treats zero gain as infinite reconstruction cost.

`IsTopologicalRingCRT` and `IsEffectiveDescent` record interfaces for the
profinite product CRT and higher-overlap descent claims. Their concrete
profinite and Amitsur-totalization instances remain open formalization work.
No declaration in this section is an axiom, and no RH conclusion is claimed.

### Weighted energy implies holomorphy and Hardy H2 (2026-09-18)

Modules: `Analysis/WeightedMellinEnergy`, `Analysis/WeightedMellinHardy`,
`RH/ChebyshevEnergyHardy`.

**Established:** `transform_integrable`, `transform_norm_sq_le`,
`transform_hasDerivAt`, and `transform_analyticAt` prove convergence,
the sharp Cauchy--Schwarz bound, differentiation, and holomorphy from
finite weighted energy on Re(z)>s/2. `vertical_memLp` proves actual
square integrability of each transformed line. `angular_plancherel`
gives (1/(2*pi))*integral |M_f(sigma+i*t)|^2 = E_(2*sigma)(f).
`energy_to_hardy` proves Hardy H2 membership; `hardy_energy_isLUB`
identifies its squared norm with E_s(f), using `energy_tendsto`.

**Conditional research reductions:** `errorMellin_analyticAt_of_energy`,
`errorMellin_hardy_of_energy`, and
`errorMellin_analyticAt_of_all_damping` specialize to the actual
Chebyshev error. Their actual weighted integrability hypotheses are **Open**.
**Boundary-trace addition:** `Analysis/WeightedMellinBoundary` proves
strong L2 convergence of finite-energy Mellin transforms to their unitary
Fourier boundary trace, along every interior sequence approaching s/2.
`transform_boundary_integral` gives convergence of actual squared-difference
integrals; `boundaryTrace_norm_sq` identifies the trace norm with energy.

**Restricted converse:** `Analysis/WeightedMellinConverse` proves
`finiteEnergy_iff_hardy_of_interior`, assuming finite energy at every
interior exponent. Fatou supplies endpoint finite energy.
`GeneralHardyConverse` precisely STATES the arbitrary-Hardy representation
obligation as an unproved Prop, not an axiom.
`hardy_boundary_of_general_converse` explicitly assumes that obligation.

The general Paley--Wiener converse and the signed-prefix/geometric-energy
transfer remain open formalization tasks. The RH-equivalent signed
arithmetic bound remains unproved.
See `RH/EnergyHardyFormalization20260918.md` and
`RH/HardyConverseBoundaryStatus20260918.md`.

### Chebyshev Mellin transform, local poles, and RH (2026-09-18)

Modules: `RH/ChebyshevMellin`, `Analysis/LogDerivZeroOrder`,
`RH/ChebyshevMellinRH`.

**Established:** `error_mellin_integrable` and `error_mellin_identity`
identify the actual integral of (psi(x)-x)*x^(-s-1) on (1,infinity) with
M(s)=-zeta'(s)/(s*zeta(s))-1/(s-1), for Re(s)>1.
`meromorphicAt_meromorphicError` extends this expression meromorphically
away from 1. `meromorphicError_order_at_zero` gives order -1 at every zeta
zero away from 0 and 1, without a simple-zero hypothesis.
`analyticAt_meromorphicError_iff` identifies analyticity with nonvanishing
there. `riemannHypothesis_iff_error_analytic` proves that Mathlib RH is
equivalent to analyticity of M throughout 1/2<Re(s)<1.
The reusable `AnalyticAt.meromorphicOrderAt_logDeriv_of_zero` proves the
finite-order local calculation for general analytic complex functions.

**Open formalization:** transfer from signed prime-power prefix energy to
Chebyshev error energy, the reference Z_b quotient, pole cancellation at 1,
and the precise residue coefficients. The forward analytic bridge is above.
**Open mathematics:** the actual all-positive-damping or subpolynomial
signed arithmetic bound. The RH equivalence above asserts neither side.
See `RH/MellinRHAnalyticLinks20260918.md`.

### Global prime-power enumeration and real cells (2026-09-18)

Module: `RH/PrimePowerEnumeration`.
The existing strict enumeration of the nonzero von Mangoldt support,
its initial value 2, and endpoint completeness have been reverified.

**Established without domain-specific hypotheses:**
- `primePowerEnumeration_existsUnique_iff`: a natural number occurs
  exactly once if and only if it is a prime power.
- `primePowerEnumeration_tendsto_atTop`: the enumeration tends to infinity.
- `primePowerEnumeration_existsUnique_cell`: every real x >= 2 lies
  in exactly one half-open cell [q_n,q_(n+1)).
- `vonMangoldt_eq_zero_between_enumerated`: the open interior contains
  no omitted nonzero coefficient.
- `enumerated_cumulative_eq_psi_on_cell`: the cumulative actual jumps
  equal Mathlib's Chebyshev psi throughout each half-open real cell.

This closes both the global enumeration obligation and the real
step-function identification obligation. It does not prove the external
sharp prime-gap estimates, the Mellin/RH links, or the signed energy bound.

### Actual prime-gap inputs and dyadic energy (2026-09-18)

Modules: `NumberTheory/PrimeGapProviders`, `Analysis/GapEnergySummability`.

**Established:** `sum_adjacent_gaps_le` bounds the total length of selected
disjoint consecutive intervals by clipping and telescoping.
For the actual zero-based prime enumeration, `next_prime_le_two_mul`
proves Bertrand's bound, `mem_dyadicIndices` proves that the finite shell
includes every relevant index, and `dyadic_gap_mass_le` proves total gap
mass at most 4X, including the final boundary-crossing gap.

**Conditional research reductions:** `dyadic_cubic_gap_le` removes the
external total-mass hypothesis in the actual-prime specialization.
`dyadic_cubic_gap_le_published_exponents` and
`dyadic_normalized_cubic_le` assemble maximal gaps C X^(21/40) and
exceptional mass D X^(16/25), at threshold X^(9/20), into the exact bound
4 X^(-1/10) + C^2 D X^(-31/100) after division by X^2.
`summable_dyadic_normalized_cubic_of_gap_bounds` proves dyadic
summability from those two explicit all-scale inputs.

**Open formalization:** the BHP maximal-gap provider and Jarviniemi
exceptional-gap provider are not proved. Absorbing their finite exceptional
ranges, global shell regrouping, and transfer to all prime-power cells are
not asserted in these declarations. See
`RH/PrimeGapProviderProgress20260918.md`.
**Open mathematics:** the actual signed arithmetic energy bound remains
unproved and is not supplied by the geometric gap results.

### Assertion (11.7): named RH-equivalence conjecture (2026-09-18)

Module: `RH/ConditionalSignedSchurConjecture`.

**Conjecture definitions, not theorems:** the existing
`ConditionalMeanGram.UniformSignedSchurTarget` is the exact assertion
(11.7), with one real K independent of Y, a finite conductor chosen for
each Y, the entire injectively parametrized head kernel, and two-sided
inverse identities. Here D counts columns 2,...,D+1.
`SignedSchurRHEquivalenceConjecture` records
`UniformSignedSchurTarget ↔ RiemannHypothesis` as a `Prop` only.

**Established finite transport:** `columnSynthesis_mem_legal`,
`cesaro_columnSynthesis`, `columnSynthesis_headClass`, and
`columnSynthesis_energy` connect the Fin D normalized matrix API to actual
legal functions, including the exact compulsory head and complete signed
tail energy.

**Conditional research reduction:**
`riemannHypothesis_of_uniformSignedSchurTarget` proves actual Mathlib RH
from (11.7), with no additional density, kernel, or inverse provider
hypothesis. The existential kernel and inverse conditions are part of
(11.7) itself. `bounded_headMinimum_of_finiteTailTarget` supplies the
intermediate uniform bound on actual legal minima.

**Remaining obligations:**
- **Open mathematics:** prove `UniformSignedSchurTarget` itself. This patch
  supplies no bound and no unconditional RH theorem.
- **Open formalization:** prove `RiemannHypothesis →
  UniformSignedSchurTarget`. The manuscript's converse uses classical
  RH-to-density, exact-head correction, and finite kernel-basis assembly.
  `signedSchurRHEquivalenceConjecture_iff_reverse` identifies precisely
  this remaining direction; it does not prove it.

No new axioms, placeholders, or assumed conjecture instances are added.

### Concrete Cesaro Gram and signed completion (2026-09-18)

Modules: `Analysis/FiniteSignedQuadratic`, `RH/ConditionalMeanGram`.
Actual infinite Gram entries are summable; head/tail splitting and the tail
sum-of-squares identity are proved. Exact signed Schur completion and the
attained affine minimum expose kernel-parametrization and inverse premises.
The uniform finite-tail and signed-Schur targets are defined; the implication
from the latter to the former proves neither bound.

Concurrent `RH/ConditionalFiniteMatrixMinimum` and
`RH/ConditionalNormalizedMatrixMinimum` already supply actual positivity,
head surjectivity and inverse minima in conductor-indexed coordinates.
They remain intact. `RH/ConditionalConductorExhaustion` proves (11.5):
`conditionalHeadMinimum_eq_iInf_fullValue` identifies the infimum over all
admissible budgets, and `tendsto_fullValue_conditionalHeadMinimum` proves
convergence along every budget N+1+k. Finite-support exhaustion and
`fullValue_antitone` are also proved, without an RH or bounded-energy premise.
The remaining finite integration work is coordinate transport/kernel-basis
assembly for the alternative Fin D signed-completion API.
See `RH/ConditionalMeanGramProgress20260918.md` for precise scope and the
historical verification/publication distinction. Assertion (11.7), or a
cofinal subpolynomial replacement, remains **Open mathematics**.

### Layer-cake, fixed-width discrepancy, and polynomial spline RH reductions (2026-09-18)

Full source: `RH/LayerCakeSublevelProgram20260918.md` (sections 1–40).
Precise coverage and provider ledger: `RH/LayerCakeLeanCoverage20260918.md`.
The archived ordinary analytic arguments are not all claimed kernel-verified.

Modules: `Analysis/CofinalQuadraticPositivity`,
`Analysis/DyadicHatRefinement`, `Analysis/HatIntegrability`,
`Analysis/HatMassIntegral`, `Analysis/FiniteKernelRefinement`,
`LinearAlgebra/SparseQuadraticEnergy`, `LinearAlgebra/SignedSchurResidual`,
`LinearAlgebra/IncreasingEnergyTolerance`, `RH/WeilPositiveDiagonal`,
`RH/FixedWidthWeilDiscrepancy`, `RH/PolynomialWeilCriterion`,
`RH/SplineWeilMatrixTargets`, `RH/PolynomialSplineRH`.

**Established:** cofinal vanishing-error positivity; actual hat refinement,
support, integrability and exact masses; complex sparse quadratic bounds;
complete signed Schur residual/inverse bounds and induction; increasing
natural-degree polynomial tolerance buffers; actual fixed-width correlation
support/diagonal, von Mangoldt cutoff equality and remainder sign; concrete
spline tests/matrices; and RH implies actual completed Weil positivity on
the already-supported smooth test class.

**Conditional research reductions:** actual Mathlib RH follows from the
fixed-width polynomial lower bound with `TwoHatWeilIdentity` and
`FixedWidthLandauDetection`. Their analytic proofs remain **Open** for
formalization. The spline/matrix consumer additionally requires
`QuantitativeTwoHatSplineApproximation` and, for literal matrix entries,
`SplineQuadraticRepresentation`; both remain **Open** for formalization.
`SplineEnergyAdmissibility`, `SplineWeilHermitian`, and the concrete uniform
entry/mass/refinement providers are tracked separately as **Open**, where not
discharged by the new elementary hat theorems.

**Open mathematical RH target:** a uniform polynomial lower bound on the
actual signed forms/matrices, or a sufficient uniform full signed Schur
certificate with a finite starting certificate. No such bound is proved.
No density-only, two-point-only, shrinking-width scalar, or unsigned bound
is substituted. No project-local axiom is added.


### Deterministic exact heads and residual amplification (2026-09-17)

Module: `RH/ParetoExactHeadResidual` (seven public theorems).

**Established:** a residual vanishing through coordinate N has its entire
Mellin transform and full energy in the tail beyond N+1. If zeta(s)=0,
Re(s)>1/2, and s!=1, every legal exact-head approximant f satisfies
||1-f||^2 >= (2 Re(s)-1)(N+1)^(2 Re(s)-1)/|s|^2. This is a residual
bound without the oscillating factor in the earlier bound on ||f||^2.
A strictly smaller complete error certificate excludes the indicated zero.

**Conditional research reduction:**
`riemannHypothesis_of_bounded_exact_head_residuals` concludes actual
Mathlib RH from a family legal at every N, exactly one on coordinates 1..N,
with one uniform bound on the actual full squared residual norm.
The uniform-bound provider remains **Open**. All assumptions occur in the
declaration type; no RH converse or arithmetic boundedness axiom is added.

The separate ordinary mathematical report
`RH_Deterministic_Exact_Head_Tail_Repair_2026-09-17.md` identifies the
known divergence of raw Mobius heads, derives their complete head-preserving
tail correction basis and signed Gram optimum, and records 15 rational
finite-witness certificates including infinite-tail bounds. Those arithmetic
basis proofs and Python integer certificates are not claimed as Lean-verified.
Random draws in this continuation: zero.

### Stochastic legal hitting and invariant Mellin obstructions (2026-09-17)

Module: `RH/ParetoStochasticHitting` (eight theorems).

**Established:** at any hypothetical zero s with Re(s)>1/2, every legal
residual has Mellin value 1/s. For any random sequence of a.e. legal
approximants, the lower squared-error bound (2 Re(s)-1)/|s|^2 holds
simultaneously at every time, at every finite random observation time,
and in expectation when that actual squared error is integrable.
The event of ever crossing a smaller error threshold has measure zero.
No independence, adaptedness, or extra moments are assumed in the
pathwise or hitting conclusions.

**Conditional research reduction:**
`riemannHypothesis_of_positive_legal_hitting` concludes actual mathlib RH
if every positive squared-error tolerance is ever reached with positive
measure. The required hitting property remains **Open**. The proof does
not assert that repeated sampling forces zero limiting error.

The separate ordinary mathematical continuation
`RH_Stochastic_Attack_and_Single_Atom_Obstruction_2026-09-17.md` proves
a finite-witness drift bound and a linear lower bound for the second moment
of single-atom random estimators fitting the first N coordinates. These
ordinary stochastic/Mobius arguments are not claimed as Lean-verified.

### Exhaustive Pareto packet walks and deterministic residuals (2026-09-17)

Modules: `Analysis/ExhaustiveProjectionWalk` and `RH/ParetoExhaustiveWalk`.
Twenty-five theorems formalize finite sampled spans, monotonicity, exhaustive
projection convergence, order-independent limiting squared error, exact
Pythagorean step gains, accumulated gain limits, and their actual legal
Pareto interpretation.

**Established:** every surjective sampling order has the same limiting
projection and error; every finite legal walk error is positive; vanishing
error is equivalent to nonsummability of the actual relative gains.
A hypothetical zero with Re(s)>1/2 gives the explicit error floor
(2 Re(s)-1)/|s|^2 at every step and at the deterministic limit.

**Conditional research reduction:**
`riemannHypothesis_of_legalWalk_nonsummable_gain` concludes actual mathlib
`RiemannHypothesis` with only the displayed actual-gain nonsummability
obligation; `riemannHypothesis_of_legalWalk_tendsto` needs no exhaustive
sampling assumption.

**Open:** proving that actual limiting legal error is zero, or proving
nonsummability of the actual gains. No uniform arithmetic gain estimate,
unconditional RH proof, or Lean RH-to-Nyman converse is asserted.

The separate research companion
`RH_Random_Walk_Nyman_Pareto_CRT_2026-09-17.md` proves an IID rank-one
random-correction convergence theorem in ordinary mathematics and combines
it with Baez-Duarte's classical full-dictionary criterion. That stochastic
trace proof and the classical reverse implication are not Lean-verified.
The numerical investigation consists of one 128-step PCG64 trajectory,
seed 20260917, with 27 distinct two-seed packets (numerical rank 22);
floating-point results are not formal numeric certificates.

### Approximate heads and regularized conditional energy (2026-09-17)

Source and precise scope: `RH/ApproximateHeadRegularization20260917.md`.
Fourteen theorems extend `Analysis/WeightedComplexPairing` and add
`RH/ConditionalMeanApproximateHeads` and `RH/ConditionalMeanRegularizedHeads`.

**Established:** a signed head-error/tail-energy tradeoff for the actual legal
witnesses; a support-independent positive regularized-cost obstruction at every
hypothetical right-half-plane zero; exact heads have zero truncated error; full
conditional-mean approximation implies the regularized feasibility property.

**Conditional research reductions:** vanishing weighted approximate-head error
and sparse subpolynomial full conditional energy imply mathlib RH. A sparse
O(N^alpha) bound confines nontrivial zeros to [(1-alpha)/2,(1+alpha)/2].
`ArbitrarilySmallRegularizedHeads A` also implies mathlib RH, with every
arithmetic feasibility requirement explicit in the theorem type.

**Open:** a provider for `ArbitrarilySmallRegularizedHeads` for the actual
positive or two-seed span, or an actual family satisfying the sparse growth and
head-error conditions. The existing canonical O(N) bound has not been improved.
No unconditional RH proof or RH-to-density equivalence is claimed.

### Conditional iid and Cesàro variational completion (2026-09-17)

Exact scope and verification evidence:
`RH/Conditional_IID_Cesaro_Lean_Continuation_2026-09-17.md`.
Ordinary mathematical proofs:
`RH/Conditional_IID_Cesaro_Proof_Companion_2026-09-17.md`, supplementing
`RH/Conditional_IID_Cesaro_Mathematical_Completion_2026-09-17.md`.

**Established:** the actual legal head infimum, bounded/cofinal-subpolynomial
energy implications to mathlib RH, the canonical Möbius O(N) upper bound,
strict tail nonattainment, and sharper signed tail Mellin obstructions.
Concrete raw and normalized residue Gram/tail matrices are positive definite;
finite head constraints have full rank and attained literal inverse-matrix minima.
The weighted Cesàro map is a bundled norm-one contraction with dense nonclosed
range, its actual adjoint and stochastic reversible kernel, and an exact kernel
closed form. All-H Mellin pairing and the complex-J functional are constructed;
normalized residue first series extend to Re(s)>0. The actual infinite-mixture
probability model has permutation invariance, simultaneous strong law and latent
recovery, exact divisibility laws, and deterministic sample-rate bounds. Every
real H vector has the required observation L² property. Randomized finite legal
coefficients satisfy exact full and smoothed expected-loss decompositions.
Previous exact finite correction obstructions and finite constraint closure remain.
The continuation adds 28 modules and extends `Analysis/MellinStepSeries`.

**Structural relocation (2026-10-11):** `RH/ParetoNormalizedResidueHilbert`
now owns `RiemannResearch.RH.Pareto.normalizedResidueHilbert` and
`RiemannResearch.RH.Pareto.normalizedResidueHilbert_sequence`.
`RiemannResearch.RH.Pareto.one_le_conditionalMellinDualSquare` now lives in
`RH/ConditionalMeanHeadObstruction`. All three names, statements, and declaration
bodies are unchanged. Arithmetic consumers import the Hilbert construction
directly; analytic consumers retain explicit Mellin imports. See
`RH/LakeDependencyAudit20261011.md` for the measured dependency changes and
verification scope. This relocation adds no mathematical assertion.

**Open mathematics:** the actual uniform/cofinal-subpolynomial signed energy bound.
**Open formalization:** the classical `PositiveResidueDensityFromRH` provider,
its converse/minimum-closure consumers, and the explicitly itemized stronger
appendix endpoints in the coverage report. The RH criterion is not advertised
as a fully checked equivalence. No custom axiom or unconditional RH proof is added.

### Coupled Pareto corrections: recovery and completion (2026-09-16)

Coverage and exact remaining obligations:
`RH/CoupledResidualCompletion20260916.md`.
Source: `RH/CoupledResidualCorrectionsSource20260916.md`.
Five previously unpublished modules are recovered, with eighteen new modules.

**Established:** `RH/CoupledResidualCorrections` retains the actual floor-indexed
dilation energies, signed correlations, normalized corrections and exact optimum.
`RH/FreshCoprimeDecomposition` proves the transported/fresh direct sum, exact
counts and dimensions. `RH/FreshCoprimeSchur.full_gain_eq_transport_add_fresh`
assembles the actual inverse-Gram remainder. `RH/PhysicalHeadResidualLift`
discharges physical-head solvability and proves the attained raw-tail minimum.
`RH/ParetoFiniteResidueCharge` constructs actual coefficients and proves charge
forcing with the linear moment ceiling. `RH/ActualResidualLaplace` proves the
actual finite Laplace formula, removable value and continuity.
`RH/DyadicResidualConstraints` proves finite source budgets and absolute/weighted
summability. `RH/TwoThreeSquareRelations` proves that all finite real two-seed
relations are generated by the independent commuting squares.
`RH/ParetoHaarComparison` proves the exact full-quotient energy loss and its bounds.
`RH/CoupledResidualChatCompletion.fresh_trace_lower` proves the actual fresh
inverse-Gram remainder is at least its squared-source sum divided by the screened
Gram trace. `decomposed_reconstruction_optimum` gives the exact normalized
transported-plus-fresh optimizer without discarding cross terms.

**Conditional:** `RH/LogarithmicCorrectionTarget` proves the cost/gain equivalence
and the implication from the named logarithmic target to mathlib's RH.
`Analysis/SharpLogarithmicResidualBarrier` and `RH/BurnolDyadicComparison`
prove the sharp cost-constant obstruction from the explicit distance envelope.

**Open mathematics:** `LogarithmicCostBound` and `LogarithmicGainBound`.
**Open formalization:** `RH/CoupledResidualAnalyticTargets` records the derivative
order, far-period integral/asymptotic gain, and actual Burnol comparison as
propositions without providers. The broader profinite and derived-descent claims
from the CRT discussion are not certified by these finite-space proofs.
No new axiom, proof placeholder, or unconditional RH theorem is introduced.

### Signed arithmetic bound: complete enumeration and unconditional range (2026-09-16)

Exact statements and remaining targets: `RH/SignedArithmeticBoundVerification20260916.md`.

**Established:** `RH/PrimePowerEnumeration` proves a complete increasing
prime-power enumeration starting at 2, its factor-two successor bound, and
`enumerated_cumulative_eq_psi`. The earlier global enumeration provider is
discharged. `Analysis/PowerCellEnergy` identifies the actual damped interval
weight with its integral. `RH/PrimePowerEnergyBounds` proves
`enumerated_critical_energy_le_linear`, `enumerated_damped_energy_le`, and
`enumerated_damped_energy_summable`: A_N <= (log 4+4)^2*(q_N-2), and the
s-damped energy is at most (log 4+4)^2*2^(2-s)/(s-2) for every s>2.
`actual_damped_signed_abel_identity` and `actual_damped_total_reset_cost`
retain the full signed form and the same canonical corrections.

**Open (mathematics):** the explicit propositions
`SignedArithmeticDampedBound` (every s>1) and
`SignedArithmeticSubpolynomialBound` (every positive growth exponent).
The verified baseline range s>2 does not prove these targets.
**Open (formalization):** the Mellin/RH equivalence, the global geometric
prime-gap providers, and the real step-function identification within cells.
No RH hypothesis, new axiom, or proof placeholder is introduced.

### Prime-power interval energy and boundary-reset continuation (2026-09-16)

Source and exact declarations: the continuation section of
`RH/VectorSpacesZetaFormalization20260916.md` (report Sections 11-19).

**Established:** `Analysis/ReciprocalCellEnergy` proves the actual x^-2
integral split, weighted mean, exact correction integral, and two-sided cubic
remainder bounds. `LinearAlgebra/FiniteCumulativeCellEnergy` now proves
`cumulative_resetJump`, `resetJump_tail_zero`,
`reset_correction_energy_exact`, and `weightedPrefixEnergy_signed_identity`.
`Analysis/CumulativeEnergySummability` proves the full infinite-sum reset
cost `reset_total_correction_energy_exact` and nonnegative-prefix
summability equivalence. `Analysis/GapEnergySummability` proves the cubic
short/large-gap split, explicit external-bound reduction, geometric
summability and its exact tail majorant.
`RH/PrimePowerCriticalEnergy` retains actual von Mangoldt coefficients:
`actualCumulative_eq_chebyshev` has an explicit support-completeness input;
`actual_interval_energy_split`, `actual_signed_abel_identity`, and
`actual_total_reset_cost` use actual prime-power-cell weights, not integer
Pareto weights.

**Conditional research reductions:** `cubic_gap_sum_le_of_external_bounds`
exposes the maximal-gap, total-mass and large-gap-mass hypotheses.
`actual_remainder_summable_of_external_cubic_gap` exposes
`externalPrimePowerCubicGapSummability`. The BHP/Jaerviniemi providers,
dyadic exponent combination, and prime-power transfer are **Open
(formalization)**. The multiplicative reference/Mellin continuation,
zero residues, energy threshold and RH-conditional asymptotic are also
**Open (formalization)**. The actual signed arithmetic bound remains
**Open (mathematics), RH-equivalent**. Neither RH nor uniform boundedness
of critical undamped arithmetic energy is proved.

### Prime-power vector spaces and zeta sampling (2026-09-16)

Scope and outstanding providers: `RH/VectorSpacesZetaFormalization20260916.md`.

**Established deductions and obstructions:**
`Analysis/SampledGaugeCompleteness` proves actual l2 coordinate recovery from
bounded diagonal filters, finite demodulation, and absence of a positive
uniform lower bound for the coordinate covariance. `Analysis/ZeroDivisorTopology`
proves finite-coordinate and translated density, tail convergence, exponential
zero-set preservation, and analytic zero-order preservation.
`Analysis/FinitePolynomialSampling` constructs finite null polynomials and
proves the exact sampling-density obstruction. `LinearAlgebra/FiniteCumulativeCellEnergy`
and `Analysis/IntegralCellEnergy` prove complete signed energy decomposition,
optimal cumulative corrections, actual integral identities, and exact boundary
correction cost. `RH/ZetaKernelObstruction` excludes the unchanged global
Hilbert zeta kernel using the actual value zeta(0)=-1/2.

**Conditional research reductions:**
`gaugeOrbit_dense_of_phase_limits` has an explicit phase-covariance limit input;
the actual zero-ordinate equidistribution provider is **Open (formalization)**.
`continued_eval_not_continuousWithinAt_zero` has an explicit arithmetic
continuation identity; its actual eta/Euler-series provider is **Open (formalization)**.
The global enumeration and power-weight moments are discharged in the later
signed arithmetic bound entry above; the remaining Chebyshev specialization is
**Open (formalization)**. The global
arithmetic energy bound is **Open (mathematics)**.
The Fock realization and full covariance asymptotics are not formalized here.
No RH proof, unproved provider declaration, or project-local axiom is added.


### Exact signed fixed-head Schur remainder (2026-09-16)

Source and precise scope: `RH/ExactSignedSchurFormalization20260916.md`.

- `RH/ParetoPointClosure`: actual point-target closure iff constant-target
  closure, by a contractive dyadic operator; no finite legal packet equals the
  point target; point-target approximation implies actual Mathlib RH.
- `LinearAlgebra/FiniteHilbertSchur`: full signed normal equations, inverse
  Gram gain, completion of the square, and old-space Gram residualization.
- `RH/ParetoSignedSchurRemainder`: actual remainder positivity, head preservation,
  legality, exact binary-seed value `log 2 - 1/2 - sum c_i inner(z_i, seed)`,
  coefficient-minimization identity, and line-projection distance `R/(1+2R)`.
  Actual decreasing remainder gains are nonsummable iff the remainders vanish.
  Nonsummable gains, or a positive harmonic lower bound, imply Mathlib RH for
  legal packets; positivity is proved rather than assumed in these consumers.
- `Analysis/ResidualHarmonicGain`: explicit harmonic residual bound and
  nonsummability comparison; reuses the existing exact gain-product criterion.
- `LinearAlgebra/OrthogonalFarSupportBound` and `SchurSubspaceGain`: full
  optimized correction-subspace gain is at most `norm(z)^2/(1-tau)`, under
  explicit support-pairing and old-space capture hypotheses.

**Not claimed:** the manuscript's one-edge finite dictionary is not identified
with the existing ordinary-budget family. Its finite-budget instantiation,
Fourier tail constants, periodic adjoint asymptotics, and uniform mean-zero
rate remain to be formalized. The actual arithmetic gain lower bound remains
open. No RH-to-density converse or project-local axiom is added.

### Failure of RH and subpolynomial complete energy (2026-09-12)

**Established implications:** `RH/ParetoL1MellinBound.lean` proves the
actual weighted L1/integral identity, head and complete-tail estimates,
and the explicit power lower bound
`mellinL1Constant s ≤ ‖e‖² * hilbertL1 e ^ mellinL1Exponent s`
from the actual Mellin value 1/s. The exponent is
(2 Re(s)-1)/(1-Re(s)); the constant is positive. The optimized clipping
constant in the companion analytic note is not asserted by this module.

`RH/RHFalseEnergyConsequences.lean` derives an actual right-half-strip
zero from failure of Mathlib's RH, supplies the legal error's Mellin value
from existing verified zeta identities, and proves that every finite legal
L1 approximating sequence has full energy tending to infinity if RH fails.
These are implications under the explicitly stated zero/RH-failure premise,
not assertions that an off-critical zero exists.

**Conditional research reduction:**
`riemannHypothesis_of_legal_subpower_l1` proves actual RH from finite
legal witnesses F_n with L1 error epsilon_n tending to zero and
epsilon_n^p * ‖F_n‖² tending to zero for every p>0.
**Open:** construction of actual finite legal witnesses satisfying both
limits jointly. The handoff's analytic L1-density construction has not been
formalized in these modules, and its energy rate remains unproved.
All signed and mixed contributions remain within the complete Hilbert norm.

### Finite optimizer and dyadic evaluation completion (2026-09-11)

**Established:** `RH/RamanujanMeanOptimizer.lean` supplies the actual inverse
coefficients and legal mean-one optimizer on each finite allowed conductor set
containing 2. The mass q satisfies 0<q<1; projection error is 1-q and minimum
mean-one variance is q⁻¹-1. Normal equations, inverse existence, and nonzero
normalization are derived. The full signed excess quadratic remains present.

`RH/ParetoFiniteErrorObstruction.lean` proves strictly positive error for
each finite legal packet and a positive error floor uniform over coefficients
on each fixed finite conductor set. This is not uniform across growing sets.

`Analysis/IndependentMeanOneObstruction.lean` proves finite-prefix
independence, exact mean-one least-squares minima, a uniform 1/2 error floor,
and convergence of the minima to 6/π² using Mathlib's Basel theorem.
`Analysis/DyadicMomentEvaluation.lean` proves the triangular/Vandermonde
factorization and finite dyadic polynomial-evaluation solvability for every K.

**Established finite-budget feasibility (14 September 2026):** `RH/ParetoDyadicMomentFeasibility.lean`
proves actual finite-integral synthesis and legal budget membership.
`everyBudgetFeasible_of_polynomial_and_realization` proves actual feasibility
at every budget 2^K from two explicit analytic providers:
`DyadicCoefficientPolynomialProvider` and `ContinuousParetoRealizationTarget`.
`ContinuousParetoRealizationTarget` is now discharged by
`RamanujanLaguerre.continuousParetoRealizationTarget` in
`RH/ParetoExponentialRealization.lean` (14 September 2026): all ordinary
moments are integrable, the zeroth moment is the exact Pareto mean, and the
continuous squared error equals the complete discrete error. These identities
are proved for every bounded sequence. `DyadicCoefficientPolynomialProvider`
is now discharged by `RamanujanLaguerre.dyadicCoefficientPolynomialProvider`
in `RH/ParetoDyadicCoefficientPolynomial.lean`: the actual coefficient matrix,
its lower triangularity, diagonal, and evaluation formula are all proved.
Both analytic providers and finite matrix invertibility are discharged.
`RamanujanLaguerre.everyBudgetFeasibleTarget` in the coefficient-polynomial
module now supplies `EveryBudgetFeasibleTarget` unconditionally: at every K,
an actual legal mean-one packet meets all K zero Laguerre constraints within
budget 2^K. A uniform full-error estimate is a separate open obligation.

`RH/ParetoDilationLogMoments.lean` now proves `ordinaryMoment_dilation`:
actual integer dilation translates the exponential lift and acts on every
integrable ordinary log moment by the exact finite binomial formula.
The zero-at-zero hypothesis accounts for the full translated boundary.

`RH/ParetoMomentOptimizer.lean` now supplies
`RamanujanLaguerre.everyBudgetOptimizerTarget : EveryBudgetOptimizerTarget`.
It embeds the exact finite budget in the genuine Hilbert space, represents
actual coefficient integrals as continuous linear observations, and constructs
a full-Pareto-error minimizer by finite-dimensional projection. No uniform
cost assumption is used; uniform cost as the budget grows remains open.

`RH/RamanujanOrdinaryMomentsProof.lean` supplies
`RamanujanLaguerre.ramanujanOrdinaryMomentsTarget` with no extra hypotheses.
Every actual packet has all ordinary moments integrable; the first nonzero
moment has order omega(d)-1 and equals (omega(d)-1)! times the product of
prime logarithms. The proof uses the exact prime-factor/dilation recurrence,
including repeated prime factors, rather than an unproved Mellin provider.
The same module now also supplies `ramanujanLaguerreCancellationTarget`:
actual Laguerre coefficients vanish below omega(d)-1, and the leading value
is (-1)^(omega(d)-1) times the product of prime logarithms. This closes the
previously conditional arithmetic cancellation target.

**Open research:** uniform moment cost, q→1, unconditional completeness/RH,
and absolute-value closure. Concrete Parseval providers and the
additional-moment constrained inverse formula remain formalization work.

### Legal sequences, Ramanujan coordinates, and bounded moment repair (2026-09-11)

**Established:** `RH/LegalMobiusConstraints.lean` formalizes actual finite
two-seed coefficient flow, its Möbius recovery, necessary coefficient limits,
and the exact omitted-five/nonnegative-coefficient error floor. The companion
`LegalMobiusHeadCorrection` retains the mean, head, norm cost, and complete
mixed-term identity of the mean correction.

`RH/IntegratedRamanujanBasis.lean` proves finite independence and exact equality
between the two-seed legal span and the span of integrated Ramanujan packets
whose conductors are divisible by 2 or 3. `IntegratedRamanujanGram` proves
strict positivity of the actual full finite Gram form. Finite independence or
positivity does not assert completeness or any uniform inverse bound.

`RH/ParetoGramMeanOptimizer.lean` proves the full projection error and
mean-one minimum formulas from actual Gram normal equations and nonzero
normalization, including the exact nonnegative excess quadratic.

`Analysis/BoundedMomentRepair.lean` proves bounded progressively matched dense
tests imply weak convergence and arbitrarily small finite convex mixtures.
`Analysis/BoundedMomentAverages.lean` proves extraction of a strictly increasing
subsequence with the complete equal-average bound B/m+4/m². The exact finite
Gram identity keeps all signed mixed terms.

`Analysis/LaguerreMomentTransform.lean` proves the finite triangular transform,
its injectivity, correction identities and the actual Bochner-integral bridge
under explicit integrability and ordinary-moment hypotheses.

**Conditional research reductions:** `RH/ParetoMomentRepair.lean` transfers
bounded matched dense tests to actual finite legal mean-one approximation and
RH. The dense actual tests, matching, and uniform actual norm bound are inputs.
`RH/ParetoLegalCompleteness.lean` connects the actual sequence annihilator to
Hilbert completeness and RH conditional on signed uniqueness or absolute-value
closure. `RamanujanLaguerreResearchTargets` gives actual exponential-Pareto
integral definitions and proves arithmetic ordinary moments imply the stated
Laguerre cancellation, conditional on the ordinary-moment provider.

**Open:** uniform variance bounds, unconditional legal completeness, and
absolute-value closure. **Formalization still pending:** concrete Laguerre
realization/Parseval, Mellin-derived arithmetic moments, dyadic finite
feasibility/optimizer inverse formulas and displayed special-function
specializations. `RH/WholePageCoverage20260911.md` records precise coverage and
retains both original source notes. Numerical tables are not certificates.

### Positivity, indicators, and signed annihilator uniqueness (2026-09-11)

**Established:** `RH/ParetoAnnihilatorPositivity.lean` defines
`LegalAnnihilator` using the actual Pareto weighted square summability and
orthogonality to `legalSeedSpan A`. Weighted square summability implies
summability against every bounded test. For any seed set containing 2,
`legalAnnihilator_nonnegative_eq_zero` proves that every nonnegative
annihilator vanishes at every positive index. The indicator corollary excludes
all positive members of its support. Index zero has weight zero and is not
detected by the pairing.

`Analysis/IndicatorAnnihilator.lean` proves the two-point counterexample:
every mean-zero indicator is empty, but the nonzero signed function (1,-1)
has mean zero. Its absolute value has mean one and its positive-level-set
indicator has mean 1/2. Thus indicator uniqueness alone does not imply signed
uniqueness, and orthogonality alone does not supply the level-set preservation
that an attempted monotone-convergence reduction would need.

**Conditional research reduction:**
`legalAnnihilator_eq_zero_of_abs_closed` gives full signed uniqueness on
positive indices if the legal annihilator is closed under pointwise absolute
value. `legalAnnihilator_anchored_eq_zero_of_abs_closed` gives function
equality to zero with the additional anchor h(0)=0.

**Open:** absolute-value closure for the actual legal annihilator. No provider
for this hypothesis, legal approximation sequence, or proof of RH is supplied.

### Reflection-pair total variance and the actual Jordan objective (2026-09-11)

This continuation adds **86 public theorems across nine modules**.

**Established:** finite conditional variance identities; the actual progression
bounds Q^-2 <= W_Q(r) and upper-half W_Q(r) <= pi^2/(2 Q^2); the complete
Pareto identity Var = J + T; and the uniform comparison
Var <= J + (pi^2/Q) U <= (1+pi^2) Var. An explicit CRT bijection proves the
actual uniform residue covariance (gcd(L,K)^2-1)/12 on every common period.
The genuine Mobius-defined Jordan weights are positive and diagonalize the
actual uniform variance of signed legal packets. Full Pareto normalization is
recorded as sum c_i log(a_i) = sum Lambda(d) H_d, preserving all mixed terms
and all positive integer dilations. The final arithmetic endpoint is
divisorLegalPacket_variance_jordan_comparison.

**Conditional research reduction:** vanishing reflection calibration and
U_Q/Q along legal mean-one packets imply actual RH via the existing proved
Pareto/Mellin bridge. Equivalence of the variance and surrogate zero-limit
criteria is proved. For fixed witnesses, disappearing conditional noise
passes the unchanged variance into calibration.

**Open:** the required legal packet sequence and its two convergence
providers. Neither conditional averaging nor period enlargement supplies
that approximation. See RH/ParetoReflectionVarianceVerification20260911.md
for all modules, precise conventions, theorem names, and audit evidence.
The coherent 86-theorem audit succeeded; ten decisive axiom checks use only
propext, Classical.choice, and Quot.sound.

### Legal family structure and exact CRT-weight calculus (2026-09-11)

This continuation adds **68 public theorems across nine modules**.

**Established:** `RH/ParetoLegalStructure.lean` (15) proves common periods,
reflection at every multiple, actual positive zeros, exclusion of the constant,
and nonclosure under pointwise multiplication. It also proves that a legal real
function has a legal square exactly when its range lies in `{0,c}` for some c.
`RH/ParetoLegalAffine.lean` (3) records the actual mean linear map and the
mean-one affine family. `RH/ParetoGeneratedAlgebra.lean` (14) constructs finite
nonunital OR polynomials, proves their full Pareto error tends to zero, and
proves they are outside every positive-seed legal span for K >= 2.

`RH/ParetoProgressionCalculus.lean` (10) proves convergent reciprocal differences,
signed sum interchange, full periodic error, strict decrease, and small-modulus
values. `RH/ParetoProgressionTaylor.lean` (10) proves the exact-head Basel bound
and signed expansions through fourth order, with explicit fifth-order error.
`RH/ParetoProgressionMidpoint.lean` (3) proves the uniform positive error bound
pi^4/(360 Q^4). `RH/ParetoProgressionDigamma.lean` (8) proves the actual digamma
formulas, full-positive series, strict increase and strict concavity.
`RH/ParetoDigammaDerivative.lean` (3) identifies the midpoint series with the
actual digamma derivative. `RH/ParetoProgressionIntegral.lean` (2) proves both
exact integral representations. The zero residue class r=Q is retained.

All 68 theorems passed the coherent source audit. The thirteen decisive axiom
checks use only propext, Classical.choice, and Quot.sound. No RH or unresolved
analytic-provider hypothesis is present. Existing normalization, refinement,
dilation-invariance and periodic-regrouping results are reused.

**Open:** full approximation within the permitted linear span and RH. The
algebra-generated approximation cannot replace that constraint. The optional
finite Gauss/cotangent rearrangement and modulus-3 evaluations are not separately
formalized here. See `RH/ParetoFamilyWeightStatus20260911.md` for exact scope,
theorem names, conventions and audit evidence.

### Convex repair of the actual normalization remainder (2026-09-11)

This continuation adds **17 public theorems across four modules**.

**Established:** `RH/DyadicSignedDampingPackets.lean` (8 theorems) proves
summability and the exact signed mixed-damping Gram identity, finite-mixture
coordinates, and complete boundary/Fourier norm identities for arbitrary real
weights and positive used dampings. Every mixed damping and frequency term
is retained. `Analysis/HilbertBasisWeakLimit.lean` (1) proves the standard
bounded-coordinate-to-pairing limit theorem.
`Analysis/WeakConvexRepair.lean` (3) implements Riesz representation and the
standard weak/convex-closure argument for arbitrary nontrivial filters.

**Conditional research reduction:** `RH/DyadicRemainderConvexRepair.lean`
(5 theorems) proves weak convergence of the actual remainder from coordinate
decay and an eventual norm bound. In particular, the two existing named
hypotheses `DyadicUniformSignedFourierMultiplierSqrtBound` and
`DyadicNormalizationRemainderUniformEnergyBound` imply that every interval
`0 < epsilon < delta` contains a finite convex mixture of actual remainders
with norm below any `eta > 0`. An explicit finite-weight theorem has
nonnegative weights summing to one and complete signed Fourier energy
below `eta^2`. Individual boundary-tail tightness is not needed for mixtures.

**Open:** both displayed analytic providers; unconditional coordinate and
weak limits; a rate or arithmetic algorithm selecting the mixtures;
centered-comparison control; full physical/legal recovery; and RH.
The mixture conclusion is not decay of individual remainder norms and does
not by itself approximate the constant. See
`RH/FourierConvexRepairStatus20260911.md` for exact scope and audit evidence.

### Zero-damping modes and exact tail criteria (2026-09-11 continuation)

This continuation adds **27 public theorems across five modules**.

**Established:** `RH/DyadicFourierZeroDamping.lean` proves that the original
normalization tends to one and every fixed nonzero signed zeta factor,
complete Abel multiplier, Fourier term, finite packet, and finite
boundary/frequency energy tends to zero as positive damping vanishes.
Zeta nonvanishing on real part one is supplied by Mathlib; no RH hypothesis
is present. `RH/DyadicFourierFrequencyDomination.lean` proves the actual
half-order coefficient moment `sum norm(c_i(h))*abs(h)^(1/2) < infinity`.
`RH/DyadicSignedFrequencyTailCriterion.lean` gives an exact signed
frequency-tail criterion for the full row limit.
`Analysis/NonnegativeSeriesTightness.lean` and
`RH/DyadicSignedBoundaryTightness.lean` supply the exact complete
finite-head/infinite-tail norm decomposition and tail convergence criteria.

**Conditional research reductions:** a provider of
`DyadicUniformSignedFourierMultiplierSqrtBound` would discharge a summable
frequency majorant and the actual boundary-coordinate limits. Given those
limits, actual remainder energy tends to zero iff the complete boundary
tails are asymptotically tight. If actual energy stays above `c > 0`,
coordinate decay forces at least `c/2` outside every fixed boundary set.

**Open:** the uniform square-root multiplier provider, unconditional actual
coordinate limits, boundary-tail tightness, both original uniform-energy
targets, complementary physical/legal recovery, and RH. Tail tightness
with coordinate decay implies the stronger zero-energy limit; it is not
inferred from bounded energy. Every signed Fourier mixed term is retained.
See `RH/FourierZeroDampingStatus20260911.md` for the precise scope.

### Full signed arithmetic Fourier bridge (2026-09-11 continuation)

This continuation adds **40 public theorems in six new modules**.
`dyadicSignedFourierBridge_proved : DyadicSignedFourierBridge` is now an
**established result for every positive damping**. There is no RH, Mertens,
Fourier-bridge, or uniform-energy premise.

**Established:** `RH/DyadicResidueConductorBounds.lean` (7) proves exact reset
harmonic reindexing, the retained signed Abel tail, the bound
`norm D_a(K,h) <= 5 + 2 log a + 2 log(1+abs(omega_h))`, and the actual
inverse-cutoff error `a*(3+abs(omega_h))/(K+1)`.
`RH/DyadicDampedConductorFourier.lean` (6) proves logarithmically weighted
actual Mobius summability and absolute conductor/frequency interchange.
`RH/DyadicResidueFourierCocycle.lean` (10) proves the exact all-frequency identity
`S_(a*b)-S_a = phase(a)*S_b`, its conductor-independent norm, the actual
dilated-residue Fourier rows, and infinite signed packet extraction.
`RH/DampedMobiusFourierSymbol.lean` (6) supplies genuine Mobius Dirichlet
HasSum providers, complex phases and the nonzero residue-symbol zeta identity.
`RH/DyadicRegularizationPhaseKernel.lean` (6) evaluates the actual
Mobius/triadic product kernel, proves absolute coefficient summability, and
retains the exact original real normalization at frequency zero.
`RH/DyadicArithmeticFourierBridge.lean` (5) assembles the actual arithmetic
family, removes its zero mode exactly, discharges the full signed Fourier
bridge, and proves the unconditional complete signed norm identity.

The key actual-family interchange first uses the signed cocycle:
successive triadic conductors have symbol difference of norm exactly
`norm S_3(h)`. The existing projected Hilbert-valued convergence is used.
No unprojected infinite Hilbert series or quantitative Mertens input is assumed.

**Still Open:** `DyadicUniformSignedFourierEnergyBound` and
`DyadicNormalizationRemainderUniformEnergyBound`. They are now unconditionally
equivalent, but neither is proved. Actual zero-damping coordinate limits,
complementary physical/legal two-seed recovery, and RH remain Open.
The quantitative Mertens and hyperbola/tail providers remain Open on that
separate route; they are not needed for the Fourier bridge.
Every frequency cross term remains inside the complete squared modulus.
See `RH/FourierSignedBridgeStatus20260911.md` for proof scope and verification.

### Unconditional fixed-conductor residue Fourier bridge (2026-09-11 continuation)

This continuation adds **29 public theorems in three new modules and one extended
module**. Both analytic inputs isolated by the preceding residue cutoff reduction
are now discharged. The specialized endpoint
`dyadicBoundaryCoordinate_residue_hasSum_fourier` has only the positive-conductor
hypothesis and is an **established result**, not a conditional research reduction.

**Established:** `Analysis/HarmonicFourierVariation.lean` (5 theorems) proves
unitary exponential and harmonic-weight variation estimates, exact reciprocal-tail
telescoping, and the harmonic/variation cutoff split.
`RH/DyadicResidueFourierKernel.lean` gains 5 phase, norm, terminal and exact-tail
lemmas. `RH/DyadicResidueFourierBounds.lean` (8) proves the unconditional bound
`norm D_a(K,h) <= 4a + 2a log(1+abs(omega_h))`, hence the required logarithmic
frequency majorant, and absolute convergence of the modular Abel differences.
`RH/DyadicResidueFourierBridge.lean` (11) proves the exact finite Mellin identity,
the nonzero zeta limit through the continuous Pareto Mellin functional, convergence
at every frequency including the separate zero mode, the actual Fourier HasSum,
and the exact absolutely convergent modular-series representation of the symbol.
It also proves the cutoff error squared bound
`norm(D_a(K,h)-symbol_a(h))^2 <= norm(1-I*omega_h)^2*(a-1)^2/(K+1)`.

No RH, Mertens, Fourier-bridge, or uniform signed-energy hypothesis occurs in
these providers. Ordered physical jump convergence remains `Tendsto`; the
`HasSum` over physical indices concerns Abel differences, and the Fourier
`HasSum` is over frequencies.

**Historical remaining obligations (updated above):** passage through the actual damped Mobius/conductor family; the
full signed arithmetic-family zeta-ratio bridge; the quantitative Mertens provider
and hyperbola/reciprocal-tail consequences; uniform complete signed boundary and
normalization-remainder energies; actual arithmetic coordinate limits and the
complementary physical/legal two-seed recovery; RH. The present majorant is linear
in the conductor and does not itself provide every positive-damping interchange.
A useful next bounded target is a logarithmic-in-conductor bound retaining the
exact reset cancellation, followed by the actual damped-family interchange.
See `RH/FourierResidueBridgeStatus20260911.md` for proof scope and verification.

### Signed infinite packets, actual comparison, and residue Fourier cutoffs (2026-09-11)

This continuation adds **30 public theorems and four definitions in four modules**.
The actual triadic comparison component of the signed Fourier bridge is now established
for every positive damping, with its binary-residue mean and nonzero-frequency sign
proved exactly. The arithmetic-family zeta-ratio expansion remains Open.

**Established:** `RH/DyadicTentFourierPackets.lean` (7 theorems) proves signed infinite
packet extraction under absolute weight summability, with a proved phase-kernel
majorant. `RH/DyadicTriadicFourierComparison.lean` (11) supplies the actual geometric
orbit and comparison Fourier series. `RH/DyadicTentLogMajorant.lean` (3) proves
absolute summability of the actual Mellin row weighted by 1+log(2+|h|).
`RH/DyadicResidueFourierKernel.lean` (9, four definitions) gives the exact signed
residue reset kernel, modular Abel identity, retained endpoint, zero-mode limit log a,
and independent physical-coordinate convergence.

**Conditional research reductions:** the dominated signed-packet extraction;
`dyadicSignedFourierBridge_of_regularizedFamily_hasSum` (actual arithmetic-family
Fourier expansion remains a hypothesis). The original conditional residue extraction
`dyadicBoundaryCoordinate_residue_hasSum_fourier_of_logarithmic_kernel` now has proved
providers for both inputs and the unconditional specialization recorded above.

**Now discharged:** the two fixed-conductor kernel obligations from this continuation.
**Historical remaining obligations (updated above):** the full signed arithmetic Fourier
bridge; quantitative Mertens and hyperbola/tail estimates; uniform complete signed
boundary energy; actual arithmetic coordinate limits and complementary physical/legal
two-seed recovery; RH. No frequency-diagonal bound replaces the signed norm.
See `RH/FourierArithmeticContinuationStatus20260911.md` for exact scope and resumption.

### Actual tent Fourier reconstruction and signed finite packets (2026-09-10 continuation)

This continuation adds **60 public theorems in five new modules**. The actual compact logarithmic tent now has an unconditional Fourier-to-Mellin identity and a continuous, summable periodization with an actual Fourier `HasSum`. Its physical extension agrees with every positive-integer dyadic boundary coordinate, including all zero gaps and negative-depth atomic cancellation. Every finite signed packet has an exact Fourier `HasSum` expansion.

**Established:** `RH/DyadicTentFourierReconstruction.lean` (19 public theorems), `RH/DyadicTentFourierSamples.lean` (20), `RH/DyadicTentCoordinateEnergy.lean` (4), `Analysis/PositiveArithmeticPrefix.lean` (5), and `RH/DyadicArithmeticAbelReduction.lean` (12). In addition to reconstruction, these prove frequency-column square summability, exact signed discrepancy centering with endpoint error at most one, and damping-uniform transfer of ordinary Mertens prefix bounds.

**Still Open:** the full infinite signed zeta-ratio/residue Fourier bridge and its cutoff domination; quantitative Mertens and hyperbola/tail estimates; uniform complete signed boundary energy; actual arithmetic coordinate limits; complementary physical-energy/legal two-seed recovery; RH. Neither coefficient-column square summability nor the finite signed packet identity supplies these limiting estimates.

The completed reconstruction discharges the periodization/integer-sample stage of the earlier Fourier ledger. The exact module map, theorem endpoints, scope, and next bounded target are in `RH/FourierTentContinuationStatus20260910.md`. All ten audited endpoints use only standard Lean foundations; substantive assumptions are assessed separately from axiom lists.


### Fourier/Mellin and signed arithmetic energy formalization (2026-09-10)

This continuation adds **78 public theorems in 15 modules**. Full source checking succeeded before publication. This is a partial formalization of the ordinary FourierBridgeUniformSignedEnergy20260910.md proof: the unconditional final Fourier bridge and uniform boundary-energy theorem are still Open as Lean providers.

**Established providers:** the exact complex root-tent Mellin integral; actual inverse-square Mellin coefficient bounds and full row absolute summability; the binary zero-frequency identification; exact integer negative-depth atomic cancellation; the actual Möbius divisor/Euler-product identity and epsilon-log bound; elementary actual normalization bounds; and unconditional full weighted coefficient energy O(epsilon^2).

**Checked conditional deductions:** dominated scalar Fourier extraction from actual approximants; infinite mean/comparison cancellation; complete signed Fourier-to-boundary norm transfer; Banach-valued Abel convergence and uniform norm assembly from logarithmic integer-conductor growth; and full continuous-dual weak convergence from uniform boundedness and actual mean/boundary limits. All substantive hypotheses remain visible in the exact theorem types.

**Open providers:** ClassicalQuantitativeMertensBound; the uniform signed hyperbola/discrepancy consequence; actual periodization and signed residue/zeta Fourier identification; compensated large-depth shell estimates and pole/constant identification; DyadicSignedFourierBridge; DyadicUniformSignedFourierEnergyBound. The actual boundary-energy theorem must not be inferred merely from the checked coefficient energy or from the axiom list of a conditional theorem.

The concrete targets and their conditional equivalence are in RH/DyadicFourierAnalyticTargets.lean. The complete 15-module map, 78-theorem counts, precise arithmetic hypotheses, and remaining proof stages are in RH/FourierBridgeFormalizationStatus20260910.md. RH/FourierBridgeUniformSignedEnergy20260910.md preserves the ordinary argument, explicitly distinguished from this formal status. The complementary physical-energy/legal recovery and RH remain separate and unproved.


### Binary residue logarithmic mean and real tent integral (2026-09-10)

This continuation adds **20 public theorems** across three new modules and the existing terminal-octave module. The actual binary residue boundary coefficient is now identified unconditionally with the logarithmic second difference of x log x and the weighted real root-tent integral. No Fourier expansion or uniform arithmetic energy estimate is assumed.

| Status | Module and endpoints | Precise checked scope |
| --- | --- | --- |
| Established | `Analysis/ScaledHarmonicBlock.lean` (3): `scaledHarmonicBlock_eq_harmonic`, `harmonic_scaled_difference_tendsto`, `scaledHarmonicBlock_tendsto` | Exact finite harmonic blocks and their logarithmic limits at positive integer scales. |
| Established | `Analysis/LogarithmicTentIntegral.lean` (10): `continuous_rootTent`, affine/support endpoints, `rootTent_div_intervalIntegrable`, `integral_rootTent_div` | The continuous real tent max(0,1-abs(x-(a+1))) has an exact weighted integral for a>0, retaining both affine pieces. |
| Established | `RH/DyadicResidueTerminalOctave.lean` (1 new): `hilbertResidue_two_terminalOctave_tendsto` | The actual surviving binary octave tends to the actual residue coefficient at every boundary index. |
| Established | `RH/DyadicResidueBinaryLogMean.lean` (6): gap/refinement endpoints, `dyadicResidueTwoTerminalOctave_eq_harmonic_blocks`, `dyadicBoundaryCoordinate_residue_two_eq_log`, `dyadicResidueTwoTerminalOctave_log_full_error_le`, `dyadicBoundaryCoordinate_residue_two_eq_tent_integral` | With q=2(i+1), r_2(i)=q log q-2(q+1)log(q+1)+(q+2)log(q+2)=integral_q^(q+2) rootTent(q,x) dx/x. The complete one-quarter square error of the terminal octave against this explicit target is at most 1/(2N+1). |

The final combined source and seven-endpoint exact-type/axiom audit `job_K8-SFDIs1G4NMB48xzzlv3aHQDpeWuDi` succeeded: verified true, exit 0, 4.570 seconds, no warnings. Audited source SHA-256: `75aae40c91b0a7a7ec76eafa345538b8ab7fa5bbad386999eb3fed19221c7fb7`. Every audited endpoint uses only propext, Classical.choice, and Quot.sound. Separate-module validation and publication follow through the checkpoint.

**Open:** construction and integer identification of the full continuous log-periodic extension; Fourier coefficients and scalar signed residue/Fourier interchange; zeta multiplier identification; the complete signed arithmetic energy bound uniform as damping vanishes; full legal two-seed recovery and complementary energy; RH. The binary mean and its weighted root-tent integral are no longer open.

`RH/DyadicCoordinateFourierReview20260910.md` is an explicitly unverified ordinary-mathematics review of the next scalar Fourier route. Its x=4/3 example explains why coordinatewise continuous tents need not form an l2-valued function; none of its new Fourier or non-l2 claims is used as a Lean provider.


### Exact boundary tents, signed step approximation, and terminal octave (2026-09-10)

This continuation adds **28 public theorems**: 27 across six new modules and one in `RH/DyadicBoundaryUniformCriterion.lean`. It establishes quantitative convergence of the entire boundary error at each fixed conductor. It does not prove uniform arithmetic energy control as the conductor and inverse damping grow.

| Status | Module and endpoints | Precise checked scope |
| --- | --- | --- |
| Established local declaration | `Analysis/DyadicSequenceInterpolation.lean`: `dyadicSequence_exact_interpolation`; `RH/DyadicBoundaryTents.lean`: `dyadicBoundaryCoordinate_step_interpolation`, `dyadicBoundaryCoordinate_step_tent_rising`, `dyadicBoundaryCoordinate_step_tent_falling` | Actual integer boundary coefficients have exact affine tent pieces at every dyadic subdivision. The real log-periodic extension and Fourier expansion are separate. |
| Established local declaration | `RH/ThresholdStepTruncation.lean`: `hilbertStepJumpPrefix_sequence`, `hilbertStepJumpPrefix_error_sq`, `hilbertStepJumpPrefix_error_sq_le`, `hilbertStepJumpPrefix_tendsto_of_bounded` | A finite signed jump prefix equals f(min(n,K)); its full weighted tail error is exact. Bounded physical sequences converge in the actual Hilbert norm. |
| Established local declaration | `RH/DyadicResidueStepApproximation.lean`: `natResidue_cast_jump`, `hilbertResidue_stepJumpPrefix_signed_boundary`, `hilbertResidue_stepJumpPrefix_error_sq_le`, `hilbertResidue_stepJumpPrefix_tendsto`, `hilbertResidue_stepJumpPrefix_boundary_error_le` | The actual residue jumps retain negative resets. Both physical squared error and the full one-quarter boundary square sum are bounded by (a-1)^2/(K+1), with a>0 and no arithmetic bound assumed. |
| Established local declaration | `RH/DyadicBoundaryUniformCriterion.lean`: `dyadicBoundaryCoordinate_square_tsum_le_norm_sq` | The full canonical boundary square sum is bounded by the physical norm squared for every vector. |
| Established local declaration | `RH/DyadicResidueTerminalOctave.lean`: `hilbertResidue_two_stepJumpPrefix_boundary_eq_octave`, `hilbertResidue_two_terminalOctave_full_boundary_error_le` | At cutoff 2N, the binary-residue boundary prefix is exactly the surviving octave sum from N+1 to 2N. Its complete boundary error is at most 1/(2N+1). No divergent sums are separated. |
| Established algebraic declarations | `Analysis/AbelCancellationMultiplier.lean`: `abel_norm_sq_identity`, `abelCancellationMultiplier_norm_le_sharp`, `abelCancellationMultiplier_norm_neg_one`, `abelCancellationMultiplier_finite_mean_cancellation` | For unit z and 0<=q<1 the complete multiplier (1-z)/(1-qz) has sharp bound 2/(1+q), attained at z=-1. Finite mean cancellation keeps every coefficient and the comparison term. No actual Fourier identification or removal of Gram cross terms is asserted. |

Combined final source check `job_2t4PrqwSDACkz3BLIU7Bpjja-yEFhpRy` succeeded: verified true, exit 0, 5.291 seconds. The source contains no placeholder proofs or added axioms. The nine-endpoint exact-type/axiom audit `job_6pKF_yDs20VmZpssK5jwNaKqTEjKTzW_` also succeeded (verified true, exit 0, 4.640 seconds), with only propext, Classical.choice, and Quot.sound; audited source SHA-256 `6fc4a1d35c922c2ed8822e8f048f77c0a27b01081058811970b8b79b1a602f1c`. Separate module validation and publication use the final checkpoint.

**Open:** full real log-periodic/Fourier identification and justified residue/Fourier limits; the actual complete signed arithmetic square-sum bound uniform in vanishing damping; the stronger O(epsilon) energy estimate; arithmetic vector/Mellin/separating limits; full legal two-seed recovery and complementary energy; separate N5 identification; RH. The fixed-conductor rate above is not a provider for the uniform arithmetic estimate.


### Actual signed boundary coefficients, residue blocks, and full Abel regrouping (2026-09-10)

This continuation adds 34 public theorems across six new RH modules. It discharges the handoff's exact-coefficient derivation and proves a complete conductor Abel representation at positive damping. The uniform arithmetic square-sum estimate is still Open.

| Status | Module and endpoints | Precise checked scope |
| --- | --- | --- |
| Established local declaration | `RH/DyadicRegularizedBoundaryCoefficients.lean`: `dyadicRegularizedFamily_boundaryCoordinate`, `dyadicNormalizationRemainder_boundaryCoordinate` | Actual full-H coefficients equal explicit signed Mobius/residue-difference series, including the complete comparison and Abel step terms. Positive damping supplies absolute convergence. |
| Established local declaration | `RH/DyadicArithmeticBoundaryBlocks.lean`: `dyadicBoundaryCoordinate_residue_eq_blocks`, `dyadicResidueBoundaryBlock_abs_summable` | Every projected residue coefficient is an absolutely convergent sum of exact adjacent weighted arithmetic blocks. Both blocks and all residues are retained. The nested formula is not flattened into an unjustified unrestricted triple sum. |
| Established local declaration | `RH/DyadicProjectedResidueAbel.lean`: `dyadicProjectedTriadicColumn_tsum_eq` | At fixed n>0 and epsilon>0, the complete projected triadic column equals -Q R_n plus (1-q) times the remaining full projected residue orbit. Actual Hilbert summability justifies the identity. |
| Established local declaration | `RH/DyadicRegularizedResidueAbel.lean`: `dyadicRegularizedResidueAbelTerm_norm_summable`, `dyadicRegularizedFamily_eq_residueAbel` | The complete Mobius sum of entire signed Abel brackets is norm absolutely summable and equals the actual arithmetic family. Separate convergence of the two bracket components is not asserted. |
| Established local declaration | `RH/DyadicBoundaryUniformCriterion.lean`: `dyadicBoundaryDetailEnergy_eq_coordinate_square`, `dyadicBoundaryDetailEnergy_le_iff_finite_sums` | Full boundary energy equals one quarter the complete sum of squared canonical coefficients. One constant must bound every finite set, not one chosen cutoff. |
| Established local declaration | `RH/DyadicSignedBoundaryNormCriterion.lean`: `dyadicNormalizationRemainder_norm_sq_eq_signedBoundary`, `dyadicRegularizedFamily_error_sq_eq_signedBoundary` | The actual remainder norm and projected approximation error equal the full explicit arithmetic square sums; all signed and mixed contributions remain inside the squares. |
| Conditional research reduction | `RH/DyadicSignedBoundaryNormCriterion.lean`: `dyadicRegularized_norm_obligations_of_signedBoundary` | A nonnegative C bounding every finite signed remainder square sum for all 0<epsilon<=1/2 supplies the existing base and physical-tail norm obligations. This uniform estimate remains an explicit hypothesis. |

Combined source check `job_DBgmOZDiHpYMUWwTVpSl2e8pvEwLrG7j` succeeded (verified true, exit 0, 5.243 seconds). Final exact-source and eight-endpoint theorem-type/axiom audit `job_7rLv2Lh7SwGRjd2cN5fT825qpHaDhxXa` succeeded (verified true, exit 0, 5.042 seconds); code SHA-256 `8b4220a1657cf91d3a7f5c4bba7f8ef04dd29c054fd7d0d040fbed2a50d50d03`. All eight audited endpoints use only propext, Classical.choice, and Quot.sound. Separate-module validation and publication use the single final checkpoint.

**Open:** one constant controlling the entire actual remainder square sum uniformly as damping vanishes; the stronger O(epsilon) squared remainder estimate; arithmetic vector/Mellin/separating limits; full legal two-seed recovery including complementary energy; the separate N5 identification; RH. The ordinary-mathematics discussion in `RH/DyadicBoundaryFourierResearchNote20260910.md` is not a checked provider and changes none of these statuses.

### Actual scalar normalization, signed Gram energy, and projected terminals (2026-09-10)

This continuation adds 35 public theorems across eight new modules. Scalar normalization is now discharged for the actual positive-damping arithmetic family. The full vector remainder, the uniform vanishing-damping norm bound, and full legal recovery remain Open.

| Status | Module and endpoints | Precise checked scope |
| --- | --- | --- |
| Established local declaration | `Analysis/AbsolutelySummableGram.lean`: `inner_tsum_eq_tsum_product`, `norm_sq_tsum_eq_tsum_gram` | Absolute norm summability supplies the full signed product-index Gram identity for real Hilbert families. |
| Established local declaration | `RH/DyadicRegularizedSignedGram.lean`: `dyadicRegularizedGram_abs_summable`, `dyadicRegularizedFamily_error_sq_eq_signed_gram` | Actual signed arithmetic Gram and cross series converge absolutely at every epsilon>0. Exact squared error against any comparison retains all off-diagonal and mixed terms. |
| Established local declaration | `RH/DyadicRegularizedMean.lean`: `regularizationZetaSeries_mul_mobius`, `dyadicRegularizedFamily_inner_one` | Mathlib's Mobius Dirichlet inversion and the actual Hilbert resolvent prove mean(F_epsilon)=1 for every epsilon>0, without a supplied arithmetic norm or mean hypothesis. |
| Established local declaration | `RH/DyadicRegularizedBoundaryEnergy.lean`: `dyadicRegularizedFamily_error_sq_eq_boundary`, `dyadicNormalizationRemainder_norm_sq_eq_boundary`, `dyadicRegularizedFamily_norm_sq_comparison_remainder` | The actual family lies in QH and norm(F-1)^2 equals its complete boundary energy. The specified remainder has mean zero, lies in QH, and its squared norm equals its full boundary energy. The comparison/remainder interaction is retained exactly. |
| Established local declaration | `Analysis/FiniteGeometricDifference.lean`, `RH/DyadicArithmeticResidueTelescoping.lean`: `dyadicRegularizedRectangle_residue_telescope` | Finite raw and projected arithmetic rectangles have an exact signed residue decomposition with the complete terminal column. No convergence premise. |
| Established local declaration | `RH/DyadicResidueOrbitGrowth.lean`: `dyadicQuotientProjection_residue_triadic_norm_le_quadratic` | The actual projected terminal residue grows at most quadratically in triadic depth, for a fixed positive starting conductor. |
| Established local declaration | `RH/DyadicProjectedResidueTerminal.lean`: `dyadicProjectedResidueTerminal_norm_summable`, `dyadicProjectedResidueTerminal_tendsto_zero` | For every fixed n>0 and epsilon>0, the projected terminal orbit is absolutely summable in H and tends to zero in H. No uniformity in n or epsilon is asserted. |

Combined source verification: `job_66edWvInJYfTYNheBUXasl4UgWNHjsRB`, verified true, exit 0, 4.939 seconds. Final combined source plus eight-endpoint theorem-type/axiom audit: `job_gE-0xmB75_YHZLRwMP8x6w6hs6ss9ihG`, verified true, exit 0, 5.074 seconds; source SHA-256 `3259f1c58104f13d6c1900733dc2a02ed8ef617fc1f95557943b14753c1fefe5`. Audited endpoints depend only on propext, Classical.choice, and Quot.sound. Separate-module validation and publication follow through one checkpoint.

**Open:** uniform boundedness of the actual complete mean-zero boundary energy as epsilon tends to zero; the stronger O(sqrt epsilon) actual remainder estimate; arithmetic vector/Mellin/separating identifications; full legal two-seed witnesses with complete complementary and boundary energies tending to zero; the separate N5 identification; RH. The computed mean and projected-terminal limit do not supply these limits. No epsilon=0 substitution into the normalized zeta-based definition is used.

### All-scale arithmetic kernel bound and positive-damping convergence (2026-09-10)

This continuation adds 32 public theorems across six new RH modules. The previous all-scale block and actual arithmetic-series convergence obligations are discharged. These results concern every positive integer dilation of the actual triadic residue. Uniform vanishing-damping bounds and RH remain unproved.

| Status | Module and endpoints | Precise checked scope |
| --- | --- | --- |
| Established local declaration | `RH/DyadicAdjointCoordinates.lean`: `dyadicHalfAdjoint_orbit_weighted_coordinate`, `dyadicHalfAdjoint_orbit_coordinate_bounds`, `dyadicHalfAdjoint_orbit_coordinate_of_constant` | Exact physical block formula for every A^j, positive-amplitude bounds and constant-block recovery. |
| Established local declaration | `RH/DyadicSparseBlockEnergy.lean`: `dyadicKernelDefect_norm_sq_le_sixteen_of_sparse_block_jumps` | Complete physical jump energy, including the exceptional first coordinate, is at most 16 under the stated sparse crossing/amplitude conditions. Explicit summability and injective finite reindexing are proved. |
| Established local declaration | `RH/DyadicResidueAdjointBlocks.lean`: `dyadicKernelDefect_halfAdjoint_triadicResidue_norm_le` | Unconditionally, norm K(A^j T_m R3) <= 4 for every m>0 and j>=0. The proposed constant 6 is improved. The sparse crossing and amplitude conditions are supplied from actual arithmetic coordinates. |
| Established local declaration | `RH/DyadicResidueDepthGrowth.lean`: `dyadicQuotientProjection_triadicResidue_norm_le_depth` | If m<=2^N, norm Q(T_m R3) <= 4N/sqrt(2)+norm R3. The exact finite reconstruction and actual terminal vector precede the norm estimate. |
| Established local declaration | `RH/DyadicRegularizedSummability.lean`: `dyadicRegularizedTerm_norm_summable`, `dyadicRegularizedTerm_summable`, `dyadicRegularizedSeriesSummable_proved` | Actual product-index arithmetic norm series converges for every epsilon>0. The entire previously named scalar-plus-vector series obligation is proved. A subpower majorant depending on epsilon supplies absolute convergence without assuming Mobius cancellation. |
| Established local declaration | `RH/DyadicRegularizedSummability.lean`: `dyadicRegularizedColumn_summable_of_pos`, `dyadicRegularizedFamily_eq_columns_of_pos`, `dyadicRegularizedFamily_resolvent_of_pos` | Actual columns, regrouping and exact infinite arithmetic resolvent, now assuming only epsilon>0. No identification of the head with the normalization remainder is asserted. |
| Established local declaration | `RH/DyadicRegularizedNormReduction.lean`: `dyadicTailRegularizedSeriesSummable_proved` | The complete existing physical tail-series summability obligation is supplied by actual base convergence and the established transfer. |
| Conditional research reduction | `RH/DyadicRegularizedNormReduction.lean`: `dyadicRegularized_norm_obligations_of_error`, `dyadicRegularized_norm_obligations_of_bounded_error` | Base and all physical tail uniform norm bounds require only the displayed actual normalization remainder. A bound independent of epsilon already suffices for these norm conclusions; O(sqrt epsilon) decay is stronger. Neither remainder estimate is proved. |

The all-scale block and depth endpoints passed combined source verification and an axiom audit in `job_k4XyCzeA4eCrXgJ31UFEZGnWBEJJ90fc` (verified true, exit 0, 7.401 seconds; source SHA-256 `f45dd693f58c38c0daab3e91e146fe2c246cd944f0255f465c10ae4b93caff72`). The full positive-damping convergence and resolvent passed `job_wQ0JTFd8NmRAKmM27SqfFrVI6BvkU0L-` (verified true, exit 0, 9.46 seconds; source SHA-256 `48386953a651cdfef15c63b959fa5def5a234bda1a26dd2f8bab6011cafe0a60`). Audited endpoints use only propext, Classical.choice and Quot.sound. The final combined source and seven-endpoint theorem-type/axiom audit passed `job_erIWxeQC1c8gwhNJJHBs4SlHvY75E5Az` (verified true, exit 0, 9.58 seconds; source SHA-256 `c915bbe8ddf24f7e4287ab0d88375aae010dc4d6a6d06cae49eb4a77b8cb90d5`). All seven endpoints use only the same three foundational axioms. Separate-module validation is performed by the publication checkpoint.

**Open:** the actual uniform normalization remainder; uniform arithmetic norm obligation (N2); arithmetic Mellin/separating limits; full legal witness recovery, including complementary energy; the specifically stated N5 fold/martingale identification; RH. Fixed positive-damping convergence does not justify any of these vanishing-damping limits.

### Actual residue jumps, kernel energy, and full-energy recovery (2026-09-10)

This continuation adds 46 public theorems across six new RH modules. It proves an unconditional first-block bound for every actual positive integer dilation. The later all-scale continuation above now supplies higher-block growth and full arithmetic-series convergence. The normalization remainder and RH remain Open.

| Status | Module and endpoints | Precise checked scope |
| --- | --- | --- |
| Established local declaration | `RH/DyadicResidueJumps.lean`: `hilbertDilation_residue_three_difference_multiple`, `dyadicKernelDefect_even_dilation` | Actual jumps vanish away from dilation multiples, equal +m at ordinary multiples and -2m at triple multiples. Every even dilation is killed by the dyadic kernel defect. |
| Established local declaration | `RH/DyadicKernelJumpEnergy.lean`: `dyadicKernelDefect_jump_energy_summable`, `dyadicKernelDefect_norm_sq_jumps`, `dyadicQuotientProjection_norm_sq_resolvent_jumps` | Exact convergent kernel energy in physical adjacent jumps, and its specialization to the actual critical resolvent. No jump or signed interaction is omitted. |
| Established local declaration | `RH/DyadicResidueKernelEnergy.lean`: `dyadicKernelDefect_residue_three_norm_sq_arithmetic`, `dyadicKernelDefect_residue_three_norm_sq_le_four` | Exact arithmetic divisibility-channel energy, including the mixed-term correction, followed by the unconditional bound norm-squared K(T_m R3) <= 4 for every m>0. This is the first kernel block, not the full quotient norm. |
| Established local declaration | `RH/DyadicRegularizedResolvent.lean`: `dyadicRegularizedRectangle_resolvent` | Exact finite arithmetic resolvent with the complete signed terminal column, at every damping and finite cutoff; no summability hypothesis. |
| Conditional research reduction | `RH/DyadicRegularizedResolvent.lean`: `dyadicRegularizedFamily_resolvent`, `dyadicRegularizedColumn_eq_orbit` | Regrouping and the infinite actual triadic resolvent require Summable(dyadicRegularizedTerm epsilon). This actual product-index convergence is now supplied for every positive epsilon by `DyadicRegularizedSummability.lean`; its specialized identities have only epsilon>0 as an assumption. |
| Established local declaration | `RH/DyadicBoundaryLegalRecovery.lean`: `dyadicBoundary_tendsto_one_iff`, `dyadicBoundaryLegalRecovery_iff_legalClosure` | Exact equivalence between physical convergence and decay of mean defect squared, full infinite boundary energy, and complementary energy; equivalence to the original legal closure target. No witness existence follows merely from the equivalence. |
| Conditional research reduction | `RH/DyadicBoundaryLegalRecovery.lean`: `riemannHypothesis_of_dyadicBoundary_meanOne_recovery` | The actual RH implication from mean-one legal two-seed witnesses with both full energies tending to zero. Existence of such witnesses remains Open. |
| Established local declaration | `RH/DyadicBoundaryEscape.lean`: `dyadicBoundaryEscape_prefixEnergy_eq_zero`, `dyadicBoundaryEscape_detailEnergy`, `dyadicBoundaryEscape_not_tendsto_one` | Actual bounded mean-one vectors have zero complementary energy and eventually-zero every finite boundary prefix, while total boundary energy and physical error remain exactly one. No legal membership is asserted. |

The first five modules' 42 declarations passed combined source verification and ten-endpoint axiom audit in `job_ls7WmphcmAjOCE5yxvoEf7EWu72VfFsA` (verified true; exit 0; 6.191 seconds; source SHA-256 `47c66a9e9556b2a3ecb6103a1aff412bfbc4bd3b7369c96e96e62c5450284320`). All ten audited endpoints use only propext, Classical.choice, and Quot.sound. The four additional exact arithmetic energy/bound declarations passed `job_CsaJThJy1PFVBLN8lyeSZWi5mTapuyJG` (verified true; exit 0; 4.228 seconds). The two arithmetic-energy endpoints also passed the axiom and theorem-type audit in `job_AL1-qq8XzsHNtopVX62xLL5Z6g-RE1hS` (verified true; exit 0; 4.852 seconds; source SHA-256 `c4b6e75c78faea1d2c9eb8c2f2c1ccb5e048866d56b806604b0c58f67fd56927`), using only the same three foundational axioms. The final checkpoint validates the separate modules before publication.

**Resolved by the subsequent all-scale continuation:** norm K(A^j T_m R3) <= 4 for all m>0 and j>=0; the finite-packet depth estimate and positive-damping product convergence are proved. The ordinary proof plan is retained as historical provenance. The normalization remainder and full legal energy recovery remain Open.

### Actual dyadic Gram/prefix providers and completed Parseval (2026-09-10)

This continuation adds 90 public theorems across fourteen new modules and the existing Gram assembly. The actual step average now has an unconditional uniform norm bound. The full arithmetic family and RH remain conditional on the obligations listed below.

| Status | Module and endpoint | Precise checked scope |
| --- | --- | --- |
| Established local declaration | `RH/DyadicBoundaryParseval.lean`: `dyadicBoundary_full_error_sq`, `dyadicBoundary_parseval_inner` | Complete convergent boundary Parseval and full physical error = mean defect squared + 4 times the boundary pairing square sum + complementary energy. No hidden quotient component or omitted mixed pairing. |
| Established local declaration | `RH/DyadicFiniteBoundaryCoordinates.lean`: `dyadicProjectedStep_finite_boundary_error_sq` | Exact actual finite signed step energy in canonical boundary coordinates. Coefficients lie in [0,1]; no signed coefficient restriction. |
| Established local declaration | `RH/DyadicBoundaryAnnulusMass.lean`, `RH/DyadicBoundaryLocality.lean`, `RH/DyadicStepGramCutoff.lean` | Annular mass at most one and exact support give normalized separation at least 2^(-R) implies raw Gram at most 1+R/4. The explicit tent-height formula is unnecessary for this provider. |
| Established local declaration | `Analysis/RotationNearestSpacing.lean`, `Analysis/TriadicRotationSeparation.lean`, `Analysis/TriadicMantissaSeparation.lean` | Actual nearest-integer errors, minimum-denominator spacing, delta_q at least 1/(2*3^q), log(1/delta_q) at most q log6, and normalized triadic mantissa separation. |
| Established local declaration | `Analysis/RotationLogarithmicPrefix.lean`: `triadicLogGramMajorant_prefix_le` | Actual nonnegative a_h from the ordinary argument has every prefix bounded by A0*N, with explicit A0. Finite packing, logarithmic blocks, and grouping are proved in four supporting Analysis modules. |
| Established local declaration | `RH/DyadicTriadicGramBound.lean`: `dyadicProjectedStep_triadic_off_diagonal` | The complete actual absolute off-diagonal triadic Gram pairing is bounded by a_(k-j), with no Gram or arithmetic provider assumed. |
| Established local declaration | `RH/DyadicRegularizedGramAssembly.lean`: `dyadicStepAbelOrbit_norm_sq_le_explicit` | Every epsilon>0 has actual step-average squared norm at most 3/2+2*A0 (approximately 10.2921). |
| Conditional research reduction | `RH/DyadicRegularizedGramAssembly.lean`: `dyadicRegularized_explicit_bounds_of_series_and_error`, `dyadicRegularized_norm_obligations_of_series_and_error` | The base and all-tail arithmetic norm bounds now require only actual series summability and the stated O(sqrt epsilon) normalization remainder. The series premise is now proved in `DyadicRegularizedSummability.lean`; the actual normalization remainder remains Open. No diagonal, off-diagonal, or prefix provider remains in these specialized theorem types. |

The combined source and theorem-type audit passed in `job_RJpGpp05PV1J-f19Afg0I7dl1qMR2iad` (verified true, exit 0, 14.607 seconds; source SHA-256 `a0913111de7dd5c7573119af326beec48e55a8eea3c1ace48e468575934cdcda`). The compact ten-endpoint axiom audit passed in `job_IcznDUFqujwWQOLplCq-lYVBAVeg9--K`; all ten depend only on propext, Classical.choice, and Quot.sound. The publication checkpoint validates the separated modules and affected dependents.

**Open:** arithmetic identification and the normalization remainder; Mellin/separating limits; full legal two-seed approximation, including complementary energy. The particular N5 fold/martingale identification and explicit tent-height formula are not established by the new coordinate formulas. Neither unconditional (N2) nor RH is proved.

### Exact dyadic Gram, complete boundary coordinates, and repair rigidity (2026-09-10)

Source: the supplied dyadic verification continuation. This advance adds 29 public theorems across four modules, while retaining the unresolved arithmetic and full-space approximation obligations.

| Status | Module and declaration | Precise checked scope |
| --- | --- | --- |
| Established local declaration | `RH/DyadicStepGram.lean`: `dyadicProjectedStep_odd_inner_step`, `dyadicProjectedStep_adjacent_norm_sq_on_annulus` | Exact off-diagonal refinement and adjacent squared energy (1-4^(-N))/3 on 2^N ≤ m < 2^(N+1). No arithmetic provider. |
| Established local declaration | `RH/DyadicStepGram.lean`: `dyadicProjectedBoundary_finite_inner`, `dyadicProjectedBoundary_finite_mean_energy` | Distinct physical projected boundaries are orthogonal, each of squared norm 1/4. Complete finite signed energies diagonalize exactly, including the mean coordinate. |
| Established local declaration | `RH/DyadicBoundaryCompleteness.lean`: `dyadicBoundarySpan_closure_eq_quotient`, `dyadicQuotientProjection_eq_of_boundary_inner` | The actual constant and projected boundaries densely span the full quotient; all their pairings determine Qf. Infinite Parseval is now supplied by DyadicBoundaryParseval; identification with the specific N5 fold remains Open. |
| Established local declaration | `RH/DyadicCenteredRepairRigidity.lean`: `dyadicRepairDifference_mem_centeredClosure_iff` | A=T₂-I is bounded below; Af is in the centered repair closure iff f is in the actual all-positive legal closure. No density hypothesis enters this equivalence. |
| Conditional research reduction | `RH/DyadicCenteredRepairRigidity.lean`: `riemannHypothesis_of_difference_one_mem_centeredClosure`, `riemannHypothesis_of_centeredClosure_exhausts_kernel` | Approximating the single explicit vector (T₂-I)1 by centered repairs implies RH. That membership is Open. Exhausting all ker Q is consequently an RH-strength input. |
| Established local declaration | `Analysis/RotationMinimumSpacing.lean`: `integer_approximation_minimum_spacing` | Integer determinant spacing: 0<h<q and 0<|qα-pq|≤|hα-ph| imply |hα-ph|>1/(2q). Concrete ingredient for the RH Gram/prefix bound; no CF assumption. |

The complete four-module source and eight-endpoint type/axiom audit passed in `job_JmttxrBmzAsPdqXpcp34vDzSyBFwEq4-` (verified true; exit code 0; 5.31 seconds; SHA-256 `9b2610554f13be12811ffab80a38c7e9fb92ca72476d7c02b596d68285f379b7`). Only standard foundational axioms occur. Final acceptance validates the separated modules with the repository checkpoint.

**Open:** the exact tent expansion and full logarithmic prefix argument are preserved as an ordinary proof candidate in [Dyadic_Gram_Prefix_Ordinary_Proof_20260910.md](RH/Dyadic_Gram_Prefix_Ordinary_Proof_20260910.md). The new continuation discharges the required Gram/prefix hypotheses using actual coefficient support and annular mass, while leaving the explicit tent-height formula unformalized. Product-index Möbius convergence, arithmetic identification, normalization remainder, Mellin limits, and full legal approximation remain Open. Neither unconditional (N2) nor RH is established. Detailed continuation: [DyadicVerificationAdvance20260910.md](RH/DyadicVerificationAdvance20260910.md).

### Vanishing-damping quotient: checked components and conditional norm assembly (2026-09-10)

Source: the user-provided continuation “The vanishing-damping quotient norm is uniformly bounded,” equations (N1)–(N31), in the two-seed signed-tail handoff. This is a **partial formalization** of that argument. The unconditional uniform arithmetic norm theorem is not yet an established Lean result.

| Status | Module and declaration | Precise checked scope |
| --- | --- | --- |
| Established local declaration | `Analysis/AbelPrefixBound.lean`: `normalized_geometric_tsum_le_of_nonneg` | A nonnegative sequence with prefix sums at most `C N` has a summable geometric series and normalized Abel sum at most `C`. Exact finite summation retains its terminal term. |
| Established local declaration | `Analysis/AbelCoboundary.lean`: `orbit_average_fixed_add_coboundary` | Exact Abel identity for an invariant vector plus a coboundary, with every required series convergence hypothesis visible. |
| Established local declaration | `Analysis/AbelOrbitGrowth.lean`: `norm_orbit_average_coboundary_le_sqrt` | Physical orbit growth bounded by `C sqrt(n+1)` implies summability and the explicit bound `4 C sqrt(1-r)` for the averaged coboundary, when `1/2 ≤ r < 1`. |
| Established local declaration | `Analysis/AbelGramBound.lean`: `norm_average_sq_le` | Diagonal bound `D(j+1)` and an off-diagonal Gram majorant with prefix bound `A N` imply the full squared Abel norm bound `D+2A`. Vector convergence is derived; the exact recurrence includes every mixed term. |
| Established local declaration | `RH/DampedMobiusSeed.lean`: `dampedMobius_centered_seed_identity`, `dampedMobiusPrefix_at_zero` | Actual finite Möbius/floor/residue identities, exact compensation of any density term, and zero-damping cancellation. These do not assume or prove quantitative Mertens cancellation. |
| Established local declaration | `RH/DyadicRegularizedNorm.lean`: `mem_dyadicQuotientSubspace_iff`, `dyadicQuotientProjection_dilation_projection`, `regularizationZetaSeries_summable` | Genuine quotient projection in the actual weighted Hilbert space, fixed-adjoint characterization, exact `Q T_m Q = Q T_m`, quotient dilation bound, and positive-damping scalar Dirichlet-series convergence. |
| Established local declaration | `RH/DyadicQuotientAbel.lean`: `dyadicQuotientDilation_orbit`, `dyadicQuotientDilation_fixed_residue_two` | Actual induced integer-dilation semigroup and physical orbits; the mean vector `QR₂` is fixed. |
| Established local declaration | `RH/DyadicTailQuotient.lean`: `mem_dyadicPhysicalTail_iff`, `dyadicTailRegularizedFamily_eq_transfer`, `dyadicTailRegularizedSeriesSummable_of_base` | Constructs the actual tail spaces and quotient projections, proves their support/variational semantics and exact arithmetic transfer. Convergence of the base arithmetic series implies convergence of the concrete tail series. |
| Conditional research reduction | `RH/DyadicQuotientAbel.lean`: `dyadicStepAbelOrbit_norm_sq_le_of_gram` | The concrete step-orbit Abel bound follows from its actual diagonal/off-diagonal Gram data and their prefix bound. Those concrete analytic providers are not yet discharged. |
| Conditional research reduction | `RH/DyadicRegularizedNorm.lean`: `dyadicRegularizedNormBound_of_analytic_estimates` | For the concrete product-index Möbius regularization, projected-series summability, a uniform actual step-orbit bound, and the actual remainder estimate (N24) imply uniform base norm boundedness. All three domain-specific inputs remain explicit. |
| Conditional research reduction | `RH/DyadicTailQuotient.lean`: `dyadicTailRegularizedNormBound_of_base` | Base summability and base boundedness imply the full concrete `C d` bound with all original `X,d,ε` quantifiers. The base bound remains an explicit hypothesis; no arbitrary-projection or transfer-identity assumption remains. |

| Established local declaration | `RH/DyadicStepLogBound.lean`: `dyadicProjectedStep_odd_norm_sq_signed`, `dyadicProjectedStep_norm_sq_le_depth`, `dyadicProjectedStep_triadic_diagonal`, `dyadicStepAbelOrbit_series_summable` | Exact weighted boundary refinement and support orthogonality prove m ≤ 2^N ⇒ ‖QT_m1‖² ≤ 1+N/4, hence the concrete triadic diagonal bound D=3/2 and positive-damping step-series convergence. The negative adjacent-step difference energy is retained. Off-diagonal/prefix estimates remain Open. |
| Established local declaration | `RH/DyadicCriticalApproximation.lean`: `dyadicCriticalPacket_norm_sq_eq`, `dyadicCriticalPacket_error_norm_sq_le`, `dyadicCriticalPacket_tendsto` | Exact signed terminal energy; squared truncation error ≤ 2^(-N)‖f‖² and genuine norm convergence for every physical vector. Integer steps admit a scale-free dyadic-cutoff accuracy certificate. |
| Established local declaration | `RH/DyadicCenteredSeedRepair.lean`: `dyadicCenteredSeed_optimal_complementary_energy`, `finite_centered_dyadic_repair_error_sq` | Actual finite dyadic directions G_m=T_mR₂−R₂ have zero quotient; scalar optimization gives the exact physical complementary-energy gain. Finite signed corrections retain the complete i,j Gram form and produce actual finite two-seed legal lifts. Energy exhaustion remains Open. |
| Established local declaration | `RH/DyadicCriticalResolvent.lean`: `dyadicQuotientProjection_norm_sq_eq_criticalResolvent`, `dyadicQuotientProjection_inner_eq_criticalResolvent` | For every actual Hilbert vector, the convergent half-adjoint resolvent gives the exact quotient norm and every mixed Gram entry. No analytic provider is assumed. The specific boundary fold and uniform arithmetic estimates remain separate obligations. |
| Established local declaration | `RH/DyadicFiniteCriticalNorm.lean`: `dyadicQuotientProjection_norm_sq_of_support`, `dyadicQuotientProjection_inner_of_support` | Exact finite critical norm and mixed Gram formulas for actual physical vectors supported below a dyadic cutoff. Convergence of the kernel lift and vanishing of the terminal adjoint iterate are proved internally. This does not yet prove the full boundary fold or the uniform arithmetic estimates. |
| Established local declaration | `RH/DyadicStepMeanIdentity.lean`: `dyadicProjectedStep_sum_error_sq`, `dyadicStepFiniteAbelAverage_error_sq` | Exact signed centered Gram error, including the scalar mean defect; finite Abel truncation retains its terminal error. Infinite mean/variance identities require the actual vector series to be summable. |
| Conditional research reduction | `RH/DyadicTailRecovery.lean`: `dyadicTailProjectedTriadicClosure_eq_quotient_of_inner_limits` | Actual arithmetic summability and separating inner-product limits imply quotient density. Finite signed lifts have actual legal membership and zero head support. The inner-product limits remain Open; recovery itself uses checked closed-subspace duality. |
| Conditional research reduction | `RH/DyadicRegularizedGramAssembly.lean`: `dyadicRegularized_explicit_bounds_of_gram_and_error` | Actual off-diagonal/prefix data, arithmetic series convergence, and the actual remainder produce the same explicit constant for the base and every physical tail, retaining both convergence conclusions. The diagonal is now discharged internally with D=3/2; the remaining analytic data stay Open. |
| Established local declaration | `RH/DyadicTriadicComplementObstruction.lean`: `dyadicTriadic_complementary_energy_gap`, `dyadic_two_channel_lift_error_eq` | A positive full-space Mellin gap for the actual residue-3 seed forces positive complementary energy when quotient error is small. Exact two-channel error retains the complete signed mixed term. No zeta-zero or RH assumption. |

**Open formal providers:** the critical fold/martingale norm and its BV estimates; uniform quantitative Möbius cancellation and damping differentiation; construction and growth of the concrete seed potential; actual off-diagonal Gram and continued-fraction prefix estimates; convergence and exact identification of the projected arithmetic series; and the concrete (N24) remainder. These are missing Lean providers for the ordinary proof, not a claim that the statements are mathematically open. The concrete logarithmic diagonal is proved with D=3/2, and the damped step series converges unconditionally for positive damping. The complete operator critical norm now has a checked resolvent provider; the specific boundary fold and BV estimates remain Open. Actual weak/Mellin limits remain Open. Finite signed legal recovery and quotient density now have checked conditional providers from actual summability and scalar inner-product limits; no convex-combination algorithm is claimed.

The complete eight-module supporting check and nineteen project dependencies passed in job `job_H3BDnrCxPZVm2eNwx5awrKGwWOkal1rV` (`verified: true`, exit code 0; submitted-source SHA-256 `376022424baaf8952e72ca2f01a98601658cfdd52fdbb7cc51a5687087a389c0`). The audited endpoints use only `propext`, `Classical.choice`, and `Quot.sound`; these axiom reports do not discharge the conditional theorem's local hypotheses. The final repository checkpoint additionally validates the separated modules.

Detailed coverage and exact remaining inputs: [`RH/DyadicRegularizedNormFormalization20260910.md`](RH/DyadicRegularizedNormFormalization20260910.md). The six-module continuation is recorded in [`RH/DyadicRegularizedVerificationContinuation20260910.md`](RH/DyadicRegularizedVerificationContinuation20260910.md).

The subsequent exact-boundary/diagonal and centered-repair source check passed in `job_fz5g6EneRkvk0yBiMb1Wb3sSBt_Kat9z` (`verified: true`, exit code 0, 6.920 s; SHA-256 `def7a780ae7713d765372423c5df8c0fd3efde76391c9aa6b8a84ce72fc031b0`). The critical truncation check passed in `job_xfWXrn2br_HD9p8nj1gDWoEUYReptO1I` (`verified: true`, exit code 0, 2.918 s). Audited endpoints use only standard foundational axioms. The two norm-assembly theorem types no longer accept a diagonal-growth provider; the other substantive assumptions remain explicit. Neither unconditional (N2) nor RH is established.

### Single-conductor obstruction with a constructed nonzero signature (2026-09-09)

Source: the user-provided Nyman–Weil note, sections 10.3–10.4, especially equation (10.5). These are unconditional established results about the actual functions and Bochner integrals.

| Result | Declaration and precise scope |
| --- | --- |
| Compact smooth interpolation | `Analysis/CompactLaplaceInterpolation.lean`: `MeasureTheory.BilateralLaplace.centeredTransform_compactLaplaceSeed` constructs an actual smooth test v_s supported in [-2,2] with Mv_s(s)=1, for every complex s. Thus the required nonzero spectral signature is constructed, rather than assumed. |
| General single-conductor obstruction | `RH/NymanSingleConductorObstruction.lean`: `singleConductorCompletion_energy_lower_bound`. For any compact smooth potential u, smooth superexponential f, and actual equality L R_n u=f below Y, the actual difference has energy at least exp(Y)|M f(s)|² at every conductor-symbol zero s distinct from 1. Its L² membership and exact transform signature are derived. No zeta-zero or RH hypothesis is used. |
| Actual arithmetic-tail growth floor | `nymanCompletionTail_artificial_zero_linear_lower_bound`, `nymanCompletionTail_explicit_artificial_zero_lower_bound`: the concrete inverse-completion tails satisfy energy >= exp(a)|M(Lv)(s)|²(M+1). The latter theorem uses the literal frequencies s=1+2πik/log(n), k!=0. |
| Constructed failure of sublinear energy | `nymanCompletionTail_compactLaplaceSeed_linear_lower_bound` gives energy >= exp(-2)|s(s-1)|²(M+1) for the concrete interpolating seed. `exists_nymanCompletionTail_normalized_energy_not_tendsto_zero` proves that every n>=2 has a compact smooth seed for which energy/(M+1) does not converge to zero. The seed's nonzero signature is fully discharged. |
| Quantified divergence for a given signature | `nymanCompletionTail_energy_unbounded_of_artificial_signature` and `nymanCompletionTail_normalized_energy_not_tendsto_zero` give the corresponding general-seed consequences under an explicitly stated nonzero transform value. |

The complete isolated check succeeded in job `job_EdjW3qXuXoisnvZV2JTfeJ3O22Ak2yyF`, `verified: true`, exit code 0, 17.196 seconds. Submitted-source SHA-256: `f5596c65d61c1725df66ca9e2d8aa82c601c3a2de49341c33dded481906a3758`. It included the two new modules and their 28 dependency modules. Axiom audits for the interpolation, general completion obstruction, and constructed nonconvergence endpoints use only `propext`, `Classical.choice`, and `Quot.sound`.

This establishes the single-conductor obstruction independently of RH. It does not establish the optimized mixed-conductor upper bound, a uniform analytic inverse for conductors 2 and 3, or RH.

This catalog is the orientation layer for the RH-focused `main` branch. Lean source files
and successful builds remain authoritative. The complete Serre II development as it
stood on 4 September 2026 is preserved on
[`serre-ii-archive-20260904`](https://github.com/Cnoack3/RiemannResearch/tree/serre-ii-archive-20260904).

## Status conventions

- **Kernel checked** means Lean has verified a proof of the declaration's exact
  type.
- **Established local declaration** means the result is not currently serving
  as a stand-in for an unfinished named research theorem. It may still have the
  ordinary hypotheses appropriate to a general reusable lemma.
- **Conditional research reduction** means Lean has checked the implication,
  but domain-specific inputs needed for the motivating theorem remain
  unresolved.
- **Open obligation** means no project declaration currently supplies that
  input. Local hypotheses do not appear in `#print axioms`, so a clean axiom
  report alone does not make a result unconditional.

## Two-seed approximation implies RH (9 September 2026)

The declarations below have namespace `RiemannResearch.RH.Pareto` and live in
`RH.ThresholdRiemannHypothesis`. They use the actual weighted Hilbert space,
actual zeta function, and all positive integer dilations. The converse
`RiemannHypothesis → hilbertOne ∈ hilbertLegalClosure {2, 3}` remains **Open**.

| Declaration | Established scope |
|---|---|
| `paretoMellin_zero_on_legalClosure_of_zeta` | A hypothetical zeta zero with Re(s)>1/2, s≠1 annihilates the entire closed legal space for any positive seeds. |
| `zeta_ne_zero_of_hilbertOne_mem_legalClosure` | Actual target membership excludes these zeros without an assumed NB bridge. |
| `riemannHypothesis_of_hilbertOne_mem_legalClosure` | For any positive seeds, actual target membership implies Mathlib's RH; reflection and boundary/trivial-zero issues are discharged by existing providers. |
| `riemannHypothesis_of_twoSeed_closure` | The complete 2,3 approximation-to-RH implication. This does not establish target membership or the reverse implication. |
| `legalClosure_distance_sq_lower_bound_of_zeta` | Full weighted squared distance is at least (2 Re(s)−1)/‖s‖² for every vector in the closed legal space at a hypothetical such zero. |
| `arithmeticZeroObstruction` | Discharges the previously open `ArithmeticZeroObstructionTarget`, including every finite two-seed legal vector. |
| `riemannHypothesis_of_legalClosure_eq_top` | Density in the actual Pareto Hilbert space implies Mathlib's RH for any positive seed set. Added 16 September 2026. |


The converse now has the following proved supporting components:

| Declaration family | Module | Exact status |
|---|---|---|
| `hilbertTail_inner_scaling`, `hilbertTail_inner_pow_scaling`, `hilbertTail_inner_sub`, `hilbertTail_inner_sub_sq_le_tailEnergy`, `hilbertTailEnergy_tendsto_zero` | `RH.ThresholdJointAdjointTail` | Actual absolutely summable weighted tails, exact scaling from a fixed-adjoint equation, exact finite blocks, full tail-energy decompositions and vanishing energy. The September 14 prefix-primitive proof supplies the needed continuous limit and quantitative coordinate recovery. |
| `continuous_eq_const_of_two_irrational_periods`, `primeLogRatio_irrational`, `continuous_primeLog_periods_constant`, `continuous_twoSeed_log_periods_constant` | `RH.PrimeLogPeriodRigidity` | Unconditional dense-period rigidity for continuous profiles and its actual distinct-prime and two-seed logarithmic specializations. The September 14 modules now construct the required continuous prefix profile from the adjoint-fixed Hilbert data. |
| `legalSeedSpan_positive_eq_residue_span`, `hilbertDilation_sub_mem_legalClosure`, `adjoint_sub_mem_full_orthogonal` | `RH.ThresholdHilbertCocycle` | Exact full-residue space identification and closed-Hilbert cocycle/orthogonality reduction, without RH or density hypotheses. |
| `adjoint_fixed_of_legal_orthogonal_of_full_density` | `RH.ThresholdHilbertCocycle` | **Conditional research reduction:** full positive-residue density is an explicit input. |
| `twoSeed_legalClosure_eq_top_of_full_density_of_joint_fixed_constants`, `hilbertOne_mem_twoSeed_of_full_density_of_joint_fixed_constants` | `RH.ThresholdTwoSeedConverse` | **Conditional research reduction:** full positive-residue density and two-seed adjoint rigidity are explicit inputs. Joint rigidity now has the checked provider `hilbertDilationAdjoint_two_three_fixed_iff`; the classical RH-to-full-density provider remains Open as a formalization obligation. |

See `RH/ThresholdEquivalenceProgress20260909.md` for the earlier status and
`RH/TwoSeedEquivalenceVerification20260914.md` for the current verified scope.

## Two-seed rigidity and full-density equivalence (14 September 2026)

Source: the conversation and `RH_Iff_Two_Seed_Approximation_20260914.md`.
The new converse argument is proved using continuous prefix primitives and
localized block-average recovery in the actual Pareto Hilbert space.

| Declaration family | Modules | Exact status |
|---|---|---|
| `dyadicInvariant_prefix_energy_bound`, `dyadicPrefixPrimitive_tendsto`, `prefixPrimitiveLimit_holder`, `prefixPrimitiveLimit_double`, `prefixPrimitiveLimit_triple` | `Analysis.DyadicInvariantEnergy`, `Analysis.MultiplicativePrefixPrimitive` | Established prefix-energy bound and actual continuous-primitive construction from discrete invariance and square-summable increments. |
| `continuousOn_Ioi_of_sq_increment_le`, `continuousOn_two_three_scaling_const`, `continuousOn_two_three_homogeneous` | `Analysis.PositiveScalingRigidity` | Established continuity and constancy/linearity consequences using the existing irrational prime-log periods. |
| `dyadicBlockAverage_recovery_bound`, `sequence_constant_of_linear_prefix_limit`, `multiplicativeSequence_rigidity` | `Analysis.DyadicBlockRecovery`, `Analysis.MultiplicativeSequenceRigidity` | **Established:** a(2n)=a(3n)=a(n) for positive n and square-summable increments imply a(n)=a(1) at every positive n. No RH or norm-control hypothesis remains. |
| `scaledFloorStep_recovery_lower_bound`, `dyadicFloorStep_recovery` | `Analysis.DyadicCellRecovery` | Established exact floor-cell integral and discrete recovery from the stated vanishing squared-error budget. |
| `hilbertNormalizedTail_scaling`, `hilbertNormalizedTail_increment`, `eq_smul_hilbertOne_of_normalizedTail_constant`, `hilbertNormalizedTail_increment_square_summable_of_dyadic_fixed` | `RH.ThresholdNormalizedTail`, `RH.ThresholdDyadicTailSummability` | Established actual weighted-tail bridge; dyadic adjoint fixedness supplies summability internally through a finite kernel estimate. |
| `hilbertDilationAdjoint_two_three_fixed_iff`, `twoSeed_legalClosure_eq_top_of_full_density`, `twoSeed_density_iff_full_density` | `RH.ThresholdJointAdjointRigidity` | **Established:** actual joint fixed vectors are exactly constants; two-seed density is equivalent to full remainder density. Equality of proper closures is not asserted. |
| `hilbertLegalClosure_eq_top_iff_one_mem`, `hilbertOne_mem_legalClosure_iff_meanOne_variance`, `hilbertOne_mem_legalClosure_iff_meanOne_variance_sequence` | `RH.ParetoMeanOneApproximation` | Established exact equivalences for positive seed sets, full Pareto variance, and all positive integer dilation indices. |
| `riemannHypothesis_iff_twoSeed_closure_of_density_from_rh`, `riemannHypothesis_iff_twoSeed_density_of_density_from_rh`, `riemannHypothesis_iff_twoSeed_meanOne_sequence_of_density_from_rh` | `RH.ThresholdTwoSeedEquivalence` | **Conditional research reduction:** sole remaining input is `PositiveResidueDensityFromRH`; joint rigidity is proved. |
| `PositiveResidueDensityFromRH` | `RH.ThresholdTwoSeedEquivalence` | **Open formalization obligation:** RH implies full positive-remainder density (strong Báez-Duarte/Bagchi theorem). This proposition has no checked provider yet. |

## Minimal seeds, balanced coordinates, and arithmetic charge (14 September 2026)

Source: `RH_Minimal_Seeds_Canonical_Basis_and_Arithmetic_Charge_20260914.md`.
These results use the actual infinite Pareto Hilbert space and finite signed
arithmetic generators. See `RH/MinimalSeedsVerification20260914.md` for scope.

| Declaration family | Modules | Exact status |
|---|---|---|
| `twoSeedAnnihilatorDefects_injective` | `RH.ThresholdAnnihilatorInjection` | Established unconditional injection of the two-seed annihilator into a pair of full-remainder annihilators. |
| `balancedGrid_difference_mem`, `balancedSelected_span_eq_twoSeedSpan`, `rough_grid_decomposition_unique` | `LinearAlgebra.BalancedGridSpan`, `RH.BalancedResidueDictionary`, `RH.BalancedScalarDictionary` | Established exact finite span equality for the valuation rule selecting one original generator per positive dilation. |
| `balancedArithmeticCut_biorthogonal`, `balancedCoefficientCLM_biorthogonal`, `scalarBalancedHilbert_linearIndependent`, `balancedCut_signal_ne_zero_iff` | `LinearAlgebra.BalancedGridCuts`, `RH.BalancedArithmeticCuts`, `RH.ParetoCoordinateEvaluation`, `RH.BalancedContinuousCoordinates`, `RH.BalancedScalarBasis`, `RH.BalancedCoefficientTargets` | Established explicit finite cuts, actual continuous biorthogonality, scalar independence, and complete exact target table. No coordinate-provider assumption remains. |
| `biorthogonal_delete_finite_iff`, `balanced_finite_deletion_iff`, `balanced_exists_minimal_iff_support_approximates`, `hilbertOne_mem_balancedWithoutFourth_iff` | `Analysis.ContinuousBiorthogonalDeletion`, `RH.BalancedMinimalTarget`, `RH.BalancedFourthDeletion` | Established finite deletion and minimal-family characterization. Removing R12-R4 preserves constant approximation but destroys ambient density. Infinite deletion is not inferred. |
| `fullResidueSpan_not_cyclic`, `fullResidueSpan_positive_distance_gap`, `integerSeed_explicit_distance_gap`, `finiteDilationFamily_distance_gap` | `RH.FiniteResidueTemplateObstruction`, `RH.IntegerSeedExplicitGap`, `RH.FiniteDilationFamilyGap` | Established: every fixed finite full-remainder template fails; the integer-seed floor and finite-family common-atom floor are explicit. |
| `two_finite_templates_optimal_of_full_density` | `RH.FiniteResidueTemplateObstruction` | **Conditional research reduction:** full positive-remainder density is explicit. Two seeds then suffice, and every single finite template fails unconditionally. The RH-to-density formal provider remains Open. |
| `physicalRemainderCoefficient_tendsto_of_hilbert_limit`, `twoSeed_smoothComponent_charge_escapes`, `rough_dilationCoefficientMass_tendsto` | `RH.ArithmeticChargeEscape`, `RH.RoughDilationMassLimits`, `RH.ArithmeticChargeHilbertLimits` | Established necessary coefficient limits and signed charge escape along any successful legal sequence. Existence of such a sequence is not asserted. |
| `squarefree_seed_no_hilbert_target_limit`, `squarefree_allowed_ramanujan_no_pointwise_limit`, `omitted_rough_squarefree_dilation_no_pointwise_limit` | `RH.SquarefreeDilationObstruction`, `RH.SquarefreeRamanujanObstruction`, `RH.RoughDilationMassLimits`, `RH.ArithmeticChargeHilbertLimits` | Established failures of squarefree-only dilations and squarefree allowed Ramanujan conductors; every rough squarefree dilation is individually necessary. |
| `total_nonnegative_energy_tendsto_atTop`, `twoSeed_roughComponent_energy_diverges_of_hilbert_limit`, `roughComponent_no_continuous_extension_along_approximants` | `Analysis.PointwiseEnergyDivergence`, `RH.RoughComponentNormDivergence`, `RH.RoughComponentProjection`, `RH.ArithmeticChargeHilbertLimits` | Established discrete Fatou argument and actual filtered-generator projection. Every nonzero rough component has diverging energy along any successful sequence; no continuous extension can agree with it on those approximants. |
| `balancedDictionary_no_series_representation_one` | `RH.SpineSeriesObstruction`, `RH.BalancedSpineSeries` | Established: no fixed coefficients in any enumeration give an ordinary convergent series representation of 1. This does not exclude changing finite coefficient arrays. |
| `BalancedSupportThinning` | `RH.BalancedMinimalTarget` | **Open conjecture:** two-seed density implies approximation of 1 using only the nonzero target support. Recorded as a proposition, not an axiom or theorem. |

The ancillary density value `3/π²` is not formalized here. The pre-existing
`PositiveResidueDensityFromRH` obligation remains Open. These structural
results do not prove RH.

## Signed boundary chords and actual residual charge (16 September 2026)

Source: user-provided boundary-observability handoff, Sections 23–31.
Exact coverage: RH/BoundaryObservabilityVerification20260916.md.

| Declaration family | Modules | Status |
|---|---|---|
| generator_gram_periodic, generator_gram_lcm, generator_gram_digamma, chord_gram_exact | RH.TwoThreeChordGram | Established exact full-tail signed arithmetic Gram formula and actual chord kernel. |
| residual_bilinear_schur, residual_cross_source | Analysis.FiniteHilbertGram | Established bilinear inverse-Gram screening and exact source correction, under actual linear independence. |
| screened_chord_gram, screened_chord_source, innovation_source, innovation_energy | Analysis.ProjectionChordObservability | Established signed screening and nested-source/energy identities; arbitrary-block LDL construction not yet formalized. |
| chord_dilation, chord_norm_sq_dilation, aligned_chord_log_bound | RH.TwoThreeChordGram | Established exact dilation and O(L log(a/L)) aligned dyadic energy, with explicit constants different from 160. |
| gain_ge_sourceSquare, gain_ge_single_correlation, matched_chord_gain | Analysis.ProjectionChordObservability, RH.TwoThreeChordObservability | Established finite projection consumers. Any synthesis/charge bounds in their types are hypotheses, not arithmetic providers. |
| matched_binary_normal, matched_ternary_normal, matchedSpace_mono | RH.TwoThreeChordObservability | Established actual finite-dimensional matched spaces and both normal-equation families. |
| tendsto_zero_of_harmonic_loss | Analysis.ResidualHarmonicGain | Established nonnegative scalar-energy decay, including finite termination. |
| limitingResidual_moments, limitingResidual_charge, positive_charge_pattern_of_not_rh, limitingResidual_mellin_lower_bound | RH.TwoSeedAnnihilatorCharge | Established actual closed-space annihilator/positive-charge consequences and Mellin lower bound. No nonzero pattern constructed unconditionally. |
| riemannHypothesis_of_dyadic_chord_bessel_charge | RH.TwoThreeChordObservability | **Conditional research reduction** to Mathlib's RiemannHypothesis. Uniform signed Bessel and actual-source charge providers: **Open**. |
| riemannHypothesis_of_moment_unique_continuation | RH.TwoSeedAnnihilatorCharge | **Conditional research reduction** to Mathlib's RiemannHypothesis. Infinite moment unique continuation: **Open**. |
| CriticalLineChordGram, FullChordEnergy160 | RH.TwoThreeChordTargets | **Open formalization obligations**, defined propositions only; informal source proofs not imported as axioms. |
| SameScaleChordBessel, BlockBoundaryObservability | RH.TwoThreeChordTargets | **Open mathematical estimates**, defined propositions only. |
## Minimal-support exact heads, common scales, and finite Gram gains (16 September 2026)

Source: `RH/RH_Minimal_Seeds_Continuation_20260916.md`, sections 10–14.
See `RH/MinimalSeedsContinuationVerification20260916.md` for exact scope and
the unformalized analytic portion.

| Declaration family | Modules | Exact status |
|---|---|---|
| `balancedTargetHead_mem_nonzeroTargetSpan`, `balancedTargetHead_exact` | `RH.BalancedHeadInterpolation` | Established actual finite interpolation on the nonzero-target support. No uniform norm bound. |
| `commonDilation_coercivity`, `fifthChargeObserver_sq_le`, `commonScaleRoughPacket_norm_sq_lower` | `RH.CommonDilationCoercivity`, `RH.CommonScaleRepairObstruction`, `RH.CommonScaleRoughPackets` | Established actual signed lower bounds with constants (1+2√2)² and 52, without cross-term deletion. |
| `commonScaleRoughPacket_norm_tendsto_atTop`, `commonScale_repaired_norm_tendsto_atTop` | `RH.CommonScaleRoughPackets`, `RH.CommonScaleRepairObstruction` | Established divergence under explicit persistent-charge and outward-scale hypotheses, including subtraction of bounded packets. |
| `fifthRoughComponentCharge_eq_four`, `fifthRoughComponentCharge_tendsto`, `commonScale_repaired_norm_tendsto_of_approximation` | `RH.CommonScaleApproximationCharge` | Established extraction of the actual four-coordinate charge and its forced limit 1/15 from Hilbert approximation. The divergence application requires the explicit exact identification of the repair coefficient with this extracted charge, with no unproved charge-limit hypothesis. |
| `minimalSeedDampingSymbol_clear_denominator`, `minimalSeedDampingSymbol_undamped`, `minimalSeedPowerDampingResidue_ne_zero`, `minimalSeedPowerDampingResidue_norm_lower` | `RH.MinimalSeedPowerDamping` | Established rational-symbol algebra and quantitative noncancellation of the concrete candidate residue. These do not assert that it is the residue of the actual sequence's Mellin transform. |
| `balancedPowerDampedSequence`, `BalancedPowerDampingNonmembership` | `RH.BalancedPowerDamping` | Actual pointwise arithmetic sequence defined. Nonmembership is an **Open formalization obligation**, recorded as a proposition; the infinite Mellin identity and analytic contradiction remain unproved in Lean. |
| `hilbertOne_mem_closure_of_bounded_exact_heads`, `hilbertOne_mem_closure_of_bounded_exact_head_energy` | `RH.ParetoExactHeadClosure` | Established closure inference from actual bounded coordinate-exact witnesses, with no abstract compactness provider. |
| `BalancedExactHeadEnergy.energy_bddAbove_iff_closure`, `energy_limit_dichotomy` | `RH.BalancedExactHeadEnergy` | Established unrestricted exact-head energy criterion for the proposed minimal support: boundedness iff supported approximation, and limit one or positive infinity. Boundedness is not asserted. |
| `FiniteHilbertGram.gramEquiv`, `residual_completion`, `residual_minimizer_unique`, `additive_inverse_schur_value` | `Analysis.FiniteHilbertGram` | Established complete signed Gram minimum and unique optimizer. The actual inverse is constructed from linear independence. Concrete RH consumer: `RH.BalancedFiniteTailGram`. |
| `BalancedFiniteTailGram.optimizedHead_norm_sq`, `optimizedHead_feasible`, `energy_le_schur_value` | `RH.BalancedFiniteTailGram` | Established specialization to actual finite allowed balanced tails, preserving exact heads. |
| `riemannHypothesis_of_bounded_exact_subspace_heads`, `BalancedExactHeadEnergy.riemannHypothesis_of_energy_bddAbove`, `BalancedFiniteTailGram.riemannHypothesis_of_uniform_tail_gain` | `RH.ParetoExactHeadClosure`, `RH.BalancedExactHeadEnergy`, `RH.BalancedFiniteTailGram` | **Conditional research reductions:** conclude Mathlib's actual `RiemannHypothesis`. The respective uniform witness, energy, or finite signed-gain bound is **Open**, with no provider supplied here. |

The minimal-support thinning conjecture and the RH-to-full-density formal
provider remain Open. This continuation does not prove RH.

## Gibbs contraction, legal wavelets, and arithmetic repair (9 September 2026)

Source: the chat research development and
`RH_Contracting_Evolution_and_Arithmetic_Repair_2026-09-08.md`, together with
the general component and distributed-repair notes. These declarations concern
the actual infinite Pareto Hilbert space, the actual signed legal arithmetic
generators, and full errors. They do not establish RH. See
`RH/ChatFormalizationCoverage20260909.md` for the claim-by-claim scope and open
formalization obligations.

Names in the analytic rows have prefix `RiemannResearch.RH.Pareto`.

| Declaration family | Modules | Established scope |
|---|---|---|
| `gibbsAction_pairing_symm`, `gibbs_dirichlet_identity`, `gibbs_conditional_loss_identity`, `gibbsAction_fixed_iff_constant` | `RH.ParetoGibbsOperator`, `ParetoGibbsEnergy`, `ParetoGibbsPositive` | Infinite kernel normalization, full weighted square summability, reversible positivity, exact energy losses, and constant fixed space |
| `hilbertGibbsContinuous`, `hilbertGibbsContinuous_isSelfAdjoint`, `hilbertGibbsIterate_tendsto` | `RH.ParetoGibbsHilbert`, `ParetoGibbsHilbertEnergy`, `ParetoGibbsConvergence` | Actual bounded positive self-adjoint operator and unconditional strong convergence of every iterate to the weighted mean |
| `tailBasis_inner`, `tailBasisSpan_closure`, `tailBasis_gibbs_inner` | `RH.ParetoGibbsTailBasis`, `ParetoGibbsTailMatrix`, `ParetoGibbsHankel` | Actual orthonormal basis for the mean-zero closure and exact infinite-operator matrix; these analytic basis vectors are not asserted to be legal arithmetic vectors |
| `gibbsSchurGamma_row_hasSum`, `gibbsComplementKernel_quadratic_le`, `paretoGibbsSharpGap` | `RH.ParetoGibbsSchur`, `ParetoGibbsSchurGamma`, `ParetoGibbsSchurEnergy`, `ParetoGibbsSpectralGap`; `Analysis.PositiveQuadraticNorm` | Exact Gamma row, uniform Schur estimate, and unconditional norm contraction by pi/4 on the whole mean-zero space |
| `gibbsSchur_truncation_defect_le`, `hilbertGibbs_meanZero_optimal_constant_iff`, `hilbertGibbsMeanZeroContinuous_norm` | `RH.ParetoGibbsGammaTruncation`, `ParetoGibbsGammaDefect`, `ParetoGibbsOptimality` | Explicit Gamma-weighted truncations have unbounded norms and bounded Rayleigh defects; the actual restricted operator norm is exactly pi/4. No complete spectral-set claim is inferred |
| `hilbertWaveletClosure_eq_legal`, `twoSeed_waveletClosure_eq_legal` | `RH.DilationWaveletAlgebra`, `DilationWaveletClosure` | Exact period cancellation, geometric infinite tail bounds, and equality of actual full wavelet and legal closed spaces |
| `binary_wavelet_hilbert_gram_bound`, `normalizedBinaryWavelet_adjacent_tendsto_zero`, `normalizedBinaryWavelet_no_uniformLowerRiesz` | `RH.BinaryWaveletPrimitive`, `BinaryWaveletNearbySupport`, `DilationWaveletBinaryNorm`, `DilationWaveletOffScale`, `DilationWaveletNearbyEnergy`, `DilationWaveletNoRiesz`; `Analysis.BoundedPrimitiveAbel`, `NormalizedPairObstruction` | Exact binary norm pi/(4m), full signed Abel Gram identity, off-scale and nearby-scale estimates, and failure of any positive uniform lower Riesz bound |
| `paretoMean_residue`, `paretoMean_dilationWaveletSequence`, `initialLegalMeanOne_mean` | `RH.ParetoResidueLogMean`, `GibbsLegalSeed` | General logarithmic means, binary geometric-tail constant, and an actual finite legal mean-one initial vector |
| `geometricTransform_residue_generator`, `paretoStep_energy_identity` | `RH.ParetoCyclotomicTransform`, `ParetoWaveletTransform`, `ParetoStepIsometry` | Actual scalar transforms of legal generators/wavelets and exact step-function integral isometry under weighted square summability |
| `hilbertGibbs_repair_energy`, `hilbertGibbs_repair_convergence`, `hilbertGibbs_legal_repair_iff_closure_unconditional` | `RH.ThresholdContractiveRepair`, `ParetoGibbsRepair`, `ParetoGibbsSpectralGap`; `Analysis.ContractiveRepair`, `MeanNormalization`, `ContractiveRepairClosure` | Exact mixed-energy identity; vanishing actual errors suffice without summability; existence of a legal repair orbit is equivalent to target membership in the legal closure. Existence itself remains open |
| `hilbertOne_mem_legalClosure_of_gibbs_invariance`, `riemannHypothesis_of_gibbs_invariance`, `riemannHypothesis_of_gibbs_repair` | `RH.GibbsArithmeticResearchTargets` | Conditional research reductions. Only legal Gibbs invariance/repair remains an unresolved input; the approximation-to-RH implication is supplied by `riemannHypothesis_of_twoSeed_closure`. |
| `RH.FiniteBoundaryRepair.smooth_finite_boundary_fullError_lower` | `RH.FiniteRepairTriangular`, `FiniteBoundaryRepairObstruction` | For N ordered balanced repair endpoints, the actual full-error floor is 1/[72((3/2)^N-1)^2], with genuine root-charge and slope hypotheses explicit |
| `RH.DistributedRepair.fullError_distributed_completion`, `RH.FiniteBalancedRepair.balancedFloor_mem_legalSeedSpan` | `RH.DistributedRepairCompletion`, `SmoothRepairAntichain`, `FiniteBalancedRepairSynthesis` | Every mixed/remainder/tail term is retained; explicit smooth divisibility antichains and actual finite legal synthesis under component balance |
| `RH.DivisorComponentJumpRow.componentCharge_eq_totient_jumps`, `smooth_seed_fullError_lower`, `smooth_jumpWeight` | `RH.ComponentJumpGram`, `DivisorComponentJumpRow`, `DivisorComponentNormBound`, `SmoothComponentClosedFloor`, `SmoothComponentJumpWeights` | Actual totient jump row and norm bound; full-error floor 2/[(A+4)(4B+9)] for every A,B>0 and complements coprime to 6; explicit interior and boundary weights |

**Open obligations:** construct finite legal mean-one Gibbs repairs with errors
tending to zero, and prove the RH-to-approximation converse. The forward
approximation-to-RH implication is now established. The exact named
specifications now have the providers recorded below for Mellin, Plancherel,
zero projection, both wavelet identities, covariance/variance and full geometric
Hilbert realization. The complete spectrum and Meixner expansion remain open.
A `Prop` definition alone records a statement; its separate provider supplies
a proof. The remaining named obligations are listed explicitly below.
Finite experiments are not used as hypotheses or extrapolated to convergence.

**Closed on 14 September 2026:** `RH.ArithmeticGeneratorLogFlux` supplies
`arithmeticGeneratorCutoffFlux_eq_harmonic`,
`arithmeticGeneratorCutoffFlux_tendsto_log`, and
`arithmeticGeneratorLogFlux_proved : ArithmeticGeneratorLogFluxTarget`.
These retain arbitrary finite cutoffs and prove the logarithmic limit from
the exact Pareto mean with a vanishing Abel boundary term. No open hypothesis
or RH assumption remains in this target.

**Closed on 14 September 2026:** `RH.ArithmeticMellinPositiveHalfPlane`
supplies `arithmeticMellinIdentityTarget_proved : ArithmeticMellinIdentityTarget`.
The generator integrability and integral formula now hold for Re(s) > 0
(away from s = 1 for the formula); finite legal synthesis proves the exact
requested strip identity. The zero-projection target is now also closed below;
the Plancherel target is closed below as well.


**Closed on 14 September 2026:** `RH.GeometricDifferentialProofs` supplies
`geometricCovarianceDerivativeTarget_proved : GeometricCovarianceDerivativeTarget`.
For every bounded real sequence and 0 < t < 1, the centered covariance series
is absolutely summable and equals t times the actual derivative of its
geometric transform. The proof establishes a locally summable derivative bound.

**Closed on 14 September 2026:** the same module supplies
`geometricDifferentialVarianceTarget_proved : GeometricDifferentialVarianceTarget`.
The exact centered second moment and covariance identity give the complete
infinite regression decomposition, with no finite truncation assumption.

**Supporting theorem, 14 September 2026:** `Analysis.FourierL1L2Plancherel`
proves agreement almost everywhere between the actual Fourier integral and
Mathlib's unitary L2 Fourier transform for L1 ∩ L2 functions, and hence the
full ordinary-integral Plancherel identity.

**Closed on 14 September 2026:** `RH.ArithmeticZeroProjectionProof` supplies
`arithmeticZeroProjectionTarget : ArithmeticZeroProjectionTarget`.
For any zeta zero with 1/2 < Re(ρ) < 1 and every finite legal arithmetic
combination, the full Pareto error equals the exact zero-mode contribution
plus the complete continuous squared residual integral. This is the original
conditional-on-a-zero statement; it assumes no unproved analytic provider.

**Closed on 14 September 2026:** `RH.ArithmeticPlancherelProof` supplies
`arithmeticPlancherelTarget_proved : ArithmeticPlancherelTarget`.
The complete Pareto error equals the actual continuous critical-line spectral
integral with its exact 1/(2π) normalization, for every finite legal arithmetic
combination. The logarithmic lift is proved L1 and L2; no truncation or
additional spectral identity is assumed.

**Closed on 14 September 2026:** `RH.GeometricHilbertRealizationProof` supplies
`geometricHilbertRealizationTarget_proved : GeometricHilbertRealizationTarget`.
This constructs the actual continuous linear contraction into geometric L2,
proves its almost-everywhere series realization and coordinate integral
adjoint, and identifies its adjoint composition with the full Gibbs operator.
The theorem applies to every ThresholdHilbert vector, not only bounded ones.

**Closed on 14 September 2026:** `RH.BinaryWaveletAdjacentAsymptotic` supplies
`binaryWaveletAdjacentAsymptotic_proved : BinaryWaveletAdjacentAsymptoticTarget`.
The exact normalized adjacent-wavelet squared distance has leading term
(6/π) log(m)/m and a proved O(1/m) remainder. The proof uses the exact arithmetic
head, an absolute bound on the entire tail, and the exact wavelet norm.

**Closed on 14 September 2026:** `RH.BinaryWaveletContinuousGram` supplies
`binaryWaveletContinuousGram_proved : BinaryWaveletContinuousGramTarget`.
It proves the exact signed Gram formula using the actual continuous primitive,
an absolutely convergent arithmetic jump series, and the complete continuous
correction integral. Unit-cell identities retain all endpoints before taking
the infinite limit.

**Supporting theorem, 14 September 2026:** `Analysis.NatStepIntegral` proves
the complete Lebesgue integral of an absolutely summable unit-cell step
function and its exact rescaling for every positive real mesh parameter.

**Supporting theorem, 14 September 2026:** `Analysis.CosineReciprocalIntegral`
proves the exact positive-half-line integrals of (1 − cos u)/u² and
1 − cos(1/x), both equal to π/2, by ordinary-integral Plancherel for the
unit-interval indicator and an explicit reciprocal change of variables.

**Closed on 14 September 2026:** `RH.ParetoCosineMassAsymptotic` supplies
`CompressedMellin.cosineMassAsymptotic : CosineMassAsymptotic`.
The complete original cosine mass divided by t tends to π as t tends to
positive infinity. Exact step integration, a logarithmic phase squeeze, and
dominated convergence with majorant 4/(1+x²) retain the whole infinite series.

**Bottom-up continuation, 14 September 2026:**
`RH.ParetoCompressedMellinUniformBound` proves `cosineMass_le_linear`,
`compressedMellinEnergy_le_two`, and `compressedMellinEnergy_le_seven_div`.
The complete energy is at most 7/t for every t ≥ 1, with an exact infinite-tail
split. This closes the scalar energy estimate needed by the phase-centered
provider; the full operator and derivative provider remains a separate target.

`RH.PairedMellinFrequencies` proves `pairedMellinFrequencies`: every real
r ≥ 4 admits positive dyadic/triadic resonance frequencies with maximum at
most 64r² and difference at most min(1,16/r²). The finite-cutoff Dirichlet
theorem supplies every scale; no continued-fraction growth hypothesis is used.

**Bottom-up reduction proved:** `RH.PairedMellinFromPhase` supplies
`actualPairedMellinProvider_of_phase : PhaseCenteredAnalyticProvider → ActualPairedMellinProvider`.
The verified cutoff resonance selection and a common normalization supply witnesses
for every 0 < δ ≤ 1 with C = 400000. The analytic provider is now constructed below; applying this reduction
supplies the actual paired witnesses.

**Bottom-up analytic construction proved:** `RH.PhaseCenteredActualOperator`
defines the actual bounded phase-centered Mellin operator, proves its complete
unit-cell pairing identity, its exact mean norm, and annihilation of each closed
single-seed space at every positive arithmetic resonance. The quantitative norm
and derivative estimates are recorded separately.

**Bottom-up kernel foundation proved:** `RH.ParetoMellinKernelPairing` constructs
bounded integral pairings on the actual Threshold Hilbert space, proves all
logarithmic Mellin kernels square-integrable, and supplies a global quadratic
remainder bound for imaginary exponentials.

**Bottom-up sharp pairing bound proved:** `RH.WeightedComplexPairingBound`
proves absolute summability and the weighted complex Cauchy inequality for every
actual physical Hilbert vector. Its operator-energy bound uses the real carrier
without identifying a real-to-complex operator norm with complex Riesz energy.

**Bottom-up actual operator norm proved:** `RH.PhaseCenteredOperatorUniformBound`
proves full square summability of the phase-centered cells and
`actualPhaseCenteredOperator_norm_sq_le_seven_div` for every real t ≥ 1.
The bound applies to the actual operator representing the original pairing.

**Bottom-up logarithmic head estimate proved:** `Analysis.LogarithmicMellinHead`
proves the complete finite bound ∑_{k=1}^N log(t/k)^2 ≤ 2t whenever 1 ≤ t
and N ≤ t, using an explicit compact-interval primitive and monotone sum–integral
comparison.

**Bottom-up complete logarithmic tails proved:** `Analysis.LogarithmicMellinBounds`
proves the exact integral of log(x/t)^2/x^2 over every positive tail. It bounds
the tail by 4/t when its boundary lies in [t/2,t], and bounds the entire tail
from 1 by 2 for frequencies 1 ≤ t ≤ 2.

**Bottom-up operator differentiation proved:** `RH.ParetoMellinOperatorDerivative`
proves a uniform quadratic remainder in operator norm for the actual Mellin
functional on the line Re(s)=1, and hence `mellinLineOperator_hasDerivAt`.
This differentiates the full bounded operator, with no pointwise-only premise.

**Bottom-up centered operator derivative proved:** `RH.PhaseCenteredOperatorDerivative`
proves differentiability of the actual phase-centered operator at every t > 0,
identifies its operator derivative, and proves the exact continuous centered
logarithmic kernel formula on the complete physical half-line.

**Bottom-up differentiated cell estimates proved:** `RH.PhaseCenteredDerivativeCells`
proves the exact centered logarithmic cell integral, its complete boundary estimate,
and the finite-head energy bound 28/t. These are estimates for the actual physical
unit-cell integrals, with no omitted crossing cell.

**Bottom-up complete derivative estimate proved:** `RH.PhaseCenteredDerivativeBound`
proves `actualPhaseCenteredDerivativeOperator_norm_bound : ∀ t ≥ 1, ‖q′(t)‖² ≤ 82/t`.
The actual integral splits at floor(t): finite head energy 28/t and complete tail
energy 4/t yield 64/t for t > 2; the small-frequency interval is handled directly.

**Closed on 14 September 2026:** `RH.PhaseCenteredAnalyticProviderProof` supplies
`phaseCenteredAnalyticProvider_proved : PhaseCenteredAnalyticProvider` with the
original operator, every original quantifier, and both original constants 7 and 82.
All six analytic clauses are proved on the actual Threshold Hilbert carrier.

**Closed on 14 September 2026:** `RH.ActualPairedMellinProviderProof` supplies
`actualPairedMellinProvider_proved : ActualPairedMellinProvider`. The construction
uses C = 400000 and δ₀ = 1 and covers every 0 < δ ≤ 1. Its unconditional
corollaries exclude an exact decomposition into the separately closed seed spaces
and force reciprocal-error growth in both approximating channels. They do not
exclude membership in the closure of the joint sum and do not settle RH.

### Named-target proof audit — 14 September 2026

Eighteen named specifications were proved with their original types. Each proof
was independently committed and pushed after the affected-module build.
Axiom inspection of every provider found only propext, Classical.choice and
Quot.sound: no admitted proofs or additional project axioms. The seven named
specifications below remain unproved; this work does not claim to close them.

| Proved specification | Proof commit |
|---|---|
| `ArithmeticGeneratorLogFluxTarget` | `bd69610` |
| `ArithmeticMellinIdentityTarget` | `b4280cb` |
| `ContinuousParetoRealizationTarget` | `7353281` |
| `DyadicCoefficientPolynomialProvider` | `a706595` |
| `EveryBudgetFeasibleTarget` | `80b770f` |
| `EveryBudgetOptimizerTarget` | `a84595e` |
| `RamanujanOrdinaryMomentsTarget` | `64d0e9e` |
| `RamanujanLaguerreCancellationTarget` | `16f4554` |
| `GeometricCovarianceDerivativeTarget` | `b9f9871` |
| `GeometricDifferentialVarianceTarget` | `c40e5a3` |
| `ArithmeticZeroProjectionTarget` | `ec1ac86` |
| `ArithmeticPlancherelTarget` | `c627cac` |
| `GeometricHilbertRealizationTarget` | `c5b04c4` |
| `BinaryWaveletAdjacentAsymptoticTarget` | `890100b` |
| `BinaryWaveletContinuousGramTarget` | `13f7321` |
| `CosineMassAsymptotic` | `a394d21` |
| `CompressedMellin.PhaseCenteredAnalyticProvider` | `90234ac` |
| `CompressedMellin.ActualPairedMellinProvider` | `f6f316e` |

The earlier batch included four supporting results, separately verified and published: log-moment
dilation (`315527b`), ordinary-integral Fourier Plancherel (`a56859d`),
exact natural-step integration (`2fef128`), and cosine reciprocal integrals
(`76fbf60`).

The actual Laguerre Parseval obligation is now supplied unconditionally by
`RamanujanLaguerre.actualParsevalTarget` in `RH/ActualLaguerreParseval.lean`.
It proves summability of the nonconstant coefficient squares and their exact
equality with the full mean-one Pareto error. The stronger
`hasSum_coefficient_sq_of_bounded` includes the constant mode for every bounded packet.
The supporting modules establish exponential-moment measure determinacy,
polynomial-annihilator uniqueness, the exponential-measure L2 realization,
actual Laguerre orthonormality, and the complete basis `Analysis.laguerreBasis`.
The assembled exact target passed Lean with only `propext`, `Classical.choice`,
and `Quot.sound`; no RH, completeness, or uniform-energy input is assumed.

All names in the remaining table lie under `RiemannResearch.RH.Pareto`;
subnamespaces are shown. These are formalization gaps, not refutations.

| Remaining specification | Missing proof |
|---|---|
| `GeometricMeixnerParsevalTarget` | Complete geometric-weight orthogonal expansion and identification of all derivative coefficients. |
| `paretoGibbsFullSpectrumTarget` | Spectral representation of the actual operator proving exactly [0, π/4] ∪ {1}. |
| `ClassicalQuantitativeMertensBound` | The precise Möbius cancellation bound with exp(−c√log(2x)); the vendored log-power-nine zero-free strip does not supply it. |
| `DyadicUniformSignedArithmeticDiscrepancyBound` | Uniform weighted partial summation for the actual coefficients, including the stated compensator and all epsilon parameters. |
| `ResearchTargets.SummablePrimeRepairs` | A quantitative logarithmic relative-gap estimate for leastSmooth35Above; the subsequent summability reduction is already proved. |
| `ThresholdRiemannHypothesisBridgeTarget` | Reverse RH-to-two-seed closure implication: RH implies full positive-residue density, and the joint adjoint-rigidity input of `ThresholdTwoSeedConverse` must be verified. The forward closure-to-RH implication is proved. |

Uniform moment-optimizer costs and the main Gibbs-repair approximation
construction also remain separate open obligations. Finite-budget existence,
the analytic identities above, and failed searches for missing infrastructure
are not proofs of those uniform or RH-related conclusions.

## Period-5040 gain, general component charges, and boundary-repair obstruction (8 September 2026)

These results concern actual signed two-seed generators and complete infinite
Pareto error. The exact finite certificates and obstruction identities use no RH
or numerical optimality premise. General matrix and distributed-repair research
is recorded separately; its uniform upper estimate remains open.

| Declaration family | Module | Established scope |
|---|---|---|
| `Analysis.lower_certificate_of_cross_mul`, `residue_lower_common_denominator` | `Analysis.LowerCertificateArithmetic` | Exact real bridges from signed integer lower certificates |
| `RH.TwoSeedThreshold.legalWitness5040_upper_certificate` | `RH.ThresholdSeedPowerCertificate5040` | Explicit rational witness; all 5040 residue caps and exact periodicity |
| `RH.TwoSeedThreshold.legalWitness5040_mem_legalSeedSpan`, `legalWitness5040_full_error_lt` | `RH.ThresholdSeedPowerInfinite5040` | Actual legal witness; summability and exact residue regrouping; full error <39/1000 |
| `RH.TwoSeedThreshold.conductor2520Generator_exhaustive`, `conductor2520Combination_full_error_gt` | `RH.ThresholdConductor2520DualLower` | All 68 legal generators covered and annihilated; every signed combination has full error >419/10000 |
| `RH.TwoSeedThreshold.legalWitness5040_uniform_improvement` | `RH.ThresholdSeedPowerGain` | Strict full-error gain >29/10000 over the entire period-2520 space; >149/9000 over every balanced single-boundary repair in the proved smooth-endpoint class |
| `RH.FiniteSeedComponentCharge.mobiusDifference_generator`, `componentFiniteError_exact` | `RH.FiniteSeedComponentCharge` | Actual endpoint divergence; arbitrary finite closed components; exact finite Riesz square remainder and full-error bound |
| `RH.seedEdge_dvd_component_iff`, `twoSeed_dvd_component_iff` | `RH.DivisorComponentArithmetic` | Divisor-component closure for legal edges in D*r when the complementary factor is coprime to the seed |
| `RH.divisor_moebius_signal_eq_totient_div`, `divisor_moebius_signal_pos` | `RH.DivisorComponentSignal` | Exact target charge phi(D)/D and its positivity for every D>0 |
| `RH.DivisorSeedComponentObstruction.divisorComponent_seedCombination_fullError_lower` | `RH.DivisorSeedComponentObstruction` | Explicit positive finite-norm error floor for fixed D>0, uniformly over all r coprime to 6 and all signed legal combinations in D*r |
| `RH.CoupledSeedComponentObstruction.conductor_seedCaps_four_two_coupled_fullError_lower`, `coupled_component_gram_completion` | `RH.CoupledSeedComponentObstruction` | Exact mixed-component completion; full error >=272/15927 when 32 and 27 both fail to divide the conductor |
| `RH.OneBoundaryRepair.adjacent_error_completion`, `smooth_single_boundary_fullError_lower` | `RH.OneBoundaryRepairObstruction` | Balanced actual Mobius-head floor repairs with one smooth root endpoint have full error >=1/18; all other endpoints are positive and do not divide the root endpoint; smoothness and summability discharged |

**Next research target:** jointly optimize the head and distributed component
repairs under exact charge balance, retaining every mixed and tail term. Numerical
tests favor permitting head error, but the tested sparse antichains do not beat the
established certificates. The period-15120 comparison is a useful next certificate target.
The closed-form seed-exponent bound and bounded-number repair extension are
now proved in the 9 September addition above. The full coupled-component network
and antichain convergence analysis remain research obligations. No convergence
to zero or RH is established here.

## Prime-seven gain and seed-power obstructions (8 September 2026)

The new rational witness certifies the jointly reoptimized enlargement from period
360 to 2520. Every old generator is retained; all signed coefficients and the full
infinite weighted error are included. No numerical-optimality or RH premise is used.

| Declaration family | Module | Exact scope |
|---|---|---|
| `Analysis.upper_certificate_of_cross_mul`, `residue_upper_common_denominator` | `Analysis.UpperCertificateArithmetic` | Generic denominator-clearing bridge and exact progression upper-weight formula |
| `RH.TwoSeedThreshold.conductor360Generator_exhaustive`, `conductor360Combination_full_error_gt` | `RH.ThresholdConductor360DualLower` | All 34 allowed endpoint pairs covered; every signed old combination has full error >27/625 |
| `RH.TwoSeedThreshold.legalWitness2520_upper_certificate` | `RH.ThresholdPrimeSevenCertificate2520` | Explicit rational witness, exact periodicity, all 2520 integer residue certificates, finite bound <421/10000 |
| `RH.TwoSeedThreshold.legalWitness2520_mem_legalSeedSpan`, `legalWitness2520_full_error_lt` | `RH.ThresholdPrimeSevenInfinite2520` | Actual legal span, summability, exact residue regrouping, and full infinite error <421/10000 |
| `RH.TwoSeedThreshold.legalWitness2520_uniform_improvement` | `RH.ThresholdPrimeSevenGain` | Strict improvement >11/10000 over every old period-360 combination; bounded current seed powers cannot halve the new witness error |
| `RH.PrimeDefectEnergy.finiteError_joint_completion`, `signed_seed_joint_forcedMass`, `conductor_omitting_seven_fullError_lower` | `RH.PrimeDefectEnergy` | Exact coupled signed prime-5/7 square completion; full coefficient-mass bounds; conductors omitting 7 have error at least 1/100 |
| `RH.SquarefreeConductorObstruction.conductor_seedValuations_fullError_lower`, `legalWitness360_beats_conductors_with_small_seedValuations` | `RH.SquarefreeConductorObstruction` | If 4 and 9 both fail to divide the conductor, every signed approximation has error at least 2/45; the old period-360 witness beats this entire infinite family |
| `RH.BoundedSeedConductorObstruction.conductor_seedCaps_three_two_fullError_lower` | `RH.BoundedSeedConductorObstruction` | If 16 and 27 both fail to divide the conductor, every signed approximation has error at least 2/95, independently of all other prime factors |

**Continuation completed above:** period 2520 to 5040 is certified, and the
general divisor-component functional now has a proved positive signal and exact
finite Riesz completion. The closed-form exponent bound is now proved in the
9 September addition; uniform residual capture remains a research obligation.
None of these results establishes RH.

## Signed seed constraints and certified finite gains (8 September 2026)

These are unconditional finite-space and full infinite-error results for the actual
seed-2/seed-3 generators and Pareto weights. They do not prove norm convergence or RH.
The prime-five enlargement retains arbitrary signed coefficients and the full weighted
error. The lower certificate checks all twelve period-dividing-36 generators;
an exhaustive-coverage theorem proves that every allowed seed/dilation pair
appears in this list.

| Declaration family | Module | Exact scope |
|---|---|---|
| `Analysis.periodic_square_error_bound` | `Analysis.PeriodicSquareBound` | A generic finite uniform bound for the squared error of a sequence with a positive period |
| `LinearAlgebra.weighted_error_dual_exact`, `weighted_error_lower_of_dual` | `LinearAlgebra.WeightedDualCertificate` | Generic exact weighted square identity and dual lower bound; positive weights and annihilation explicit |
| `RH.TwoSeedThreshold.legalWitness180_full_error_lt`, `legalWitness360_full_error_lt` | `RH.ThresholdPrimeFiveInfinite180`, `RH.ThresholdPrimeFiveInfinite360` | Explicit legal witnesses with full infinite squared error <47/1000 and <44/1000; summability, regrouping and tail enclosure proved |
| `RH.TwoSeedThreshold.conductor36Generator_exhaustive`, `conductor36Combination_full_error_gt` | `RH.ThresholdConductor36DualLower` | Every allowed conductor-36 generator appears among the twelve indexed generators; every indexed combination has full squared error >49/1000 |
| `RH.TwoSeedThreshold.legalWitness180_uniform_improvement`, `legalWitness360_uniform_improvement` | `RH.ThresholdPrimeFiveGain` | Strict full-error improvements exceeding 2/1000 and 5/1000 over every old combination |
| `RH.PositiveSeedCone.generator_defects_exact`, `finiteError_completion`, `positive_seed_cone_full_lower` | `RH.PositiveSeedCone` | Exact prime-five/seven defects; arbitrary nonnegative finite seed combinations have full error at least 37/1299, with summability discharged |
| `RH.PositiveSeedCone.signed_seed_primeFive_forcedMass`, `signed_seed_exists_negative_primeFive` | `RH.PositiveSeedCone` | Arbitrary signed finite combinations satisfy the prime-five square bound; error <1/52 forces a negative coefficient at dilation 5 |

The finite upper certificates live in `RH.ThresholdPrimeFiveCertificate180` and
`RH.ThresholdPrimeFiveCertificate360`. These use exact rational arithmetic, with no
numerical-optimality assumption. The positive-cone constant is sharp for the two-defect
halfspace relaxation; no attainment assertion for the actual positive cone is made.

**Open obligations:** the general arithmetic-component transport theorem, four-gcd
covariance and centered Abel tail estimate, quantitative Mellin lift obstruction, and
any scalable residual-capture estimate are research arguments or targets in the
accompanying note, not consequences claimed for this formalization.

**Completed finite target:** the jointly reoptimized enlargement from conductor
360 to 2520 is now certified above, retaining all old generators and the full error.
For asymptotic work, use cofinal periods such as `lcm(1,...,N)` so that every
positive integer dilation, including higher prime powers, eventually appears.

## Two-seed threshold paper: partial formalization (8 September 2026)

Kernel-checked support results below do not prove the paper's main RH equivalences. The September 8, 32-page edition has 195 source labels. See `RH/ThresholdPaperCoverage.md` for the historical 151-label audit and `RH/ThresholdAffineCoverage.md` for the 22-module extension, all 44 new Section 11 labels, exact hypotheses, and open obligations. Names have the common prefix `RiemannResearch` unless an ordinary algebraic namespace is shown.

| Declaration family | Module | Exact scope |
|---|---|---|
| `CoarseLift.coarse_lift_energy_lower_bound` | `Analysis.CoarseLiftObstruction` | Exact signed Hilbert coarse-lift obstruction; symmetric map and annihilator explicit |
| `WeightedFiniteProjection.fiber_pairwise_variance`, `fiber_defect_eq_zero_iff`, `optimal_partial_correction` | `LinearAlgebra.WeightedFiniteProjection` | Actual finite weighted error, defect nullspace and scalar repair; mass/positivity hypotheses explicit |
| `Pareto.progressionWeight_certificate_bounds`, `progressionWeight_partial_split` | `RH.ParetoProgressionTails` | Actual infinite progression masses, exact heads and certified tails |
| `Pareto.progressionWeight_normalization`, `progressionWeight_compatibility`, `periodic_paretoInner_mixed` | `RH.ParetoPeriodicRegrouping` | Positive compatible weighted finite quotients and exact periodic mixed norms |
| `Pareto.legalSeedSpan_dilation`, `power_seed_mem_legalSeedSpan`, `paretoMean_rawPullback` | `RH.ThresholdDilationAlgebra` | Every positive integer dilation, legal span and boundary pushforward |
| `Pareto.weighted_square_dilation`, `paretoMean_dilation_of_square`, `paretoInner_dilation_boundary_of_square` | `RH.ThresholdDilationEnergy` | Arbitrary real weighted square-summable input; exact norms, means, mixed laws and anchor anomaly |
| `TwoSeedThreshold.legalWitness36_full_error_lt`, `legalWitness36_mem_legalSeedSpan` | `RH.ThresholdFiniteCertificate`, `RH.ThresholdInfiniteCertificate` | Genuine legal period-36 full squared error <53/1000; no unresolved analytic or RH premise |
| `TwoSeedThreshold.period36Basis_linearIndependent`, `period36_omitted_3_2`, `period36_omitted_3_4`, `period36_omitted_3_6`, `period36_omitted_3_12` | `RH.ThresholdPeriod36Basis` | Exact independence of eight functions and four omitted-generator identities; not coarse-6 rank |
| `Pareto.hilbertSequence_range`, `hilbert_norm_weighted_sq`, `hilbertDilation_comp`, `hilbertDilationAdjoint_one` | `RH.ThresholdHilbertSpace`, `ThresholdHilbertDilation`, `ThresholdHilbertMean` | Actual complete real weighted H, all-positive-integer bounded dilations/isometries, exact inner product, mean and adjoint-fixed unit target; joint rigidity remains open |
| `Pareto.hilbertLegalClosure_dilation`, `hilbertLegalClosure_power_list` | `RH.ThresholdHilbertLegal` | Actual legal closures in H, all-integer invariance and common-base finite-list classification |
| `Pareto.legalSeedSpan_list_gcd_one`, `legalSeedSpan_prime_eq_packetSpan`, `legalSeedSpan_error_summable` | `RH.ThresholdSeedEuclidean`, `ThresholdPrimePackets`, `ThresholdLegalIntegrability` | Actual algebraic synthesis and prime-packet identification; full finite-legal error is summable; no density/RH conclusion |
| `TwoSeedThreshold.phaseDelta_le_twelfth_weight`, `phaseDelta_lower_correction`, `universalPhaseConstant_certificate` | `RH.ThresholdPhaseConstant`, `ThresholdPhaseSharpBound`, `ThresholdPhaseLowerBound`, `ThresholdPhaseTail` | Actual logarithmic phase constant, two-sided tails with cubic correction 1/[144(N+1)^3], and exact rational enclosure; arithmetic witness identification remains open |
| `Analysis.PhaseWitness.error_eq_floor_add_excess`, `error_eq_floor_iff` | `Analysis.PhaseWitnessGeometry` | Conditional research reduction: arithmetic witness, its moments and legal annihilation are explicit open inputs |
| `WeightedFiniteQuotient.averageMatrix_apply`, `average_tower`, `error_decomposition`, `defect_finrank` | `LinearAlgebra.WeightedFiniteQuotient`, `WeightedQuotientDefectRank` | Actual weighted finite matrices, full projection defect and ambient complementary rank; nonzero masses explicit |
| `Pareto.refinementAverage_formula`, `refinement_error_decomposition`, `progressionWeight_refinement_tower` | `RH.ThresholdWeightedCRT` | Concrete specialization to genuine infinite progression weights for every positive integer refinement factor |
| `Pareto.affineBranch_positive_partition`, `affineBranchCoefficient_uniform_defect`, `affineProjection_block_discrepancy` | `RH.ThresholdAffineBranches`, `ThresholdAffineProjectionBlocks` | Actual arithmetic head, normalized weighted branch coefficients and finite projection blocks; infinite operator and HS assembly remain open |
| `Ring.compression_product_defect`, `hom_difference_cocycle`; `StarRing.compression_square_defect_finite_gram`; `Real.unit_rankOne_difference_sum_sq` | `LinearAlgebra.CompressionProductDefect`, `RankOneProjectionDistance` | Exact ordered operator algebra and complete finite mixed Gram/rank-one identities |
| `LinearAlgebra.SpectralCutoff.diagonal_half_cutoff`, `certified_half_cutoff_bounds`, `repeatedError_nondecreasing` | `LinearAlgebra.SpectralCutoffRepair`, `SpectralRepeatedFit`, `SpectralDiagonalRealization` | Explicit finite diagonal synthesis, factor-two bounds and repeated-fit full-error growth; actual weighted legal covariance realization remains open |

## Bounded exact interpolation and weighted CRT target (9 September 2026)

See [RH/ThresholdBoundedInterpolation.md](RH/ThresholdBoundedInterpolation.md) for the exact minimum-norm argument, capacity dichotomy, finite-head construction, all-component two-seed charge constraints, and weighted CRT Schur-complement target.

| Declaration family | Module | Exact scope / status |
|---|---|---|
| `Analysis.BoundedInterpolation.cauchySeq_of_bounded_exact_energy`, `exists_minimum_head`, `minimum_head_pythagoras`, `exists_exact_heads_tendsto_of_bounded` | `Analysis.BoundedInterpolation` | Established Hilbert-space support: actual closed-subspace projections, exact minimum-head completion, and strong convergence plus exact target error from an explicit uniform interpolation bound. |
| `Pareto.hilbertLegalClosure_of_bounded_exact_heads` | `RH.ThresholdBoundedInterpolation` | **Conditional research reduction:** uniformly bounded finite legal exact heads imply membership of the actual unit target in the genuine weighted legal closure. All positive integer dilations remain available. |

- **Open:** provide uniformly bounded full squared norms for finite legal exact interpolants, in particular for seeds {2, 3}.
- **Open:** prove that the weighted CRT Schur-complement tail energies remain uniformly bounded. The exact infinite-tail matrix assembly, its inverse, and attained minimization are now proved in `RH.ParetoExactHeadCRT`; the uniform bound is still missing.
- **Open:** assemble the RH criterion bridge in Lean. The cited classical full-residue criterion does not establish a two-seed converse.
- The finite/closed exact-head infimum equality and capacity dichotomy are proved in the research note; they are not asserted to be fully formalized by these declarations.

## Exact Pareto packets, arithmetic obstructions, and the remaining bound (9 September 2026)

See [RH/RHChatFormalization.md](RH/RHChatFormalization.md) and the preserved [research note](RH/RH_CRT_Packet_Research_2026-09-09.md). These are support results and concrete constructions, not a proof of RH.

| Declaration family | Modules | Exact scope / status |
|---|---|---|
| `ExactHeadCRT.tail_schur_completion`, `exists_inverse_tail_optimizer`, `mixed_uniform_defect` | `RH.ParetoExactHeadCRT` | Actual infinite tail weights, every mixed defect, positive Gram matrix, constructed inverse, and attained constrained minimum. |
| `nearbyDilationGram_exact`, `nearbyDilationGram_div_log_tendsto` | `RH.NearbyDilationGram`, `NearbyDilationAsymptotic`, `Analysis.PeriodicHarmonicMean` | Full infinite remainder retained; exact harmonic extraction and fixed-periodic logarithmic limit. |
| Residue gcd covariance, phi/theta identities, sharp jump completion | `RH.ResidueJumpCovariance`, `ResidueNearbyAsymptotic`, `OptimizedResiduePackets`, `OptimizedResidueHarmonic`, `OptimizedResidueIdentities`, `SmoothResidueJumpOptimality` | Exact arithmetic providers, including the sharp one-half fixed-seed coefficient. |
| Concrete Hilbert packets, dyadic substitution, logarithmic Gram/transfer limits | `RH.OptimizedResidueHilbert`, `OptimizedResidueSubstitution`, `OptimizedResidueAsymptotic`, `OptimizedCorrectionNormAsymptotic`, `OptimizedTransferAsymptotic` | Actual legal vectors, nonzero repair direction, exact vanishing remainder, closure equivalence, and full norm limits. |
| `optimizedPacketIterate_energy_telescope`, `optimizedPacketUniformBound_target_membership` | `RH.OptimizedPacketRecursion`, `ParetoPacketCoordinates`, `LinearAlgebra.OrthogonalSchurRepair` | Concrete all-N legal mean-one exact heads and complete signed energies. **Only the final membership implication assumes the open uniform bound.** |
| Complete Haar coordinates and sharp future transfer | `RH.ParetoHaarCoordinates`, `ParetoSchurTransfer`, `LinearAlgebra.SchurTransferSharpBound` | Actual isometry and reconstruction, arithmetic coefficients, causal recurrence, and attained sharp amplification. |
| Tail process identities and target-induced completeness | `RH.ParetoTailMartingale`, `ThresholdInterpolationCompleteness` | Exact covariance and mean-zero obstruction; target membership plus all integer dilations implies closure equals top. No Gaussian or independence claim. |
| Forced head charges and full arithmetic mixed energy | `RH.ExactHeadCharges`, `RoughComponentHead`, `RoughComponentExhaustion`, `ComponentHeadEnergy`, `RoughProfileCancellation` | Automatic finite component exhaustion, exact divisor inversion and profile partition, every ordered cross term, and the negative linear mixed-energy limit. |
| `fixed_prefix_norms_not_bounded` | `RH.FixedPrefixIncidence`, `SmoothHeadBoundaryFlux`, `SmoothPrefixFlow`, `SmoothPrefixDivergence` | Actual fixed original-generator prefix obstruction, with quantitative energy growth. |
| `roughDiagonalHead_div_tendsto_explicit`, `hasSum_squarefree_coprime_six` | `RH.RoughProfileBounds`, `RoughDiagonalLimit`, `RoughDiagonalEvaluation`, `NumberTheory.SquarefreeEulerSeries` | Actual dominated convergence and exact Euler-product evaluation give the full diagonal limit `6/(5*pi^2)`. |
| `arithmeticMellin_identity` | `RH.ParetoMellinFunctional`, `ParetoMellinDilation`, `ParetoMellinHolomorphic`, `ParetoResidueMellinArithmetic`, `ParetoResidueMellinContinuation`, `ArithmeticMellinIdentity` | Actual integral, continuity, dilation, Abel identity, holomorphic continuation, and finite coefficient linearity. |
| `meanOne_exactHead_tail_energy`, `finite_legal_seed_not_cyclic`, `finite_legal_seed_positive_distance_gap`, `finite_legal_seed_interpolation_unbounded` | `Analysis.AnalyticZeroPersistence`, `FiniteExponentialZeros`, `RH.ArithmeticMellinSymbolZeros`, `ParetoMellinHeadObstruction`, `FiniteSeedMellinObstruction` | Exact mean-one head/tail-error identity, nonreal arithmetic zeros, and genuine continuous Mellin separation; no unresolved identity or zero-existence providers. |

- **Open:** `Pareto.OptimizedPacketUniformBound` and the broader `UniformLegalExactHeadBound`. No proof of either is asserted.
- The forward formal bridge from two-seed closure membership to Mathlib's `RiemannHypothesis` is proved. The two-seed closure membership/uniform bound itself remains open.
- The exact Euler-product constant, automatic finite component exhaustion, and actual signed arithmetic cancellation have proved providers. Numerical experiments remain informal.

## Adjoint operators and quantitative affine phase limit (8 September 2026)

These 64 additional public declarations are established support results, not a proof of RH. All scales are actual positive integers. See `RH/ThresholdAdjointPhaseProgress.md` for exact definitions, verification receipts, and remaining bridges.

| Declaration family | Module | Exact scope |
|---|---|---|
| `Pareto.hilbertDilationAdjoint_coordinate`, `hilbert_coordinate_recovery`, `hilbertDilationAdjoint_all_fixed_iff`, `hilbert_coordinate_defect_bound` | `RH.ThresholdHilbertAdjoint` | Actual finite weighted-block adjoint formula on every real H vector; signed coordinate recovery and stability; constants are precisely the fixed vectors for ALL integer adjoints. Two-selected-seed rigidity and legal annihilator identification remain open. |
| `Pareto.hilbertDilationAdjoint_dilation`, `hilbertBlockProjection_coordinate`, `hilbertBlockProjection_pythagoras`, `hilbertBlockProjection_best_approximation` | `RH.ThresholdHilbertProjection` | Actual bounded projection `P_m=(1/m)T_m T_m*`, symmetry, idempotence, full energy/least-squares equalities, zero exceptional head and genuine weighted block means; not a finite legal projection. |
| `Pareto.affineProjectionEnergyTail_le`, `affineColumnEnergy_le_quarter_successor_sq` | `RH.ThresholdAffineTailBounds` | Actual complete squared-entry tail at most `1/[6(N+1)]` uniformly in m, and actual squared-column discrepancy at most `1/[4(j+1)^2]`; infinite comparison operator assembly is separate. |
| `Pareto.affineProjection_phase_gap_rate`, `affineProjectionEnergyTotal_tendsto`, `affineProjectionEnergyTotal_positive_floor` | `RH.ThresholdAffinePhaseLimit` | Actual numerical discrepancy satisfies `0 <= 2s-E_m <= 2/(3m^2)`, tends to `2s`, and is at least `17/216` for m>=3. No RH or unproved analytic input. Identifying this series with the infinite operator HS norm remains open. |

## Established RH and support declarations

| Declaration | Module | Statement / purpose | Status |
|---|---|---|---|
| `RiemannResearch.RH.Pareto.geometricProbability_integral`, `geometricProbability_product_integral`, `paretoWeight_hasSum`, `geometricKernel_hasSum` | `RiemannResearch.RH.ParetoGeometricMixture` | Actual geometric-mixture beta integrals, probability normalization, and complete infinite kernel marginals | Kernel checked; no spectral hypothesis |
| `RiemannResearch.RH.Pareto.geometricKernel_gram_integral`, `geometricKernel_cutoff_energy_identity`, `geometricKernel_double_energy_identity` | `RiemannResearch.RH.ParetoGeometricEnergy` | Exact finite Gram integral with explicit boundary; absolutely convergent full double-series energy for bounded sequences | Kernel checked; every tail and mixed term retained |
| `RiemannResearch.RH.Pareto.geometricTransform_integral`, `geometricTransform_sq_integral`, `geometricTransform_full_energy` | `RiemannResearch.RH.ParetoGeometricTransform` | Actual infinite geometric transform: mean, squared integral, and exact positive energy loss | Kernel checked for bounded sequences; all interchanges proved |
| `RiemannResearch.RH.Pareto.positiveWeight_block`, `dilation_partial_sum`, `paretoMean_dilation`, `paretoInner_dilation` | `RiemannResearch.RH.ParetoDilation` | Full Pareto block law, mean preservation, and exact inner-product scaling | Kernel checked; bounded sequences, positive dilation, anchoring explicit |
| `RiemannResearch.RH.Pareto.packetCombination_error_summable`, `primePowerCombination_full_error_floor`, `linear_square_summable_iff` | `RiemannResearch.RH.ParetoSequenceCertificates` | Genuine full-tail packet error bound; nonzero linear sequences are not Pareto square-summable | Kernel checked; arithmetic boundedness and convergence discharged |
| `RiemannResearch.RH.Pareto.paretoInner_optimal_scalar_gain`, `ramanujanPacket_enlargement_covariance`, `ramanujanPacket_prime_power_mul_mean_zero` | `RiemannResearch.RH.ParetoCovariance` | Actual infinite-sum covariance and scalar Schur gain; exact mixed-packet means for positive powers of a new prime | Kernel checked; scalar norm nonzero and arithmetic prime hypotheses explicit |
| `RiemannResearch.RH.Pareto.smoothingSeed_head`, `smoothingSeed_linear_head_energy`, `smoothingSeed_packet_expansion` | `RiemannResearch.RH.ParetoSmoothing` | Exact general-order smoothing head, signed energy expansion, and genuine multiples-sum packet coefficients | Kernel checked finite arithmetic; no asymptotics assumed |
| `ArithmeticFunction.logWeight_mul`, `sum_moebius_mul_log_sq`; `RiemannResearch.RH.Pareto.smoothingSeed_quadratic_head_error` | `RiemannResearch.NumberTheory.ArithmeticLogWeight`, `RiemannResearch.RH.ParetoQuadraticSmoothing` | Logarithmic Dirichlet-convolution derivation and quadratic Mobius-Mangoldt smoothing identity | Kernel checked finite algebra; includes the Lambda convolution term |
| `ProbabilityTheory.integral_const_sub_sq_total_variance`, `integral_const_sub_sq_condExp_pythagoras`, `integral_condVar_eq_integral_sq_residual` | `RiemannResearch.Probability.ConditionalVarianceError` | Exact bias/conditional-variance decomposition for genuine probability measures | Kernel checked; probability measure, L2 membership, sub-sigma-algebra explicit |
| `RiemannResearch.RH.Pareto.residue_mul_floor`, `residue_difference`, `mobiusDifference_residue`, `mobiusDifference_packet`, `ramanujanPacket_divisor_sum` | `RiemannResearch.RH.ParetoResidueDuality` | Genuine residue dilation, first differences, Mobius duality, packet incidence, and divisor reconstruction | Kernel checked; dual indices m > 1, packet q > 0 |
| `RiemannResearch.RH.Pareto.prime_divisor_transform`, `ramanujanPacket_mul_prime_of_not_dvd`, `ramanujanPacket_mul_prime_of_dvd` | `RiemannResearch.RH.ParetoPrimePackets` | Both prime enlargement identities, including repeated-prime channels | Kernel checked; p prime and q > 1; no independence assumption |
| `RiemannResearch.RH.Pareto.dualSix_normSq`, `dualSix_error_floor`, `witnessGram_eq_certificateMatrix`, `certificateMatrix_mul_numerators`, `primePowerCombination_error_floor` | `RiemannResearch.RH.ParetoFiniteCertificates` | Genuine Mobius rows have exact norm 92 and explicit signed Gram matrix; arbitrary prime-power combinations have finite weighted error at least 3562158/256250081 | Kernel checked arithmetic instantiation; infinite Hilbert closure is not asserted |
| `RiemannResearch.RH.Pareto.primorialDual_normSq`, `primorialDual_primorialPacket_zero`, `primePowers_primorials_error_floor` | `RiemannResearch.RH.ParetoFiniteCertificates`, `RiemannResearch.RH.ParetoPrimorialObstruction` | Norm 3880 and error floor 1/3880 for arbitrary combinations of prime powers and Mathlib primorials | Kernel checked finite coordinate bound; signal and annihilation discharged |
| `RiemannResearch.RH.Pareto.exists_squarefree_large_prime_support`, `boundedPrimeSupport_no_pointwise_limit` | `RiemannResearch.RH.ParetoBoundedInteraction` | No fixed distinct-prime interaction order admits pointwise convergence to 1 on positive integers | Kernel checked; positive conductors and a uniform fixed primeFactors.card bound |
| `RiemannResearch.RH.Pareto.anchoredGreen_inverse`, `anchoredGreen_solves_dirichlet`, `anchoredLaplacian_energy_with_boundary`, `anchoredLaplacian_energy` | `RiemannResearch.RH.ParetoAnchoredGreen` | Genuine max-kernel inverse action and exact finite energy, retaining the right boundary flux | Kernel checked operator formulation; zero-boundary specialization explicit |
| `RiemannResearch.RH.Pareto.mobiusPotential_difference`, `finiteMobiusRiesz_eq_gradient`, `mobiusPotential_energy`, `mobiusPotential_laplacian_energy` | `RiemannResearch.RH.ParetoMobiusPotential` | Actual finite Mobius potential and witness energy identities, including the last gradient summand | Kernel checked; boundary vanishing requires support in 1..M; multiples inversion remains open |
| `RiemannResearch.LinearAlgebra.finite_weighted_square_completion`, `finite_weighted_dual_bound` | `RiemannResearch.LinearAlgebra.FiniteWeightedEnergy` | Reciprocal-weight square completion and dual lower bound used by actual Pareto certificates | Kernel checked; nonzero/positive weights and positive dual norm explicit |
| `RiemannResearch.GroupTheory.AddSubgroupCRT.diagonal_injective_iff` | `RiemannResearch.GroupTheory.AddSubgroupCRT` | The simultaneous quotient map for two additive subgroups is injective exactly when their intersection is trivial | Kernel checked generalized CRT |
| `RiemannResearch.GroupTheory.AddSubgroupCRT.exists_diagonal_eq_iff` | `RiemannResearch.GroupTheory.AddSubgroupCRT` | A pair of residue classes has a common lift exactly when its overlap difference vanishes | Kernel checked; image equals kernel in the two-subgroup CRT sequence |
| `RiemannResearch.GroupTheory.AddSubgroupCRT.difference_surjective` | `RiemannResearch.GroupTheory.AddSubgroupCRT` | Every class modulo the sum of two additive subgroups is represented by a residue difference | Kernel checked surjectivity endpoint |
| `RiemannResearch.RH.PrimePhaseCRT.intPrimeLogRelation` | `RiemannResearch.RH.PrimePhaseCRT` | Every integer linear relation between logarithms of two distinct primes is trivial | Kernel checked from positivity of logarithm and uniqueness of prime powers |
| `RiemannResearch.RH.PrimePhaseCRT.periodSubgroup_inf` | `RiemannResearch.RH.PrimePhaseCRT` | The period subgroups generated by `2π / log p` and `2π / log q` have trivial intersection for distinct primes | Kernel checked unconditional prime specialization |
| `RiemannResearch.RH.PrimePhaseCRT.modularMap_injective` | `RiemannResearch.RH.PrimePhaseCRT` | The exact two-prime phase-residue map is injective | Kernel checked; does not assert topological density |
| `RiemannResearch.RH.PrimePhaseCRT.modularMap_exact` | `RiemannResearch.RH.PrimePhaseCRT` | A two-prime residue pair has a common real ordinate exactly when its overlap difference vanishes | Kernel checked exact algebraic CRT |
| `RiemannResearch.RH.StrictDiagonalDominance.posDef_of_strictlyRowDiagonallyDominant` | `RiemannResearch.RH.StrictDiagonalDominance` | A real Hermitian matrix with each positive diagonal strictly dominating its absolute off-diagonal row sum is positive definite | Kernel checked via the spectral theorem and Gershgorin |
| `RiemannResearch.RH.Log3Bounds.two_mul_logThreePartialSum_le_log_three` | `RiemannResearch.RH.Log3Bounds` | Every finite odd-power partial sum at one half gives a rigorous lower bound for `Real.log 3` | Kernel checked Mathlib series specialization |
| `RiemannResearch.RH.Log3Bounds.log_three_interval_15` | `RiemannResearch.RH.Log3Bounds` | `1098612288668109 / 10^15 < Real.log 3 < 1098612288668110 / 10^15` | Kernel checked from 27 exact terms plus a proved tail bound |
| `RiemannResearch.RH.Log3FiniteMatrixFormula.summable_aInfinitySummand` | `RiemannResearch.RH.Log3FiniteMatrixFormula` | The infinite archimedean-mode series used in the candidate exact-real formula scaffold is summable | Kernel checked by comparison with the convergent inverse-cube series |
| `RiemannResearch.RH.Log3FiniteMatrixFormula.evenFiniteLowerFormula`, `RiemannResearch.RH.Log3FiniteMatrixFormula.oddFiniteLowerFormula` | `RiemannResearch.RH.Log3FiniteMatrixFormula` | Candidate exact-real 20-by-20 formulas faithfully transcribed from the user-provided recovered verifier | Formula scaffold only; denominator validity, high-mode order bounds, Hermitianity, interval enclosures, and localized-Weil operator provenance remain open |
| `RiemannResearch.RH.CombinedGain.dualCapture_mono` | `RiemannResearch.RH.CombinedGain` | Restricting to a compressed legal dual-witness family cannot increase supremal capture | Kernel-checked order-theoretic compression lemma |
| `RiemannResearch.RH.CombinedGain.gain_lowerBound_of_actualDirectionOverlap` | `RiemannResearch.RH.CombinedGain` | A Cauchy quadratic certificate and an actual-direction overlap bound yield the inverse-free standardized gain lower bound | Kernel-checked implication; the concrete Gram Cauchy premise is explicit |
| `RiemannResearch.RH.CombinedGain.classwiseSecondMoment` | `RiemannResearch.RH.CombinedGain` | Finite-set Cauchy bounds squared class signal by class cardinality times its second moment | Kernel checked |
| `RiemannResearch.RH.CombinedGain.participation_of_secondMoment` | `RiemannResearch.RH.CombinedGain` | Converts a positive second-moment estimate into the global participation lower bound | Kernel checked |
| `RiemannResearch.RH.CombinedGain.exponentialAccumulation_le_exactProductGain` | `RiemannResearch.RH.CombinedGain` | The exact greedy product ledger dominates the cumulative exponential participation certificate | Kernel checked |
| `RiemannResearch.RH.CombinedGain.weightedCapture_of_exponential` | `RiemannResearch.RH.CombinedGain` | Pointwise exponential capture implies a threshold-free weighted rational capture estimate | Kernel checked |
| `RiemannResearch.RH.CombinedGain.jointProduct_closure` | `RiemannResearch.RH.CombinedGain` | Certified capture and certified absolute cross-flux multiply to a lower bound for the factorized observable | Kernel-checked implication; arithmetic providers remain open |
| `RiemannResearch.RH.CombinedGain.jointProduct_forces_absoluteScale` | `RiemannResearch.RH.CombinedGain` | A joint product certificate with capture at most one still forces an absolute cross-flux lower bound | Kernel checked scale obstruction |
| `RiemannResearch.RH.CombinedGain.TwoChannel.gain_eq_first_add_schur`, `gain_eq_first_iff`, `first_lt_gain_iff` | `RiemannResearch.RH.TwoChannelConditionalGain` | Exact unequal-norm two-channel Gram gain equals the first-channel gain plus the signed-overlap-residualized Schur increment, with exact zero and strict-gain criteria | Kernel checked algebra; actual legal arithmetic witnesses and quantitative residual-correlation bounds remain open |
| `RiemannResearch.RH.CombinedGain.TwoChannel.gain_sub_score_eq_schur_squares`, `score_eq_gain_iff` | `RiemannResearch.RH.TwoChannelConditionalGain` | One common two-channel optimizer has an exact sum-of-squares deficit and is the unique maximizer under positive pivots | Kernel checked; does not add independently optimized raw gains |
| `RiemannResearch.RH.CombinedGain.TwoChannel.gain_mul_gram_sub_pairing_sq`, `normalized_actualDirection_defect` | `RiemannResearch.RH.TwoChannelConditionalGain` | Exact signed Cauchy defect supplies the concrete actual-direction premise for inverse-free gain bounds and quantifies information discarded by that bound | Kernel checked; arithmetic overlap, legal support, return-covariance, and asymptotic sampling remain open |
| `RiemannResearch.RH.Statement` | `RiemannResearch.RH.Basic` | Stable local name for mathlib's RH proposition | Kernel checked |

## Conditional RH reductions

These declarations are complete proofs of implications, but they are not unconditional
proofs of the motivating RH statements.

| Declaration | Module | Verified consequence | Status |
|---|---|---|---|
| `ProbabilityTheory.conditional_energy_gap_of_variance_contraction`, `integral_const_sub_sq_le_bias_add_conditional_energy` | `RiemannResearch.Probability.ConditionalVarianceError` | Converts a supplied conditional-mean contraction into an energy gap and an error bound | Conditional research reduction; the actual pi/4 contraction provider is Open |
| `RiemannResearch.RH.Log3IntervalCertificate.evenBlock_posDef` | `RiemannResearch.RH.Log3IntervalCertificate` | The exact rational even-block preconditioner and row certificate imply positive definiteness for any supplied Hermitian 20-by-20 matrix satisfying the displayed `hdiag` and `hrow` bounds | Kernel checked conditional certificate; identification of the exact-real formula layer with the localized Weil operator and both enclosure hypotheses remain open |
| `RiemannResearch.RH.Log3IntervalCertificate.oddBlock_posDef` | `RiemannResearch.RH.Log3IntervalCertificate` | The exact rational odd-block preconditioner and repaired row certificate imply positive definiteness for any supplied Hermitian 20-by-20 matrix satisfying the displayed `hdiag` and `hrow` bounds | Kernel checked conditional certificate; identification of the exact-real formula layer with the localized Weil operator and both enclosure hypotheses remain open |

## RH chat: Pareto–Nyman, Green, and single-test tails (updated 9 September 2026)

Source: user-provided RH_Candid_Assessment_Pareto_Green_CRT_2026-09-07.md and
the associated chat. Exact inventory, verification evidence, hypotheses, and
remaining obligations: RH/ChatFormalizationReport.md. The recorded original
publications added 39 and 41 public theorems; the latest continuation adds
40 more, alongside the additional upstream research cited below. The full
discussion remains incompletely formalized and RH remains unproved.

| Module | New scope and status |
|---|---|
| RH.ParetoNymanPointwise; RH.ParetoUniformLaw; RH.ParetoNymanNorm | Actual reciprocal-floor distribution, pointwise residue identity, full squared-error norm transfer and finiteness for finite positive-conductor combinations |
| RH.ParetoResidueMean | General residue mean log(n), actual packet mean vonMangoldt(q), prime-power and zero-mean specializations |
| RH.ParetoBinaryApproximation | Exact complete-Pareto binary quadratic and optimum 1-log(2) |
| RH.NymanInverseMobius | Actual mixed two/three synthesis forces the Möbius head; finite support and reciprocal cancellation A_M(1)=0 |
| RH.ParetoPacketGreenGram | Ramanujan increments and gcd formula; exact finite boundary term and full summable tail |
| Analysis.SubpowerTailObstruction | Two conditional obstructions for actual L² tails: subpower growth and eventual power bounds, retaining logarithmic support and fixed transform signature |
| RH.RiemannHypothesisStrip | Actual Mathlib RH iff all actual open-strip zeta zeros lie on the critical line |
| RH.SingleTestTailCriterion | Conditional theorem concluding actual RH; detector nonvanishing, tail L², support, cancellation and subpower growth remain explicit hypotheses |
| RH.ConductorBoundedReciprocal | 6 established declarations: actual symbol gap, reciprocal bound and exact convergent geometric series |
| Analysis.ConductorL2Inverse | 17 established theorems: actual Lebesgue L² translations, operator geometric inverse series, both inverse identities, norm bound n/(sqrt(n)-1) and bijectivity for n>1 |
| Analysis.ConductorL2Support | 9 established theorems: exact inverse values on full left blocks almost everywhere; a compact input has an inverse nonzero on positive-measure sets below every threshold |
| Analysis.CenteredTransformPlancherel | 4 established theorems: actual centered/Fourier convention, spectral integrability and full-line Plancherel with normalization 1/(2π), including smooth-superexponential functions |
| RH.ParetoApproximationRatio | 3 established declarations: exact bias/variance error and equivalence of two small-error properties in a scalar-closed bounded class; existence of approximations remains Open |
| RH.ParetoFiniteSchur | 20 established finite-control identities for the complete Pareto law, with explicit invertible Gram action; all-scale variance convergence remains Open |
| RH.ParetoLegalApproximationClosure | 9 established theorems: exact Hilbert norm/error identity, equivalence of legal closure with small error/noise ratio, prime-pair packet formulation, and actual RH from legal small error, error convergence, mean-one variance convergence, or small noise/signal ratio using the proved Mellin bridge. The approximation hypotheses remain unproved; no RH-bridge hypothesis is required. |
| Analysis.CountableLaplaceDetector | 10 established declarations: countable entire zeros, simultaneous real tilt, normalized compact bump, transform shift and smooth compact detection of a specified countable spectrum |
| RH.CountableTiltDetector | Established existence of a nonzero smooth compact pole-annihilating countable-spectrum detector; actual-zeta specialization is now supplied by RH.CountableZetaDetector; original whole-strip detector remains Open |
| RH.CountableZetaDetector | Standard actual-zeta zero countability and an unconditional smooth compact polar-annihilating detector for all nontrivial zeta zeros; no growth estimate asserted |
| RH.FixedZetaDetectorCriterion | 3 established theorems: properties of one fixed choice of the actual compact detector, and conditional RH/quantitative zero-free consequences. Detector existence is discharged; actual tail L², support, cancellation and growth remain explicit |
| RH.SingleZetaDetectorCriterion | Conditional research reduction to actual RH with detection only at actual strip zeros; an actual detector is supplied by RH.CountableZetaDetector. Tail L², support, cancellation and subpower growth remain explicit obligations for an arbitrary/mixed optimizer |
| RH.NymanConductorTailObstruction | Exact canonical-tail signature at conductor-multiplier zeros; linear energy floor and failure of subpower growth under a nonzero artificial-zero signature; for every fixed conductor, a genuine zeta-detecting compact potential with a positive linear tail floor is constructed |
| Analysis.ActualL2Norm; RH.ConductorDifferenceEnergy | Exact translation-difference squared-energy identity with its full remainder, reverse triangle lower bound, and actual conductor operator with strictly positive L² gap for n at least two |

The countable-spectrum smooth compact detector and its actual-zeta specialization
are established. The forward legal-approximation-to-RH implication is also
established; the RH-to-approximation converse remains Open here. The original
whole-strip infinite-convolution detector and the full classical
Nyman–Beurling equivalence remain unformalized in this development. Subpower growth and asymptotic
variance reduction for a suitable mixed family remain mathematically unproved.
The canonical one-conductor family is obstructed whenever its head has a
nonzero artificial-zero signature. A stronger universal finite-jet obstruction
for a fixed nonzero head is proved in prose in
[the conductor-tail audit](RH/NymanConductorTailObstruction.md), but its
derivative-signature and moment/projection steps remain Open in Lean.
The criterion does not identify the mixed optimizer with canonical tails.
The genuine centered Plancherel theorem does not by itself identify that
mixed family's actual transform factorization.


## Pareto noise and arithmetic repair (8 September 2026)

Source: RH_Noise_Signal_Arithmetic_Repair_2026-09-07.pdf; detailed coverage and
source hashes: RH/ParetoNoiseSignalReport.md.

| Declarations | Module | Scope and status |
|---|---|---|
| scale_error_completion; finite_pair_remainder_identity | LinearAlgebra.NoiseSignalQuadratic | Kernel checked scalar optimization and exact finite weighted-pair remainder |
| paretoError_at_optimal_scale; paretoError_optimal_scale_minimizes; primePowerCombination_noiseSignal_floor | RH.ParetoNoiseSignal | Actual complete Pareto variance/NSR; bounded sequences and nonzero mean explicit; prime-power NSR at least 1/91 |
| mobiusDifference_arithmeticRepair; arithmeticRepair_eq_mixedPrimeLift | RH.ParetoArithmeticRepair | Genuine four-residue construction, full defect response, head preservation and finite packet legality |
| paretoInner_scaleRepair; arithmeticRepair_variance; arithmeticRepair_variance_le | RH.ParetoRepairCovariance | Exact full covariance and actual arithmetic diagonal bound; no correlation omitted |
| packetCombination_fixedSupport_full_error_lower_bound; packetCombination_fixedSupport_noiseSignal_lower_bound | RH.ParetoCoprimeObstruction | Actual full infinite reciprocal-square mass and fixed-support error/NSR floors; conductor divisibility witnesses explicit |
| smooth35Repairs_fixed_base_no_pointwise_limit | RH.ParetoRepairObstruction | Automatic composite invariant for all smooth35 repair scales plus any fixed finite packet base; varying coefficients allowed |
| hiddenNoise_mean_zero; hiddenNoise_interval_mass; hiddenNoise_interval_energy_odd; hiddenNoise_interval_energy_even | RH.ParetoHiddenNoise | Genuine sequence, exact finite interval laws and energies; asymptotics not asserted |
| paretoError_tendsto_mobiusDifference; boundedPrimeSupport_no_paretoError_limit | RH.ParetoDefectContinuity | Full-error convergence forces genuine arithmetic defects; boundedness separately for each approximant |
| coprimeReciprocalSquareMass_eulerProduct; coprimeReciprocalSquareMass_six; packetCombination_two_three_noiseSignal_lower_bound | RH.ParetoEulerProduct | Kernel checked complete Euler mass, with exact pi-squared floors |
| primeDualRepresenter_norm_sq; packetResidueCoefficient_prime_error_bound | RH.ParetoPrimeDualNorm | Kernel checked exact dual norm 2(p²+1) for p≥3 and actual packet coefficient bound |
| paretoInner_residue_four; paretoMean_residue_two; paretoInner_residue_two | RH.ParetoResidueMoments | Kernel checked complete infinite moments from digamma series |
| hiddenNoise_secondMoment_log_bound; hiddenNoise_firstMoment_log_bound | RH.ParetoHiddenNoiseAsymptotics | Kernel checked error≤18 from 2 log n, all n≥3; exact blocks and full tails supplied by RH.ParetoHiddenNoiseMoments |
| hiddenNoise_conditioned_limit_all; hiddenNoiseConditionedLimit | RH.ParetoHiddenConditioningVerified | Kernel checked actual conditioned limit (π²−6)/9; all indices; substitution, domination and constant evaluation proved |
| integral_fermi_first; integrable_fermi_first | RH.FermiIntegral | Kernel checked actual integral π²/12 and integrability |
| arithmeticRepair_binary_variance_log_bound | RH.ParetoRepairModulus | Kernel checked full discrete variance≤8(h/n²)(1+log(n/h)) for 0<h≤n |
| summable_prime_inv_mul_log_rpow; summable_prime_loglog_div_mul_log_rpow | RH.PrimeLogSummability | Kernel checked unconditional prime-weight convergence from Chebyshev |
| prime_repairs_limit_and_summable_of_log_gap | RH.ParetoRepairSummability | Kernel checked conditional reduction from an explicit quantitative gap; all variance and limit estimates discharged |
| summablePrimeRepairs_of_leastSmooth35_log_gap | RH.Smooth35RepairCompletion | Exact named SummablePrimeRepairs target follows from only the missing quantitative least-smooth gap input; conditional arithmetic reduction |
| residual_tendsto_zero_iff_not_summable | Analysis.ResidualGainProduct | Kernel checked exact recurrence/product and strict-gain exhaustion criterion; Analysis.ResidualGainTermination covers a gain equal to one |
| not_repairBesselBound_leastSmooth35Above | RH.ParetoBesselSmoothObstruction | Kernel checked NEGATIVE resolution of the report's proposed normalized Bessel bound for its actual least-smooth scale choice |
| repairBessel_commonScale_card_sq_le | RH.ParetoBesselClusters | Actual full Pareto cluster energy forces square-root cardinal bounds; Analysis.SmoothScaleReciprocal and RH.PrimeReciprocalTail contradict them |
| leastSmooth35Above_spec; leastSmooth35Above_le_twice | RH.Smooth35Choice | Actual minimal smooth scale and elementary factor-two bound, without a quantitative gap theorem |
| arithmeticRepair_common_anchor_cancel; arithmeticRepair_common_anchor_sum; arithmeticRepair_adjacent_chain | RH.ParetoRepairAnchorCancellation | Exact shared-scale and adjacent-scale changes of basis, retaining collective and terminal anchor coefficients |
| arithmeticRepair_binary_neighbor_defect; arithmeticRepair_common_anchor_variance_bound | RH.ParetoRepairAnchorCancellation | Compensating defect transfers to the neighboring scale; full variance bound uses the neighbor gap |
| tailOrthogonalize_energy_split; tailOrthogonalize_preserves_defect; arithmeticRepair_tail_elimination | RH.ParetoTailOrthogonalization | Exact Schur energy, preserved arithmetic head/defect, positive anchored pivot; the binary invariant is preserved |
| paretoInner_finsetCombination; paretoInner_finsetCombination_of_orthogonal | RH.ParetoFiniteGram | Exact full signed Gram expansion and Parseval for finite bounded orthogonal families with their actual coefficients |
| paretoInner_finsetCombination_le_total_energy; paretoInner_finsetCombination_le_tsum_energy | RH.ParetoFiniteGram | Valid Cauchy--Schwarz bound by unweighted coefficient square sum times total diagonal energy; not the refuted normalized Bessel bound |
| finiteTailProjection_orthogonal; finiteTailProjection_energy_split; finiteTailProjection_preserves_head; finiteTailProjection_pos_of_anchor | RH.ParetoFiniteTailProjection | Simultaneous finite projection for an already orthogonal bounded tail family, exact norm split and positive anchored pivot |
| TwoChannelCancellation.centered_energy; TwoChannelCancellation.correlation_identity; TwoChannelCancellation.correlation_fourth_power | LinearAlgebra.TwoChannelCancellation | Exact Hilbert variance/covariance identities; fourth-power cancellation under explicit centered-norm lower bounds |
| PairedAnnihilatorObstruction.no_exact_decomposition; PairedAnnihilatorObstruction.reciprocal_error_lower_bound | LinearAlgebra.PairedAnnihilatorObstruction | Conditional research reduction from explicitly quantified paired annihilators; actual arithmetic witness construction remains Open |
| summable_adjacent_arithmeticRepair_variance; summable_adjacent_arithmeticRepair_sq_norm | RH.ParetoAdjacentSummability | Unconditional full diagonal summability for every positive adjacent integer scale |
| inverseSmooth35_tsum; inverseSmooth35_shift_tsum | Analysis.Smooth35ReciprocalMass | Exact full reciprocal smooth-grid mass 15/8 and quadrant tails |
| arithmeticRepair_binary_variance_sqrt_telescope; summable_ordered_disjoint_arithmeticRepair_variance | RH.ParetoDisjointRepairSummability | Full variance bounded by 64 times the reciprocal-square-root potential drop; unconditional disjoint-interval summability |
| summable_smooth35SuccessorRepair_variance; smooth35SuccessorRepair_span_eq | RH.ParetoSmoothAdjacentSummability | Actual least-smooth replacement family has summable full variances and exactly the original algebraic span, without quantitative smooth gaps |
| exists_head_mean; mem_legal_iff_exists_budget | RH.FiniteTwoSeedHeadMean | Actual two-seed finite head and complete-mean interpolation, with algebraic budget exhaustion |
| residue_finset_coefficient; residueGramQuadratic_pos | RH.ParetoResidueGramStrict | Exact coefficient recovery, residue independence and strict positivity of the full infinite-tail Gram form |
| residue_constrained_minimum_identity; residue_constrained_minimum_strict | RH.ParetoConstrainedResidueMinimum | Exact constrained minimum and strictness under actual stationarity and constraint equations |
| budgetErrorInfimum_antitone; exact_approximation_iff_budget | RH.ParetoTwoSeedBudgetMinimum | Actual constrained budget infima and algebraic exhaustion; no vanishing-error limit asserted |
| paretoHeadMean_energy_identity; paretoHead_one_mean_zero_cost | RH.ParetoHeadMeanEnergy | Exact complete head/mean minimizer and nonnegative remainder; sharp constant-head cost |
| closedRepairProjection_tendsto_zero; infiniteRepairPivotSpan_closure; infiniteRepairPivot_summable_iff | RH.ParetoClosedRepairTails | Actual closed Hilbert tails, orthogonal pivots, completeness and strong convergence under the stated triangular hypotheses |
| infiniteRepairPivot_sharp_lower_at_anchor | RH.ParetoTailPivotEnergy | Full mean-zero pivot energy lower bound at the actual physical anchor, including sparse indexing |
| finiteRepairPivot_tendsto; finiteRepairPivot_energy_gap | RH.ParetoFinitePivotLimit | Finite pivots converge to actual infinite pivots with exact energy difference |
| originalRepairSeries_converges_iff | RH.ParetoReversePivotExpansion | Exact transformed-coefficient convergence criterion retaining the complete moving-boundary term |
| adjacentBinaryRepair_covariance; adjacentBinaryRepair_abel | RH.ParetoAdjacentRepairCalculus | Full signed covariance differences and Abel summation retaining terminal anchors |
| binaryDilation_combination_energy_le_cumulative_tail; adjacentBinaryRepair_combination_energy | RH.ParetoAdjacentKernelBounds | Exact minimum-kernel factorization and full signed Gram energy |
| CompressedMellin.cellDensity_eq; CompressedMellin.phase_difference_square | RH.ParetoCompressedMellinCosine | Exact actual cosine density and signed phase identities |
| CompressedMellin.cosineDeficit_summable; CompressedMellin.cosineMass_le_quadratic | RH.ParetoCompressedMellinSummability | Unconditional actual cosine-series convergence and full majorant |
| CompressedMellin.compressedMellinEnergy_eq; CompressedMellin.fullCosineIdentity | RH.ParetoCompressedMellinNorm | Exact complete complex-cell norm; supplies FullCosineIdentity without additional analytic hypotheses |
| CompressedMellin.actual_no_exact_decomposition; CompressedMellin.actual_reciprocal_error_obstruction | RH.ParetoMellinObstructionTargets | Conditional research reductions for actual seed closures. CosineMassAsymptotic, PhaseCenteredAnalyticProvider and ActualPairedMellinProvider remain Open |

Four of the original six named targets have unconditional positive providers:
ResidueFourMoment, HiddenNoiseSecondMoment, HiddenNoiseFirstMoment and
HiddenNoiseConditionedLimit. The proposed RepairBesselBound is disproved for
the actual least-smooth choice (and all eventually comparable smooth choices).
This was an open suggestion in the PDF, not a theorem claimed proved there.

The finite covariance step now has proved replacements: exact anchor cancellation,
reverse orthogonal elimination, finite tail projection, and exact Gram identities.
See RH/ParetoCovarianceRepairReport.md. Transformed coefficients and all final
anchors are retained. The finite projection assumes an already orthogonal tail
family; a full recursive existence theorem is not claimed. These operations do
not remove the binary composite obstruction or prove infinite convergence.

The remaining named positive target is SummablePrimeRepairs. Its analytic
steps and exact conditional assembly are proved; the published quantitative
smooth35 gap theorem itself is still unformalized. It is an explicit hypothesis
of the conditional provider, not an axiom or an assumed variance estimate.

Other open translations include the fixed-old-space gain asymptotic, full
Hilbert infimum/closure results, and cited spectral and RH-criterion literature.
RH and global convergence of a sufficient repair system remain unresolved.

## Pareto analytic obligations (7 September 2026)

The exact bounded-sequence geometric error identity is now established as
`RiemannResearch.RH.Pareto.geometricTransform_full_error_identity` in
`RiemannResearch.RH.ParetoGeometricTransform`. The following obligations remain Open:

- The Kalvoda–Šťovíček weighted Hankel diagonalization and the actual sharp pi/4
  contraction on the constant-orthogonal subspace; no project axiom supplies it.
- Cyclotomic logarithmic-derivative identification of the conditional packet means;
  the present geometric transform is the actual infinite power series.
- Smoothing mean asymptotics from Mertens estimates, fixed-conductor large-prime
  asymptotics, Mellin/Plancherel specialization, and finite Euler-product growth.
- Full Hilbert-space dual closure, bounded pointwise/convex-average approximation,
  and matrix-valued multichannel Schur optimizers with arithmetic providers.
- Mixed-radix conditional independence and martingale energy specialization.
- Extension of the geometric identities from bounded sequences to arbitrary
  weighted L2 sequences, and a joint-measure conditional-expectation identification.
- Uniform corrected-energy decay, growing-conductor convergence, and RH remain
  mathematically unproved; these are not merely unfinished Lean translations.

The generic conditional-variance declarations assume ordinary probability/L2
hypotheses. The two contraction corollaries additionally assume `hcontract` and
are classified as conditional reductions above. Floating-point illustrations
from the research notes have not been converted to interval certificates.

## RH combined-audit import (3 September 2026)

The original combined-audit development is collected under
`RiemannResearch.RH.CombinedAudited` and imports the unique Lean content from
the audited-source archive.  The present extension records the subsequently
supplied `rh_irreducible_targets_progress_package_2026-09-03.zip`.  The package
archive has SHA-256 digest
`443ec212dfb2d6e23ee3687c5ffddcbafb80b973e5a48dd4206635aab34188eb`,
which agrees with the previously supplied manifest.  The staged
`ProgressManifest` update records the archive and extracted-payload hashes;
`SourceClaimIndex` separates formal declarations from numerical or documentary
source material.

### Verified finite and functional-analytic results

- The original import retains the exact Boolean-sign, raw-count/reciprocal,
  weighted-Pythagoras, scalar-counterterm, scalar-Schur, two-polar-mode,
  finite Morse-index, limit-positivity, and norm-contraction results.  The
  associated research targets remain definitions or propositions unless a
  proof is actually present.
- `RiemannResearch.RH.PrimeGapCurvature` contains `gap`, `adjacentSlope`, and
  `adjacentCurvature`, together with the exact affine-kernel theorems
  `adjacentCurvature_eq_zero_iff`, `adjacentCurvature_affine`,
  `adjacentCurvature_add_affine`,
  `exists_affine_on_range_of_curvature_eq_zero`, and
  `curvature_eq_zero_iff_exists_affine_on_range`.  The determinant identities
  `tripleDet_eq_gap_mul_gap_mul_slopeDiff` and `consecutiveTripleDet_eq` are
  supplemented by `tripleDet_eq_weighted_adjacentCurvatures` and its ordered
  specialization `tripleDet_eq_weighted_adjacentCurvatures_of_lt`.  The latter
  pair gives the exact telescoping compression of an arbitrary three-point
  determinant into adjacent curvatures.  The same module retains the scalar
  two-block mean/Schur and bandwidth-two recurrence families.  These are exact
  finite identities, not asymptotic prime-gap estimates.
- `RiemannResearch.RH.FiniteCurvatureGreen` packages adjacent curvature as
  the concrete linear map `finiteCurvatureMap` between finite coordinate
  spaces.  It proves
  `ker_finiteCurvatureMap_eq_range_affineProfileMap` and the equivalent
  range and coordinate forms of “equal curvature iff affine difference.”
  The two-prefix construction `profilePrefixLinearMap` is an explicit right
  inverse; `finiteCurvatureMap_comp_profilePrefixLinearMap` and
  `finiteCurvatureMap_surjective` give the exact section and surjectivity
  statements.  These are finite algebraic results, not a Weil-form
  identification or an RH proof.
- `RiemannResearch.RH.FiniteMeanZeroSlope` packages adjacent slope
  differences and arithmetic-mean centering as linear maps. It proves that
  centered curvature-prefix slopes have coordinate sum zero, that adjacent
  differences recover the original curvature vector, and that every zero-sum
  slope vector is recovered by centering its adjacent differences.
  `curvatureMeanZeroSlopeEquiv` gives the resulting exact linear equivalence,
  while `finiteAdjacentSlope_profilePrefix_eq_centeredSlope_add_mean` records
  the constant-slope gauge change from the anchored prefix profile. This is
  finite-dimensional algebra, not dyadic density, a Weil-form identification,
  or an RH proof.
- `RiemannResearch.RH.FiniteEndpointProfile` prefix-integrates arbitrary
  finite slope vectors on the unit grid and proves exact telescoping in both
  directions. It packages profiles with zero initial and final coordinates as
  `endpointZeroProfileSubmodule`, proves that centered curvature-prefix
  slopes integrate into that submodule, and reconstructs every member from its
  finite curvature. `curvatureEndpointZeroProfileEquiv` is the resulting
  linear equivalence from `Fin n → ℝ` curvature data to endpoint-zero
  profiles, including `n = 0`. This closes a finite coordinate chain; it is
  not dyadic density, a Weil-form identification, or an RH proof.
- `RiemannResearch.RH.FiniteDirichletGreenMatrix` gives the closed
  piecewise formula for the unit-grid endpoint-zero Green kernel. Its columns
  are the profiles of standard curvature vectors, arbitrary centered profiles
  are their finite Green superpositions, and the interior restriction is a
  symmetric, entrywise nonpositive matrix whose `mulVec` recovers the
  interior profile. `finiteCurvature_green_sum` proves the exact inverse
  identity, including the vacuous `n = 0` case. This is a finite-dimensional
  coordinate result, not dyadic density, a Weil-form identification, or an RH
  proof.
- `RiemannResearch.RH.FiniteDirichletGreenEnergy` proves the exact
  finite summation-by-parts identity
  `finiteDirichletGreenMatrix_quadraticForm_eq_neg_slopeEnergy`, identifying
  the Green quadratic form with the negative sum of squares of the centered
  slope vector. Theorems
  `finiteDirichletGreenMatrix_quadraticForm_nonpos` and
  `finiteDirichletGreenMatrix_quadraticForm_eq_zero_iff` establish
  nonpositivity and negative definiteness, including `n = 0`. This is a
  finite-dimensional energy identity, not a Weil-form identification or an RH
  proof.
- `RiemannResearch.RH.FiniteDirichletGreenGram` proves the exact mixed
  bilinear summation-by-parts identity, realizes the centered-slope map as
  multiplication by `finiteCenteredSlopeMatrix`, and factors the finite
  Dirichlet Green matrix as the negative Gram matrix of that slope transform,
  uniformly including `n = 0`. This is a finite-dimensional coordinate
  factorization, not a dyadic/Haar density result, a Weil-form identification,
  or an RH proof.
- `RiemannResearch.RH.FiniteSlopeCompression` defines the curvature-space
  pullback `Tᵀ K T` of an arbitrary real finite slope-space kernel `K`
  through `finiteCenteredSlopeMatrix`, proves its exact mixed bilinear
  identity, and shows that symmetry is preserved. This is a finite-dimensional
  generic kernel congruence, not a Weil-form identification, a positivity claim
  for a concrete arithmetic kernel, dyadic/Haar density, or an RH proof.
- `RiemannResearch.RH.FiniteCenteredSlopeMatrixFormula` proves the exact
  two-branch entries of `finiteCenteredSlopeMatrix` on the standard curvature
  basis, including the centering normalization. This is finite coordinate
  algebra, not a concrete Weil-kernel construction, positivity or density
  theorem, or an RH proof.
- `RiemannResearch.RH.FiniteDyadicHaarSlope` constructs literal dyadic
  Haar atoms and proves zero-sum membership, exact squared norms, pairwise
  orthogonality, and the three-jump curvature formula.
- `RiemannResearch.RH.FiniteDyadicHaarBasis` proves the full finite
  mean-zero slope basis, coefficient normalization, Parseval, and sparse
  curvature basis, including dimension zero.
- `RiemannResearch.RH.FiniteDyadicHaarCompression` proves exact literal
  Haar/curvature congruence and equivalence of finite nonnegativity in all
  directions. `FiniteSlopeCompression` supplies general family/basis versions.
  Actual cell-integral Weil kernels, arithmetic positivity, analytic density
  and limits remain open; these results are finite coordinate algebra.
- `RiemannResearch.Analysis.FiniteCellKernel` proves actual iterated-integral
  reconstruction for finite real cell steps and jointly continuous kernels,
  with all integrability used. Separated one-variable terms cancel on
  mean-zero steps. It also supplies continuous-kernel subtraction and
  uniform rectangle-integral error bounds, global finite-step norm bounds,
  and square integrability without disjoint-cell assumptions. Quadratic
  subtraction carries explicit inner and outer integrability evidence.
- `RiemannResearch.Analysis.SupportL2Bound` proves the support Cauchy bound
  `(∫ |u|)^2 ≤ 2R * ∫ u^2` with explicit L1/L2 integrability and vanishing
  outside `[-R,R]`, including the zero-length interval without division.
- `RiemannResearch.Analysis.CompactKernelQuadraticContinuity` proves product
  and iterated integrability for bounded measurable kernels on a fixed support
  window, exact quadratic subtraction, and quantitative L1/L2 continuity.
  It shows that square-integral convergence on the common window implies
  convergence of the actual full-line quadratic integrals. For jointly
  continuous kernels it also gives an explicitly conditional transfer of
  nonnegativity from a mean-zero L2-dense test class. The density and
  approximating-test positivity inputs remain hypotheses; no arithmetic
  positivity, Weil identification, or RH conclusion is supplied.
- `RiemannResearch.Analysis.ComplexKernelQuadratic` defines the actual
  conjugate-first complex quadratic form for real kernels and proves absolute
  product and outer integrability before Fubini. For symmetric continuous
  kernels it identifies the form exactly with the sum of the real quadratic
  forms of the real and imaginary parts. Its positivity transfer retains real
  positivity as an explicit premise and concludes zero imaginary part plus a
  nonnegative real part; complex numbers are not assigned an order.
- `RiemannResearch.Analysis.PrimitiveEnergy` proves the exact signed identity
  `q_abs(u) = -2 * ∫ U^2` for compactly supported real integrable mean-zero
  tests, where `U(t)=∫ x in Iic t, u x`. Joint measurability and absolute
  triple integrability precede Fubini; primitive-square integrability and
  component nonpositivity are also proved, including empty support intervals.
- `RiemannResearch.Analysis.HingeKernel` defines the common hinge and proves
  continuity, evenness, and exact finite-window inactivity. This previously
  published module is retained and used by HingeKernelIntegral and ScrewPrimePart.
- `RiemannResearch.RH.FiniteDyadicCellKernel` constructs equal dyadic cells,
  proves their support bounds and Haar-step mean zero, and identifies actual
  kernel integrals with the exact Haar compression, including R=0 and m=0.
  It also proves pointwise vanishing outside the support window, square
  integrability, and the exact support-length L1-to-L2 estimate. It specializes
  the primitive-energy identity and cumulative-square integrability to Haar steps.
- `RiemannResearch.RH.DyadicL2Density` constructs genuine averages on the
  literal Ioc dyadic cells, proves their exact zero-sum Haar reconstruction
  in the existing unnormalized basis, and establishes whole-line squared-L2
  convergence for every integrable, square-integrable, compact-window-supported
  mean-zero real test. The proof handles R=0 before positive-width cancellation
  and includes m=0. This closes the real fixed-window dyadic density bridge;
  arithmetic positivity, completed-Weil agreement, and support
  exhaustion, and the RH endpoint remain open.
- `RiemannResearch.RH.ArithmeticDyadicPositivityTransfer` is a conditional
  research reduction: positivity of the exact arithmetic-screw quadratic form
  on every dyadic Haar coefficient vector at every level transfers to every
  real integrable, square-integrable, mean-zero test on the same compact
  support window. A matrix-facing form uses the existing unnormalized
  `arithmeticScrewHaarMatrix` without rescaling. The all-level matrix
  premise also conditionally yields zero imaginary part and nonnegative real
  part for the actual complex form on mean-zero tests with integrable component
  squares. The all-level positivity premise, support exhaustion, completed Weil
  identification, and RH endpoint remain open.
- `RiemannResearch.RH.ArithmeticFiniteApproxPositivity` defines the literal
  Haar compression of the exact finite arithmetic approximation and proves its
  quadratic reconstruction and the signed implication `q_approx ≤ q_actual`.
  It now also proves approximation evenness, cell and Haar symmetry, Hermitian
  structure, an exact native `Matrix.PosSemidef` interface, and conditional
  fixed/all-level real and complex transfers. A generic entrywise interval
  certificate implies native PSD when its exact enclosures and strict margins
  are supplied. No finite certificate, completed-Weil agreement, or RH endpoint
  is proved.
- `RiemannResearch.Analysis.TranslationKernelCellIntegral` proves a generic
  four-corner double-integral theorem and exact cells for exponential,
  absolute-value, and exponential-absolute-value translation kernels on
  arbitrary oriented intervals. The exponential-absolute-value second
  primitive is globally `C²`, including at the origin.
- `RiemannResearch.RH.ArithmeticFiniteEntryFormulas` evaluates the finite
  approximation cell as the exact signed sum of the polar cell, the full finite
  von Mangoldt prime-power cells, the linear absolute-value cell, and the
  subtracted truncated archimedean cells. It then expands every entry of the
  literal unnormalized Haar matrix as a finite double sum. These are exact
  finite formulas, not positivity certificates.
- `RiemannResearch.RH.ArithmeticFiniteFirstLevel` proves that the first
  nonempty Haar matrix is PSD exactly when its unique diagonal is nonnegative,
  with a literal four-cell formula. At `R = 1/4`, `N = 2`, `J = 0`,
  Lean certifies the admissible cutoff but proves that diagonal is below
  `-5/1536`. This is an exact obstruction to that finite truncation, not to
  the actual arithmetic form, whose signed comparison remains
  `q_approx ≤ q_actual`. The module also records the vacuous level-zero PSD
  and zero-window matrix boundaries.
- `RiemannResearch.RH.ArithmeticFiniteFirstLevelCertificate` proves the
  exact level-one, cutoff-two scalar formula and rigorous rational lower
  bounds for its polar and first four archimedean contributions. Exact bounds
  for Euler's constant, `log π`, `log 2`, and π give the live linear/pole
  coefficient an upper bound of `269/100`. At `R = 1/16`, `J = 4`,
  the unique diagonal is above `1/500000`, yielding native finite PSD and,
  through the signed comparison, native PSD of the actual arithmetic Haar
  matrix at that same window and level. This is not all-level positivity,
  completed-Weil positivity, or RH.
- `RiemannResearch.RH.ArithmeticFiniteSecondLevelCertificate` proves the
  exact three-dimensional unnormalized Haar compression at level two,
  including all nine Toeplitz entries and a sum-of-squares quadratic
  decomposition. At `R = 1/16`, `N = 2`, and `J = 4`, certified
  rational Taylor enclosures give the finite quadratic form the unconditional
  lower bound `21/100000000` times the sum of squares of its three Haar
  coefficients. Hence the finite matrix is natively positive semidefinite,
  and the signed tail comparison transfers the same lower bound and native
  PSD to the actual arithmetic Haar matrix at this fixed window and level.
  The complete range-two von Mangoldt sum, polar correction, live
  gamma/pole coefficient, four archimedean modes, and Haar normalization are
  retained. This is not all-level or all-window arithmetic positivity,
  completed-Weil positivity, or RH.
- `RiemannResearch.RH.ArithmeticFiniteThirdLevelCertificate` proves the
  exact seven-dimensional unnormalized Haar compression at level three.
  At `R = 1/16`, `N = 2`, and `J = 4`, exact rational exponential
  enclosures, reflection blocks, rational shears, and strict row diagonal
  dominance give the unconditional lower bound `1/1000000000` times the
  sum of squares of all seven Haar coefficients. An exact eight-cell
  prefix-sum identity proves the auxiliary form is below the literal finite
  arithmetic form, and the signed tail comparison transfers the same bound
  and native PSD to the actual arithmetic Haar matrix at this fixed window
  and level. The complete range-two von Mangoldt sum, polar correction,
  live gamma/pole coefficient, four archimedean modes, and Haar normalization
  are retained. This is not all-level or all-window arithmetic positivity,
  completed-Weil positivity, or RH.
- `RiemannResearch.RH.ArithmeticFiniteFourthLevelCertificate` proves the
  exact fifteen-dimensional unnormalized Haar compression at level four.
  At `R = 1/16`, `N = 2`, and `J = 5`, all sixteen primitive
  values are enclosed by rigorous rational exponential bounds. Exact
  jump-stencil and Toeplitz identities, an eight-plus-seven reflection split,
  denominator-1000 rational shears, and strict row diagonal dominance give
  the unconditional lower bound `1/1000000000` times the sum of squares of
  all fifteen Haar coefficients. The exact auxiliary comparison retains the
  complete range-two von Mangoldt sum, polar correction, live gamma/pole
  coefficient, all five archimedean modes, and Haar normalization. The
  established signed tail comparison transfers the same lower bound and native
  PSD to the actual arithmetic Haar matrix at this fixed window and level.
  This is not all-level or all-window arithmetic positivity, completed-Weil
  positivity, or RH.
- The seven-module level-five certificate package, culminating in
  `RiemannResearch.RH.ArithmeticFiniteFifthLevelCertificate`, extracts reusable
  endpoint-jump, reflection-block, coefficient-Gram, rational interval, and
  integer-shear certificate infrastructure. At `R = 1/16`, `m = 5`,
  `N = 2`, and `J = 5`, exact rational exponential enclosures and
  denominator-10000 unit-upper shears give the unconditional lower bound
  `1/1000000000` times the sum of squares of all thirty-one native
  unnormalized Haar coefficients. The odd sixteen-dimensional and even
  fifteen-dimensional reflected blocks have certified positive margins
  `7500436/10^15` and `12178181/10^15`. The literal finite form retains the
  complete range-two von Mangoldt sum, polar correction, live gamma/pole
  coefficient, and all five archimedean modes. The signed comparison proves
  the same quantitative bound and native PSD for the actual arithmetic Haar
  matrix at this fixed window and level. This is not all-level or all-window
  arithmetic positivity, completed-Weil positivity, or RH.
- `RiemannResearch.Analysis.HingeKernelIntegral` proves positive-part
  power derivatives at every point, hinge primitives, and the exact
  four-corner double cell formula, including threshold crossings.
- `RiemannResearch.RH.ScrewPrimePart` defines the von Mangoldt weighted
  prime-power hinge series, proves local finiteness and continuity, and
  evaluates its finite-sum rectangle integrals exactly.
- `RiemannResearch.RH.ScrewArchimedeanSeries` constructs the continuous,
  even archimedean series and proves summability, an explicit uniform
  tail majorant `B_J`, and `tendsto_archimedeanTailMajorant_zero`.
- `RiemannResearch.Analysis.ExponentialKernelGram` proves an integrable
  Volterra-feature product identity and the square-integral Gram formula
  `exponentialKernel_finite_gram`. For every positive rate this gives
  nonnegativity on arbitrary finite configurations of real points.
  It now also proves absolute integrability of the three-variable Volterra
  product and `exponentialKernel_integral_gram`, so the actual convolution
  quadratic form is nonnegative for every measurable integrable real test.
- `RiemannResearch.RH.ScrewArchimedeanPositivity` proves
  `neg_archimedeanScrewTail_finite_nonneg` and
  `neg_archimedeanScrewSeries_finite_nonneg`: the negative archimedean
  series and every infinite tail are nonnegative on finite configurations
  with zero-sum real coefficients. Summability and interchanges are proved.
  For actual integrals, `neg_archimedeanScrewTerm_dyadic_integral_eq`
  isolates each exponential Gram term exactly.
  `neg_archimedeanScrewTail_integral_eq_tsum` proves the infinite-tail
  interchange on every integrable real test by an absolute product-space
  majorant, while `neg_archimedeanScrewTail_dyadic_integral_bounds_l1`
  gives dyadic nonnegativity and the explicit bound
  `4 * B_J * (∫ |u|)^2`. The sharp support-based theorem
  `neg_archimedeanScrewTail_dyadic_integral_bounds_l2` strengthens the upper
  bound to `8 * R * B_J * ∫ u^2`. This controls one signed component,
  not complete arithmetic positivity.
- `RiemannResearch.RH.ArithmeticScrewKernel` defines the full elementary
  arithmetic expression with polar, prime-power, linear, and archimedean
  terms. It proves continuity, evenness, value zero at zero, symmetry of the
  anchored kernel, and `arithmeticScrewHaarMatrix_quadratic`, the exact
  actual integral/Haar-matrix identity. Its finite approximation has
  explicit pointwise errors on bounded windows.
- `RiemannResearch.RH.ScrewPolarQuadratic` proves the exact polar
  quadratic identity for integrable real tests with integrable positive and
  negative exponential moments. It retains the constant correction
  `8 * (∫ x, u x)^2`, derives the mean-zero reduction, and specializes it
  to dyadic Haar steps. Its hyperbolic version gives `-8 C^2 + 8 S^2`
  for mean-zero tests, retaining the mean correction in the general theorem.
  These are signed component identities; no
  nonnegativity of the full arithmetic form or RH consequence is asserted.
- `RiemannResearch.LinearAlgebra.FiniteQuadraticError` proves
  `quadratic_error_of_entrywise_bound` for arbitrary real finite matrices.
- `RiemannResearch.RH.ArithmeticScrewCellBounds` proves exact finite
  prime-power cell sums for N>exp(2R), entry errors at most
  `4*B_J*h^2`, and `dyadicCell_arithmeticScrewApprox_quadratic_error`
  with bound `4*B_J*h^2*(sum_i |s_i|)^2` in every slope direction.
  On mean-zero Haar steps, its exact actual-minus-approximation identity is
  the negative archimedean tail quadratic form, yielding the one-sided
  enclosure `q_approx ≤ q_actual ≤ q_approx + 8*R*B_J*∫u^2` for N>exp(2R).
  This lower approximation need not be nonnegative.
- `RiemannResearch.RH.ArithmeticScrewQuadraticDecomposition` proves
  `dyadicHaarStep_arithmeticScrewFunction_quadratic_decomposition` and
  `arithmeticScrewHaarMatrix_quadratic_decomposition`: exact signed polar
  squares, all active von Mangoldt prime-power hinge quadratics, negative
  cumulative-primitive energy, and the infinite positive Volterra Gram series.
  Every sign and coefficient is inherited from the defined elementary function.
  This assembles components; it does not prove full arithmetic positivity.
  Source-normalization/Lerch agreement, identification with the zeta
  zero sum or Weil distribution, analytic density, complexification,
  the Weil/RH endpoint, and all-window full arithmetic positivity remain
  **Open**. No theorem in this batch proves or assumes the RH-strength
  arithmetic positivity target.
- `RiemannResearch.RH.FiniteCurvatureWeightedGreen` constructs the explicit
  weighted least-energy representative in every finite-curvature fiber.  Its
  moment formula `weightedAffineProjection` removes the weighted-orthogonal
  affine component, while `weightedOrthogonalPrefix` is a right inverse to
  `finiteCurvatureMap`.  Theorems
  `weightedOrthogonalPrefix_orthogonal_affineRange`,
  `weightedOrthogonalGreen_pythagoras`,
  `weightedOrthogonalGreen_minimizes`, and
  `weightedOrthogonalPrefix_unique_minimizer` give orthogonality,
  Pythagoras, minimization, and uniqueness under positive weights.  This is a
  finite-dimensional auxiliary Green construction, not a Weil-form
  identification or an RH proof.
- `RiemannResearch.RH.TripleCurvatureCompression` defines
  `tripleCurvatureLinearMap`, `selectedTripleCurvatureMap`, and the finite
  weighted form `selectedTripleCurvatureEnergy`.  The theorem
  `sum_weight_mul_tripleDet_sq_eq_selectedTripleCurvatureEnergy` factors any
  selected finite family of ordered triple-determinant squares through
  adjacent curvature, while `selectedTripleCurvatureEnergy_nonneg` proves
  positivity for nonnegative weights.  This auxiliary PSD result is not an
  identification with the Weil form.
- `RiemannResearch.RH.InnovationLittleOObstruction` proves that the literal
  fixed-prefix condition `ActualInnovationLittleO` forces the nonnegative
  monotone bandwidth-two energy to vanish.  In particular,
  `bandwidthTwoInnovation_eq_zero_of_actualLittleO` shows that every
  bandwidth-two innovation is zero when all pivots are positive.  This is a
  formal obstruction/guardrail and does not establish an RH criterion.
- `RiemannResearch.LinearAlgebra.DualGreenProjection` defines `greenOperator`
  and `dualGreenProjection`.  The declarations `dualGreenProjection_apply`,
  `dualGreenProjection_mapsTo`, `dualGreenProjection_residual_mem_ker`,
  `dualGreenProjection_idempotent`, `dualGreenProjection_factorization`, and
  `dualGreenProjection_orthogonal_ker` establish the abstract Green projection
  mechanism.  `dualGreen_energy`, `dualGreen_pythagoras`, and
  `dualGreen_minimizes` give the exact energy, Pythagoras, and minimization
  statements.  Their hypotheses remain explicit and do not assume the
  analytic realization required by the RH program.
- `RiemannResearch.LinearAlgebra.TwoBlockCommonOptimizer` packages the
  vector common-optimizer and exact Schur-mismatch argument.  Its distinct-form
  layer proves `twoBlockForm_commonOptimizer_identity`,
  `twoBlockFormMismatch_eq_commonFlux`, minimization, and equality rigidity.
  The basis-free `twoBlockFormOptimizer` inverts the summed normal map via
  bilinear duality; `existsUnique_twoBlockForm_minimizer` proves existence
  and uniqueness for finite-dimensional symmetric blocks when one block is
  positive definite and the other is nonnegative.  Its scalar-weighted
  same-form layer defines `weightedTwoBlockOptimizer` and proves the closed
  parallel-sum formula `weightedTwoBlockLoss_completion`, minimization, and
  equality and mismatch rigidity.  These theorems vectorize the earlier scalar
  two-block identities while retaining one global optimizer.  They are finite
  linear algebra and do not identify the block forms with the completed Weil
  form or establish RH.
- `RiemannResearch.LinearAlgebra.FiniteWeightedEnergy` proves the exact finite
  identities and dual certificates `affine_normal_det_double_sum`,
  `affine_normal_det_nonnegative`, `affine_normal_det_positive`,
  `weighted_functional_sq_le`, and
  `weighted_functional_energy_lower_bound`.  These results are independent of
  the numerical scripts and of any limiting argument.
- `RiemannResearch.LinearAlgebra.RankOneSchur` contains the scalar identities
  and bounds `rank_one_scalar_identity`, `rank_one_scalar_lower_bound`,
  `rank_one_elimination_lower_bound`, and `rank_one_elimination_attained`, plus
  the Hilbert-space theorems `rankOne_highMode_lower_bound`,
  `rankOne_highMode_attains`, and `rankOne_highMode_lower_bound_neg`.  They
  isolate the finite algebra required by the proposed high-mode elimination
  without identifying a truncated matrix with the full operator.

The new declarations above were individually kernel checked before
integration and are included in the repository-wide validation performed by
the publication checkpoint.  This verification covers the exact finite and
functional-analytic statements only, not any unresolved asymptotic or RH
claim.

### Evidence not promoted to a Lean theorem

The two `L = log 3` interval runs, including the larger robustness run, remain
reproducible candidate computer-assisted evidence.  Their output and hashes
are recorded for provenance, but the printed pivots are not treated as Lean
proofs.  Promotion would still require a formally verified interval
implementation together with the analytic reduction, Hermitianity and entry
enclosures, operator provenance, and the passage from finite compressions to
the relevant infinite operator.

These additions materially strengthen the exact finite-dimensional part of
the program, but they do **not** prove the Riemann Hypothesis.  The decisive
remaining work includes quantitative control of the actual signed endpoint
moments and adjacent-prime curvature innovations, the common-optimizer
boundary/Schur term, certified finite-block positivity, high-mode positivity
and tail bounds, and a noncircular spectral or trace construction connecting
those estimates to RH.

## Planned research areas

| Area | Initial target |
|---|---|
| Nyman–Beurling | Define the fractional-part generators in `L²(0,1)` |
| de Branges theory | Hermite–Biehler functions and reproducing-kernel spaces |
| Hilbert–Pólya | A precise conditional spectral formulation |
| Operator theory | Closed, densely defined, and self-adjoint operators |
| Spectral triples | Finite-dimensional prototype, then compact resolvent |
| Noncommutative geometry | C*-algebra representations and commutators |
| Field with one element | Select and encode a precise F₁ framework |

## Exact arithmetic-channel effects (7 September 2026)

Source: the user-provided paper argument
`RH_Exact_Arithmetic_Channel_Effects_2026-09-07.md`, sections 2–10.
The publication checkpoint checks the exact declarations below and their imports.
This is a substantive partial formalization of that paper, not a claim that every
paper proof, the complete Weil identification, or an RH implication is formalized.
The table below records the declaration scopes and the outstanding obligations.

| Module | Principal reusable declarations | Exact verified scope |
|---|---|---|
| `LinearAlgebra.SignedChannelUpdate` | `LinearMap.IsSymm.signed_change_synthesis`, `signed_gain_sum`, `signed_complete_square`, `signed_schur_nonnegative_iff`, `signed_universal_monotone_iff`, `signed_null_coupling_negative_witness`, `signed_minimum_eq_iff_normal`; `LinearMap.signed_change_sum_forms`, `signed_hilbert_projection_accounting`, `signed_no_gain_of_existing_span` | Native complex sesquilinear signed expansions with all mixed terms; signed completion and minimization assuming a supplied signed normal-equation solution; universal monotonicity iff channel positivity and vanishing signed mixed couplings; actual Hilbert accounting and redundant-channel obstruction. Existence of a Moore–Penrose/range solution is not proved. |
| `LinearAlgebra.GreenChannelBoundaryUpdate` | `RiemannResearch.LinearAlgebra.GreenChannelBoundary.woodbury_inverse`, `gluing`, `schur_update_inverse`, `innovation_update`, `boundary_migration`, `symmetric_schur_update`, `symmetric_inverse_energy_drop`, `update_nonsingular`, `MigrationExample.exact_migration` | Exact real finite-matrix inverses, screened updates and gluing under explicit ordinary invertibility/symmetry assumptions. The rational example proves total 1→2/3 and boundary 0→1/6. A general Loewner-order theorem and complex/operator extensions are not claimed. |
| `RH.PrimePowerReturnBoundary` | `RiemannResearch.RH.PrimePowerReturn.finiteAR1_inverse`, `finiteAR1_det_ne_zero`, `compressedPrimeGreen_inverse`, `compressedPrimeGreen_det_ne_zero`, `compressedPrimeGreen_inverse_singleton` | Direct multiplication proves all nonempty finite chain inverses and both endpoint corrections, including the coincident endpoints for the singleton. Only p>1 is needed for the prime-parameter identity. Identification with compression of an infinite operator remains separate. |
| `RH.PrimeCurvaturePolarBridge` | `RiemannResearch.RH.PrimeCurvaturePolarBridge.halfDensity_existsUnique_iff`, `halfDensity_complex_existsUnique_iff`, `translated_polarNull_iff_unique_curvature`, `halfDensity_polar_annihilation`, `halfDensity_complex_polar_annihilation`, `halfDensity_coefficientMass_positive`; `Matrix.signed_complex_congruence`, `physicalMass_identity`; `LinearMap.sesquilinear_curvature_compression` | Constructive unique real/complex curvature coordinates for exactly two polar constraints at positive nodes with nonzero adjacent gaps. The actual translated-bump integral equivalence has explicit integrability and nonzero base-moment hypotheses. Full signed congruence and distinct coefficient/physical mass are retained. No prime-grid density or signed positivity is assumed or established. |
| `Analysis.SquarePartitionLocalization` | `RiemannResearch.Analysis.SquarePartitionLocalization.partitionDefect_eq_half_sum_sq`, `partitionDefect_nonneg`, `sum_autocorrelation_localized`, `gluingCorrelation_zero`, `autocorrelation_add` | Exact finite square-partition defect and actual complex autocorrelation integrals, with their necessary integrability hypotheses. Both mixed correlations remain. No uniform gluing bound is asserted. |
| `RH.SignedWeilCorrelation` | `RiemannResearch.RH.SignedWeilCorrelation.correlationValue_sub`, `correlationValue_sum`, `correlationValue_net_effect`, `correlationValue_gluing`, `primePowerCorrelationValue_localization`, `primePowerCorrelationValue_cutoff_stable` | Signed finite von-Mangoldt correlation value with both pole terms, gamma regularizer and arbitrary diagonal constant. Actual-test localization under explicit integrability assumptions; exact cutoff invariance assumes omitted weighted values vanish. Full Weil/zero-side identification and the fixed archimedean constant are not supplied by these declarations. |
| `Analysis.WeightedAbelDiscrepancy` | `RiemannResearch.Analysis.weighted_abel_discrepancy` | Actual finite Abel summation against an arbitrary differentiable comparison primitive, retaining both endpoints; local differentiability/continuity assumptions only. |
| `RH.PrimePowerDiscrepancy` | `RiemannResearch.RH.primePowerHalfCutoff_exact_discrepancy`, `primePowerHalfCutoff_add_density` | Actual Λ(n)/sqrt(n) partial summation against 2(sqrt(x)−1), with the upper discrepancy boundary and continuous-density cancellation retained. No arithmetic estimate is assumed. The logarithmic-variable full Weil assembly is still open. |
| `RH.PrimeSquarePartialSummation` | `RiemannResearch.RH.primeSquareSector_eq_cutoff`, `primeSquareCutoff_exact_remainder`, `primeSquareSector_exact_remainder`, `primeSquareProfile_variation`, `abs_primeSquareSector_remainder_le` | Actual prime-square weights log(p)/p; supported-profile full sum equals its finite cutoff; exact main integral and discrepancy remainder; variation bound conditional on the displayed uniform discrepancy bound. Mertens and the autocorrelation/profile asymptotic assembly are not proved. |
| `RH.BroadTestNormalization` | `MeasureTheory.integral_sq_secondDeriv_sub_quarter`, `integral_exp_mul_secondDeriv_sub_quarter_eq_zero`; `RiemannResearch.RH.broadProfileNormalizer_sq`, `broadProfileNormalizer_lower`, `broadPolarOperator_broadBump_integral_sq`, `broadTest_eq_dilated_profile`, `broadTest_integral_sq`, `broadTest_polarMoments`, `normalizedBroadProfile_integral` | Actual compact C² broad-test construction, exact norm formula, positive lower bound, unit L² mass, both vanishing polar moments, dilation and profile mean. These are established analytic statements; no Mertens or RH hypotheses are used. |

### Remaining formalization obligations

- **Open:** identify the completed Weil distribution and zero-side pairing with
  the full explicit arithmetic correlation formula; evaluate the archimedean
  constant and complete the discrepancy representation (paper (3.4)/(4.3)).
- **Open:** discharge the correlation integrability/compact-cutoff hypotheses
  uniformly for the intended smooth test family; derive the discrepancy gluing
  expression (5.3) and compact-potential inverse/uniqueness plus its derivative
  localization repair (5.4)–(5.6).
- **Open:** complete Moore–Penrose range-existence/inertia and infinite Green
  operator provenance where needed; none is inferred from a finite inverse.
- **Open:** prime-log mesh density, common-bump approximation and exact two-moment
  correction in the compact-test topology, and the all-window Weil criterion.
- **Open:** the Mertens estimate, actual autocorrelation assembly of the square
  asymptotic, higher-prime-power/gamma limits and their O(R⁻²) errors.
- **Open:** the semiboundedness⇒RH proof, including an actual Weil distribution,
  Bochner–Schwartz temperateness, half-line Laplace holomorphy and the exact
  logarithmic-derivative pole obstruction.

The normal-equation and discrepancy-bound hypotheses in the corresponding
general theorems are explicit; kernel checking does not supply the missing
research inputs. No statement here establishes the desired all-window signed
arithmetic positivity.

## Nyman–Weil arithmetic completions (7 September 2026)

Source: user-provided argument,
`RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md`,
sections 4, 5, 7, 9, and 10.
The four candidates passed serialized isolated checks and key-declaration axiom
audits using only propext, Classical.choice, and Quot.sound. The final
publication checkpoint validates the actual modular imports and retained work.

| Module | Principal declarations | Established scope |
|---|---|---|
| `RH.NymanConductorArithmetic` | `RiemannResearch.RH.vonMangoldt_mul_nymanConductorBeta`, `nymanConductorBeta_mul_inverse`, `nymanConductorInversePrefix_exact`, `nymanTwoThree_prefix_feasible` | Actual full prime-power convolution, constructive Dirichlet inversion, exact finite-prefix matching, and concrete 2/3 feasibility. |
| `RH.ArithmeticConductorCommonZeros` | `RiemannResearch.RH.ArithmeticConductorCommonZeros.conductorSymbol_zero_iff_phase`, `conductorSymbol_zero_re`, `conductorSymbol_two_three_common_zero_iff`, `common_conductor_products_zero_iff` | Actual complex symbols; phase lattice and real part one; only common 2/3 zero is one; shared-factor product characterization away from one. Integer log independence is proved. |
| `Analysis.RemoteLaplaceTail` | `MeasureTheory.RemoteLaplaceTail.integral_kernel_norm_sq`, `norm_integral_mul_sq_le`, `remote_energy_lower_bound`, `null_completion_energy_lower_bound` | Evaluated kernel norm and actual Bochner-integral bound. The last result explicitly assumes supported L2 tail, weighted integrability, and actual transform nullity; no requested inequality is an input. |
| `LinearAlgebra.NullChannelTail` | `LinearMap.IsSymm.null_sub_diagonal`, `null_completion_mixed`, `null_completion_diagonal`, `null_completion_cross`, `null_compactification_change` | Exact Hermitian null-channel and head–tail identities, including full mixed terms. Radical membership is an explicit hypothesis. |

### Conditional research reductions and open providers

- **Completed below:** actual arithmetic completion, support, regularity, and transform nullity.
- **Completed below:** the full Weil distribution and actual arithmetic radical membership.
- **Completed below:** removable zeta-multiplier values and actual analytic multiplicities.
- **Open:** the optimized mixed-tail subexponential upper bound and its all-window RH implication.

The four modules prove reusable arithmetic, complex-analysis, integral, and
Hermitian-form results. They do not prove RH or its missing upper bound.

### Isolated verification evidence

| Module | Successful job | Runtime |
|---|---|---:|
| `RH.NymanConductorArithmetic` | `job_kgsqlFuPuZmPodfH1_Phd8YzCgy0HPxc` | 2.108 s |
| `RH.ArithmeticConductorCommonZeros` | `job_dy3c8yGmVXI0og2C8DF1t1K04Gy1mkiJ` | 2.266 s |
| `Analysis.RemoteLaplaceTail` | `job_lWfGz1EfW0z4pMidsDYav2pvXSNFMFDM` | 3.622 s |
| `LinearAlgebra.NullChannelTail` with its exact dependency source | `job_dznjEZ6WPZ-breuErkv6acQyz_UK2k-G` | 3.192 s |

Each returned verified true and exit code zero. The last check included the
unchanged SignedChannelUpdate source because isolated file checks do not
emit importable object files. The integrated module keeps its normal import.
Repairs concerned pinned APIs, cast normalization, the already-declared
Hermitian hypothesis's inclusion, and symmetry rewrite orientation.
Unused tactic arguments and draft status comments were removed before integration.
These isolated checks alone do not establish checkpoint publication.

## Nyman–Weil analytic and arithmetic completion

Source argument: §§2–10 of `RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md`.
This entry records the completion providers below; it does not certify every statement or numerical experiment in that note. The exact mathematical statements passed the combined Lean check recorded below. Publication also requires the native module-compilation checkpoint.

Write `E = SmoothSuperexponentialDecay`: a test is C∞ and every actual iterated derivative decreases faster than every positive exponential. The arithmetic return, integral transforms, correlations, and differential operator below are concrete functions. Their identities and admissibility are conclusions of the listed providers.

| Established coverage | Principal modules / endpoints |
|---|---|
| Actual arithmetic synthesis, local finiteness, C∞ regularity, and Dirichlet-convolution composition | `ArithmeticReturnSupport`, `ArithmeticReturnConvolution`: `arithmeticReturn_eq_sum`, `arithmeticReturn_contDiff`, `arithmeticReturn_mul`. |
| Closed Möbius coefficients of the actual constructive inverse | `NymanInverseMobius`: `nymanConductorInverse_eq_mobius_sum`, `nymanConductorInverse_eq_mobius_tsum`. For `n≥2` and `k>0`, these identify the existing Dirichlet inverse with `n ∑_{n^j∣k} n^j μ(k/n^j)` and prove that the apparent infinite series terminates. |
| Explicit coefficient and crude tail-size bounds | `NymanInverseCoefficientBound`: `sum_abs_nymanConductorInverse_div_sqrt_le` proves the actual coefficient bound 2n√M(1+Nat.log n M). `ActualL2Norm` and `NymanTailCrudeBound`: `nymanCompletedTest_eq_finite_translates`, `nymanCompletionTail_actualL2Norm_crude_upper_bound` prove the literal finite-translation identity and note (9.8) for the actual constructed tail. The L² triangle and translation bounds concern ordinary integrals, with finite-energy hypotheses supplied. |
| Actual finite inverse potential and remote support after applying `L = D²−1/4` | `ArithmeticInverseCompact`, `ArithmeticCompletionDifferential`: `nymanCompletionTail_tsupport`. For a seed supported in `[a,b]`, the inverse potential has support in `[a,b+log M]`, and the differential tail has support in `[a+log(M+1),∞)`. |
| Poisson cancellation and full output regularity | `NymanPoissonCancellation`, `ArithmeticReturnPoisson`, `LogarithmicSchwartzTransport`, `ArithmeticReturnDerivatives`, `NymanReturnRapidDecay`. The actual logarithmic kernel is Schwartz; the zero frequency cancels; every derivative of the actual return has arbitrary exponential decay. |
| Actual completed-test and tail membership in E | `NymanCompletionAdmissibility`: `smoothSuperexponentialDecay_nymanCompletedTest`, `smoothSuperexponentialDecay_nymanCompletionTail`, `nymanCompletionTail_admissible_and_tsupport`. |
| Actual transform factorization, including absolute Fubini, entire continuation, and both integrations by parts | `ArithmeticReturnMellin`, `BilateralLaplaceEntire`, `BilateralLaplaceDifferential`, `NymanTransformNullity`. The entire formula is `M(L R_n u)(s) = s(s−1) conductorZeta_n(s) M(u)(s)`. |
| Actual tail transform and its negative zero signature | `NymanTailTransform`: `centeredTransform_nymanCompletionTail`, `centeredTransform_nymanCompletionTail_zeta_signature`, `centeredTransform_nymanCompletionTail_polar`. |
| Compact smooth potential for every compact smooth polar-annihilating input | `CompactPolarPotential`, `CompactPolarPotentialUniqueness`: `existsUnique_compact_smooth_polarPotential`. The actual conditions `M f(0)=M f(1)=0` supply a unique smooth `v` in the original support interval with `Lv=f`. Both support and uniqueness are proved. |
| Removable value and actual zero multiplicities | `ZetaConductorRegularization`, `NymanPeriodicLFunction`, `NymanConductorContinuation`: the actual coefficient L-function equals the entire continuation of `ζ(s)(1/n−n^(−s))`; its value at 1 is `log n/n`. Analytic orders, conductor simple zeros, and the exact conductor-2/3 common-zero and minimum-order statements are proved for the stated conductor conditions. |
| Actual full Weil form on E | `SmoothCompactCutoff`, `CompactCutoffConvergence`, `CompactCutoffVerticalDecay`, `WeilZeroSumConvergence`, `WeilCutoffArchimedeanConvergence`, `WeilNoncompactExplicitFormula`: `actual_noncompact_Weil_explicit_formula_of_smooth`. These supply compact approximation, all weighted derivative L1 limits, a uniform spectral majorant, the multiplicity-weighted zero-sum limit, the complete von Mangoldt limit, and both pole/gamma limits. |
| Actual arithmetic Weil nullity, including signed terms | `WeilGammaFourierAdapter`, `NymanWeilNullity`, `NymanFullReturnWeilNullity`, `NymanWeilRadicalNullity`. The Fourier gamma term is identified with the regulated spatial term, retaining its exact diagonal constant. Actual completed returns have zero complete Weil value; the corresponding mixed radical statements use the actual form. |
| Exact full-form spectral pairing and head–tail accounting | `WeilSpectralPairing`: `arithmeticWeilPairing_eq_zero_sum`, `arithmeticWeilPairing_hermitian`, `arithmeticWeilPairing_self_eq`. `NymanActualTailWeilAccounting`: `infinitePrimePowerCorrelationValue_nymanCompletionTail_eq_head`, `arithmeticWeilPairing_head_nymanCompletionTail_eq_neg_head`. These prove the actual complete-form identities `Q(τ)=Q(Lv)` and `W(Lv,τ)=−Q(Lv)`. |
| Actual arithmetic completion of every compact smooth polar-annihilating test beyond any prescribed gap | `ActualArithmeticTailExistence`: `exists_actual_arithmetic_tail_after`. Given compact smooth `f`, the actual conditions `M f(0)=M f(1)=0`, a conductor `n≥2`, and any real gap `Y`, this constructs a compact smooth potential `v` and finite inverse cutoff `M`. The resulting actual arithmetic tail belongs to E, has support in `[Y,∞)`, annihilates both poles, and satisfies `Q(τ)=Q(f)` and `W(f,τ)=−Q(f)`. |
| Complete prime/square/higher-power split and exact arithmetic-return compensation | `PrimePowerSectorDecomposition`: `primePowerSeries_eq_prime_add_square_add_higher`. `NymanPrimeSquareCompensation`: `primeCorrelationSector_smul_poleCancellation_nymanFullReturn_compensation`. This partitions the convergent actual von Mangoldt series and proves compensation for each real scalar multiple of `L R_n u` with compact smooth `u`. It retains the complete square sector, the higher-power diagonal and displacement correction, the exact gamma diagonal, and the gamma displacement integral. |
| Arithmetic and limiting ingredients for prime–square compensation | `MertensElementary`, `MertensPrimeDiscrepancy`, `PrimeCompensationLimits`, `NoncompactPrimeSquareLimit`, `NoncompactPrimeSquareScaling`, `ArchimedeanCorrectionLimit`, `RealAutocorrelationSquare`. These provide the unconditional bounded prime Mertens discrepancy, the complete signed noncompact square identity, actual gamma/higher-power second moments, and vanishing displacement corrections under the stated profile hypotheses. Fixed-profile limits do not substitute for the varying arithmetic-return family. |
| Generic normalized broad-kernel bounds and quantitative mean-square limit | `BroadKernelUniformBounds`: `eventually_normalizedBroadKernel_bounds`, `integral_sq_normalizedBroadKernelProfile`, `tendsto_mean_normalizedBroadKernelProfile`. `BroadKernelMeanSquareRate`: `eventually_mean_sq_normalizedBroadKernelProfile_error`. Under the explicitly stated kernel moment, profile integrability, boundedness, and nondegeneracy hypotheses, these prove eventual uniform bounds, exact normalization, the limiting squared mean, and an `O(1/R)` error for that squared mean. They do not assume the target convergence. The actual arithmetic-return instantiation and its stronger weighted estimates are supplied below. |
| Second-order broad-profile energy estimate, including the actual return kernel | `BroadKernelEnergySecondOrder`: `differentialBroadKernelEnergy_second_order_bound`, `nymanBroadKernelEnergy_second_order_bound`. The first-order profile correction is a derivative whose cross integral vanishes for a compact smooth seed. The resulting energy error is bounded by `C/R²`, and the actual `nymanReturnKernel` satisfies the required moment hypotheses. |
| Actual scaled arithmetic family, its norm, and its literal zeta coefficient | `NymanReturnAbel`, `NymanBroadKernelBridge`, `NymanBroadKernelEnergy`, `NymanKernelZetaMass`: the actual return equals the spatial kernel convolution, the scaled test equals the differential broad profile, its energy equals the actual integral of the squared norm, and the kernel mass gives the exact coefficient at ζ(1/2). |
| Positive normalization at every positive scale | `NymanBroadNormalizationPositive`: `nymanBroadNorm_pos`, with exact unit norms for both the real scaled profile and the physical complex arithmetic test. These require conductor n≥2, a compact C∞ real seed, nonzero seed integral, and R>0; they are not restricted to eventual positivity. |
| Actual Schwartz convergence with all weighted derivatives | `ScaledKernelWeightedApproximation`, `BroadKernelWeightedApproximation`, `WeightedNormalizationConvergence`, `SuperexponentialSchwartz`, `NymanBroadSchwartzConvergence`, `NymanBroadSchwartzTopology`: `tendsto_nymanBroadSchwartzMap`. For the stated nondegenerate compact seed, the actual scaled normalized family converges to the negative normalized seed in Mathlib's Schwartz topology. Uniform bounds and convergence in every weighted derivative seminorm are proved. |
| Complete varying-family compensation and both linear asymptotics | `NymanBroadCorrelationBounds`, `NymanBroadCorrelationScaling`, `NymanBroadCorrectionLimits`, `NymanBroadSquareAsymptotic`, `NymanBroadPrimeSquareCompensation`, `NymanBroadPrimeAsymptotic`. The actual square sector is −R(∫φ)²/(2∫φ²)+O(1), and the actual prime sector is +R(∫φ)²/(2∫φ²)+O(1). Their sum tends to the explicitly retained full diagonal constant. The entire gamma and higher-power displacement corrections are O(R⁻²) and tend to zero. No limit of the bounded signed square remainder is asserted. |
| Exponential lower bound for the actual remote arithmetic tails | `NymanActualTailEnergy`: `nymanCompletionTail_energy_lower_bound`, `nymanPolarCompletionTail_energy_lower_bound`. At an actual zeta zero ρ with Reρ>1/2, the constructed tail has energy at least (2Reρ−1)exp((2Reρ−1)Y)|M f(ρ)|². Its L² membership, supported-transform identity, and weighted integrability are derived from the actual completion providers. |

The arithmetic/transform chain passed `nullity2`; cutoff and correlation providers passed `cutoff2`; the noncompact explicit-formula/nullity chain passed `fullweil2`; the compact potential, uniqueness, and prime-power sector decomposition passed `kernel_clean2`. The exact spectral pairing, universal tail existence, head–tail accounting, and actual-return compensation passed `tails1`. The generic normalized broad-kernel bounds and quantitative mean-square rate passed `profile4`. The actual inverse's Möbius formulas and second-order broad-profile energy estimates passed `remaining_algebra2`. Earlier successful checks supply the stated elementary Mertens and sector-moment providers. The coordinator's verification ledger remains authoritative for individual module inclusion.

The compact Weil foundation is imported from **Anthropic's Zeta23**, [anthropics/formal-math at commit `fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`](https://github.com/anthropics/formal-math/tree/fbdc36bbf17d20af3fd0447c6d1a8a02773c9844/zeta23), under **Apache License 2.0**, copyright 2026 Anthropic, PBC, with original contributor notices retained. The exposed unconditional theorem is `Zeta23.WeilEF.EF_lit_zetaZeroConfig`. Its zero carrier is the actual nontrivial zeros of `riemannZeta`, and its multiplicities are `(analyticOrderAt riemannZeta ρ).toNat`. The imported dependency closure, relocation, license, and source audit are documented in `RH/WeilExplicitFormula/PROVENANCE.md`, `NOTICE.md`, and `LICENSE.md`. This foundation is credited upstream; the new transport, extension, and completion providers connect it to this project's actual arithmetic tests.

### Combined verification and remaining RH target

The complete chain above passed job `job_Krj1svNf3MBDoFYei95fp6xuWVuq_WxM` with `verified: true`, exit code 0, and 70.777 seconds of compiler time. Its exact combined-source SHA-256 is `f2e7e50f4b562650118381dcf77205a82a7930d8fca69dc6a2d06ee7bf26f59b`. The check included 176 source modules: 106 authored completion modules, 58 credited upstream/adapter modules, and 12 pre-existing project dependencies. Every import remains modular in the persistent project; source inlining was only the isolated-check mechanism.

The environment is Lean `v4.33.0-rc2` and Mathlib commit `51e6992efd06126df61a496bebf8f49482a4e129`. Eleven final endpoint axiom audits, including the actual explicit formula, universal arithmetic completion, common-zero multiplicities, exact compensation, prime asymptotic, Schwartz convergence, normalization, and tail-energy bound, use only `propext`, `Classical.choice`, and `Quot.sound`.

The additional coefficient/crude-tail-size chain passed job `job_-r8DwnTrVWQiTUe4yCyohmVnhlzVB81Z` with verified true, exit code 0, and 6.202 seconds. Its 32-module combined-source SHA-256 is `c7c0a6786436cc4ac332f8ba7b4a2a0c86f5d2693528e8f88e241d95d86c630c`. It adds three authored modules to the completion set, for 109 authored modules in total.

The RH target remains open: an appropriate subexponential upper bound for the optimized **mixed-conductor** remote tails has not been proved. These unconditional completion identities, null channels, and prime–square compensation do not establish that upper bound or RH. This entry also does not certify every earlier optimizer calculation, truncated-residual endpoint formula, or numerical experiment in the source note.

### Summable-tail uniqueness and completed regularity upgrade (2026-09-11)

**Established:** `Analysis/DyadicBlockRigidity.lean` proves the previously
missing implication in the Fourier/Sobolev argument. If A is summable,
sum n(n+1)(A(n)-A(n+1))² is finite, and A(2n)=A(n)/2, then A(n)=0 for every
positive n. In particular sum (n A(n))² is finite, with no additional
regularity hypothesis.

The proof is discrete. For c(n)=n A(n), dyadic block averages tend to zero.
Exact averaging increments, disjoint blocks, and Cauchy-Schwarz give
c(n)² <= (1/2) sum_{j >= 2n}(c(j+1)-c(j))². The difference sequence is square
summable by the original weighted energy. Tail decay and dyadic invariance
then force vanishing.

`RH/ParetoSummableTailRigidity.lean` proves the actual application:
`LegalAnnihilator.signedTail_weighted_square_summable` is a checked
provider, and `legalAnnihilator_eq_zero_of_summable_signedTail` gives
uniqueness from actual weighted L2 orthogonality, seed 2 availability,
and summability of the signed tail. The energy and dyadic equations are
derived from the original Pareto definitions. The former Fourier/Sobolev
formalization obligation is **Discharged**.

Recovered prior verified results are preserved:
`RH/ParetoSignedTails.lean` (exact tails, mean, and energy),
`Analysis/SummableMultiples.lean` (summable inversion and grouped equations),
`Analysis/SummableDiscreteAbel.lean` (summation by parts),
`Analysis/DyadicTailRigidity.lean` (terminal orbit lemmas),
`Analysis/FirstMomentTails.lean` and `RH/ParetoFirstMomentUniqueness.lean`
(first-moment uniqueness), and the eventual-sign/oscillation extension to
`RH/ParetoAnnihilatorPositivity.lean`.

**Open research:** proving that the canonical residual has summable signed
tails. This regularity is not inferred from weighted L2 membership alone.
No unconditional RH conclusion is asserted. Other unformalized claims from
the two source notes are listed in `RH/ParetoTailRigidityVerification20260911.md`.

### Grouped signed tails and exact-head energy growth (2026-09-12)

**Established:** `RH/ParetoGroupedSignedTails.lean` removes absolute
summability of the signed tail from the actual pairing identities.
Weighted L2 membership alone supplies summability of the binary and triadic
grouped tails. For every positive dilation m, the actual pairings equal
m times their respective grouped sums. Actual legal annihilators therefore
satisfy both grouped equations whenever seeds 2 and 3 are available.
The signs and the negative triadic coefficient -2 are retained inside each
summand. No divergent positive/negative channels are separated.

Supporting declarations:
- `Analysis/SummableDiscreteAbel.lean`: `ordered_abel_finite`,
  `ordered_abel_tendsto`; the finite boundary term is explicit.
- `Analysis/SummableMultiples.lean`: `sum_divisibility_mask_range`,
  `binary_block_sum`, `triadic_block_sum`, `finite_signed_divisibility_sum`.
- `RH/ParetoSignedTails.lean`: `signedTail_shift_difference_summable`.
- Actual endpoints: `dyadic_pairing_eq_grouped_signedTail`,
  `triadic_pairing_eq_grouped_signedTail`,
  `LegalAnnihilator.binary_grouped_signedTail_eq_zero`,
  `LegalAnnihilator.triadic_grouped_signedTail_eq_zero`.

**Established zero obstruction:** `paretoMellin_exact_head_power_lower`
and `RH/ParetoLegalHeadGrowth.lean` prove that a zeta zero s with
Re(s)>1/2 forces every legal vector f equal to one through N>=3 to satisfy
`((2*Re(s)-1)/(4*norm(s)^2))*(N+1)^(2*Re(s)-1) <= norm(f)^2`.
The actual Mellin nullity provider is used; no arithmetic nullity assumption
is left in `legal_exactHead_power_lower_of_zeta`.
`legal_exactHead_energy_tendsto_atTop_of_zeta` proves full energy divergence.

**Conditional research reduction:**
`riemannHypothesis_of_legal_exactHead_subpower` concludes Mathlib's actual
`RiemannHypothesis` from an actual legal exact-head family whose full squared
norm is o((N+1)^p) for every p>0.

**Open:** construction of a family meeting the joint exact-head and
subpolynomial full-energy requirements. **Open:** inversion of the simultaneous
binary/triadic grouped equations in the full weighted L2 class.
Summability of grouped differences does not supply summability of the tail
or license the earlier separated multiples inversion. RH remains open.

### Finite two-seed energy and exact rough-source splitting (2026-09-14)

**Established:** `RH/TwoSeedExactHeadEnergy.lean` defines the infimum of the
actual full squared Pareto Hilbert norm over finite legal combinations of
seeds 2 and 3 equal to one through N. The feasible set is proved nonempty,
the energy is nonnegative and monotone in N, and the compulsory head costs
at least N/(N+1). Arbitrary near-minimizers have an actual finite dilation
budget. For each fixed N, the finite-budget energies decrease to this
unrestricted finite-legal infimum. No rate uniform in N or exchange of
limits is asserted.

The actual Mellin zero obstruction gives a polynomial lower bound for this
infimum uniformly over all finite budgets.
`riemannHypothesis_of_cofinal_subpower` concludes Mathlib's actual RH if,
for every p>0, there is C such that arbitrarily large N satisfy
energy(N) <= C*(N+1)^p. Different exponents may use different cofinal
sequences, and the finite budgets are unrestricted.
**Open:** proving this cofinal subpolynomial upper bound.

**Established source calculation:** `Analysis/AdjacentGreenPair.lean`
evaluates the exact adjacent-pair square completion at Pareto weights.
It proves the signed Pythagorean split, the symmetric-profile correction
1/(2*n^2*(n^2-1)), and the finite selected-subset bound 1/(6*X^3).
The bound is elementary and needs no prime-counting estimate.
`RH/AdjacentGreenSource.lean` applies the split to the actual full finite
prefix Green energy for every even conductor. For the cumulative rough
source minus a gcd-atom coefficient field with g(1)=0, the compulsory jump
is proved from the definition. The unpaired coordinate 1 is retained.
`RH/AdjacentGreenSourceCorrection.lean` identifies the full prefix energy
of the optimal profile minus the symmetric neighboring profile exactly,
and proves the same uniform 1/(6*X^3) bound for selected centers beyond X.
**Open:** controlling the remaining distance of the repaired source to
the legally supported CRT atom span. These finite source identities do
not supply the full two-seed subpolynomial energy bound.

### Closed head minimizers and unbounded arithmetic projection (2026-09-15)

**Established finite-head repair:** `RH/FiniteTwoSeedHeadRepair.lean`
constructs a continuous linear repair from actual finite legal vectors.
For each fixed N, every vector in the closed two-seed legal space can be
approximated by finite legal vectors with exactly the same first N physical
coordinates. The operator norm may depend on N; no uniform estimate follows.

**Established optimum geometry:** `RH/TwoSeedHeadEnergyGeometry.lean`
constructs the canonical minimum-norm vector F_N in each closed exact-head
fiber. The finite legal infimum is unchanged on taking this closure:
`closedMinimizer_norm_sq` identifies norm(F_N)^2 with the actual energy(N).
For M>=N, `nested_minimizer_energy` gives exactly
energy(M) = energy(N) + norm(F_M-F_N)^2.
There is no missing tail or unsigned replacement.

`energy_bddAbove_iff_closure` proves that boundedness of energy(N) is
equivalent to membership of the constant one in the closed two-seed legal
space. In this case the minimizers converge strongly to one, every
energy(N)<=1, and energy(N) tends to 1.
Unconditionally, `energy_limit_dichotomy` proves that energy(N) tends either
to 1 or to positive infinity. This does not prove boundedness, a growth
upper bound, or a reverse implication from RH to two-seed closure.

**Established component necessity:** `RH/RootComponentExactHeadEnergy.lean`
realizes the actual arithmetic root projection on finite legal vectors by
selecting whole generators. Its projected head is forced by the exact head,
and its head energy is asymptotic to N/9; eventually its full norm squared
is at least N/18, uniformly over all finite dilation budgets.
`eventual_normalized_root_cancellation` proves, writing U for this component,
(inner(U,F-U)/norm(U)^2 + 1)^2 <= 18*norm(F)^2/N.
Thus any sublinear full-energy family requires asymptotically complete
signed cancellation. A uniform component angle separated from opposition
would force linear full-energy growth.
The supporting full signed Hilbert inequalities are in
`Analysis/DestructiveComponentEnergy.lean`.

**Established unconditional instability:** `RH/RootComponentUnbounded.lean`
uses m=6^(k+1) and the actual normalized binary wavelets W_m.
The four-generator packet p_k=W_m-W_(m+1) has full norm tending to zero,
whereas its root projection is exactly W_m and has norm one.
It vanishes at all physical coordinates below m.
Hence the root projection has no norm bound even on the finite legal
vectors vanishing on any fixed finite head, and has no continuous Hilbert
extension agreeing with it on the finite legal span. No RH or closure
assumption is used.

`exists_nearby_head_preserving_large_root` strengthens this: every
neighborhood of every finite legal vector, with any fixed finite head held
exactly, contains finite legal vectors with arbitrarily large root norm.
Near-optimal full energy alone therefore gives no component norm control.
This does not exclude choosing some better controlled representatives.

The instability does not force growth of the canonical source energy.
`closedMinimizer_orthogonal_packet` and `closedMinimizer_packet_energy`
prove, for k>=N, inner(F_N,p_k)=0 and exactly
norm(F_N+t*p_k)^2 = energy(N) + t^2*norm(p_k)^2.
The full Hilbert minimizer remains well-defined even though its algebraic
arithmetic component need not have a continuous extension.

**Open:** prove the actual cofinal subpolynomial upper bound for energy(N),
or control the corresponding orthogonal energy increments. The component
instability theorem rules out general component norm bounds inferred solely
from full-energy size; it neither supplies the source estimate nor disproves
the full signed-energy route. RH remains open.

### Compressed projection source mass and full Hilbert cutoff synthesis

Established in `Analysis/ProjectionCompressionDefect.lean`,
`LinearAlgebra/SourceSpectralMass.lean`, and
`Analysis/CompressedProjectionModes.lean`.

For orthogonal projections P and Q, a head source x in Q, and a tail t in
Q-perp, the exact full-source defect retains its signed cross term:
norm((I-P)(x+t))^2 = norm((I-P)x)^2 + norm((I-P)t)^2
- 2 inner((I-Q)Px,t).
The corresponding error is at most
2 norm(t) norm((I-Q)Px) + norm(t)^2.

For a finite orthonormal head eigenfamily satisfying QPe_i=lambda_i e_i,
the actual projections Pe_i realize the diagonal Gram matrix, full synthesis
norm, and signed error. Eigenvalues in [0,1] follow from these geometric
hypotheses. No modal norm identity is supplied as an extra assumption.

Let mu_i=c_i^2, k=sum((1-lambda_i)mu_i), and
L=sum(lambda_i(1-lambda_i)mu_i). The latter is exactly
norm((I-Q)Px)^2. With m(eta)=sum_{lambda_i<eta}(mu_i), the finite estimates are
k-L/eta <= m(eta) <= k+L/(1-eta) for 0<eta<1.
The actual half-cutoff/full-source comparison is
abs(m(1/2)-norm((I-P)(x+t))^2)
<= 2L + 2 norm(t) sqrt(L) + norm(t)^2.

The finite-subspace witness
h_eta=sum_{lambda_i>=eta}(c_i/lambda_i)Pe_i belongs to P and satisfies
norm(h_eta)^2 <= norm(x)^2/eta and
norm(x-h_eta)^2 <= m(eta)+L/eta^2.
These are full Hilbert norms, not truncated coordinate norms.
The one-mode theorem `arbitrarily_small_polarization_full_omission`
shows that arbitrarily small positive polarization is compatible with
omitted mass one.

**Formalization boundary:** the eigenfamily and its compression equations
are geometric inputs. This module does not assemble a cofinal family of
actual two-seed matrices or prove their source-mass decay. The infinite
weak-* limit and Pareto countermodel in the companion research note are
analytic results, not assertions of completed Lean formalization.

**Open:** establish arithmetic source improvement for the actual joint
binary and triadic legal spaces. Small leakage or weak-* compactness alone
does not prove disappearance of the low spectral mass. RH remains open.

### Arithmetic source improvement and far dilation limits

`Analysis/ProjectionSourceImprovement.lean` proves exact signed single-column
refitting, its Rayleigh gain, strict improvement from nonzero source
correlation, and membership of the refitted vector in an enlarged subspace.
Its Pythagorean identity includes every adjustment of the old coefficients.

For tail subspace T and current projection P, if
norm(Pz)^2 <= a norm(z)^2 with a<1, the full gain from any p+z, p in P,
z in T, is at most norm(T(b-Pb))^2/(1-a).
An additional source-tail bound gives the relative ceiling
a/(1-a) times norm(b-Pb)^2.
These concentration bounds are explicit hypotheses, not arithmetic conclusions.

`RH/TwoSeedFarDilationBlindSpot.lean` defines the actual binary and triadic
seeds together with all dilation indices greater than six. All generators
are legal, but every vector in their full Hilbert closure vanishes at
physical coordinate six. The squared error against hilbertOne is therefore
at least 1/42. This restricted family is not the full two-seed legal span.

**Analytic continuation, not yet fully formalized:** the companion note
derives an exact periodic Laplace formula for source correlations. It proves
strict improvement by every sufficiently large binary period multiple and a
joint two-seed lower bound in terms of the period mean, the signed quadratic
dilation charge, and a fourth-moment remainder. An explicit period-dependent
tail estimate supplies the hypotheses of the general gain ceiling.

**Open:** a nonsummable relative improvement rate for the actual cofinal
budget spaces. Strict improvement at every finite stage is insufficient:
the restricted family above can keep improving while retaining its positive
coordinate floor. No source-charge lower bound in terms of the full defect,
nor an RH proof, is supplied here.

### Ordinary adjacent packets and signed cross-seed covariance

**Established:** `RH/AdjacentDigitCovariance.lean` proves the complete
signed moved-interval head/tail identity for two arbitrary positive digit
seeds. Both infinite sums are proved summable. The full tail is uniformly
bounded, with no positivity assumption on the mixed covariance.
The period-six binary, ternary, and mixed jump means are respectively
1, 2, and 0. For d_p,m = digit(p,m)-digit(p,m+1), the actual Hilbert
covariance satisfies:
m(m+1) <d_2,m,d_2,m>/log(m) -> 1;
m(m+1) <d_3,m,d_3,m>/log(m) -> 2;
m(m+1) <d_2,m,d_3,m>/log(m) -> 0.
Explicit uniform deviations from the corresponding harmonic terms and
the equality with the actual bundled Hilbert inner product are verified.

**Established:** `RH/AdjacentDilationPackets.lean` defines the original
scaled generator and its ordinary adjacent difference A_p,m. It proves
the normalization, exact zero target mean, source correlation
<1-P1,A_p,m> = -<P1,A_p,m>, and the exact Mellin factor
zeta(s)/s * (1-p^(1-s)) * ((m+1)^(1-s)-m^(1-s))
on Re(s)>1/2, s != 1. This last domain is explicit in the Lean theorem.

**Written analytic continuation, not yet fully formalized:** the note
RH_Adjacent_Packets_and_Zero_Ordinates_2026-09-15.md gives the stronger
mixed bound (14+8 zeta(2))/(m+1), by signed period-six Abel cancellation
throughout the infinite tail, the shrinking-frequency zero-ordinate
scaling limit, and full-period numerical block audits. These conclusions
remain written results. The original packet diagonal laws log(m)+O(1)
and 2 log(m)+O(1) are now formalized in AdjacentPacketNormBounds.lean.

**Open:** control the actual source correlations and the entire screened
matrix across the ordinary block M <= m < 2M. A sufficient estimate is
D_M <= C log(2M)(D_M-D_2M)+epsilon_M with epsilon_M -> 0 independently
of RH. Same-index packet decorrelation and leading zero-ordinate
equidistribution do not discharge this obligation. No RH proof is supplied.

### Two-three resonance cell and canonical ordinary budget

**Established:** `LinearAlgebra/TwoThreeResonanceCell.lean` proves the
exact four-square decomposition of the five-dimensional leading screened
quadratic form. Its kernel consists precisely of multiples of
(1,1,1,-1,-1); the form lies between 2/3 and 7/3 times squared coefficient
size on the compatible complement. The module gives the exact dual
completion, a compatible optimizer attaining the four-charge source energy
Q, and Q(h) >= (3/7) |h|^2 for compatible h. These are finite quadratic
identities, not a provider of the actual Gram asymptotic.

**Established:** `RH/TwoThreePacketRelations.lean` proves the actual
Hilbert generator cocycle, product-seed decomposition, and exact relation
A_2,3k + A_2,3k+1 + A_2,3k+2 - A_3,2k - A_3,2k+1
= A_2,k - A_3,k. It proves source compatibility for any source orthogonal
to the two old packets, including the actual projection residual when
those packets belong to the old subspace. The common source sum is the
legal composite-seed correlation with A_6,k.

**Established:** `RH/FiniteResidueIndependence.lean` proves that every
finite relation among residue(n), n >= 2, has zero coefficients.
`RH/TwoThreeCanonicalBudget.lean` proves that retaining every ternary
generator and only binary generators with 3 not dividing the dilation
index leaves the actual ordinary budgetSpan unchanged. Every elimination
stays within the original budget.

**Further written results:** RH_Resonance_Cell_and_Canonical_Budget_2026-09-15.md
gives the general fixed-slope full covariance kernel, the four-charge
asymptotic with trial coefficient control, and the full five-cycle inverse
Gram formula. Canonical independence, dimension 2M-floor(M/3), and the
concrete cell covariance bounds are now formalized below. Covariance
constants are not asserted uniform over growing slopes.

**Open:** a quantitative lower bound for the actual signed source
variation across the entire ordinary block, with all cross-cell energies
retained. Neither the positive finite quadratic form nor removal of exact
relations establishes the required nonsummable relative improvement.
The RH-closing estimate remains open.

### Formal canonical basis and quantitative resonance gain

**Established:** RH/TwoThreeCanonicalBasis.lean proves independence of
the actual canonical generator family, its exact cardinality, and
finrank(budgetSpan M) = 2*M-M/3 for every natural M.
RH/TwoThreeHilbertBudget.lean transports the same basis and dimension
to the existing Pareto budgetHilbert, proves nestedness, and discharges
the old and new cell membership conditions within the original budgets.

**Established:** Analysis/FiniteHarmonicBounds.lean proves uniform finite
harmonic cutoff bounds. RH/AdjacentPacketNormBounds.lean proves the
original packet diagonal laws with explicit bounded errors.
RH/ResonantDigitOverlap.lean, RH/ResonantHarmonicHead.lean, and
RH/OldNewDigitHead.lean prove exact signed overlap/head/tail identities
and the concrete periodic coefficients. RH/CrossResonanceCovarianceBounds.lean,
RH/OldNewCovarianceBounds.lean, and RH/SameScaleCovarianceBounds.lean
give unconditional, scale-independent remainder bounds for every entry
of the seven-column cell Gram matrix, for k >= 24. The entire infinite
tail is retained. These are fixed cell slopes, not uniform estimates
over all ratios in a growing ordinary block.

**Established:** Analysis/SmallColumnCovariance.lean gives a weighted
Young transfer estimate, instantiated by RH/AdjacentPacketCovarianceTransfer.lean
for actual binary and ternary packets. Analysis/ResonanceCellRefit.lean
gives exact trial identities and enlarged-space lower bounds.
Analysis/ResonanceLeadingGram.lean retains every signed mixed Gram entry
and bounds the corrected energy by L*energy(a)+(21/2)*E*sizeSq(a),
under an explicit raw Gram error E. RH/TwoThreePacketRefit.lean supplies
the actual packet consumer. RH/TwoThreePacketLogGain.lean already gives
the unconditional ordinary-budget gain sizeSq(h)/(7*log(k)+K) <= D_M-D_2M,
for k > 0 and 3*k+3 <= 2*M.

**Established:** RH/TwoThreePacketSharpGain.lean assembles all 49 actual
raw Gram entries with the fixed error B = 4*twoSeedEnergy+2259. It proves
ordinary_budget_sharp_log_gain:
sizeSq(h)/((7/3)*log(k)+K) <= D_M-D_2M,
where K=(21/2)*B+7/3, k >= 24, and 3*k+3 <= 2*M.
It also proves ordinary_budget_four_charge_gain:
sourceEnergy(h)/(harmonic(k)+(63/4)*B) <= D_M-D_2M.
Both have only the stated numerical index assumptions. The covariance
providers and original-budget membership obligations are fully discharged.
The explicit correction is followed by full old-space refitting.

**Still written rather than formally asserted:** the general fixed-slope
covariance kernel, the full screened five-vertex inverse Gram formula,
and the exact four-charge asymptotic with trial coefficient bounds.
The canonical dimension and the concrete cell entry estimates above are
now formal results, superseding their earlier written-only status.

**Open:** a lower bound on the actual source variation sufficient to
force nonsummable relative gains across the entire ordinary block.
No source lower bound, RH assumption, or zero-ordinate distribution
hypothesis is hidden in the unconditional local estimates. Local gains
must not be summed without controlling the cross-cell Gram matrix.

### Cofinal bounds force full Pareto projection convergence (2026-09-26)

**Conditional research reduction:** a fixed energy bound at arbitrarily late
exact-head approximants in the actual closed residue span forces the limiting
projection defect to vanish. No RH-to-density implication is assumed.

- `CoefficientStabilization.limitEnergy_eq_zero_of_cofinally_bounded_exact_head_errors`
  in `RH/ExactHeadCofinalBounds` reuses the actual residual-tail product lower bound.
- `CorrectionTail.projection_norm_tendsto_zero_of_cofinal_bounded_tailError`
  specializes it to the arithmetic Möbius tails and concludes full norm convergence.
- `projection_norm_tendsto_zero_of_subsequence_bounded_tailError` permits any
  cofinal index map, without strict monotonicity.
- `riemannHypothesis_of_cofinal_bounded_tailError` applies the checked
  convergence-to-RH direction.

**Open:** a constant `C` with
`∀ M, ∃ n ≥ M, ‖CorrectionTail.tailError n‖^2 ≤ C`.
This is weaker than the previously required bound at every index.
The existence of such a cofinal bound is not established.

### Uploaded Pareto projection proof: correction energy and arithmetic tails (2026-09-22)

**Established:** the internal argument in the uploaded `Pasted markdown.md`
is assembled in the existing concept owners and dedicated modules.
See `RH/ResidueProjectionProofFormalization.md` for the equation map,
indexing convention, and precise boundary of the classical RH endpoint.

- `Pareto.hilbertSequence_sq_le_norm_sq` in `RH/ParetoCoordinateBounds`
  gives the physical-coordinate square bound.
- `Pareto.normalizedResidue_partial_sum_harmonic` in
  `RH/ParetoResiduePartialSummation` retains the arbitrary-cutoff boundary.
- `GramMobiusCorrection.mobiusResidual_projection` and
  `error_eq_mobius_matrix_correction` prove the exact full correction energy.
- `GramMobiusCorrection.mobiusSynthesis_mem` is owned by
  `RH/ResidueGramMobiusCorrection`; `RH/ResidueGramCorrectionPairing`
  reuses it instead of redeclaring the membership lemma.
- `ProjectionSchur.limitEnergy_eq_one_sub_log_sub_schur_tsum`,
  `projection_norm_tendsto_sqrt_limitEnergy`, and
  `canonical_saturation_equivalences` in `RH/ResidueSchurLimits`
  identify the limiting defect and all six equivalent saturation conditions.
- `CorrectionTail.tailError_eq_mobiusResidual_sub`,
  `correction_eq_weighted_tail`, `correction_sq_le_tail_product`,
  `projectedDualTailEnergy_tendsto_zero`, and `tailError_energy_split`
  in `RH/ResidueProjectionCorrectionTail` retain the actual complete
  arithmetic tail and both factors in its Cauchy–Schwarz estimate.

**Conditional research reductions:** `riemannHypothesis_of_tail_products`,
`riemannHypothesis_of_bounded_tailError`, and the shifted Schur endpoint.
**Open:** the arithmetic product decay, a sufficient uniform tail-energy
bound, or equivalent Schur saturation. None is asserted unconditionally.

**External theorem formalization obligation:** the argument
`hBaezDuarte : RiemannHypothesis → hilbertOne ∈ closedSpace` remains
explicit in `projection_norm_iff_riemannHypothesis_of_baez_duarte`.
This missing provider for a known classical theorem is distinct from
the open mathematical assertion `limitEnergy = 0`.

### Actual prime sensors, coefficient mass and moving ordinate lags (2026-10-11)

Established structural results and conditional arithmetic consumers:

- RH/CombinedPrimeSensors.lean proves the actual correlated prime Gram
  inner(k_q,k_r)=2+2*q^2*1_{q=r}, the complete aggregate remainder identity,
  and the finite-prime actual distance floor s/(2*(1+s)).
- RH/TwoSeedPrimeCoefficients.lean proves exact prime coefficient recovery,
  the full one-prime error decomposition, quantitative error bounds, and
  necessary coefficient sums tending to -1/q under legal norm convergence.
- RH/PrimeCoefficientStability.lean retains the exact normalized sensor
  synthesis square 2*sum(c^2)+2*(sum(c/q))^2 and proves the joint finite
  coefficient error bound sum(A_q+1/q)^2 <= 2*(1+s)*||1-F||^2.
- RH/ResidualCutoffSchedule.lean extends the exact residual product and
  zero-energy iff nonsummable relative-gain endpoint to every monotone
  cutoff schedule, with no prescribed dilation factor.
- RH/PrimeCoefficientGain.lean proves that actual full-optimizer new-prime
  coefficient energy E is at most 2*(1+s)*(D_A-D_B). It provides an RH
  consumer for a nonnegative nonsummable minorant of E/(2*(1+s)*D_A).
- Analysis/OrdinateLagPhase.lean proves exact lag-gap boundary strips,
  finite and moving-lag phase displacement bounds, and correlation transfer.
  Same-frequency correlation tends to one under the endpoint counting
  premise alone.

Six modules add 48 public supporting theorems. Exact-module import/audit
job job_tuoD2lCM0tuG4R0nzrxDxe0gR6sTRVEI completed with verified=true.
These are not unconditional RH or actual-zero equidistribution results.
The RH applications are **conditional research reductions**. Open:
actual nonsummable prime-fit-energy minorant, actual relative-gain/cost
provider, and any actual-zero enumeration/counting/marginal instantiation
used for the moving-lag application. Uniform Landau/zero-density providers
from the original handoff and reverse two-seed density are not discharged.
See RH/ZeroOrdinateResidualGainContinuation20261011.md.


### Chebyshev midpoint, actual Pareto energy and endpoint obstruction (2026-10-11)

Seven modules formalize exact finite algebra and actual Chebyshev energy.
Established: midpoint bijection and weighted squares with the terminal term;
prime-power projection and multiplicative twisting; local exp/log through degree
three; signed harmonic identity H_N = R_N^2/(N+1) + D_N; exact unit-cell and global
continuous/Pareto energy; finite comparison bounds; strict and endpoint off-line
zero energy obstructions.

`RH/ChebyshevEnergyCriterion.lean` supplies
`ChebyshevMellin.offLineZeroDampedEnergyDivergence`, discharging
`OffLineZeroDampedEnergyDivergenceTarget`, including the endpoint s = 2 Re rho.
`ChebyshevMellin.riemannHypothesis_of_all_chebyshev_damping` is a
**conditional research reduction**. Open: the actual arithmetic conditions
`forall epsilon > 0, ErrorFiniteEnergy (1+epsilon)` without assuming RH.
The full handoff is only partly formalized; the actual B2 expansion and full
coefficientwise exp/log are not claimed to have been proved by this task.

The seven-module import and ten selected transitive axiom checks passed server
job `job_uK7mcrCfduM7ynT0dmh3asLdW-k8794f`; all selected checks reported only
`propext`, `Classical.choice`, and `Quot.sound`.
See `RH/ChebyshevHandoffVerification20261011.md` for precise scope and obligations.

### Backwards RH implication audit: innovations, endpoint, and critical feedback (2026-10-13)

`RH/OptimalDilationInnovation.lean` retains exact signed floor-dilation
correlations and column norms for the actual full projection spaces. It proves
both the ordinary gain bound and the stronger adjacent-gain product bound.
Every-scale quadratic-source feedback forces geometric decay. The scalar
contraction is isolated in `Analysis/AdjacentGainContraction.lean`.

`Analysis/FiniteSpectralJensen.lean` proves the finite correction-weighted
Jensen lower bound, positive-tail fact, and positive-envelope version.
`Analysis/FiniteSpectralCriticalFeedback.lean` proves the critical moving-margin
limit argument. `RH/ParetoActualSpectralCriticalFeedback.lean` connects it to
the actual compact spectral system and existing RH bridge, retaining all
source weights and the complete contrast.

`RH/FiniteEndpointGram.lean` proves the actual cross-scale signed pairing and
first-site-subtracted Gram bound. `Analysis/ResidualEndpointFeedback.lean`
proves the endpoint coefficient, cofinal limit argument, and reciprocal
quadratic-recurrence bound, including possible zero iterates.

Conditional research reductions:
- `riemannHypothesis_of_cofinal_twoSource`: Open — a fixed positive quadratic
  lower bound for the actual two-dilation source on a cofinal set.
- `riemannHypothesis_of_cofinal_quarticSource`: Open — the weaker quartic
  lower bound on a cofinal set. Its scale is suggested by adjacent gains;
  no arithmetic provider is asserted.
- `riemannHypothesis_of_actual_compactSpectrum_cofinal_critical_contrast`:
  Open — the displayed actual critical-margin contrast estimate with an
  additive error satisfying inner-log-scale times error tending to zero.
- `riemannHypothesis_of_cofinal_endpoint_feedback`: Open — the stated actual
  first-coordinate endpoint bound, up to an error tending to zero.

The exact implications do not prove RH or the feasibility of their open
hypotheses. The external Burnol lower-bound comparison is discussed in the
[audit note](RH/BackwardRHVerification20261013.md), and is not newly formalized
by this checkpoint. Provenance: the user's request to verify the preceding
argument before attacking A and then B. These are independently formalized
deductions; no novelty claim is made. Final server checkpoint acceptance is
required before publication.

### Common quotient-cell variance and inverse-Gram certificates (2026-10-16)

Established: Analysis/FiniteWeightedVariance.lean proves exact centered moments,
translation and pairwise variance identities, monotonicity in sets and weights,
the diameter bound, two-coordinate lower bounds, and scalar two-offset completion.

RH/CanonicalMobiusPrimeCells.lean proves the concrete boundary cell condition
q*b <= n < (q+1)*a, the equivalence q*(b-a)<a for a<=b, and the Mertens-profile
increment and Lipschitz estimate. Its interval variance bound specializes to
V_P([b,2a)) <= (2a-b)*(2a-b-1)^2/(8ab). Exact coordinate moments, the full
first-cell residual split, and the two-cell mean incompatibility term retain
the entire complementary infinite energy.

RH/CanonicalMobiusCellCeiling.lean proves the exact finite-envelope split and
the bounds cell variance <= complete selected energy <= inverseCeiling.
Every normalized witness gives the upper certificate consisting of cell
variance, the cell mean square, the full finite complement, and the explicit
diagonal tail allowance. All signed cross terms remain in residual squares.

The development adds 32 public theorem declarations and three definitions.
Open: uniform arithmetic bounds for the cell mean and complement along growing
legal families. No uniform complete-energy bound, squarefree closure, or RH
is asserted. The Baker--Harman--Pintz consequence and Python numerical
enclosures in the research record are not Lean-verified arithmetic providers.
Research record: RH/CanonicalMobiusCommonCellResearch20261015.md.

### Squarefree Q exact-head blocks and complete Parseval convergence (2026-10-16)

Conditional research reduction: `RH/QSquarefreeExactHeadAverages.lean`
specializes the actual block-average theorem to the algebraic squarefree span.
`squarefree_span_iff_common_period` proves that every legal squarefree vector
has a squarefree common-period divisor-span representation, and conversely.
`exists_squarefree_exact_head_block_averages` provides increasing selections,
finite squarefree-legal blocks, squarefree common periods, exact growing heads,
strong convergence to one, and vanishing complete arithmetic Parseval energy.
The Parseval sum remains over all positive integers, not just squarefree indices.
`squarefree_full_error_bound_of_periodic_tail_bound` obtains both legality and
the full Q bound from the literal finite-period tail, deriving periodicity and
boundedness from the divisor span. The theorem
`squarefree_closure_capacity_and_rh_of_bounded_exact_heads` assembles actual
squarefree closure, capacity divergence, and Mathlib RH under the same hypothesis.

Open: construct the squarefree legal exact-head family with one uniform full-Q
error bound, or its uniformly bounded literal finite-period tail provider.
This entry does not establish that arithmetic bound or unconditional RH.
See `RH/QSquarefreeExactHeadAveragesResearch20261016.md`.

### Full-Pareto parity-normalized optimizer L1 criterion (2026-10-18)

Current-main imported-module and eight axiom checks passed
`job__TKW3JuTSDLUYSAnDOBhp-_XucQVpLvi` (2026-10-18).
Final project validation and publication remain gated by checkpoint.

Earlier server Lean verification: `job_KLC6tRtfgzFA8tJxNO_O6Ly9wK01PzEp` passed the
integrated module, optimizer characterization and theorem axiom checks.
The checked declarations use only `propext`, `Classical.choice` and `Quot.sound`.

The combined quantitative extension passed server job
`job_fY-hwuPB0JcXS0v3H1ZourWi2xhAxArJ`, including the finite dyadic
identity and recurrence. Its axiom checks report only the same three foundations.

Established identities and constructions:
- RH/ParetoParityOptimizer.lean constructs the unique minimizer in the full
  Pareto norm over g₂,...,g_M (M=n+3), with even conditional mean 1 and odd
  conditional mean 0. The legal expansion, both observations, exact distance
  completion, uniqueness and unconditional Hilbert convergence are proved.
- The even indicator has mean, squared L2 norm and L1 norm 1-log(2).
- Analysis/SingleObservationProjection.lean supplies reusable orthogonal
  observation and exact target-distance completion lemmas.
- RH/ThresholdHilbertL1.lean proves L1 continuity and the exact negative-mass
  identity (L1 norm minus mean)/2.
- RH/MobiusResidualFirstCoordinate.lean adds the exact positive identity
  r(1)=limitEnergy/2 + ||r-(1/2) hilbertDilation₂ r||², including its lower bound.

- RH/FiniteResidueDilation.lean proves actual legal finite-span dilation and the
  exact identity r_{2M}(1)=delta_{2M}-delta_M/2+||r_{2M}-D2 r_M||^2.
  The repository's unscaled D2 is (1/2) times hilbertDilation 2.
- ParetoParityOptimizer proves e_M=p*delta_M/(p-delta_M), p=1-log(2),
  and the exact dyadic optimizer completion with both norm-square and energy
  difference corrections retained. It implies e_{2M} <= e_M/2 + (||U_{2M}||_1-p).
- The limiting excess satisfies (2-sqrt(2))*e_infinity <= ||U_infinity||_1-p
  <= sqrt(e_infinity), with an exact first-coordinate square completion.
  These same-stage lower bounds are asserted for the limit, not finite cutoffs.

Conditional research reduction:
- ParetoParityOptimizer.riemannHypothesis_of_l1Norm_tendsto proves that the
  concrete optimizer L1 norms tending to 1-log(2) imply RiemannHypothesis.
  Its sole hypothesis is this scalar limit.
- The scalar limit, L1 convergence to the indicator of divisibility by 2,
  and negative mass tending to zero are proved equivalent for this sequence;
  each therefore suffices for RH. No RH-to-limit converse is asserted.
- Vanishing first-coordinate negative part, U_M(1) tending to zero, and the
  original L1-norm target are proved equivalent; each suffices for actual RH.
- The L1-norm target along any cofinal selection of stages suffices for RH.
- One-point refinements (2026-10-18): `optimizer_error_dyadic_first_bound`
  proves e_{2M} <= e_M/2 - U_{2M}(1), using the exact completion above.
  `riemannHypothesis_of_cofinal_optimizer_first_lower` needs only:
  for every epsilon > 0 and M0, some M >= M0 has U_M(1) >= -epsilon.
  This is a sufficient conditional reduction; the one-sided bound remains Open.
  The imported candidate and five axiom checks passed
  `job_zbKfieMvF_8p93VhgbklZi5owu4kq0vU` with only the standard foundations.
- **Open:** prove any of these equivalent convergence conditions for the
  actual optimizers. The reduction does not discharge this analytic input.

### Recovered Pareto parity continuation integration (2026-10-19)

Established identities and interfaces integrated from the preserved checked
source commit `3e698b7e48af90aae6d91bb159333f83cbb8ec35`:
- `RH/ParetoL1DualTest.lean`: complete-L1 bounded physical dual tests.
- `RH/ParetoProjectionOvershoot.lean`: explicit first-point sign test,
  full positive-projection sum, and critical cofinal overshoot endpoint.
- `RH/FiniteDyadicEndpoint.lean`: the all-real scaled completion retains
  the full signed coordinate and norm-square remainder; rational specialization
  and the explicit arithmetic-provider estimate are separate consequences.
- `RH/GramEndpointCriterion.lean`: raw mixed inverse-Gram cofinal criterion.

The integration adds 12 theorems and one definition; the rest of the original
20-statement inventory uses existing canonical definitions and results rather
than duplicate theorem spellings. No second overshoot module is exported.
Conditional research reductions: the cofinal overshoot and raw-Gram RH
consumers. Open: prove the actual arithmetic upper/lower bounds in their types.
See `RH/ParetoParityIntegrationResearch20261019.md` for source recovery,
original verification evidence, and the statement-by-statement coverage map.

### Exact Pareto overshoot endpoint gaps (2026-10-19)

Established identities and inequalities in `RH/ParetoOvershootEndpointGap.lean`:
- Exact bounded-sign-test slack and the limiting endpoint-gap decomposition.
- The finite equality retains the signed dyadic defect at each positive stage.
- Finite and limiting first-coordinate quadratic lower bounds.
- The energy-only refinement `omega >= (1 - sqrt(2)/2) delta +
  ((3 sqrt(2) - 4)/4) delta^2` for the actual limiting residual.

The new module adds seven theorems. Together with the 12 recovered additions
above, this continuation contributes 19 new theorems and one definition.
The seven declarations and axiom checks passed
`job_qiE3BO2Vyy78TlZUs_CXtOgzC3Vp75NW` with only standard foundations.
Conditional quantitative consumer: an actual upper bound
`omega <= (1 - sqrt(2)/2) delta + eta` gives
`((3 sqrt(2) - 4)/4) delta^2 <= eta`.
Open: obtain a vanishing arithmetic endpoint error for the actual optimizers.
See `RH/ParetoParityIntegrationResearch20261019.md` for the exact identities.

### Finite-head localization of the Pareto overshoot estimate (2026-10-19)

Established in `RH/ParetoNegativeMassHead.lean` and
`RH/ParetoOvershootHeadCriterion.lean`: the complete negative-part vector,
exact finite-head/tail pairing, and the unconditional enclosure
`0 <= omega_M - B_(M,H) <= sqrt(delta_M/(H+1))` for the actual optimizer.
The diagonal head H=M-1 converges to the complete limiting overshoot.

Conditional research reduction: the cofinal finite positive-part head budget
`B_(M,M-1) <= (1 - sqrt(2)/2) delta_M + epsilon` is equivalent to vanishing
of the limiting residual and has a checked RH consumer.
Open: prove this arithmetic head budget for the actual inverse-Gram coefficients.
The requested unconditional overshoot upper bound remains unproved.

Twelve public declarations and all axiom checks passed
`job_lrmajfiqgiMyazUYjWdGWUw8uQAZMnQi` using only standard foundations.
See `RH/ParetoOvershootArithmeticAttemptResearch20261019.md` for exact
identities, the remaining obligation, and the primary-literature audit.

### Direct floor encodings and orthogonal CRT projection identities (2026-10-19)

Established:
- `RH/CRTCarryArithmetic.lean`: actual integer floor, unconditional bounds,
  exact quotient and real-floor formulas, general valid representatives,
  integer gauge shifts, periodicity, symmetry, jumps, head drift, and Bezout existence.
- `Analysis/ScreenedCarry.lean`: literal I-minus-starProjection, signed raw
  Gram energy, Pythagoras, membership, invariant screened Gram/source data,
  equal spans and actual target projections, exact distance gains, and finite blocks.
- `RH/QCRTCarry.lean`: directly encodes the floor sequence using encodeQ;
  proves its synthesis identity, representative independence, conductor bound,
  and complete-Q energy, projection and finite-block results.
- `RH/QCRTPrimorialCarry.lean`: application to the existing all-divisor
  primorialStage and the complete new-prime block, including composite old divisors.
- `RH/QCRTCarryBlockBridge.lean`: identifies the direct floor encoding with
  the existing QCarryScreenedBlock.pairVector, fullBlock and their screen;
  transfers the complete divisor-stage equality and full trace estimate.

No residual-exhaustion estimate is proved. The ordinary explicit hypotheses
are positive conductors, integral valid CRT coefficients, and old-space membership.
Seven central axiom checks use only standard Lean foundations.
See `RH/QCRTCarryResearch20261019.md` for the scope and mathematical boundary.

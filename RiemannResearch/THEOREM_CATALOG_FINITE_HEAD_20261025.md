# Finite-head convergence: theorem catalog supplement

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

# CRT Gram minimizers: theorem catalog supplement

28 October 2026. See [research memorandum](RH/CRTGramMinimizersResearch20261028.md).

## Established statements

Module `RH/QCRTGramMinimizer.lean`, namespace `RiemannResearch.RH.QCRTGramMinimizer`:

- `optimizer_feasible`, `completion`, `norm_completion`: actual coprime CRT seed, complete affine feasible set, and target-zero/target-one minimization.
- `energy_schur`, `optimizer_normal`: exact signed Gram equations, with the inverse supplied by proved linear independence.
- `seed_energy_gain`, `energy_le_seed`: exact energy reduction and comparison to the explicit coprime-counting seed.
- `objective_norm_gap`, `objective_error_gap`, `objective_gap_le_tail`: squared displacement between the two minimizers bounded by the complete Q tail of the constant vector.
- `missing_prime_value`: an exact head ending immediately before an omitted prime forces value 2 at that prime.

## Conditional research reduction

`riemannHypothesis_of_bounded_energy` requires a uniform bound on the actual complete norm energy of the constructed minimizers, squarefree periods, and the explicit expanding prime cover.

Open: supply a finite constant B bounding every stage's minimum energy. Neither the divergent explicit seed nor finite numerical improvements discharge this provider.

## Separate computational evidence

Exact rational Python certificates bracket the actual minima at L=30,210,2310,30030. Full-tail floating-point computations reach L=9699690. These numerical intervals have not been formalized in Lean. See the accompanying computation bundle and the research memorandum for exact witnesses, executable certificate scripts, and completed verification logs.

## Exact-head correction certificates and conductor gaps

See [continuation memorandum](RH/MinimumEnergyCorrectionCertificates20261028.md).

Established Lean statements:

- `RH/QResidueEnergyCertificates.lean`: complete signed correction gain with its
  norm-square remainder; one-direction optimization; exact dictionary-enlargement
  and head-enlargement energy identities and their monotonicity consequences.
- `RH/QCRTCorrectionCertificates.lean`: actual compensated correction blocks,
  automatic zero-head membership and squarefree legality, and the complete signed
  finite coefficient certificate. The stage-independent bound is still Open.
- `RH/QCRTFiniteCertificates.lean`: binary legal vectors at periods 6 and 30,
  exact heads 2 and 5, complete energy at most 1; canonical stages j=1 and j=4
  therefore have minimum energy at most 1.
- `RH/QCRTConductorGap.lean`: exact head agreement propagates across conductor
  gaps; every period-210/head-10 and period-30030/head-15 feasible vector has
  complete energy greater than 1. In particular,
  `minimumEnergyApproximant_fourteen_gt_one` rules out C=1 for the entire
  canonical diagonal. An arbitrary finite common bound remains Open.

The 23 rational trial-vector certificates in the
[experiment bundle](https://chatgpt.com/library?file_id=libfile_3a2612c77a048191b8ec721ccd53ffca&account_id=personal) extend slower/smaller head schedules. Their independent Python checker includes the entire infinite
tail. They are not Lean numerical theorems. Trial-vector lower bounds are not
asserted as lower bounds on the minima; the conductor-gap Lean statements are
separate actual lower certificates.

## Blocks, complete tails, and half-period oscillation

See [blocks and oscillations memorandum](RH/MinimumEnergyBlocksAndObstructions20261028.md).

- `RH/QResidueWeightEnclosures.lean`: exact periodic finite-prefix identities,
  followed by two-sided enclosures of the complete inverse-square progression
  tails. No omitted Q atoms are treated as zero.
- `RH/QCRTConvexBlocks.lean`: actual canonical finite affine blocks preserve
  the smallest head and satisfy the full signed double-sum energy identity.
  A larger-period fixed-head minimum dominates every such block with the exact
  squared-distance remainder. Mixing a fixed-period plateau adds a squared
  distance to the earliest-head minimum.
- `RH/QCRTPeriod210Certificate.lean`: an explicit signed ternary vector with
  exact head 6 and complete energy <47/50. The same bound holds for the actual
  canonical stage j=5. Finite arithmetic is kernel checked.
- `RH/QCRTBinaryBlockGain.lean`: an explicit rational convex block of the
  period-6 and period-30 binary certificates improves the period-6 certificate
  by at least 1/1000000 in complete squared norm; its exact head is 2.
- `RH/QHalfPeriodHeadOscillation.lean`: full signed half-period identities;
  no squarefree-period exact-head-6 vector has global range [0,1], and no
  exact-head-14 vector has global range [-1,1]. Period arithmetic is discharged.
- `RH/QHalfPeriodLogarithmicOscillation.lean`: every prime-covering squarefree
  period 2m and exact head H<2m force the exact increment
  f(m+t)-f(m)=Nat.log 2 t when 0<t and 2t<=H. The actual canonical family
  satisfies this identity and has no finite uniform coordinate-amplitude bound.
  These are amplitude obstructions, not a proof of unbounded Q energy.

The [additional experiment bundle](https://chatgpt.com/library?file_id=libfile_03406b562cb88191a3558ec2f0aa3edb&account_id=personal)
contains independently checked rational full-tail convex-block certificates and
larger-period, slower-head candidates through period 510510. These numerical
intervals are separate Python evidence, not Lean numerical theorems.

Open: the common complete-Q energy bound (or bounded cofinal schedule) required
by the existing RH criterion. Neither finite block gains nor growing pointwise
oscillation settle this obligation. No new conditional RH wrapper is asserted.

## Period/head balance, dilation obstruction, and prime repair

Continuation of the exact-head handoff, Sections 9.A and 9.B; see
[the detailed research memo](RH/PeriodHeadBalanceAndFreshDilation20261028.md).

- `RH/QCRTPeriodHeadBalance.lean`: actual primorial minimum-norm heads,
  exact period-gain/head-cost Pythagorean identities, and the telescoping
  signed energy budget for any monotone schedule sigma with n<=sigma(n).
  The RH consumer is explicitly conditional on the cumulative budget bound.
- `RH/QFreshDilationObstruction.lean`: the continuous finite divisor
  charge annihilates V_L and D_m f for every Q vector f whenever m does not
  divide L. Their closed span cannot have exact head L. At L=6 the complete
  error is 2/(37*zetaTwo) plus an explicit squared-norm remainder.
  Compensated residues outside the old period have charge 1/d and escape
  this restricted obstruction.
- `RH/QCRTPrimeRepair.lean`: for a missing prime p<L, an exact head
  through p-1 in V_L admits an explicit optimized repair in V_(pL) with exact
  head p. The full signed energy is proved, its denominator is nonzero,
  and squarefree legality is discharged when L is squarefree.

All three modules and ten main declaration axiom audits passed Lean.
The memo separates a rational complete-tail Python certificate from Lean
numerical theorems. RH remains open: neither the signed-budget bound nor
uniform control of the repairs through all composite head coordinates has
been established. This continuation does not interpret the restricted
dilation obstruction as an obstruction to the full squarefree dictionary.


## Delayed-head primorial schedules

See [the delayed-conductor research memorandum](RH/DelayedCRTConductorSchedule20261028.md).
The earlier fixed-stage minimizers and conductor-gap obstructions are unchanged.

- `RH/QCRTDelayedSchedule.lean`: equality of complete zero-head spaces and
  minimum-norm adjustments across conductor gaps; concrete head plateaux at
  periods 510510 and 9699690; exact comparison with the obstructed old period.
- `RH/QCRTGapRefinement.lean`: after adjoining 17, actual head-15 vectors have
  one free coordinate in the old twenty-site obstruction. The exact signed
  square completion gives the complete lower bound
  32932869651286797001/(20748169979939001600*zetaTwo), and in particular >9649/10000.
- `RH/QCRTMinimumHeadCost.lean`: for the actual minimum-norm primorial family,
  the next-conductor cost equals squared mismatch divided by the complete
  tangent capacity; its exact coefficient form and energy-ceiling acceptance
  criterion are proved with explicit feasibility and positive-capacity hypotheses.
- `RH/QCRTPeriod510510Certificate.lean`: a concrete legal 14-atom vector is
  exactly one through 16 and has complete energy at most
  3108600811/3125000000<1. Its integer ceiling sum and whole-tail estimate are
  kernel checked. The actual minimum at period 510510, head 15 is therefore <1.

- `RH/QCRTPeriod9699690Certificate.lean`: a concrete legal 17-atom vector is
  exactly one through 20 and has complete energy at most
  311254353881/312500000000<1. The actual period-9699690/head-19 minimum
  satisfies the same bound. Every prefix ceiling and the full tail are checked.

The [reproducibility packet](RH/DelayedCRTComputations20261028.md) contains
six exact computational certificates with immutable rational witnesses and a
standard-library verifier. The tighter 510510/head15 bound <0.975197 and the
223092870/head23 bound <0.990495 are external arithmetic certificates, not
Lean numerical theorems. Floating-point discovery values are labeled separately.

Open: the uniform complete-energy bound for an infinite cofinal schedule.
Finite favorable examples and the exact capacity test do not prove that the
period-enlargement search terminates at every head. No new RH wrapper is added.

## Epsilon witnesses and complete exact-head errors

See [the epsilon continuation memorandum](RH/EpsilonCRTApproximation20261028.md).

- `RH/QExactHeadEpsilonBounds.lean`: full signed error identity for an exact
  head, the complete estimate error² ≤ 2(energy−1)+4τH, and
  τH ≤ 1/(zetaTwo*H) ≤ 76/(125H). The explicit legal period-9699690/head-20
  vector has complete error <17/50, with all arithmetic kernel checked.
- `RH/QSquarefreeEpsilonCriterion.lean`: direct forall-epsilon/exists-legal-
  witness characterization of closure, the conditional RH consequence, and
  a sufficient provider for actual primorial minima with H*epsilon² ≥608/125
  and energy ≤1+epsilon²/8. Period enlargement preserves successful energy
  certificates, and requiring an arbitrarily large period adds no strength.
  Complete-error witnesses admit a selected sequence with norm <2.

Open: the universal epsilon provider itself. The formulation avoids assuming
a bound on the original canonical family; it does not prove existence of
arbitrarily accurate legal vectors. The external head-23 error <0.3 remains
computational evidence, separate from the Lean error <0.34 theorem.

## Dyadic cofinal schedules and comparison with Pareto errors

See [the cofinal-schedule memorandum](RH/CofinalCRTAndMeasureComparison20261028.md).

- `RH/QCRTDyadicEpsilonSchedule.lean`: epsilon(n)=2^(-n), head(n)=5*4^n,
  exact head-tail budgets, and error²≤(1841/2500)*epsilon(n)² under the stated
  energy budget. The fixed dyadic witness provider is equivalent to the earlier
  all-epsilon provider. From that open provider, actual minima admit strictly
  increasing cofinal period indices, energy≤9/8, and norm convergence to qOne.
  The head-5 and head-20 provider instances are unconditional Lean theorems.
- `RH/QExactHeadMeasureComparison.lean`: the exact full Q/Pareto operator
  identity and the matching-head error bounds
  zetaTwo*(H+1)/(H+2)*normQ²≤normP²≤zetaTwo*normQ².

The [head-80 packet](RH/CofinalScheduleHead80Certificate20261028.md) supplies a
new external exact-rational complete-energy upper certificate
13222897792897/13159200000000<129/128 and complete error<0.201. It is independently
verified computationally, not kernel checked as an actual-vector theorem.

Open: the dyadic provider for every stage. Restricted head-320 searches did
not meet 513/512; this is numerical evidence, not a full-dictionary obstruction.
No unconditional convergence to qOne or RH theorem is asserted.

## Symbolic residual barriers and coefficient transformations

See [the symbolic investigation](RH/SymbolicCRTResidualAndMatrixTransforms20261029.md).

- `RH/QSquarefreeExactHeadResidualBarrier.lean`: exact actual-residual tail
  pairing and signed completed-square energy identity for every legal exact
  head, including the full infinite tails. Conditional on the actual residual
  being nonzero, every cofinal exact-head family has error and energy tending
  to infinity, including the actual primorial minima. Frequently bounded
  selected energies suffice to force residual zero. The missing residual
  moment for weak convergence is equivalent to residual vanishing.
- `LinearAlgebra/FiniteConstrainedMatrixReparametrization.lean`: exact
  transformation of the entire signed Gram form and head constraints,
  equality of feasible-energy sets under surjective coefficient maps, and
  preservation of the attained constrained minimum and its original
  minimizing coefficients.

These are symbolic theorems; no numerical certificate was added or promoted.
Open: eliminate the nonzero-residual branch arithmetically or provide genuine
all-epsilon witnesses. Choosing epsilon indices, changing legal coordinates,
or transferring to Ramanujan/Pareto alone does not discharge this obligation.
No unconditional cofinal convergence or RH theorem is asserted.

## Ramanujan/Pareto weak-star tests and compatible finite heads

See [the closure audit and finite reconstruction](RH/RamanujanParetoWeakStarClosure20261028.md).

Established symbolic results:

- `Analysis/ProjectedObservationTests.lean`: exact projected-observation
  defect, internal-test limits to the target projection, and actual WeakDual
  restriction with its evaluation theorem.
- `RH/ParetoRamanujanSquarefreeAnnihilator.lean`: explicit physical witness
  (2,-6,-12,20,0,...) with Pareto norm squared 40. The squarefree Ramanujan
  orthogonal complement is nonzero. Its mean is zero, so it does not refute
  constant membership. Pairing -1 with g4 excludes the full-conductor scope.
- `RH/QParetoResidualDualTransport.lean`: exact reciprocal correction to
  dual transport, faithful annihilator transfer, actual residual mean, head/tail
  commutation, and the complete transported residual-tail certificate.
- `RH/QSquarefreeCompatibleHeads.lean`: nonsquarefree Möbius charges vanish
  for radical-compatible jumps; explicit fresh-prime interpolation of every
  compatible anchored finite head; existential choice of a fresh prime;
  Pareto legality and exact finite Ramanujan expansion.

Conditional research reduction:

- `RH/ParetoProjectedHeadTests.lean`: cofinal exact heads and genuine WeakDual
  convergence for the SAME legal family force the target projection to equal
  the target. Only the countable projected-point tests are needed; their
  all-epsilon formulation is explicit. No separate norm bound is assumed.

Open: prove those complete projected-point test limits, genuine weak-star
convergence for an actual cofinal exact-head family, or the earlier all-epsilon
energy provider. Finite packet moments, injectivity of a compact coefficient
map, and finite interpolation do not discharge this requirement. No RH proof
or unconditional target-membership theorem is asserted.


## Exact-head optimizer coalescence and finite dual closure

See [the symbolic continuation](RH/CRTOptimizerCoalescenceAndDualClosure20261028.md).

Established statements:

- `Analysis/AffineEnergyMinimum.lean`: attained affine norm-energy minima are
  exactly the vectors orthogonal to their tangent space.
- `Analysis/CenteredAffineDisplacement.lean`: complete centered signed energy
  remainder and its sharp displacement bound.
- `RH/QExactHeadOptimizerComparison.lean`: actual zero-head multiplier bound;
  sharp constant 4(H+1)(H+2), exact Q/P Pythagoras, and the projected response
  equation derived from actual affine minimization.
- `RH/QAffineEnergyMinimizers.lean`: explicit Q and Pareto projection
  constructors with their common affine membership and minimality proved.
- `RH/QSquarefreeCanonicalFeasibility.lean`: canonical Mobius competitors in
  finite primorial dictionaries, actual head-kernel tangent, and its proved
  finite dimensionality in both metrics.
- `RH/QExactHeadOptimizerCoalescence.lean` and
  `RH/QPrimorialOptimizerCoalescence.lean`: the preexisting unconditional
  sublinear canonical energy supplies H_j times the squared Q/P optimizer
  displacement tending to zero. The fixed least-prime schedule has finite
  squarefree legality, exact heads, attained minima, and no unknown energy
  premise in its coalescence theorem.
- `RH/QConductorGapEnergy.lean`: exact signed ramp and mixed head-energy
  identities for arbitrary signed high-conductor blocks; complete-norm delay
  budget with no restrictions on coefficient signs or squarefreeness.
- `RH/QMobiusDelayedBlock.lean`: exact forced-prefix floor formula and a finite
  maximum conductor delay under any fixed-head energy ceiling. The slope's
  nonvanishing is discharged by the existing Mobius reciprocal theorem.
- `RH/QSquarefreeFiniteDualClosure.lean`: finite-head compatibility iff;
  four-site Riesz witnesses; orthogonal complement of the finite-annihilator
  span equals the radical-compatible subspace; exact residual distance from
  the finite-annihilator closure and membership iff the residual is zero.

Open: bound the common complete energies on a cofinal subsequence, or prove
completed projected-point tests for that same family. Coalescence of these
constrained minimizers does not imply either sequence converges to the
constant or identify the unconstrained Q/P projection residuals. No RH proof
or constant-membership provider is asserted. Finite-head rank and abstract
sharpness examples in the memorandum remain paper-level refinements.

## General squarefree-head constraint energies (29 October 2026)

See [the general-d memorandum](RH/GeneralSquarefreeConstraintEnergy20261029.md).

- Analysis/WeightedConstraintEnergy.lean: exact symbolic three-site completion,
  weighted Cauchy--Schwarz consequence, complete head/selected-sites/complement
  split, nonnegative omitted series, and exact finite shared-site-family
  Schur completion. The scalar correction S/(1+aS) strictly increases when
  positive conductance is added.
- RH/QSquarefreeConstraintEnergy.lean: arbitrary squarefree radical-square
  relation; exact complete Q energy identity for every head through d-1;
  the lower bound with denominator 2d^4-d^2+1; arbitrary radical-fibre
  complete identities; legal-span and closed-legal-span specializations.
- RH/SquarefreeParetoConstraintEnergy.lean: sequence-preserving measure transfer,
  exact complete Pareto identity, the lower bound with denominator
  2d^4+d^2+d, and its native Pareto Hilbert formulation.
- The d=5 constants are exact rational checks in both metrics.

No uniform upper bound for complete legal exact-head energies is supplied.
No residual-vanishing or RH provider is discharged. The general
weighted-window matrix theorem remains separate from these certificates.
The finite-family physical support assembly is supplied below.

## Complete finite radical-fiber families (29 October 2026)

See [the multi-fiber proof and scope](RH/MultiFiberEnergyCertificates20261029.md).

Established, with no upper-energy or RH hypothesis:

- `Analysis/WeightedSharedFamilyEnergy.lean` proves the disjoint physical
  support sum and complete infinite energy identity, retaining every square
  remainder and every omitted coordinate. Adding a fresh positive pair
  strictly improves the shared-site correction.
- `NumberTheory/RadicalFiberSeparation.lean` proves disjointness for distinct
  multiples, arbitrary radical-fiber pairs, and distinct powers d^k;
  it also proves the positive-power radical identity and head separation.
- `RH/SquarefreeMultiFiberEnergy.lean` proves general finite-family complete
  Q and Pareto identities, their inequalities, the native Pareto version,
  power-family and closed-legal-span specializations, and both d=5
  two-fiber complete-energy bounds.
- `five_two_fiber_constants` certifies Q correction 32202/38037251 and
  improvement 1442401/46633669726, and Pareto correction 13/16015 and
  improvement 25/819968, exactly.
- `radical_family_certificates_le_one` proves both lower certificates
  are at most one, by the compatible unit sequence. This is not a
  legal-closure membership theorem.

The infinite Pareto correction 1/[d(d+1)(2d^2-2d+1)] for all powers,
the whole-radical-fiber Euler product, the Q geometric remainder bounds,
and the exact-head weak-compactness discussion are paper-level in the
memorandum. The finite-family applications have no unresolved
disjointness, radical-identity, summability, or omitted-energy provider.
Uniform complete upper energy for legal exact-head approximants remains Open.

## Exact-head repair and exponential conductor cost (29 October 2026)

See [the paper proof and failed next-stage test](RH/ExactHeadRepairAndConductorGrowth20261029.md).

Established finite symbolic statements:

- `RH/QSquarefreeQuantitativeRepair.lean`: explicit signed finite repair
  operator; exact head, squarefree legality, complete signed error identity,
  and error amplification by `1 + norm(repairOperator H p)`.
  `repaired_energy_of_accuracy` proves the target energy when the input
  satisfies the displayed complete-error tolerance. Existence of those
  accurate inputs is not asserted.
- `RH/QExactHeadConductorBarrier.lean`: exact complete Q-to-Pareto error
  transfer and the unconditional estimate
  `zetaTwo * errorQ² <= ((5/4)*zetaTwo+4)/H` under the exact-head energy budget.

Conditional research reduction:

- `log_conductor_lower` and `no_subexponential_family` assume the external
  `ContinuousCutoffLowerBound`. The former proves a lower bound on
  `log N`; the latter rules out `log(N_j)/H_j -> 0`, also assuming
  `N_j -> infinity`. Burnol's analytic theorem supplies the lower envelope
  in the paper proof; its provider remains Open in Lean.

Separate paper and computational results:

- The paper proves explicit amplification `15 H^(3/2)`. This numerical
  operator bound is not claimed as a Lean declaration.
- The checker in `RH/ExactHeadRepair320Check20261029.md` exactly checks two specified
  direct H=80-to-H=320 repairs, with correction conductors 331 and 326.
  Both satisfy all head equations but have complete energy above 513/512,
  already certified by downward-rounded finite prefixes. These are external
  integer certificates, not Lean numerical theorems or lower bounds on the
  unrestricted H=320 optimum.
- The largest individual conductor must eventually grow exponentially in H
  for any all-stage target family, by the paper application of Burnol.
  The largest conductor is distinct from the CRT period and prime cutoff.

Open: the all-stage input approximation/provider, an actual H=320 energy
witness, and kernel verification of the original H=80 actual-vector
certificate. No RH proof or uniformly bounded cofinal construction follows.


## Minimum-energy transitions and moving prediction budgets (2026-10-29)

Research report: [MinimumEnergyOptimizerTransitions20261029.md](RH/MinimumEnergyOptimizerTransitions20261029.md).
Paper-only repair estimate: [MinimumEnergyLinearRepairBound20261029.md](RH/MinimumEnergyLinearRepairBound20261029.md).

The existing QCRTPeriodHeadBalance already gives the complete-norm signed
period/head recurrence; QCRTMinimumHeadCost already gives the exact one-site
capacity cost; QSquarefreeExactHeadResidualBarrier already supplies the
fixed-residual bounded-subsequence argument. The additions below reuse those
results rather than claiming the recurrence or residual argument as new.

Unconditional declarations:

- Analysis/AffineEnergyTransition: minimumOff, minimumOff_completion,
  normal_unique, minimumOff_decomposition, energy_transition, and
  signed_correction_energy give the actual enlargement projection and
  least-norm extension with exact signed complete-energy accounting.
- Analysis/AdjointConstraintMinimum: gram_solution_completion,
  gram_solution_equal_iff, gram_solution_vector_independent, and
  gram_solution_isLeast handle any solved adjoint Gram equation;
  exists_gram_solution_of_feasible proves multiplier existence for feasible
  data in a finite-dimensional observation space, without row independence.
- RH/QPrimorialEnergyTransition: primeAnchor_monotone and primeHead_monotone;
  enlargedTangent, enlargedMinimum, enlargementVector, extensionCorrection;
  optimizer_energy_transition and optimizer_signed_correction;
  qOptimizer_eq_minimumAt identifies the agenda's optimizer with the existing
  minimum in the identical dictionary. energy_telescope and
  energy_bounded_iff_net_sums_bounded preserve cumulative signed increments.
  prime_minimum_measure_bounds compares the actual complete Q/P minima.
- RH/QPrimorialExtensionGram: observation is the physical new-head map on
  the actual enlarged tangent with its inherited complete-Q norm;
  correction_observation, exists_multiplier, correction_eq_adjoint,
  extension_energy_of_gram_solution, and
  optimizer_transition_of_gram_solution realize the Gram formulation.
  All feasibility premises are discharged for the squarefree-successor
  heads of the prime schedule. No pseudoinverse is constructed.
- RH/QSquarefreeEnergyTransitions: nonsquarefree_next_value and
  minimumAt_eq_of_nonsquarefree prove zero extension cost at dependent
  physical sites. denseSchedule i = 2*i gives head H=i+1 in the divisor
  dictionary of primorial(2H). dense_headCost_bound proves the actual cost
  is at most 4*nextMismatch(i)^2/(zetaTwo*(i+1)), discharging nearby-prime
  existence with Bertrand. dense_energy_signed_bound retains all enlargement
  gains. predictionBudget_le_harmonic and predictionBudget_le_log assume a
  uniform bound on the actual moving nextMismatch.
- RH/QCRTPredictionBudget: trial_legal and trial_head give the actual cofinal
  exact-head family; trial_error_le controls its complete error by the
  literal predictionBudget.

Conditional research reductions:

- QPrimorialEnergyTransition.residual_eq_zero_of_frequently_bounded:
  frequently bounded complete energies on the cofinal prime schedule kill
  the fixed limiting residual.
- QPrimorialEnergyTransition.riemannHypothesis_of_net_sums_bounded and
  riemannHypothesis_of_summable_positive_increments: their displayed
  arithmetic signed-budget premises remain Open.
- QCRTPredictionBudget.riemannHypothesis_of_subpolynomial_predictionBudget:
  assumes log(1+predictionBudget N)/log(N+2) tends to zero.
- QCRTPredictionBudget.riemannHypothesis_of_bounded_nextMismatch: assumes
  one B >= 0 bounds |nextMismatch i| for every i. This gives logarithmic
  complete energy, sufficient for the existing Mellin-zero RH consumer.
  Neither prediction premise is proved.

The separate paper obtains norm(repairOperator H p) <= 17H and complete-error
amplification <= 18H when 1 <= H < p <= 2H. This numerical bound is not a
Lean declaration. It does not supply accurate raw legal approximants.

Open: bounded signed cumulative increments, a bounded cofinal energy
subsequence, or a subpolynomial moving prediction budget for an actual
specified family. Canonical coefficients and optimized normal equations
cannot be combined across different vectors. No unconditional RH proof
or all-stage exact-head energy provider is claimed.

## Complete energy controlled by squarefree conductor gaps (2026-10-29)

Research report: [SquarefreeGapEnergyImprovement20261029.md](RH/SquarefreeGapEnergyImprovement20261029.md).

Established declarations:

- Analysis/DiscreteFloorGap: floor_gap_count is the exact quotient-difference
  count with all interval multiplicities. band_energy_le and floor_gap_sum_le
  give finite inverse-square band bounds; gap_majorant_log simplifies the
  balanced cutoff expression.
- RH/QCompensatedResidueGap: floor_gap_sq retains the signed residue difference;
  compensatedResidue_gap_energy includes the complete infinite tail.
  compensatedResidue_gap_log_bound proves, for 2 <= n < r <= 2n,
  norm(g_n-(r/n)g_r)^2 <= (r-n)*(7+log(n/(r-n)))/(zetaTwo*n^2).
  No prime or squarefree gap hypothesis is needed for this norm theorem.
- RH/QSquarefreeGapHeadCost: minimumAt_single_head_gap_bound and
  dense_headCost_gap_bound apply the estimate to the actual norm minimizers.
  squarefreeAnchor is the least squarefree successor of i+2, with verified
  minimality and membership below 2(i+2). The literal gapBudget takes the
  minimum of the old and new costs at each site.
  gapBudget_le_predictionBudget proves it never exceeds the old cost majorant.
  dense_energy_gapBudget_signed_bound retains every periodGain.
  trial_error_le_gapBudget controls complete approximation error.

Conditional research reduction:

- QSquarefreeGapHeadCost.riemannHypothesis_of_subpolynomial_gapBudget assumes
  log(1+gapBudget N)/log(N+2) tends to zero. This actual arithmetic limit is
  Open; the improved correction cost does not bound moving nextMismatch.

Paper-level applications, not additional Lean theorems: elementary squarefree
gaps O(sqrt(n)) yield a sufficient moving-prediction threshold O(n^(1/4)).
Kumchev et al., arXiv:2211.09975, Theorem 1, gives gaps at most
11*n^(1/5)*log(n), yielding the sufficient threshold O(n^(2/5)).
The latter theorem is cited as an external ordinary mathematical input;
neither it nor either prediction-growth provider has been added as an axiom.
No unconditional RH proof or bounded cofinal optimizer energy is claimed.

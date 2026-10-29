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

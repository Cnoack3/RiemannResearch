# Pareto tail research: formalization coverage (2026-09-11)

Source: user-provided arguments in
RH_Regression_Analytic_Repair_20260911.md and
RH_Two_Seed_Tail_Rigidity_Continuation_20260911.md.

This is a partial formalization of the two complete notes. It is not a
verification of every claim in them and does not prove RH. The theorem types
below, rather than informal descriptions, specify what has been checked.

## Established by this development

### Actual tails and energy
RH/ParetoSignedTails.lean defines signedCoefficient h n = w_n h_n,
the raw signedTail, and anchoredSignedTail (zero at index zero).
For every actual weighted L2 sequence it proves:
- signedCoefficient is absolutely summable.
- The raw tail equals the full mean minus the finite prefix.
- Tails tend to zero.
- At every positive n, A(n)-A(n+1)=w_n h_n.
- A(1)=paretoMean h.
- n(n+1)(A(n)-A(n+1))^2 = w_n h_n^2, including the zero-weight endpoint.
- Exact equality and summability of the full difference energy.
- Zero anchored tails imply h_n=0 at every positive index.

The zero index carries no Pareto mass. Function equality for h requires an
explicit zero-coordinate anchor; positive-index results do not.

### Summable inversion and actual dyadic orthogonality
Analysis/SummableMultiples.lean:
- eq_zero_of_summable_multiples: an absolutely summable real sequence with
  every divisibility-filtered sum zero is identically zero.
- tsum_multiples_eq: exact reindexing at a positive dilation.
- dyadic_scaling_of_summable_multiples_equations: A(2n)=A(n)/2.
- multiples_equation_of_summable_binary_grouped and
  dyadic_scaling_of_summable_binary_grouped: the explicitly grouped Q2
  equation yields the same result, with absolute summability retained.

The inversion proof uses finite divisibility exclusion and dominated
convergence; it does not assert an unjustified infinite Mobius rearrangement.

Analysis/SummableDiscreteAbel.lean proves summation by parts for a summable,
zero-anchored real sequence and a bounded test.

RH/ParetoSummableTailRigidity.lean uses the *actual* legal annihilator:
- paretoInner_eq_signedTail_jump.
- dyadic_pairing_eq_signedTail_multiples.
- LegalAnnihilator.signedTail_dyadic_scaling.

Thus the relation A(2n)=A(n)/2 is derived from the true Pareto pairings when
the signed tail is summable. It is not assumed as an arithmetic input.

### Restricted uniqueness
Analysis/DyadicTailRigidity.lean proves the terminal orbit argument from
dyadic invariance and convergence to zero, together with its weighted-tail
and weighted-square-summability specializations.

RH/ParetoSummableTailRigidity.lean proves:
- legalAnnihilator_eq_zero_of_weighted_tail_tendsto, assuming summability of
  A and n A(n) tending to zero.
- legalAnnihilator_eq_zero_of_summable_weighted_tail, assuming summability
  of A and of (n A(n))^2.

These are fully proved restricted theorems. The additional tail hypotheses
are displayed and are not inferred from weighted L2 membership alone.

### First absolute moment
Analysis/FirstMomentTails.lean proves that summability of a and of n|a_n|
gives summability of its tails and n A(n) tending to zero. The proof uses
Tonelli for a nonnegative triangular kernel and an explicit vanishing-tail
bound.

RH/ParetoFirstMomentUniqueness.lean proves
legalAnnihilator_eq_zero_of_first_absolute_moment:
if 2 belongs to the seed set, h is its actual weighted L2 legal annihilator,
and sum |h(n)|/(n+1) is finite, then h(n)=0 at every positive n.
No Fourier-regularity provider, RH assumption, or numerical evidence enters
this theorem. It is now a consequence of the stronger summable-tail result.

### Sign oscillation
RH/ParetoAnnihilatorPositivity.lean is extended with:
- Vanishing of an eventually nonnegative dyadic annihilator.
- Descending elimination of every finite remaining head.
- legalAnnihilator_eventually_one_sign_eq_zero.
- legalAnnihilator_anchored_eq_zero_of_eventually_one_sign.
- legalAnnihilator_both_signs_arbitrarily_far.

Any legal annihilator with a nonzero positive coordinate therefore has both
positive and negative values beyond every cutoff.

## Relevant pre-existing checked results

- RH/IntegratedRamanujanBasis.lean and IntegratedRamanujanGram.lean:
  the allowed basis/span and actual finite Gram strict positivity.
- RH/ParetoGramMeanOptimizer.lean:
  projection_error_exact, normalizedProjection_variance,
  normalizedProjection_completion, normalizedProjection_minimizes.
  The exact normal equations and nonzero normalization are explicit inputs.
- RH/RamanujanMeanOptimizer.lean on current main supplies actual finite
  inverse coefficients and nonzero normalization. Its existing proofs and
  the intervening main update are preserved by this recovery.
- LinearAlgebra/OrthogonalSchurRepair.lean:
  schurRemove_norm_sq and schur_line_complete_square, plus linear-constraint
  preservation when the directions annihilate the relevant functional.
- Analysis/ResidualGainProduct.lean and ResidualGainTermination.lean:
  exact gain product, convergence iff nonsummability in the nonterminating
  case, and the finite-termination/full-gain extension.
  Nonsummability of the actual arithmetic gains is not provided.
- RH/ParetoLegalCompleteness.lean and the existing legal-closure modules:
  actual annihilator/completeness and conditional RH bridges.
- RH/ParetoMellinHeadObstruction.lean:
  the complete exact-head Mellin energy lower bound under Mellin nullity.

These are existing project results, not newly proved claims of this turn.

## Completed regularity upgrade and remaining coverage

The formerly missing Fourier/Sobolev implication is now discharged in its
coefficient form by Analysis/DyadicBlockRigidity.lean. No Fourier-regularity
provider or extra weighted-tail decay hypothesis is needed.

For c(n)=n A(n), define
M_K(n)=2^{-K} sum_{2^K n <= r < 2^K(n+1)} c(r).
Absolute summability of A gives M_K(n) -> 0 for every positive n.
The original difference energy implies sum (c(j+1)-c(j))^2 < infinity.
The exact telescoping identity and disjoint dyadic blocks yield
(M_K(n)-c(n))^2 <= (1/2) sum_{j >= 2n}(c(j+1)-c(j))^2.
Passing K to infinity, then following the orbit 2^k n, gives c(n)=0.
Consequently sum (n A(n))^2 is finite (indeed zero).
This establishes the missing implication by a discrete proof; it is not a
formalization of a general-purpose Sobolev/distribution theory.

RH/ParetoSummableTailRigidity.lean now contains the checked provider
LegalAnnihilator.signedTail_weighted_square_summable and the complete theorem
legalAnnihilator_eq_zero_of_summable_signedTail.
Its assumptions are exactly actual weighted L2 legal orthogonality, seed 2
availability, and summability of the anchored signed tail. The energy and
dyadic scaling are derived, not supplied as unproved arithmetic hypotheses.
A separate zero-coordinate anchor yields equality of the entire sequence.

Other claims from the notes not newly established by this formalization:
- The precise periodic kernel integral, its higher-order derivative
  asymptotic, and eventual strict finite mean-zero variance repair.
- The full two-seed L1 density/PNT approximation argument.
- The logarithmic L2 lower bound for the near-period telescoping construction.
- The exact finite-prime sieve defect and growing two-seed Gram lower bound.
- The general Fourier boundary description and restricted Mellin/asymptotic
  classification of annihilators.
- The full exact-head variational dichotomy and all arithmetic-flow
  specializations not covered by existing modules.

This list records coverage; failure to formalize an argument is not a
counterexample to it.

## Open mathematical research obligations

The completed regularity upgrade does not establish that the canonical
RH residual has summable signed tails. That regularity claim, unconditional
L2 legal approximation, and exhaustion of the residual by actual arithmetic
gains remain open research obligations. The L1 construction alone supplies
no L2 convergence.

## Verification policy
All new proofs use focused imports, with no sorry, admit, project-local
axioms, or unsafe declarations. The principal uniqueness theorem's axiom
audit lists only propext, Classical.choice, and Quot.sound. Local hypotheses
remain part of its exact type. Final project acceptance is the serialized
checkpoint that builds changed modules and their reverse dependents.

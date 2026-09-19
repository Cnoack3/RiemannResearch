# Theorem catalog

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

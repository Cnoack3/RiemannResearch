# Vector spaces and zeta zeros: Lean coverage, 2026-09-16

Source: the user's V_Zeta_Vector_Spaces_Research_2026-09-16.md and its preceding
V_Zeta_Zeros_Fourier_Chebyshev handoff.

This is a checked formalization of the Hilbert-space deductions, topological
obstructions, finite sampling obstruction, and signed local energy identities.
It is not a complete formalization of every analytic assertion in the report.
In particular, neither RH nor zero-ordinate equidistribution is proved here.

## Established reusable results

- Analysis/SampledGaugeCompleteness.lean constructs diagonal unit-modulus
  actions on complex l2. It proves norm convergence of dominated coordinate
  filters, finite sample demodulation identities and bounds, and completeness
  of the sampled orbit from explicit phase-covariance limits. The recovery
  proof uses dominated convergence of the squared-coordinate sum, not an
  assumed convergence or completeness conclusion. It also proves that the
  limiting coordinate diagonal has no positive uniform lower bound, even
  after arbitrary fixed finite rescaling.
- Analysis/ZeroDivisorTopology.lean proves finite-coordinate density, density
  of every translate, and convergence of actual coordinate tails to zero.
  It proves preservation of zero sets by multiplication by Complex.exp, and
  preservation of analyticOrderAt under analytic exponential multiplication.
  The zeta specialization uses Mathlib's actual riemannZeta.
- Analysis/FinitePolynomialSampling.lean constructs a nonzero polynomial,
  with zero constant coefficient, vanishing on any finite complex sample set.
  Its coefficient energy is positive while its sampled energy is zero.
  Consequently no positive unrestricted lower sampling bound exists.
  A centered lower bound must pay at least sample-cardinality/height; unbounded
  sample density therefore rules out a uniform centered bound. Indexed
  samples retain multiplicities even when some complex phases coincide.
- LinearAlgebra/FiniteCumulativeCellEnergy.lean retains the complete signed
  cell energy, proves exact square completion, constructs the telescoping
  optimal jump correction, proves attainment of the finite minimum, and proves
  the exact correction-energy identity including the terminal boundary term.
- Analysis/IntegralCellEnergy.lean identifies those signed quadratics with
  actual Bochner integrals under the required integrability hypotheses.
  It proves mean attainment, nonnegative geometric remainder, mean minimality
  and uniqueness, exact excess energy, exact correction cost, and the
  finite sum of actual cell integrals.
- RH/ZetaKernelObstruction.lean rules out a Hilbert Gram representation of the
  unchanged expression riemannZeta(s + star w) on any domain containing zero.
  This uses the actual theorem riemannZeta_zero = -1/2. It is a concrete global
  obstruction; it does not claim the report's sharper sign statement for
  every real diagonal point between 0 and 1/2.

## Conditional research reductions and providers

The word Open below distinguishes an unchecked provider from a new
mathematical conjecture. The cited classical inputs are established
mathematics, but their application has not been formally supplied here.

1. Open formalization provider: actual zero-ordinate sampling.
   Main declaration:
   RiemannResearch.Analysis.SampledGauge.gaugeOrbit_dense_of_phase_limits.
   For every pair of coordinates, its hequid hypothesis is convergence of
   the actual finite normalized phase covariance to the Kronecker delta.
   This is weaker data than a Hilbert completeness conclusion and the proof
   derives completeness from it. The intended specialization takes
   frequency q = Real.log q and times n equal to the positive zero ordinates.
   The construction and completeness deduction are checked; an enumeration
   of all actual zeros with multiplicity and the Ford--Zaharescu/Hlawka
   provider are not supplied. There is no RH hypothesis in this deduction.
   Primary source supporting the analytic input:
   https://arxiv.org/abs/math/0405459, equations (1.1), (3.8).

2. Open formalization provider: continued arithmetic evaluation.
   Main declaration:
   RiemannResearch.Analysis.continued_eval_not_continuousWithinAt_zero.
   The vector eta is an actual l2 element, with its tails constructed in Lean.
   The assumptions are a zeta zero rho, evaluate(0)=1, and the continuation
   formula evaluate(tail eta s)=zeta(rho)*exp(-H s) for every finite head s.
   Tail convergence and the discontinuity, even on the minimal tail domain,
   are proved. The arithmetic eta(p^k)=1/k, its weighted membership, and its
   Euler-series continuation identity still need checked providers.

3. Partially discharged provider: the Chebyshev specialization.
   The continuation update below proves the critical x^-2 moment formulas on
   actual positive intervals, uses Mathlib's actual von Mangoldt coefficients,
   and identifies finite cumulative sums with the Chebyshev sum under the
   explicit CompleteThrough support condition. The later update in
   SignedArithmeticBoundVerification20260916.md supplies the global enumeration
   and the general power-weight moments. Identification of the real step
   function inside every interval and the global RH criterion remain Open
   (formalization).

4. Open mathematical obligation: the actual global centered arithmetic bound.
   Nothing here proves integral_1^X (psi(x)-x)^2/x^2 dx = O(log X), or all
   of its exponentially damped equivalents. Finite optimization and its
   correction cost are exact identities, not such an estimate. The finite
   jump corrections are not asserted to be legal Nyman--Beurling corrections.

## Remaining report results not formalized in this change

- The exact infinite sampled mean-square identity and trace-norm convergence
  of its covariance operators; the full scalar-weight frame impossibility.
- The fixed-support first-order Landau covariance asymptotic, its prime-local
  Toeplitz/Poisson-kernel representation, and its sharp operator norm.
- The positive log-zeta kernel, symmetric Fock exponential construction, and
  identification of the resulting closed span with the Dirichlet-series RKHS.
- The full arithmetic realization of the dense classes with different zero
  divisors, and the sharp bounded-evaluation threshold in the V_sigma norms.
- The full summation-unboundedness argument, finite Chebyshev Gram inverse,
  full-zero Nyman--Beurling bound in the report's precise normalization, and
  Burnol's Sonine-space theorems. Existing Nyman/Pareto project results are not
  duplicated or silently identified with these differently normalized claims.

## Verification and trust boundary

The coherent proof candidate passed Lean with exit code 0. Axiom inspection
of the main completeness, discontinuity, zero-multiplicity, finite sampling,
correction-energy, integral-excess, and zeta-kernel declarations reported only
propext, Classical.choice, and Quot.sound. No sorry, admit, unsafe declaration,
or project-local axiom was introduced. Local hypotheses remain in theorem
types; an axiom report does not discharge them.

The final project checkpoint is the acceptance gate for separate-module
imports, exports, source audit, affected modules, and publication.


## Continuation Sections 11-19: exact coverage of the 2026-09-16 update

The following results extend the earlier work. They do not turn the report's
analytic reductions into a proof of RH.

### Established declarations

All namespaces below begin with RiemannResearch.

- Analysis.ReciprocalCellEnergy.integral_residual_square_split identifies the
  actual integral of (c-x)^2/x^2 on [a,b] with
  (1/a-1/b)(c-m)^2 + R, for 0<a<b. Here
  m=log(b/a)/(1/a-1/b) and R=b-a-log(b/a)^2/(1/a-1/b).
  intervalRemainder_cubic_bounds proves
  (b-a)^3/(12*b^2) <= R <= (b-a)^3/(12*a^2).
  Mean minimality, nonnegativity, and the actual constant-correction integral
  are checked, not supplied as assumptions.
- LinearAlgebra.CumulativeCellEnergy.cumulative_resetJump and
  resetJump_tail_zero construct the first N jumps plus the compensating jump
  at index N; their cumulative value vanishes for every n>N.
  reset_optimal_head attains the target on the original head.
  weightedPrefixEnergy_signed_identity is the exact Abel identity with all
  signed earlier-current cross terms and the terminal subtraction.
  reset_correction_energy_exact is the full finite correction cost after
  reset, independent of any terminal mass.
- In Analysis/CumulativeEnergySummability.lean,
  LinearAlgebra.CumulativeCellEnergy.reset_total_correction_energy_exact
  proves that the entire infinite-sum squared correction cost equals the
  finite excess energy, not merely a prefix or a lower bound.
  Analysis.NonnegativeEnergy.summable_iff_nonnegative_prefix_bound proves
  the general nonnegative summability/bounded-prefix equivalence.
- Analysis.GapEnergy.cubic_gap_sum_le splits short and large gaps.
  cubic_gap_sum_le_of_external_bounds derives the cubic estimate from the
  explicitly named externalMaxGap, externalTotalMass, externalLargeGapMass
  hypotheses. summable_remainder_of_cubic_gap, summable_of_geometric_majorant,
  and tail_tsum_le_of_geometric_majorant prove the summability reductions
  and the full geometric tail bound C*r^k/(1-r).
- RH.PrimePowerCriticalEnergy.actualJump is the actual von Mangoldt
  coefficient, never a geometric proxy. actualCumulative_eq_chebyshev uses
  StrictMono q and the explicit CompleteThrough q n condition.
  actual_interval_energy_split is the sum of actual interval integrals,
  split into signed cumulative discrepancy and geometric remainder.
  actual_signed_abel_identity uses the actual weights 1/q_i-1/q_(i+1).
  actual_total_reset_cost equates the entire squared correction norm with
  that discrepancy energy. actual_discrepancy_summable_iff_bounded_prefix
  is only a criterion; it does not prove its boundedness condition.

The convention is zero-based: cell i is [q_i,q_(i+1)], and its cumulative
coefficient is the sum through index i. The reset jump is at q_N, after N
corrected cells. No initial interval is silently included; when q_0=2 the
unchanged [1,2] contribution cancels from the excess and correction cost.
These weights are distinct from the integer Pareto weights in
RH/ArithmeticCumulativeEnergy.lean.

### Conditional research reductions and outstanding inputs

1. Open (formalization): Baker--Harman--Pintz maximal prime gaps and
   Jaerviniemi's large-gap total-mass estimate, transfer to all prime-power
   intervals, and the resulting global cubic-gap summability.
   Update 2026-09-18: NumberTheory/PrimeGapProviders proves actual-prime
   total dyadic gap mass <= 4X, so that input is no longer external for
   this specialization. The exact exponent combination and dyadic
   summability from the two remaining strong estimates are also proved.
   Those two estimates remain explicit hypotheses; see
   RH/PrimeGapProviderProgress20260918.md.
   The finite algebra and geometric majorant reduction are checked. In particular,
   RH.PrimePowerCriticalEnergy.actual_remainder_summable_of_external_cubic_gap
   explicitly assumes externalPrimePowerCubicGapSummability; it does not
   assert that the classical providers have already been formalized.
   Intended sources from the user-provided report:
   https://doi.org/10.1112/plms/83.3.532 and
   https://arxiv.org/abs/2212.10965.
2. Open (formalization): the general weighted spaces E_s and geometric
   membership G in E_s for s>9/10; positive reference jumps, Dirichlet
   convolution exponentiation and its multiplicative coefficients; the
   meromorphic reference Z_b on Re z>9/20, with a simple pole at 1 and no
   zeros. No Lean declaration in this update asserts those analytic facts.
3. Open (formalization): the quotient zeta/Z_b, pole cancellation at 1 and
   preservation of zeta zeros with their multiplicities; the actual Mellin
   integral initially on Re z>1, its meromorphic continuation, residues
   -m_rho/rho, and the half-plane Hardy/holomorphy bounds. Meromorphic
   continuation is not being identified with convergence of the original
   integral on the larger half-plane.
4. Open (mathematics): the bound for the actual signed arithmetic
   discrepancy. The report's all-positive-damping or critical
   subpolynomial-growth target is RH-equivalent, not proved by this note.
   Finite optimization and geometric summability do not supply that bound.
   A uniformly bounded critical undamped correction norm is not the target:
   the report derives divergence (not yet formalized here), even under RH.
5. Open (formalization): the energy-threshold/rightmost-zero characterization
   and the RH-conditional logarithmic asymptotic. The report's constant is
   the sum over distinct nontrivial zeros of m_rho^2/|rho|^2; multiplicities
   are not discarded and RH is an essential hypothesis. The explicit-formula
   and B^2 providers remain unchecked in this continuation update.
   Intended source: https://arxiv.org/abs/1306.1657.

### Verification boundary for this continuation

The coherent candidate is checked with autoImplicit disabled. Axiom
inspection of the central interval, cubic, signed-Abel, geometric-tail,
Chebyshev-identification, and total-reset theorems reports only propext,
Classical.choice, and Quot.sound. Substantive local hypotheses remain visible
in theorem types and are not discharged by that audit. The single final
push-enabled checkpoint validates the actual module graph and publication.


## Later update: actual global enumeration and unconditional energy bounds

See `RH/SignedArithmeticBoundVerification20260916.md` for exact statements.
`RH/PrimePowerEnumeration.lean` now discharges the global enumeration and
endpoint Chebyshev-identification provider: strict monotonicity, positivity,
complete support, the first value 2, and q_(i+1)<=2*q_i are proved.
`Analysis/PowerCellEnergy.lean` supplies the actual general power-weight
interval integral. `RH/PrimePowerEnergyBounds.lean` proves the unconditional
critical bound A_N<=(log 4+4)^2*(q_N-2), and uniform damped prefix boundedness
and summability for every s>2. The same critical reference mean and reset
corrections are retained.

**Still Open (mathematics):** `SignedArithmeticDampedBound` requires every
s=1+epsilon>1, including 1<s<=2. `SignedArithmeticSubpolynomialBound` requires
every positive growth exponent, including 0<delta<1. These are explicit
proposition definitions with no proof provided. Neither the estimates here
nor the completed enumeration prove them. The Mellin/RH equivalence remains
Open (formalization), separately from the mathematical bound.

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

3. Open formalization provider: the Chebyshev specialization.
   The integral theorems apply to arbitrary actual measures with explicitly
   integrable 1, f, and f^2. The report uses f(x)=x and the measure
   x^(-s-1)dx restricted to each prime-power interval. These measure choices,
   their moment formulas, the identification of the cumulative coefficients
   with the actual von Mangoldt function, and the global RH energy criterion
   have not been specialized in these modules.

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

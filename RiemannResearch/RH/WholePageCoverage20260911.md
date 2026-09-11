# Whole-page formalization coverage — 11 September 2026

Source: the supplied conversation, from the search for legal sequences through
Ramanujan coordinates, Schur/Laguerre repair, independence/completeness, and
indicator/absolute-value annihilator discussion. The two original research
notes are retained alongside this record as informal source snapshots.

This record separates mathematical research obligations from remaining work
needed to formalize otherwise justified informal arguments. A Lean proposition
definition records an obligation; it does not prove that obligation. Numerical
tables in the source snapshots remain exploratory and uncertified.

## New formalization

| Source claim | Module | Scope |
|---|---|---|
| Actual two-seed floor expansion and local Möbius flow; necessary prime coefficient limits; omitted-five and nonnegative coefficient error floors | `LegalMobiusConstraints.lean` | Actual finite coefficients and full Pareto error. Convergence conclusions require actual vanishing approximation error. |
| Head-preserving legal correction, exact mean, linear norm cost and signed mixed term | `LegalMobiusHeadCorrection.lean` | Exact identities; no small-tail bound asserted. |
| Integrated Ramanujan independence and exact allowed-conductor legal span | `IntegratedRamanujanBasis.lean` | Finite algebraic basis and actual legality; completeness is a separate question. |
| Strict positivity of every nonzero finite Ramanujan Gram quadratic | `IntegratedRamanujanGram.lean` | Actual complete Pareto energy; finite positivity is not a uniform spectral lower bound. |
| Gram normal equations, projection error, mean-one normalization, minimum variance and exact excess | `ParetoGramMeanOptimizer.lean` | Full Pareto Gram form; normal equations and nonzero normalization explicit. |
| Bounded progressively matched dense tests yield weak convergence and finite convex mixtures | `Analysis/BoundedMomentRepair.lean` | Density of the actual testing family and the uniform bound are hypotheses. |
| Equal-weight subsequence averages and B/m+4/m² | `Analysis/BoundedMomentAverages.lean` | Proved from bounded norms and weak nullity, retaining every signed pairing. |
| Finite legal mean-one convex approximation and RH implication | `ParetoMomentRepair.lean` | Conditional research reductions; actual legal packets and actual norm throughout. |
| Finite Laguerre transform, triangular cancellation and ordinary-integral bridge | `Analysis/LaguerreMomentTransform.lean` | Ordinary moment vanishing and integrability explicit; not a proof of the arithmetic moment provider. |
| Actual exponential lift, Laguerre integrals, budget constraints and remaining analytic targets | `RamanujanLaguerreResearchTargets.lean` | Named propositions for unresolved providers; ordinary-moment provider implies actual Laguerre cancellation conditionally. |
| Actual sequence annihilator → Hilbert orthogonality/completeness/RH | `ParetoLegalCompleteness.lean` | Signed uniqueness or absolute-value closure remains explicit. |

## Further formalization from the same chat

- `RamanujanMeanOptimizer.lean` assembles the actual finite Gram inverse and
  mean-one optimizer. For every finite allowed conductor set containing 2,
  the inverse mass q is positive and strictly below 1, the projection error
  is 1-q, and the minimum mean-one variance is q⁻¹-1. Legality, normal
  equations, and nonzero normalization are derived, not research hypotheses.
- `ParetoFiniteErrorObstruction.lean` proves positive error for each finite
  legal packet and a positive error floor uniform over all signed coefficients
  on any fixed finite positive conductor set. The floor depends on that set
  and does not obstruct approximation by growing conductor sets.
- `Analysis/IndependentMeanOneObstruction.lean` gives actual finite-prefix
  vectors, linear independence, exact least-squares coefficients and minimum,
  a uniform 1/2 lower bound, and convergence of the minima to 6/π² using
  Mathlib's proved Basel sum. It rules out every sequence of mean-one finite
  combinations in this example.
- `Analysis/DyadicMomentEvaluation.lean` proves the exact triangular times
  Vandermonde determinant, nonzero dyadic leading coefficients, and finite
  solvability for all K and all prescribed moment vectors.
- `ParetoDyadicMomentFeasibility.lean` proves legality at budget 2^K and
  finite synthesis of the actual Laguerre integrals under explicit moment
  integrability. Its all-budget feasibility theorem still requires
  `DyadicCoefficientPolynomialProvider` and
  `ContinuousParetoRealizationTarget`. The matrix algebra is now proved;
  those two analytic providers remain unproved.

## Existing results reused

- `ParetoPacketGreenGram`: actual Ramanujan divisor sum, increments,
  negative prefix, signed weighted Green identity and explicit infinite tail.
- `ParetoResidueDuality`: Möbius inversion and residue/packet decomposition.
- `ParetoResidueMean`: actual integrated Ramanujan mean equals von Mangoldt,
  with prime-power and non-prime-power specializations.
- `ParetoFiniteSchur`: simultaneous full Gram correction, exact completion,
  optimality, and explicit inverse-provider formulation.
- `FiniteTwoSeedHeadMean`: finite-budget exact head and mean feasibility.
- `ParetoTwoSeedBudgetMinimum`: monotonicity when the head is fixed and the
  independent dilation budget increases. This does not establish monotonicity
  of the Laguerre diagonal sequence with changing constraints.
- `ThresholdInterpolationCompleteness`: constant in legal closure implies
  full completeness, via bounded integer dilations and a complete tail basis.
- `ParetoAnnihilatorPositivity` and `Analysis/IndicatorAnnihilator`:
  nonnegative uniqueness, indicator corollary, signed counterexample, and
  signed uniqueness conditional on absolute-value stability.

## Still open as analytic research

1. Uniform full-error bound for actual moment-matching legal witnesses,
   including the proposed schedule M=2^K.
2. Vanishing approximation error / completeness of the two-seed system.
3. Absolute-value closure of its signed annihilator.
4. The all-scale tail-energy or incremental gain estimate needed to construct
   RH approximants unconditionally.

## Not yet fully formalized from this page

- The complete continuous Pareto–Laguerre realization and Parseval theorem.
- Mellin differentiation and the arithmetic moment provider for every B_d.
- The analytic polynomial coefficient identity and continuous realization
  needed to discharge actual dyadic feasibility; its finite polynomial
  evaluation algebra is now proved. The additional-moment constrained inverse
  matrix optimizer formula remains to be formalized.
- The exact finite-budget conductor cardinality, and the pseudoinverse formula
  for the redundant generator matrix; the checked optimizer formulation uses
  actual normal equations instead.
- The page's closed pi/log constants for the B2/B6 repair, one-seed resonance
  constants and exact off-line-zero exponential-cost estimate, insofar as
  their precise displayed specializations are not supplied by an existing
  checked declaration.
- Certification of the numerical tables. The counterexample's finite-prefix
  minima and their exact limit 6/pi² are now proved; an explicit encoding of
  the same vectors inside infinite ell² is not included.

Continuous Laguerre polynomials live in the exponential-variable L² space.
Their projections into the discrete Pareto step-function space are testing
vectors; they must not be silently asserted to be an orthonormal basis of
that smaller space.

No unconditional RH theorem is claimed. Final verification/publication status
must be read from the successful checkpoint, not from this scope record alone.

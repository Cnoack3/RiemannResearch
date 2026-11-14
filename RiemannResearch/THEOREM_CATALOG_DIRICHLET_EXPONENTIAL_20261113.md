# Actual Dirichlet exponentials in the Pareto Hilbert space

Date: 2026-11-13. Source: the user's Pareto Nyman–Beurling discussion and
request to formalize the actual convolution exponential in Lean.

## Verification status

The complete public module `RH/ParetoDirichletExponential.lean` and all 13 new modules passed Bazel/BuildBuddy Lean verification on 2026-11-13. Target: `//RiemannResearch/RH:ParetoDirichletExponential`; exit code: 0. [Verification invocation](https://app.buildbuddy.io/invocation/9cf04a20-f8d3-4e55-96c3-66433e128550).

The complete generalized-divisor moment estimate is proved and supplies the analytic input to the public endpoint. Hilbert membership and absolute Hilbert Taylor convergence for bounded arithmetic inputs, the actual residue-exponential limit to δ₁, and prime-conductor algebraic-span nonmembership are established. The public `residueExponential` definition and its norm-limit theorem have no external moment, envelope-energy, or Hilbert-membership parameter. The reusable generic lemmas retain their quantitative inputs in their own types.

## Objects and normalization

All arithmetic products are Mathlib's actual Dirichlet-convolution products:

\[
(f\star g)(n)=\sum_{d\mid n}f(d)g(n/d),\qquad
\delta_1(n)=\mathbf 1_{\{n=1\}},\qquad
\exp_\star(f)(n)=\sum_{r=0}^{\infty}\frac{f^{\star r}(n)}{r!}.
\]

In particular, the zeroth convolution power is \(\delta_1\). The positive
constant sequence is the different arithmetic function
`zetaReal`, with value zero at zero and value one at every positive integer.
The residue input is the existing physical generator
\(g_k(n)=(n\bmod k)/k\), represented arithmetically by `residueAF k`.
The exact bridge to `residueFraction` and `normalizedResidueHilbert` is proved.

The physical Pareto Hilbert space is the existing `ThresholdHilbert`, with

\[
\|f\|_H^2=\sum_{n\ge1}\frac{|f(n)|^2}{n(n+1)}.
\]

Its `paretoPointHilbert 0` realizes \(\delta_1\), while `hilbertOne` realizes
the positive constant sequence. The existing closed residue space is
`CoefficientStabilization.closedSpace`.

## Arithmetic and analytic declarations

| Module | Main declarations and purpose |
|---|---|
| `NumberTheory/DirichletExponential.lean` | `convolutionExp`, `convolutionPower_zero`, `convolutionExp_summable`, `convolutionExp_nonneg`, `convolutionExp_mono`, `residueAF_exp_prime_pow_lower`, `residueAF_exp_unbounded`: the actual scalar exponential series and its arithmetic growth. |
| `NumberTheory/DirichletExponentialPrimePowers.lean` | `zetaReal`, `zetaReal_pow_isMultiplicative`, `zetaReal_pow_prime_pow`, `zetaReal_pow_prime_pow_le`: the constant-one majorant and generalized-divisor prime-power coefficients. |
| `NumberTheory/DirichletExponentialBounds.lean` | `small_prime_euler_product_sq_le`, `summable_and_tsum_le_of_finite_euler_bound`, `summable_norm_exp_terms_of_norm_sq_le_factorial`, `summable_exp_terms_of_norm_sq_le_factorial`: finite Euler-product control and absolute Banach-series convergence. |
| `NumberTheory/DirichletExponentialTail.lean` | `sum_reciprocal_square_tail_le`, `euler_tail_factor_le_exp`, `euler_tail_product_le`: elementary bounds for the omitted large-prime Euler factors. |
| `NumberTheory/DirichletExponentialLocalFactors.lean` | `divisorMomentTerm`, `divisorMomentTerm_mul`, `hasSum_zetaReal_pow_prime_power_scaled`, `divisorMomentTerm_prime_local_small`: the multiplicative moment summand and exact small-prime local series. |
| `NumberTheory/DirichletExponentialLocalTail.lean` | `zetaReal_pow_prime_pow_sq_term_le`, `zetaReal_pow_prime_pow_sq_summable`, `zetaReal_pow_prime_pow_sq_tsum_le`: large-prime local second-moment bounds. |
| `NumberTheory/DirichletExponentialMoments.lean` | `divisorMomentTerm_finite_euler_bound`, `divisorMomentTerm_summable_and_bound`, `moment_bound_le_factorial`, `zetaReal_pow_square_summable_and_bound`: the complete generalized-divisor second-moment estimate. |
| `NumberTheory/DirichletExponentialScalarBounds.lean` | `convolutionExp_one`, `residueAF_exp_one`, `convolutionPower_abs_le_zetaReal`, `convolutionExp_abs_le_scaled_zetaReal`: exact first coordinates and the universal bounded-input comparison. |
| `RH/ParetoDirichletExponentialHilbert.lean` | `powerHilbert`, `powerHilbert_exp_norm_summable`, `powerHilbert_exp_summable`, `powerHilbert_exp_tsum_sequence`, `convolutionExp_square_summable_of_power_energy`: actual power vectors, their Hilbert sum, and exact physical-coordinate identification. |
| `RH/ParetoResidueExponentialLimit.lean` | `convolutionPower_tendsto`, `convolutionExp_tendsto_of_uniform_bound`, `residueAF_exp_tendsto_unit`, `residueAF_exp_unit_lower`, `residueExpHilbert_tendsto_unit`: unconditional scalar limits and the Hilbert limit from a common square-summable envelope. |

The complete-moment module proves the decisive provider
`zetaReal_pow_square_summable_and_bound`:

\[
\sum_{n\ge1}\frac{((\zeta^{\star r})(n))^2}{n^2}
\le (12e^2)^r r!,\qquad r\ge0.
\]

This bound, together with the complete-space series assembly, supplies
square summability of the actual envelope \(G=\exp_\star(\zeta)\), and
absolute convergence of the exponential Taylor series in \(H\).
The public endpoint now supplies this provider explicitly, so its final
theorem statements contain no analytic-energy assumption. The reusable generic
assembly retains all quantitative inputs in its own type.

## Actual residue-exponential limit

For each fixed coefficient \(n\), eventually \(g_k(n)=n/k\), so
\(g_k(n)\to0\). Each Dirichlet power depends on finitely many divisor
coefficients. Tannery's theorem applies to its exponential series with the
uniform scalar majorant \((n+1)^r/r!\). Thus

\[
E_k(n):=\exp_\star(g_k)(n)\longrightarrow\delta_1(n).
\]

The zeroth term and coefficientwise monotonicity give

\[
0\le\delta_1(n)\le E_k(n)\le G(n),\qquad
(E_k(n)-\delta_1(n))^2\le G(n)^2.
\]

The generic dominated-convergence consumer takes the envelope energy as
an explicit input. The public module `RH/ParetoDirichletExponential.lean`
supplies it using `zetaReal_exp_square_summable`, defines the actual
`residueExponential : ℕ → ThresholdHilbert`, and proves
`residueExponential_tendsto_unit` without an extra analytic assumption.
No prime assumption is needed for this limit. The full assembly has passed Lean verification.

## Public endpoint

`RH/ParetoDirichletExponential.lean` contains the following declarations:

| Declaration | Exact content |
|---|---|
| `bounded_power_square_summable_and_bound` | Every bounded arithmetic input inherits the factorial inverse-square second-moment estimate. |
| `bounded_convolutionExp_square_summable` | The actual convolution exponential of every bounded real arithmetic input has finite complete Pareto energy. |
| `bounded_convolutionExp_norm_summable` | Its actual Hilbert Taylor terms are absolutely norm summable. |
| `zetaReal_exp_square_summable` | The universal envelope has finite complete Pareto energy. |
| `residue_exp_square_summable` | Every residue exponential has finite Pareto energy. |
| `residueExponential`, `residueExponential_sequence` | A bundled Hilbert vector with exactly the infinite arithmetic coefficients. |
| `residueExponential_tendsto_unit` | Convergence in the Hilbert norm to the actual Dirichlet unit. |
| `residueExponential_not_mem_atomSpan` | For a prime conductor, exclusion from the algebraic residue span. |
| `residueExponential_unbounded_prime_legality_iff_density` | Actual unbounded-prime legality is equivalent to `closedSpace = ⊤`. |
| `riemannHypothesis_of_residueExponential_unbounded_prime_legality` | Actual unbounded-prime legality implies Mathlib RH. |
| `residueExponential_unbounded_prime_legality_iff_riemannHypothesis` | The RH equivalence, with the explicit `hDensity` converse provider. |

## Closed-span legality and exact RH boundary

`RH/ParetoPrimeLimitLegality.lean` contains the checked generic declarations
`tendsto_of_dominated_physical_coordinates`,
`firstPoint_mem_of_unbounded_prime_legality`,
`unbounded_prime_legality_iff_closedSpace_eq_top`, and
`riemannHypothesis_of_unbounded_prime_legality`.

For an actual family converging to \(\delta_1\), the proposition
`UnboundedPrimeLegality E` is exactly

\[
\forall N\in\mathbb N\;\exists p\ge N:\quad p\text{ prime and }E_p\in V.
\]

The generic and specialized proofs establish

\[
\text{UnboundedPrimeLegality}(E)\iff V=H,
\qquad
\text{UnboundedPrimeLegality}(E)\Longrightarrow\mathrm{RH}.
\]

The forward direction takes a cofinal legal prime subsequence, uses
closedness to obtain \(\delta_1\in V\), and invokes the existing equivalences
`firstPoint_mem_iff_one_mem` and `closedSpace_eq_top_iff_one_mem`.
The implication from the resulting constant membership to Mathlib's
`RiemannHypothesis` is already supplied by the project.

The reverse RH-to-density implication is a separate known classical
approximation theorem whose analytic provider is still missing from this
repository. The optional RH equivalence explicitly assumes

```lean
hDensity : RiemannHypothesis → closedSpace = ⊤
```

No unconditional Lean equivalence with RH is claimed. See
[RHToDensityDependencyAudit20260921.md](RH/RHToDensityDependencyAudit20260921.md)
and its natural-approximation update. The new files do not prove
membership of \(E_p\) in \(V\) for a single fixed prime, for every prime,
or for an unbounded family of primes.

## Algebraic-span obstruction

For distinct primes \(p,q\) and every \(a\ge0\), the actual quadratic term
proves

\[
E_p(q^a)\ge\frac{a+1}{2p^2}.
\]

Hence \(E_p\) is unbounded. Every algebraic residue-span vector has a bounded
physical sequence by finite linear-combination induction. The module `RH/ParetoResidueExponentialFiniteSpan.lean` proves `bounded_physical_sequence_of_mem_atomSpan`,
`not_mem_atomSpan_of_sequence_eq_residueExp`, and
`residueExpHilbert_not_mem_atomSpan`.
This excludes finite residue combinations. It does not exclude membership
in the closed residue span, since bounded approximants can converge in
\(H\) to unbounded vectors.

## Conditional research reductions and Open obligations

| Result | Domain-specific obligation |
|---|---|
| Deduce RH from actual residue-exponential legality | **Open:** prove `UnboundedPrimeLegality residueExponential`, equivalently the actual residue-density statement. The checked implication theorem does not supply this hypothesis. |
| Obtain an unconditional Lean equivalence with RH | **Open formalization dependency:** supply `hDensity : RiemannHypothesis → closedSpace = ⊤`. This known classical converse remains an explicit argument in the RH equivalence. |
| Decide legality for one specified prime | **Open in these modules:** establish or refute `residueExponential p ∈ closedSpace`. The cofinal criterion and algebraic-span nonmembership do not decide this statement. |

The envelope-energy and factorial-moment obligations are discharged by checked provider declarations. The established theorem is actual unbounded-prime legality iff `closedSpace = ⊤`, together with its implication to Mathlib RH. No unconditional RH conclusion or fixed-prime closed-span conclusion is claimed.

## Exponentiating the entire legal space

The follow-up [exponential-legality catalog](THEOREM_CATALOG_EXPONENTIAL_LEGALITY_20261113.md)
formalizes coefficientwise convergence for arbitrary real inputs, proves that
bounded-input legality preservation is equivalent to density, and supplies a
positive Hilbert vector with an exponential of infinite energy. Full legality
preservation on V is therefore false; the bounded-input density question remains open.

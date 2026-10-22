# Pareto covariance research: formal coverage

9 September 2026. Source: the conversation's advanced report,
`ParetoCovarianceRepairReport_Advanced_2026-09-08.md`, preserved in
`ParetoCovarianceChatReport.md` as an explicitly informal source.

The continuation contains **21 Lean modules and 230 theorem declarations**:
222 public declarations and 8 private supporting lemmas. The proof bodies passed
coherent Lean checks. These counts include elementary identities, supporting
lemmas, and conditional implications; they are not counts of independent
unconditional arithmetic results. Project acceptance additionally checks the
standalone imports and exported module graph through the publication checkpoint.

## Established constructions and identities

### Unconditional summability of an equivalent repair family

Let `p : ℕ → ℕ` be strictly increasing with `3 ≤ p i`. Let `E(n)` be the
existing actual least `3,5`-smooth integer strictly above `n`, and set

\[
q_i=\min(E(p_i),p_{i+1}),\qquad W_i=U_{p_i,q_i}.
\]

`smooth35SuccessorEndpoint_spec` proves that the intervals are ordered and
disjoint, with `p_i < q_i ≤ 2p_i`. The complete Pareto variance satisfies

\[
\sum_{i<N}\operatorname{Var}(W_i)
\le64\left(\frac1{\sqrt{p_0}}-\frac1{\sqrt{p_N}}\right).
\]

Consequently `summable_smooth35SuccessorRepair_variance` is unconditional.
`smooth35SuccessorRepair_span_eq` proves exact equality of the algebraic spans
of this family and the original repairs `U_{p_i,E(p_i)}`. Interior terms cancel
their common anchor with the exact signed coefficient; terminal terms retain
their original smooth anchor. The proof requires no quantitative smooth-gap
theorem and no prime-distribution theorem. Prime enumeration starting at seven
is a special case of its hypotheses.

The underlying `arithmeticRepair_binary_variance_sqrt_telescope` proves

\[
\operatorname{Var}(U_{n,n+h})\le
64\left(n^{-1/2}-(n+h)^{-1/2}\right),\qquad 1\le h\le n.
\]

The same development proves summability of the complete squared norms and
variances of all adjacent integer repairs. `inverseSmooth35_tsum` evaluates the
entire reciprocal smooth grid as `15/8`, with exact shifted-quadrant tails.

This does not transfer diagonal summability back through an arbitrary change
of coefficients, nor establish convergence of arbitrary weighted sums. The
original uniform Bessel bound remains refuted by the existing library.

### Exact compressed Mellin norm

For physical integer `n+1`, the modules use the actual quantities

\[
w_n=\frac1{(n+1)(n+2)},\quad
d_t(n)=1-\cos\left(t\log\left(1+\frac1{n+1}\right)\right),
\]
\[
h_t(n)=\frac{(n+2)e^{it\log(n+1)}-(n+1)e^{it\log(n+2)}}{1-it}.
\]

They prove `0 ≤ d_t(n) ≤ t² w_n`, convergence of the entire cosine series, and

\[
w_n|h_t(n)|^2=\frac{w_n+2d_t(n)}{1+t^2},\qquad
\sum_{n\ge0}w_n|h_t(n)|^2
=\frac{1+2\sum_{n\ge0}d_t(n)}{1+t^2}.
\]

`fullCosineIdentity` supplies the previously missing provider for
`FullCosineIdentity`. Both the signed mixed term and the infinite Pareto tail
are retained. This is an exact cell-energy identity; construction and derivative
estimates for the phase-centered bounded operators remain separate obligations.

### Closed tails, pivots, and convergence

The modules use the existing actual `ThresholdHilbert` carrier and the closed
spans of the specified tail generators. They construct infinite reverse pivots,
prove their orthogonality and completeness in the generated space, and prove
strong convergence of the tail projections to zero under the stated triangular
head hypotheses. Separate anchor lemmas handle sparse physical coordinates.

`originalRepairSeries_converges_iff` gives the full criterion for the actual
ordered partial sums: summability of the transformed pivot energy **and**
vanishing of the actual moving-boundary projection. It proves the coefficient
transform and its stabilization rather than assuming an abstract expansion.
The criterion does not assert that its two conditions hold for every proposed
coefficient sequence.

Finite projections converge to the infinite ones and retain an exact energy-gap
identity. The head-and-mean module constructs the minimizer, proves the exact
nonnegative-remainder identity, and proves the cost bound for mean-zero vectors
matching the constant head. Pivot lower bounds use their actual physical anchors.

### Finite arithmetic construction and full Gram form

Actual dilations of the two residue seeds can match every specified finite
positive head and any prescribed complete Pareto mean within a finite budget.
Möbius difference recovers residue coefficients and proves strict positivity of
the genuine full-tail Gram form for nonzero coefficient vectors.

The constrained energy identity supplies strict optimality when its actual
stationarity and constraint equations hold. The budget infima are nonnegative,
monotone in the budget for a fixed head, and exhaust the algebraic legal space.
The explicit inverse-matrix solution and the vanishing infinite-budget limit
are not supplied by those statements.

### Adjacent calculus and general cancellation

Adjacent repair modules prove exact covariance differences, Abel summation with
the terminal anchor, the full signed Gram expansion, and the minimum-kernel
factorization and cumulative absolute-coefficient bound.

The general Hilbert module proves the exact variance/covariance/correlation
identities. Its fourth-power estimate assumes the displayed lower bounds on
the two centered norms. The paired-annihilator module proves non-decomposition
and reciprocal-error channel norm bounds **assuming**
`PairedAnnihilatorEstimates`. The arithmetic construction of those witnesses is
not hidden inside a theorem or added as an axiom.

## Module map

| Group | Modules | Theorem declarations | Main scope |
| --- | ---: | ---: | --- |
| General cancellation | 2 | 19 | Exact identities and conditional dual implications |
| Summability and replacement | 4 | 20 | Complete variances, actual replacement family, equal span |
| Finite construction | 4 | 46 | Head/mean interpolation, strict full Gram form, constrained infima |
| Closed tails and pivots | 5 | 89 | Actual projections, anchors, complete expansion and boundary criterion |
| Adjacent calculus | 2 | 26 | Exact signed covariance and terminal-preserving Abel identities |
| Compressed Mellin identities | 4 | 30 | Full cosine convergence/norm identity and explicit analytic targets |

The canonical filenames, source hashes, and isolated-check records are listed
in `ParetoCovarianceChatManifest.md`. All Lean modules use named subject
directories and are exported from `RiemannResearch.lean`.

## Remaining obligations

| Obligation | Status and precise limitation |
| --- | --- |
| `FullCosineIdentity` | Proved by `CompressedMellin.fullCosineIdentity` |
| `CosineMassAsymptotic` | Open: the sharp limit of the actual cosine mass divided by frequency |
| `PhaseCenteredAnalyticProvider` | Open: actual bounded-operator representation, annihilation, norm and derivative estimates |
| `ActualPairedMellinProvider` | Open: quantitative frequency pairing for the actual separately closed seed spaces |
| Arithmetic channel blow-up and correlation asymptotic | Conditional: generic implications are proved, but the arithmetic providers and centered lower bounds still need assembly |
| Original least-smooth family's diagonal summability | Still depends on the unformalized quantitative spacing input; the new equivalent family has an unconditional proof |
| Collective adjacent-series convergence and sharp powers | Open: the full monotone-coefficient convergence theorem, all-one limit, spectral formulas, and critical leading constant |
| Complete graph and matrix solution | Open: the report's complete core-graph parameterization, explicit inverse/Schur formula, and attainment assembly |
| Infinite joint approximation target | Open: finite interpolation and decreasing infima do not prove the full error tends to zero |

The existing Bessel refutation and earlier verified results are retained. No
result in this continuation proves RH. Numerical tables in the informal report
remain numerical evidence, not Lean theorems.

## Verification evidence

The successful coherent checks were:

- General identities: `job_cfDBK86w_sQZ5BcJpewWaU6tEtONS9Yd`.
- Summability and equal span: `job_ZK7C5xdVFGF74Qp1GQ5UtNgdLdiwzx0o`.
- Finite construction: `job_Gv7ARrftwoWIFuZZny8_hBbACie2xlO5`.
- Closed tails: `job_DyVHAzxoIG59DP9B8GvkK5ZIc2kD2_y3`.
- Adjacent calculus: `job_8TTqm8B4uGkVvICbiSzj7mCrJeXNUVSx`.
- Mellin norm and providers: `job_GXd3-Fc6ZrJvt2Ie_GWfYXI__PRGzzBh`.
- Focused cosine import check: `job_oVrZB3LM2RTHBzdAZNeOxf54u8cuiiKH`.

The existing project built successfully before these checks. The final
publication checkpoint is the acceptance gate for the new standalone modules,
their exports, the source audit, and affected dependencies. Ordinary Mathlib
foundations are distinct from the explicitly listed open domain hypotheses.

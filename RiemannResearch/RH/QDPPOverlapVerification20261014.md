# Q divisor DPP: verified global overlap and independent moving-window limits

Date: 14 October 2026.
Source: the user-provided Section 7 of
[QDPPMovingWindowsResearch20261014.md](QDPPMovingWindowsResearch20261014.md).
This reference supports the statements and local calculation, not a novelty claim.
Existing local prime-power providers and the complete Q divisor basis are reused.

## Coordinates and exact global identity

Let Z = zeta(2), q(n) = 1/(Z n^2), and let psi_r(n) denote the normalized
divisor wavelet in counting coordinates. Physical n corresponds to Lean index
i = n-1, and physical conductor r corresponds to basisIndex (r-1).

For positive n,m put g = gcd(n,m) and

```
D = {p prime : v_p(n) != v_p(m)}
F(n,m) = product_(p in D) 2(1-p^(-2)).
```

The new theorem `basisFeatures_absolute_tsum_mismatch` proves the actual
absolutely convergent identity

\[
\sum_{r\ge1}|\psi_r(n)\psi_r(m)|=\frac{g^2}{nm}F(n,m).
\]

The Lean prime set is `valuationMismatchPrimes`, a finite filter of the union
of the prime supports of n and m. In the usual arithmetic notation,
A = nm/g^2 and D is the set of primes dividing A, giving the requested
A^(-1) product_(p|A) 2(1-p^(-2)). The source uses the valuation prime set
directly; this patch does not add a separate declaration rewriting that set
as `Nat.primeFactors (n*m/g^2)`.

## Finite products first, then the justified infinite limit

`RH/QDivisorWaveletOverlap.lean` proves:

- `qDivisorWavelet_eq_jordan_of_dvd` and `qJordanTwo_mul_coprime`.
- Multiplicativity and nonnegativity of the actual absolute-overlap arithmetic
  function, with the prime-power bridge to the existing local wavelets.
- `absoluteOverlapAF_divisor_euler`: an exact finite Euler product for every
  positive conductor L.
- `absoluteOverlapAF_divisor_saturated`: the evaluated finite product once
  each local exponent cutoff contains its complete support.
- `absoluteOverlapAF_divisor_ratio_of_square_dvd`: if (nm)^2 divides L,
  its divisor sum is g^2 F(n,m) times the corresponding divisor sum at site 1.
- The finite prime-correction bounds, including F <= 2^card(D) and
  F^2 g^2 <= 4nm.

The pre-existing `QPrimeWaveletOverlap.lean` supplies the exact local sums:
equal valuations give p^(2v) p^2/(p^2-1), unequal valuations give
2 p^(2 min(v,w)), and all terms above min(v,w)+1 vanish.

`RH/QDivisorDPPOverlap.lean` then proves actual absolute summability from the
complete-basis Hilbert provider. Parseval at physical site 1 supplies the
normalization sum_r A_r(1)^2/J_2(r) = Z. The divisors of
(nm)^2 (N+1)! exhaust all positive conductors, and their saturated identities
converge to the full overlap sum. This is not an assumed infinite prime law.

`prime_inverse_product_tendsto` and `prime_product_tendsto` verify the Euler
limits along the exhaustive finite prime sets of (N+1)!:

\[
\prod_{p\mid (N+1)!}(1-p^{-2})^{-1}\longrightarrow Z,\qquad
\prod_{p\mid (N+1)!}(1-p^{-2})\longrightarrow 1/Z.
\]

These are explicit cofinal finite-product convergence statements. A separate
Mathlib `HasProd` declaration over the prime subtype is not introduced.

## Uniform kernel estimates

The equality is followed by the checked estimates

\[
|K_N(n,m)|\le\frac{g^2}{nm}F(n,m)
\le\frac{g^2}{nm}2^{|D|},\qquad
|K_N(n,m)|^2\le\frac{4g^2}{nm}.
\]

The strongest bound here is the evaluated absolute overlap itself.
`wavelet_sum_abs_le_overlap` applies it to any finite set of these wavelets
with arbitrary real diagonal weights of absolute value at most one.
Consequently reordering, choosing a finite subset, or tapering the basis
does not remove the fixed-offset overlap obstruction.

## Independent Bernoulli configurations at moving fixed offsets

`RH/QDivisorDPPIndependentWindows.lean` proves, for counting offsets i<j,

\[
|K_N(x+i+1,x+j+1)|\le\frac{2(j-i)}{x+1}.
\]

Here the displayed sites are physical; the Lean kernel arguments are x+i and
x+j. Thus if x_N tends to infinity, all distinct fixed-offset off-diagonal
entries tend to zero. The projection rank can be any sequence rank_N;
no growth assumption on that sequence is required.

The generic module `Probability/DeterminantalIndependentLimit.lean` reuses
the finite-restriction DPP law to prove exact mixed occupied/vacant
configuration probabilities. It proves that a diagonal kernel limit sends
each such probability to the corresponding product.

For any finite distinct offsets, if the diagonal entries converge to rho_i,
`basisLaw_fixed_offsets_configuration_tendsto` proves, for every occupied
subset S of the window,

\[
\mathbb P(X_N\text{ occupies exactly }S\text{ in the window})
\longrightarrow
\prod_{i\in S}\rho_i\prod_{i\notin S}(1-\rho_i).
\]

This proves the complete finite law, including all higher joint events.
`basisLaw_fixed_offsets_bernoulli_subsequence` also proves existence of a
strictly increasing subsequence and limiting marginals in [0,1], using
compactness of the finite marginal cube and the actual diagonal bounds.
The configuration consumer applies to every subsequence on which the
marginals converge. Neither a coupling across ranks nor stationarity is assumed.

## Unit-lattice sine exclusion

`basisLaw_not_unit_lattice_sine_limit` assumes the two adjacent marginals
converge to the same density rho with 0<rho<1. It proves that their joint
occupation probability cannot converge to the sine-law target

\[
\rho^2-\left(\frac{\sin(\pi\rho)}{\pi}\right)^2.
\]

The actual pair probability converges to rho^2 and the subtracted sine term
is strictly positive. This excludes the law, not only one chosen kernel
gauge. It is a specific unit-lattice obstruction at moving locations tending
to infinity.

## Conditional scaling consumer and remaining obligations

`basisKernel_scaled_tendsto_zero_of_gcd_budget` is a conditional research
reduction for arbitrary moving sites and real scale factors a_N. Its explicit
geometric obligation is

\[
4a_N^2\frac{\gcd(n_N,m_N)^2}{n_Nm_N}\longrightarrow0.
\]

Under that hypothesis the actual rescaled off-diagonal kernel a_N K_N(n_N,m_N)
tends to zero. The hypothesis is visible in the declaration; the theorem does
not construct a proposed continuum unfolding or supply its budget.

Still open in this patch:

- A general HasProd API statement and the separate quotient-prime-set rewrite
  mentioned above; neither is needed for the checked kernel bounds or limits.
- The quantitative C_epsilon A^(-1+epsilon) theorem, growing-window
  Hilbert--Schmidt estimates, and the Poisson and hole scaling providers.
- Continuum unfoldings outside the explicit vanishing budgets, including
  scales comparable to location or other regimes where that budget fails.
- Independent-prime identification of the entire auxiliary spectral PMF,
  the sharper moving-head vacancy estimate, and far-tail refinements.
- Legal-residue approximation, an arithmetic zeta determinant/trace identity,
  and a Hilbert--Polya spectral identification.

The arithmetic and fixed-offset obstruction results are unconditional and include the
constant mode. The scaled-kernel consumer retains its displayed geometric hypothesis. They prove no new RH theorem.

## Verification

The finite arithmetic identities and budget passed server snippet
`job_9dEfhwWHTpXsvqYMPZqKO8-O0DGMzWx7` (exit code 0, verified true).
The global absolute overlap and actual uniform kernel bound passed
`job_juavi5YRdhg6xb-y76rbN0aVB76g99R3` (exit code 0, verified true).
The Bernoulli subsequence and probability-level sine exclusion passed
`job_qfEvSf6m2PmNteElb2Q9aMCTLDaXJ_KW` (exit code 0, verified true).
The final source-module check and central axiom audit
`job_XVI1iRRut29tJv5d814MWJ3dEtOXDb6Z` succeeded (18.002 seconds,
exit code 0, verified true). It built all four final modules, containing
54 new theorem declarations. All 11 printed central declarations use only
propext, Classical.choice, and Quot.sound. No unresolved proof placeholder,
custom axiom, or unsafe declaration appears in the added sources.

The final publication checkpoint is reported separately at task completion.
It must validate the aggregate and any integrated source before pushing;
a queued checkpoint is not a publication or verification claim.

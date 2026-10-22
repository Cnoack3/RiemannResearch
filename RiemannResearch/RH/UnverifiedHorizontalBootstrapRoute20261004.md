# Unverified route to a larger phase-Gram support

Status: research argument only. None of the analytic providers below has been formalized here, and this is outside the Lean-established result ledger.

Historical route: the corrected and strengthened argument is now recorded in
`GrowingPhaseGramBootstrapAudit20261005.md`, including a sharp factor one-half
and fixed-critical-scale conditioning. The abstract algebraic core is proved in
`Analysis/HorizontalPhaseBootstrap.lean`; actual-zeta providers remain Open.

Let `L = log T`, `ell = log X`, `d = floor X`, and use every integer frequency `1 <= n <= d`. Let `G` be the normalized multiplicity phase Gram and `H` the centered Landau Gram with entries `N(T)^(-1) sum (n/m)^(rho-1/2)`. Reflection across `Re rho = 1/2` expresses its real-part correction using `cosh`.

## Source-checked density quantifiers

Chourasiya–Simonic, *An explicit form of Ingham's zero density estimate*, arXiv:2507.15184v2, 30 September 2025, Corollary 1, counts all complex zeros with their multiplicities. It holds uniformly for `sigma in [1/2,1]`, `T >= 3*10^12`. On `[.5,.625]`, the three table constants are `(8.185,9.461,167.8)`; on `[.625,.875]`, they are `(21.77,8.290,147.0)`. The power of `T` is `3(1-sigma)/(2-sigma)` and the logarithm power is at most 3. The proof of the corollary explicitly handles the interval within `.28/log T` of `1/2`; no fixed-sigma inference is needed.

For `0 <= s <= 3/8`, substituting `sigma=1/2+s` gives the `T` exponent `1-2s/(3/2-s) <= 1-4s/3`. Taking coordinatewise maxima of the constants and using `log T >= 1` gives

    N(1/2+s,T) <= 200 T^(1-4s/3) (log T)^3.

For `3/8 <= s <= 1/2`, monotonicity from `sigma=7/8` extends the same inequality: its exponent is `1/3`, and `1-4s/3 >= 1/3`. Reflection therefore gives a uniform bound `B(s) <= 400 T L^3 exp(-(4/3)L s)` for the number of copies with `abs(beta-1/2) >= s`.

Primary source: https://arxiv.org/pdf/2507.15184

## Proposed deterministic bootstrap

Set `D = diag(log n - ell/2)`, so `norm D <= ell/2`, and `v_gamma=(n^(i gamma))`. For a cutoff `delta0`, retain good copies with `abs(beta-1/2)<=delta0` and define

    M_k = N(T)^(-1) sum_good (beta-1/2)^(2k) v_gamma v_gamma*.

Positivity gives `0 <= M_k <= delta0^(2k) G`. The exact even commutator expansion is

    H_good - G_good = sum_{k>=1} ad_D^(2k)(M_k)/(2k)!.

Since `norm ad_D <= ell`, this yields

    norm(H_good-G_good) <= (cosh(delta0*ell)-1) norm G.

For bad copies, the rank-one operator contribution is at most `d exp(abs(beta-1/2)*ell)`. Integration of the preceding uniform density bound gives, if `ell < (4/3)L`,

    norm(H_bad-G_bad)
      <= C d L^2 exp(-((4/3)L-ell)*delta0)
           * (1+ell/((4/3)L-ell)),

using the actual Riemann–von Mangoldt lower bound `N(T) >= c T L` for sufficiently large `T`. Choose

    delta0 = (2*ell + 4*log L)/((4/3)*L-ell).

Then the bad bound is `O(exp(-ell)/L^2)`, while `epsilon=cosh(delta0*ell)-1` tends to zero whenever `ell=o(sqrt L)`.

The centered Landau estimate, without using a horizontal-normalization lemma, would give

    alpha = norm(H-I)
      <= C [ell/L + X^(5/2)*log(2X)/(T L)
                       + X^(3/2)*L/T + X^2/T].

Here the covariance term follows from the actual proved arithmetic Schur bound in `PrimePowerCovarianceConjugation.lean`; the entrywise analytic estimate remains a Landau provider. This `alpha` tends to zero for `ell=o(sqrt L)`. If `beta` denotes the bad-copy bound, then

    norm(G-I) <= alpha + beta + epsilon*norm G
              <= alpha + beta + epsilon*(1+norm(G-I)),

so, for `epsilon<1`, `norm(G-I) <= (alpha+beta+epsilon)/(1-epsilon)`.

The proposed support is therefore `X=exp(o(sqrt(log T)))`. This requires checking the commutator series, positivity/operator norm details, exact centered Landau provider, and actual-zero instantiation. It must not be listed as a Lean-verified theorem.

## Source for the cluster-square provider

Goldston–Lee–Schettler–Suriajaya, arXiv:2503.15449v4 (30 March 2026), Propositions 1–2 and equations (5.4)–(5.6), all explicitly unconditional, use all complex zeros with multiplicity. Their `N^circledast(T)` is exactly `sum_distinct H(gamma)^2`. With their `L0=log T/(2 pi)` and `U=1/L0`, the Fujii second-moment bound gives `integral (Delta_U N)^2=O(T)`. The nonnegative pair-count identity gives `U N^circledast(T) <= O(T)+O(L0^2)`, hence `sum_distinct H(gamma)^2=O(T L0)=O(N(T))`.

This supplies an unconditional paper-level source, not an existing Lean proof. The source expressly states that the underlying Selberg argument is nontrivial.

Primary source: https://arxiv.org/pdf/2503.15449

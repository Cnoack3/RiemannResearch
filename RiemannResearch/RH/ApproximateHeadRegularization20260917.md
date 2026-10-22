# Approximate heads and regularized conditional energy: verified RH reductions
Date: 2026-09-17

## Status

This continuation proves 14 theorems and introduces four definitions.
It does not prove the Riemann hypothesis. The new RH implications are
**conditional research reductions** whose arithmetic hypotheses remain open.

The main strengthening removes exact head interpolation. It also permits
energy bounds only at arbitrarily large selected scales, with different
selected scales for different exponents.

The source files are:

- Analysis/WeightedComplexPairing.lean — general signed head–tail inequality.
- RH/ConditionalMeanApproximateHeads.lean — actual arithmetic obstruction,
  sparse approximation criterion, and quantitative zero strip.
- RH/ConditionalMeanRegularizedHeads.lean — regularized variational criterion.

All RH conclusions use Mathlib's actual RiemannHypothesis proposition.

## Actual quantities

Fix a set A of positive seed integers. The witnesses g belong to the project's
actual finite legal span legalSeedSpan A. The statements apply, in particular,
to A = {2,3} and to the full positive seed set.

For n >= 1 put
\[
 Cg(n)=\frac1n\sum_{k=1}^n g(k),\qquad
 w_n=\frac{2}{(n+1)(n+2)}.
\]
These are the actual Cesaro conditional mean and fixed mixture weights.
Define
\[
 E(g)=\sum_{n\ge1}w_n|Cg(n)|^2,\qquad
 H_N(g)=\sum_{1\le n\le N}w_n|1-Cg(n)|^2.
\]

E is the full conditional-mean squared norm, not the unsmoothed Pareto norm
and not the approximation error. The series converges for every legal g,
by the existing proved legal-witness summability result.
H_N is a weighted error; it does not require pointwise exact interpolation.

## Signed head–tail barrier

For s with beta = Re(s) > 1/2, let
\[
 b_s(n)=n\left(n^{-s}-2(n+1)^{-s}+(n+2)^{-s}\right),
\]
\[
 P_s(N)=\sum_{n=1}^N b_s(n),\quad
 D_s=\sum_{n\ge1}\frac{|b_s(n)|^2}{w_n},\quad
 T_s(N)=\sum_{n>N}\frac{|b_s(n)|^2}{w_n}.
\]
The existing Mellin development proves that these dual sums converge,
P_s(N) tends to 1, and
\[
 T_s(N)\le K_s N^{1-2\beta},\qquad
 K_s=\frac{3|s(s+1)|^2}{2\beta-1}\quad(N\ge1).
\]

If s != 1 and zeta(s)=0, every actual legal g satisfies the exact signed identity
\[
 \sum_{n\ge1} b_s(n)Cg(n)=0.
\]
Separate the head and tail before taking any estimate:
\[
 P_s(N)=
 \sum_{n\le N}b_s(n)(1-Cg(n))
 -\sum_{n>N}b_s(n)Cg(n).
\]
The two weighted Cauchy–Schwarz bounds and
|u-v|^2 <= 2|u|^2+2|v|^2 give
\[
 |P_s(N)|^2\le 2D_s H_N(g)+2T_s(N)E(g).
\]
Consequently, uniformly over all legal g, for all sufficiently large N,
\[
 \boxed{\frac14\le
     2D_s H_N(g)+2K_sN^{1-2\beta}E(g).}
\]

These are approximate_head_dual_obstruction and
approximate_head_scaled_obstruction_eventually. The source keeps the complete
signed Mellin pairing. The final energy is the actual full energy, with all
cross terms, rather than a sum of absolute coefficient contributions.

## Sparse polynomial energy and zero locations

Suppose Y_j tends to infinity, every g_j is legal, and
\[
 H_{Y_j}(g_j)\longrightarrow0.
\]
Suppose, at arbitrarily large indices j,
\[
 E(g_j)\le C\,Y_j^\alpha.
\]
Then every zero s with Re(s)>1/2 and s != 1 must satisfy
\[
 2\operatorname{Re}(s)-1\le\alpha.
\]
Indeed, if alpha is smaller than this gap, the energy term in the boxed
barrier tends to zero along those good indices, as does the head-error term.
This contradicts its fixed lower bound.

For alpha >= 0, zeta reflection gives the quantitative confinement
\[
 \boxed{\frac{1-\alpha}{2}\le\operatorname{Re}(\rho)
                    \le\frac{1+\alpha}{2}}
\]
for every nontrivial zero rho. A positive alpha below 1 is already an
informative strip improvement, provided its arithmetic hypothesis is proved.

Formal declarations:

- zeta_ne_zero_of_sparse_polynomial_approximate_heads
- nontrivial_zero_strip_of_sparse_polynomial_approximate_heads

If the same legal family has, for every epsilon > 0, a constant C_epsilon
and arbitrarily large indices with
\[
 E(g_j)\le C_\epsilon Y_j^\epsilon,
\]
then RH follows. The constants and good index sets may depend on epsilon.
An eventual bound at every scale is not required.

This is riemannHypothesis_of_sparse_subpolynomial_approximate_heads.
Exact heads remain a special case, since
conditionalHeadError_eq_zero_of_exact_head proves H_N(g)=0 when g=1
on the first N positive integers.

## A single regularized objective

Define
\[
 J_{\alpha,N}(g)=H_N(g)+N^{-\alpha}E(g).
\]
The arithmetic target can now be stated without choosing one witness family
in advance:

For every alpha > 0, delta > 0, and cutoff R, there exist N >= R and an actual
legal g such that J_{\alpha,N}(g) < delta.

This is ArbitrarilySmallRegularizedHeads A.

The stronger obstruction proved in this continuation is: if zeta(s)=0,
Re(s)=beta>1/2, s != 1, and alpha < 2 beta-1, then, uniformly over all legal g,
for all sufficiently large N,
\[
 \boxed{J_{\alpha,N}(g)\ge
     \frac1{4(2D_s+1)}.}
\]
To see this, choose N so large that
2K_s N^{alpha+1-2 beta} <= 1. The previous barrier is then at most
\[
 2D_s H_N(g)+N^{-\alpha}E(g)
 \le (2D_s+1)J_{\alpha,N}(g).
\]

The formal declarations are regularizedHeadCost_obstruction_eventually and
riemannHypothesis_of_arbitrarilySmallRegularizedHeads.

Existing full conditional-mean approximation implies this new feasibility
condition. Choose a legal g with full error below delta/2; its fixed finite
energy is suppressed by N^(-alpha) for large N. This implication is also
formalized as arbitrarilySmallRegularizedHeads_of_conditionalMeanApproximation.

Thus the verified chain is
\[
 \text{full legal conditional-mean approximation}
 \Longrightarrow \text{arbitrarily small regularized costs}
 \Longrightarrow \mathrm{RH}.
\]
No unproved RH-to-density implication is used.

## What remains open

1. Prove ArbitrarilySmallRegularizedHeads for the actual arithmetic legal span,
   or construct a family satisfying the sparse approximate-head conditions.
2. Preserve the full signed Gram energy when estimating the regularized cost.
   For any fixed finite dictionary, it is a concrete quadratic optimization
   problem, but a uniform growing-scale estimate has not been established.
3. The converse from RH to Nyman–Beurling density remains a separate unfinished
   formalization in the existing project. No checked equivalence is claimed here.

The existing canonical Mobius construction supplies an O(N) conditional-energy
bound. Its exponent alpha=1 yields only the full critical strip through the
new strip theorem; it does not establish the subpolynomial hypothesis.
This continuation provides no unconditional improvement of that arithmetic bound.

## Verification provenance

Base project commit: 945601d9b30e1e49b9dea41178076e55d0ebb302.

Successful complete proof-candidate checks:

- job_kFHG5r4l88Pqyky-ig06SITHOEQZnMI0: sparse approximate heads and zero strip.
- job_4bW3wJgCiwFslzm4Mi0QRotUr3l5Zrcb: regularized obstruction and RH criterion.
- job_r0p6lVM4yZr_gsBwmC7VrYgkD7lKK8tN: connection from full approximation.

Each returned exit_code 0 and verified true. The principal declarations'
axiom reports contain only propext, Classical.choice, and Quot.sound.
There are no proof placeholders or custom axioms.

The final project checkpoint additionally validates the saved modules and their
affected dependents before publication. Its commit is reported with delivery.

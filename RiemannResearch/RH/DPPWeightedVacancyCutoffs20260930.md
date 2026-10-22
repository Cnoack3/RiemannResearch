# DPP continuation: weighted vacancy, physical cutoffs, and determinant separation

Date: September 30, 2026.

This continues the September 21 DPP coupling, Mellin, Fredholm, and cutoff
note against RiemannResearch base
`dccea3f784c99129e08ec3aa1f9da4484b320b06`.

## Actual arithmetic objects

Lean's counting coordinate i represents physical site i+1. Write
`w_i = 1/((i+1)(i+2))`, `K_N(i,j) = integerKernel N i j`,
and `K_infty = limitingKernel`.

The new `IntegerDPPWeightedVacancy.lean` defines

\[
\mu_N=\sum_{i\ge0}w_i(1-K_N(i,i)),\qquad
H_{N,M}=\sum_{i<M}w_i(1-K_N(i,i)),
\]
\[
T_{N,M}=\sum_{i\ge0}w_{i+M}(1-K_N(i+M,i+M)).
\]

The limiting mass reuses the existing
`HistoricalTargets.weightedVacancyMass`; no substitute diagonal or
independent process is introduced.

## Exact identities and unconditional conclusions

The full tail is retained in

\[
\boxed{\mu_N=H_{N,M}+T_{N,M}.}
\]

Its certified bound is

\[
0\le T_{N,M}\le\frac1{M+1},\qquad
H_{N,M}\le\mu_N\le H_{N,M}+\frac1{M+1}.
\]

Every finite mass is strictly positive and at most one. The masses are
antitone in N and converge unconditionally to

\[
\mu_\infty=\sum_{i\ge0}w_i(1-K_\infty(i,i)).
\]

The first-site defect gives

\[
\mu_\infty\ge\tfrac12\,\mathrm{limitingVacancy}.
\]

The module proves `weightedVacancyMass_zero_iff_top` and
`finiteWeightedVacancyMass_tendsto_zero_iff_top`: zero limiting mass, or
convergence of the finite masses to zero, is equivalent to density of
the actual residue span. Under not RH, the limiting mass is strictly
positive.

For finite computations, `weightedVacancyPrefix_eq_gram_trace` gives

\[
H_{N,M}
=1-\frac1{M+1}
-\operatorname{tr}\bigl(
W_M B_{N,M}G_N^{-1}B_{N,M}^{\mathsf T}\bigr).
\]

Here `B` is the actual window observation matrix, and `G_N` is the full
Pareto Gram matrix. Its arithmetic tails and mixed terms are retained.

## A finite certificate and the remaining arithmetic provider

Define

\[
C_{N,M}=H_{N,M}+\frac1{M+1}.
\]

The theorem `weightedVacancyCutoffCertificates_iff_top` proves

\[
(\forall\varepsilon>0\;\exists N,M:\ C_{N,M}<\varepsilon)
\quad\Longleftrightarrow\quad
\mathrm{closedSpace}=\top.
\]

The theorem `riemannHypothesis_of_weightedVacancyCutoffCertificates`
concludes Mathlib's `RiemannHypothesis` from that explicitly stated
certificate provider.

**Open:** produce these certificates for every positive epsilon. The
uniform tail bound alone does not supply the required arithmetic ranks
or prove RH.

## Quantitative determinant separation

`ContractiveProducts.lean` now proves an exact single-factor recurrence
for the difference of two products. It also proves, for
`0 <= b_i <= c_i <= 1`,

\[
\left(\prod_i b_i\right)\sum_i(c_i-b_i)
\le\prod_i c_i-\prod_i b_i
\le\sum_i(c_i-b_i).
\]

`MultiplicativeOccupancy.lean` lifts this to finite occupation variables
and exact expectations of weighted holes. No independence, negative
association, or DPP assumption is needed for the general comparison.

`IntegerDPPWeightedDeterminant.lean` specializes it to the genuine
limiting arithmetic DPP. Put

\[
B_M=\prod_{i<M}(1-w_i),\quad
\mu_{\infty,M}=\sum_{i<M}w_i(1-K_\infty(i,i)).
\]

For the existing `dampedPrefixDeterminant M`, denoted `D_M`, the exact
identity `dampedPrefixDefect_eq_integral` is the expectation of the
complete occupation product minus its benchmark. The resulting bounds are

\[
B_M\mu_{\infty,M}\le D_M-B_M\le\mu_{\infty,M}.
\]

Both limits exist without RH. With
`F_infty = dampedPrefixLimit` and
`p_* = paretoProductBenchmark`, passage to the limit gives

\[
\boxed{p_*\mu_\infty\le F_\infty-p_*\le\mu_\infty.}
\]

Consequently, the module directly identifies

\[
\mu_\infty=0\quad\Longleftrightarrow\quad F_\infty=p_*.
\]

The observation cutoff M here is distinct from arithmetic projection
rank N. These results use actual finite determinant expectations and
their established limit.

## Verification and scope

The complete coherent candidate, including the general product comparison,
the occupation expectation, the cutoff criterion, and the determinant
comparison, passed an isolated Lean run with exit code 0.
The decisive declarations

- `dampedPrefixLimit_defect_bounds`;
- `riemannHypothesis_of_weightedVacancyCutoffCertificates`;

reported only `propext`, `Classical.choice`, and `Quot.sound`.
The certificate hypothesis remains visible in the latter theorem's type.
Repository acceptance additionally uses the final change-aware checkpoint.

This continuation does not discharge the provider for full spatial
coupling, full negative association, infinite-dimensional operator
Fredholm identification, the sharp log comparison
`mu <= log(F/p_*) <= 2*mu`, or spectral min-max cutoff estimates.
It does not assume RH or construct an undamped infinite Mellin DPP.

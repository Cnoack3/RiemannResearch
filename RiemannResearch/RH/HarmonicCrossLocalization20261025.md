# Harmonic signed-cross investigation — 25 October 2026

## Status

The requested unconditional limit \(X_M\to0\) was **not proved**. A new unconditional localization removes the infinite physical tail beyond \(M^2\) and the diagonal from the limit problem. The remaining finite-window limit is explicit and still open.

The RH theorem is a conditional research reduction, with that limit as its only displayed arithmetic hypothesis. No unconditional RH theorem, or converse from RH to this particular harmonic family's convergence, is asserted.

## Actual family and normalization

For \(N\ge1\), let \(q_N\) be the least prime exceeding \(N\), and set
\[
a_N=\sum_{d\le N}\frac{\mu(d)}d,\qquad
G_N=-\sum_{d\le N}\mu(d)g_d+q_Na_Ng_{q_N},
\quad g_d(n)=\frac{n\bmod d}{d}.
\]
All norms and pairings below use the complete Pareto measure
\(P(n)=1/[n(n+1)]\), \(n\ge1\). The Q-defined trials are transferred to P with physical coordinates unchanged.

Write
\[
r_N=G_N-1,\quad H_M=\sum_{N=1}^M\frac1N,\quad
F_M=\frac1{H_M}\sum_{N=1}^M\frac{G_N}{N},\quad R_M=F_M-1.
\]
For \(M\ge1\),
\[
\|R_M\|_P^2=D_M+X_M,\qquad
D_M=\frac1{H_M^2}\sum_{N\le M}\frac{\|r_N\|_P^2}{N^2},
\]
\[
X_M=\frac2{H_M^2}\sum_{1\le N<L\le M}
\frac{\langle r_N,r_L\rangle_P}{NL}.
\]
Earlier verified results give \(\|r_N\|_P^2\le9N\), hence
\(0\le D_M\le9/H_M\to0\).

An estimate \(E_N/N\ll1/\log N\), with \(E_N=\|r_N\|_P^2\), does not imply \(E_N\to0\).

## Newly verified localization

The module is RH/DenseHarmonicLocalization.lean, in namespace
RiemannResearch.RH.QPrimeBalancedExactHead.

The exact heads imply
\[
R_M(n)=\frac1{H_M}
\sum_{N=1}^{\min(M,n-1)}\frac{r_N(n)}N.
\]
Consequently,
\[
|R_M(n)|\le\frac{3\min(M,n-1)}{H_M}.
\]
The module proves the two resulting bounds separately and proves convergence at every fixed positive coordinate.

For every \(K\),
\[
0\le\sum_{n\le K}\frac{|R_M(n)|^2}{n(n+1)}
\le\frac{9K}{H_M^2}.
\]
Thus any window \(K_M=o(H_M^2)\) contributes vanishing energy by this bound. In particular every fixed finite head vanishes. This does not justify passing to the whole norm.

The global amplitude and exact Pareto tail mass give
\[
0\le T_M:=\sum_{n>M^2}\frac{|R_M(n)|^2}{n(n+1)}
\le \frac{9M^2}{H_M^2(M^2+1)}
\le\frac9{H_M^2}\longrightarrow0.
\]
This controls the **entire omitted tail** unconditionally.

Define
\[
A_M=\sum_{n=1}^{M^2}\frac{|R_M(n)|^2}{n(n+1)}.
\]
The full signed equality and its consequences are
\[
\boxed{X_M-A_M=T_M-D_M,}
\]
\[
\boxed{A_M-\frac9{H_M}\le X_M\le A_M+\frac9{H_M^2},}
\]
\[
\boxed{X_M-A_M\to0,\qquad
X_M\to0\ \Longleftrightarrow\ A_M\to0.}
\]

Principal declarations:

- harmonicResidual_truncated: exact support truncation.
- harmonicResidual_pointwise_tendsto: fixed-coordinate convergence.
- harmonicResidual_head_le: \(9K/H_M^2\) head bound.
- harmonicResidualVector_eq_average_sub: identification with the actual harmonic average minus one, for \(M>0\).
- harmonicResidual_energy_exact: complete energy equals diagonal plus signed cross.
- harmonicResidual_quadratic_tail_le: unconditional \(9/H_M^2\) tail bound.
- harmonicCross_sub_quadratic_head_exact: full signed remainder equality.
- harmonicCross_quadratic_head_bounds: two-sided bound.
- harmonicCross_sub_quadratic_head_tendsto: unconditional remainder convergence.
- harmonicCross_tendsto_iff_quadratic_head: equivalence of the two limits.
- riemannHypothesis_of_harmonic_quadratic_window: RH follows **if** \(A_M\to0\).

The reusable amplitude argument was added to RH/ParetoAmplitudeCertificates.lean as quadratic_tail_le, quadratic_tail_tendsto, and energy_tendsto_iff_quadratic_head.

## Remaining arithmetic target

It suffices to prove
\[
\sum_{n\le M^2}\frac1{n(n+1)}
\left(\sum_{N=1}^{\min(M,n-1)}\frac{r_N(n)}N\right)^2
=o(H_M^2).
\]
The square contains the complete signed Möbius and prime-anchor contributions. Absolute-amplitude estimates give an upper bound too large to establish this target.

For example, the stronger covariance estimate
\[
\langle r_N,r_L\rangle_P\le C\frac NL\qquad(1\le N<L)
\]
with fixed \(C\ge0\) would yield
\[
X_M\le\frac{2C}{H_M^2}
\sum_{L=2}^M\frac{L-1}{L^2}\le\frac{2C}{H_M}.
\]
Together with \(X_M\ge-9/H_M\), this would prove the requested limit.
**Open:** this covariance estimate has no established arithmetic provider. This implication is ordinary analysis in this memo, not a separately formalized theorem.

## Earlier zero-energy estimates

A focused source audit of RH/ActualSamplingHeights.lean,
RH/RamanujanZeroSignal.lean, and Analysis/FiniteGramSignalStability.lean found estimates for a different family.

Granting the horizontal-zero input
\(\mathcal E(T)/T\ll1/\log T\) controls signal sampling in each finite inverse-Gram norm. Existing cutoff-selection results permit sufficiently large heights even along growing dictionaries. The remaining issue is not merely dependence of constants on the dictionary.

The normalized target-error identity retains
\[
\|1-F_{D,T}\|^2
=\kappa_D^{-1}-1+\|F_{D,T}-F_{D,\infty}\|^2.
\]
Perfect signal sampling leaves the capacity defect. No checked identity currently transfers that horizontal-zero estimate into a bound for the present \(A_M\) or \(X_M\). The analytic zero-density input also remains an explicit provider hypothesis in the inspected Lean development.

## Classical comparison

The harmonic coefficient of the unanchored Möbius contribution is
\[
-\mu(d)\frac{H_M-H_{d-1}}{H_M},
\]
close to the logarithmic taper
\(-\mu(d)(1-\log d/\log M)\). The moving-prime correction is an additional term.

Bettin, Conrey and Farmer, *An optimal choice of Dirichlet polynomials for the Nyman–Beurling criterion*, [arXiv:1211.5191](https://arxiv.org/html/1211.5191v1), Theorem 1, prove the standard logarithmic Möbius polynomial's mean-square asymptotic under RH and an additional inverse-square zeta-derivative moment bound. This is relevant precedent for the taper. It supplies neither an unconditional estimate here nor a proved transfer for our moving prime anchors.

## Exploratory computation

Ordinary floating-point calculations gave the following ranges after adding analytic bounds on omitted infinite tails:

| \(M\) | Approximate range for \(X_M\) |
|---:|---:|
| 1024 | 0.00841717–0.00845879 |
| 2048 | 0.00755376–0.00768050 |
| 4096 | 0.00681034–0.00693102 |
| 8192 | 0.00619565–0.00637070 |

These are **not certified numerical intervals**: floating-point roundoff was not enclosed. They establish no limit.

The computation expands \(F_M=\sum_dc_dg_d\), uses balance
\(\sum_dc_d/d=0\), and evaluates
\(F_M(n)-F_M(n-1)=-\sum_{d\mid n}c_d\) by a divisor sieve.
Energy cutoffs were respectively 50, 50, 200, and 500 million; diagonal energy was evaluated through 200,000. Coefficient sign bounds control the omitted tails.

## Verification

The saved module and principal axiom checks passed server job
job_YwyzVxTmfA95igggaQcTOxCOeqoYpYuo, with reported verification time
13.344 seconds. The printed RH declaration explicitly retains hwindow.
The principal axiom lists contain only propext, Classical.choice, and Quot.sound; these lists do not discharge hwindow.

The final publication checkpoint separately validates the complete unpublished delta and its required dependency scope.

Next work should target the moving finite-window square mean or actual covariance decay. Fixed-coordinate convergence, reciprocal-mass divergence, finite numerical trends, and elimination of the far tail do not supply that estimate on their own.

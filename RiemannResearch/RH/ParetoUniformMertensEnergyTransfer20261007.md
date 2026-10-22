# Sharper uniform Mertens-to-energy transfer: paper proof and source audit

Date: 7 October 2026.

Status: the finite logarithmic transfer in Section 2 is formalized as
`canonicalMobius_energy_of_uniform_mertens_log` in
`RH/CanonicalMobiusLogEnvelopeEnergy.lean`; its full-file Lean check passed with
exit code 0 and empty diagnostics. The sharper rate corollaries, compact-trial
constants and literature specialization below remain **paper consequences**.
Nothing here establishes the optimizer-tail provider or RH.

## 1. Exact existing inputs

All repository references in this section are pinned to
`da1d01a43df6cc60a04b7af8d2f20dfe415ee7a8`.

Let `M(y)` be the Mertens function, `m_N = mobiusReciprocalSum N`,
`A_N = canonicalMobiusHilbert N`, and
`H_J = harmonic J = sum_{j=1}^J 1/j`.

`RH/MobiusReciprocalCutoff.lean` proves
`mobiusReciprocalSum_cutoff_bound_of_uniform_M_bound`: for positive integers
`N,J`, nonnegative `epsilon`, and `|M(y)| <= epsilon y` for every real `y >= N`,

\[
|m_N|\le \frac1J+\frac1{NJ}+\epsilon(H_J+1). \tag{1}
\]

`RH/CanonicalMobiusQuantitativeEnergy.lean` proves
`canonicalMobiusHilbert_harmonic_energy_bound`: for `K >= 2`, the same uniform
summatory bound, and `|m_N| <= B`,

\[
\frac{\|A_N\|^2}{N}
\le \frac3N+2K\{\epsilon(H_K+1)+B\}^2+\frac4K. \tag{2}
\]

This controls the **complete infinite physical norm**. In its proof the last
term comes from the full far tail; no truncation or discarded square is used.
Both inputs are applicable to arbitrary positive `N`; no RH premise is present.

## 2. A stronger finite transfer

**Proposition.** Suppose `N >= 1`, `0 < epsilon <= 1`,

\[
L=1+\log(1/\epsilon),\qquad h=\epsilon L\le\frac12,
\]

and `|M(y)| <= epsilon y` for all real `y >= N`. Then

\[
\boxed{|m_N|\le5\epsilon\{1+\log(1/\epsilon)\},\qquad
\frac{\|A_N\|^2}{N}\le\frac3N+
260\epsilon\{1+\log(1/\epsilon)\}.} \tag{3}
\]

**Proof.** Let

\[
J=\lceil1/\epsilon\rceil,\qquad K=\lceil1/h\rceil.
\]

The ceiling is the nonnegative integer ceiling. Because `epsilon > 0`,
`L >= 1`, `h > 0`, and `h <= 1/2`, these integers satisfy `J >= 1`, `K >= 2`.
The exact ceiling inequalities imply

\[
\frac1J\le\epsilon,
\quad \frac1{NJ}\le\frac1J\le\epsilon,
\quad \frac1K\le h,
\quad Kh\le1+h\le2. \tag{4}
\]

Since `h >= epsilon`,

\[
J\le1/\epsilon+1\le2/\epsilon,
\qquad
K\le1/h+1\le1/\epsilon+1\le2/\epsilon.
\]

For either `R = J` or `R = K`, the checked harmonic inequality
`harmonic_le_one_add_log` therefore gives

\[
H_R+1\le2+\log R
\le2+\log2+\log(1/\epsilon)
\le3L. \tag{5}
\]

The last step uses `log 2 <= 1` and `L >= 1`; in fact its left side is at most
`L+2 <= 3L`. Apply (1) at `J` and use (4)--(5):

\[
|m_N|\le2\epsilon+3\epsilon L\le5h.
\]

Set `B=5h` in (2). Its whole middle-window coefficient is nonnegative and obeys

\[
D:=\epsilon(H_K+1)+5h\le3h+5h=8h.
\]

Consequently,

\[
2KD^2+4/K\le128Kh^2+4h\le256h+4h=260h,
\]

which proves (3). Every term of (2), including its far-tail contribution, has
been retained. The constant can be slightly reduced using `Kh <= 3/2`, but
`260` facilitates direct comparison with the existing square-root transfer.

## 3. Consequence for the existing checked stretched profile

The checked theorem `M_stretched_loglog_bound` in
`NumberTheory/PrimeNumberTheorem/MertensStretchedDecay.lean` supplies some
`d > 0`, `B >= 0` with

\[
|M(y)|\le B y\exp\{-d\Phi(y)\},\qquad
\Phi(y)=\{(6+\log y)\log(6+\log y)\}^{1/11},\quad y\ge1.
\]

The profile is increasing and tends to infinity. For each large `N`, put

\[
\epsilon_N=(B+1)e^{-d\Phi(N)}.
\]

It supplies a uniform summatory bound for every `y >= N`. Eventually
`epsilon_N <= 1` and
`h_N = epsilon_N{1+log(1/epsilon_N)} <= 1/2`. Equation (3) applies.
Since `log(B+1) >= 0`,

\[
h_N\le(B+1)(1+d\Phi(N))e^{-d\Phi(N)}.
\]

For any `0 < rho < 1` and `t >= 0`,

\[
(1+t)e^{-t}\le\frac1{1-\rho}e^{-\rho t}. \tag{6}
\]

Indeed `exp((1-rho)t) >= 1+(1-rho)t >= (1-rho)(1+t)`.
Thus eventually

\[
|m_N|\le\frac{5(B+1)}{1-\rho}e^{-\rho d\Phi(N)},
\qquad
\|A_N\|^2\le3+
\frac{260(B+1)}{1-\rho}N e^{-\rho d\Phi(N)}. \tag{7}
\]

For example `rho=3/4` gives constants `20(B+1)` and `1040(B+1)` and exponential
coefficient `3d/4`. The existing assembled theorem uses coefficient `d/2`
because it applies `canonicalMobius_energy_of_uniform_mertens_square` with a
square-root envelope. This is a quantitative improvement to the same checked
arithmetic provider, not a replacement of it with a stronger unproved one.

## 4. Complete compact trial constants

For `N=4m+4`, write `Y1=N-1`, `Y2=N/2-1`, `Y3=N/4-1`. The exact decomposition
and its full signed expansion are already checked in
`RH/ParetoCompactTrialEnergy.lean`. Only after that equality, the checked bound
is

\[
U_N\le3\{196\|A_{Y1}\|^2+338\|A_{Y2}\|^2+36\|A_{Y3}\|^2\}. \tag{8}
\]

If `||A_Y||^2 <= 3+C Y E(Y)` eventually, where `E` is nonincreasing, then once
all three indices exceed the provider cutoff and `N >= 8`, each `Yi >= N/8`.
Equation (8) yields the explicit whole-family envelope

\[
\boxed{U_N\le5130+1122 C N E(N/8).} \tag{9}
\]

Here `5130=9(196+338+36)` and
`1122=3(196+338/2+36/4)`. Before weakening its positive linear factor the
upper bound is exactly

\[
5130+3C(374N-570)E(N/8).
\]

For (7), take `E(Y)=exp(-rho d Phi(Y))`. A sufficient **still open** arithmetic
product budget is therefore a cofinal

\[
N e^{-\rho d\Phi(N/8)}S_{4m}\longrightarrow0,
\]

since `S_{4m} -> 0` is already established. Equation (9) does not prove this
budget. The stronger finite energy transfer is now formalized separately;
its rate and compact-trial assembly remain open formalization tasks.

## 5. Recent primary sources and limitations

1. Ethan Simpson Lee and Nicol Leong,
   *New explicit bounds for Mertens function and the reciprocal of the Riemann
   zeta function*, arXiv:2208.06141v5, revised 9 September 2026.
   https://arxiv.org/html/2208.06141v5
   Theorem 1.1, equation (12), supplies an unconditional explicit bound of order
   `x log x exp(-eta (log x)^(3/5)/(log log x)^(1/5))`. After the eventual
   monotonicity and polynomial absorption are proved, (3) gives a paper
   envelope `||A_N||^2 <= 3+C N exp(-a (log N)^(3/5)/(log log N)^(1/5))` for a
   positive `a`. This literature theorem is not currently a checked repository
   provider. It must remain distinct from (7).

2. Werner Ehm, *On certain Gram matrices and their associated series* (2024).
   https://arxiv.org/html/2405.06349v2
   Section 8 retains an explicit Mobius-inversion error in its quadratic-form
   decomposition and calls its estimation a major challenge. It supplies useful
   exact arithmetic organization, not a solved inverse-Gram or optimizer-tail
   cancellation estimate.

3. Helmut Maier and Michael Th. Rassias,
   *Explicit estimates of sums related to the Nyman-Beurling criterion* (2018).
   https://arxiv.org/html/1806.05070v1
   Theorem 2.1 gives power saving for a particular long interval
   `sum_{k^D <= n < 2 k^D} mu(n) g(n/k)`, `D >= 2`, with `g` its Estermann-type
   function. No identification with the full present stage-dependent optimizer
   coefficients has been established; this is not a complete-source provider.

4. Radu Ioan Bot and Bernd Hofmann,
   *Conditional stability versus ill-posedness for operator equations with
   monotone operators in Hilbert space* (2016).
   https://www.mat.univie.ac.at/~rabot/publications/jour16-09.pdf
   Section 4, equation (4.8), derives bias bounds `R alpha+d(R)` from approximate
   source conditions. Quantitative rates require control of `d(R)`; positivity
   and regularization alone do not supply uniform rates for our changing finite
   stage operators.

5. Francois Alouges, Sebastien Darses and Erwan Hillion,
   *Polynomial approximations in a generalized Nyman-Beurling criterion* (2022).
   https://www.numdam.org/articles/10.5802/jtnb.1227/
   Their unconditional approximation construction leaves coefficient control as
   the substantive remaining input. This reinforces the distinction between
   growing-threshold source escape and fixed-threshold tightness.

Recent-source audit: arXiv:2510.18132, *Beurling Nyman Geometry and Gram Matrix
Structure, Ladder Density and Polynomial Decay via Mellin Smoothing* (2025),
https://arxiv.org/pdf/2510.18132, cannot be used through its stated Theorem 6.1
proof as-is. Page 7 asserts
`|(j'-j)log2+(k'-k)log3| >= min(log2,log3)(|j'-j|+|k'-k|)`, false for the two
indices `(1,0)` and `(0,1)`. This observation rejects that proof step; it is not
a claim that every possible repaired decay theorem is false.

## 6. Sharp one-mode obstruction to closing the product budget

The direct normal-equation product estimate is a useful improvement over the
threshold optimization. In a finite head Hilbert space let
`L=A* A`, `x=(I+L)^(-1)b`, and let `c` be any legal trial head. Then exactly

\[
T=\langle b-x,b-c\rangle+\langle Ax,Ac\rangle,\qquad
\|b-x\|^2=T-S,
\]

so

\[
T\le\|b-c\|\sqrt{T-S}+\|Ac\|\sqrt S.
\]

In the actual compact trial, `||b-c|| <= |q_N|` and `||Ac||^2 <= U_N`, giving
`T <= |q_N| sqrt(T)+sqrt(U_N S)`. This displayed finite bound is a paper
consequence. `RH/ParetoCompactTailProduct.lean` formalizes the underlying exact
signed pairing, its convergence to the defect, and the sharp product lower
floor; no separate declaration of this simplified finite bound is exported.

The coefficient of its product term is asymptotically sharp even with full
physical trial energy. Fix `delta > 0`, choose any `lambda_N -> infinity` with
`lambda_N=o(N)`, and take a single head source with `||b||^2=delta`, tail map
`A=sqrt(lambda_N)`, and exact-head trial `c=b`. The **full** trial energy is

\[
U_N=\|c\|^2+\|Ac\|^2=\delta(1+\lambda_N).
\]

The exact quantities are

\[
q_N=0,\quad
T_N=\frac{\delta\lambda_N}{1+\lambda_N},\quad
S_N=\frac{\delta\lambda_N}{(1+\lambda_N)^2},\quad
D_N(t)=\frac{\delta\lambda_N}{t+\lambda_N}.
\]

Thus `U_N=o(N)`, `D_N(t)<=U_N/t`, and the mass above each fixed `cN` eventually
vanishes, while

\[
T_N\to\delta>0,\qquad S_N\to0,\qquad U_NS_N\to\delta^2.
\]

This is an abstract audit model, not the actual arithmetic spectrum. It shows
why a stronger trial envelope still cannot establish `U_NS_N -> 0` by geometry
alone. The retained signed optimizer-trial pairing is the next arithmetic
quantity to attack.

# Lean provider-gap continuation — 2026-10-05

This continuation verifies and strengthens the saved provider candidates against
base `d63493371c5aa8dd4f69897d3df62cdd4d09a317`. It proves finite moment,
Landau-residual, and actual signed-tail estimates. It does not prove RH or
replace the missing displacement-sensitive analytic density theorem.

## Actual good-copy moment refinement

Write `G = phaseGram T d`, `B_k = goodMoment T d δ k`, and
`H = landauGram T d`. All use every actual zero copy, its analytic
multiplicity, integer frequencies `1,…,d`, and the original full `Ncount`
normalizer. In formulas involving `N(T)=0`, inverses and division use
Lean's total convention `0⁻¹=0`; otherwise they are ordinary division.
For `δ ≥ 0`, the kernel proves

\[
0\le B_k\le \delta^{2k}B_0,\qquad
\|B_k\|\le\delta^{2k}\|B_0\|,\qquad \|B_0\|\le\|G\|.
\]

The first comparison is the exact weighted rank-one identity

\[
\delta^{2k}B_0-B_k=
\frac1{N(T)}\sum_{c\in\operatorname{Copies}(T)}
\left(\delta^{2k}1_{|\beta_c-1/2|\le\delta}
-1_{|\beta_c-1/2|\le\delta}(\beta_c-1/2)^{2k}\right)v_cv_c^*.
\]

Each coefficient is nonnegative. Its quadratic form and the proved Rayleigh
characterization give the norm comparisons, including the empty-copy and
zero-dimensional cases. The centered comparison is

\[
\left\|B_k-\frac{\delta^{2k}\|B_0\|}{2}I\right\|
\le\frac{\delta^{2k}\|B_0\|}{2}.
\]

It feeds the existing absolutely convergent even-commutator series. With
`ell = log d`, `d ≥ 1`, and the complete signed bad correction `R_bad`,

\[
\|H-G-R_{\rm bad}\|
\le \frac{\|B_0\|}{2}(\cosh(\delta\ell)-1).
\]

`goodCorrection_truncation_norm_le_zeroth` gives the same bound minus the
explicit first `J` scalar majorant terms for the norm of the omitted operator
tail. No bad term is deleted from the exact identity before estimating it.

Declarations live in `HorizontalEuclideanMoments`, `ActualZeroPhaseMoments`,
`ActualZeroLogDiagonal`, and `ActualZeroPhaseOperators`.

## Full leading-budget Landau convergence

The existing fixed-`c=2` analytic provider bounds the complete operator
residual by a constant times the three-term envelope divided by log height.
Set `L = log(T+3)`, `ell = log d`. The exact scalar identity is

\[
\frac{\mathcal E(L,\ell)}L
=\frac{e^{7\ell/2-L}}L
+L e^{5\ell/2-L}+e^{2\ell-L}.
\]

For `L → ∞`, the kernel now proves the equivalence

\[
\mathcal E(L,\ell)/L\to0
\quad\Longleftrightarrow\quad e^{7\ell/2-L}/L\to0.
\]

For sufficiency, the leading term is eventually at most one; thus
`7 ell/2 − L ≤ log L`. The explicit elementary estimate `log L ≤ L/6`
for `L ≥ 144` implies `ell ≤ L/3`. The other terms are then bounded by
`L exp(−L/6)` and `exp(−L/3)`, both tending to zero. Necessity uses only
nonnegativity of the three terms. It concerns this envelope, not the actual
signed residual, which can have cancellation.

Consequently, for eventual `d(T) ≥ 1`,

\[
\frac{d(T)^{7/2}}{(T+3)\log(T+3)}\to0
\implies \|\operatorname{actualLandauResidual}(T,d(T))\|\to0.
\]

In particular it suffices that
`log d(T) ≤ a + (2/7) log(T+3) + b log log(T+3)` eventually, with `b < 2/7`.
This allows every fixed logarithmic factor below the endpoint:

\[
d(T)=O((T+3)^{2/7}\log(T+3)^b),\qquad b<2/7.
\]

Wolfram independently simplified the variable part of the leading exponent
to `((7b−2)/2) log L`. The full support bound gives the majorant
`exp(7a/2) * L^((7b−2)/2)`; its limiting behavior is Lean-checked.
The original signed prime-power covariance operator is retained.
Declarations live in `LandauGrowingSupport` and `ActualLandauOperatorResidual`.
The classical sharper Landau–Gonek estimate remains an analytic formalization
gap; this continuation extends the already proved fixed-`c=2` provider.

## Harmonic cap for the actual signed bad operator

Let `H_d = sum_{n=1}^d 1/n` and define

\[
W_d=\frac{d+\sqrt{d(d+1)H_d/2}}2.
\]

`FiniteHyperbolicHarmonicCap` proves this closed expression, nonnegativity,
and, for `d ≥ 1`,

\[
W_d\le\frac d2\bigl(1+\sqrt{1+\log d}\bigr).
\]

The proof pairs a finite exponential product with its reversed-index copy:
the product equals a sum of `cosh(t(x_i−x_j))`, so its maximum for `|t|≤1`
is at `t=1`. A common frequency translation cancels. For integer logarithmic
frequencies the endpoint product is `(sum n)(sum 1/n)`.

The actual zero strip gives `|2(β_c−1/2)|≤1`. For the two normalized
exponential vectors, their real cross-inner-product is exactly `d/N(T)`.
The rank-two signed-row coefficient is therefore at most `W_d/N(T)`.
Summing the original strict-bad weights gives exactly `strictTail T δ`.
The actual operator is Hermitian, so both quadratic-form signs yield

\[
\|H_{\rm bad}(T,d,\delta)\|
\le\operatorname{Budget}(T,d,\delta)
\le\frac{\operatorname{strictTail}(T,\delta)}{N(T)}W_d.
\]

The sharper complementary rank-two coefficient also gives, for
`r = strictTail/N`, the asymmetric spectral interval
`[−r(W_d−d), r W_d]`. The kernel proves `W_d ≥ d` and the centered norm bound

\[
\left\|H_{\rm bad}-\frac{rd}{2}I\right\|
\le r(W_d-d/2)
=\frac r2\sqrt{d(d+1)H_d/2}.
\]

In particular,
`||goodHyperbolic|| ≤ ||landauGram|| + (strictTail/N) W_d`.
The denominator is still the full zero count. The negative sinh square,
composite-frequency interactions, and analytic multiplicities are retained.
These declarations live in `ActualHyperbolicHarmonicTail`; generic Hermitian
kernel and negative rank-two lemmas live in the existing finite algebra modules.

## Remaining analytic formalization inputs

The cumulative theorem `Zeta23.thmA₀_cumulative` and its existing strict-tail
consumer were type-checked and their axioms audited. They give, eventually
and uniformly for every nonnegative cutoff,
`strictTail/N ≤ 1/3 + ε`. The new finite cap consumes that fraction, but a
constant fraction does not establish smallness for growing `d`.

This insufficiency is logical, not a claim about an actual configuration of
zeta zeros: a model count with two thirds on the line and one third at a
fixed symmetric displacement satisfies the proportion, yet for a cutoff
tending to zero its strict-tail fraction remains one third. Therefore the
proportion alone cannot imply a vanishing count-only tail budget.

A sufficient remaining actual input is only the one-point condition

\[
\frac{\operatorname{strictTail}(T,\delta(T))}{N(T)}W_{d(T)}\to0.
\]

It is stronger than the exact directional signed-surplus provider already
proved equivalent to the desired masked hyperbolic lower form. It need not
be obtained from a density law on the entire zero strip.

For comparison, a near-line uniform estimate
`N(1/2+δ,T) ≤ C T (log T)^k exp(−4δ log T/3)` suffices at
`ell=O(sqrt(log T))` with
`δ=(3/4)(ell+p log log T)/log T`, provided `p>k−3/4`.
Reflection, `N(T) ≍ T log T`, and the harmonic cap give the scalar budget
`O((log T)^(k−3/4−p))`. The additive finite-height zero count is retained
by formalizing Theorem 1 with its difference
`N(σ,T)−N(σ,H)` and retaining `N(σ,H)≤N(H)`, rather than
silently replacing that finite count by zero using an unavailable Lean
finite-RH certificate. The cutoff margin does not change the limiting centered
support threshold `cosh(3c²/8)<7/5` in the square-root-log regime.

Chourasiya–Simonič, arXiv:2507.15184v2, Corollary 1, supplies a mathematical
uniform near-line estimate with log power at most three (plus lower-order
terms); it is not imported as a Lean theorem here. Its formalization and the
actual shrinking-cutoff provider remain open in this project. The separate
physical fully screened Pareto transfer is also not supplied by these bounds.

## Verification and sources

The coherent candidate check succeeded with only `propext`, `Classical.choice`,
and `Quot.sound` in the audited declarations. Targeted compilation of the
exact integrated modules succeeded, as did the final import/type/axiom audit.
Publication through the repository checkpoint additionally requires affected-module
and reverse-dependent validation. No new axiom,
`sorry`, or `admit` is introduced.

- Gonek, *An explicit formula of Landau and its applications to the theory of
  the zeta-function* (1985), Theorem 1:
  https://www.sas.rochester.edu/mth/people/faculty/gonek-steve/assets/pdf/8-landau-form.pdf
- Chourasiya–Simonič, *An explicit form of Ingham’s zero density estimate*,
  arXiv:2507.15184v2, Corollary 1 and Theorem 1:
  https://arxiv.org/html/2507.15184v2
- Alpöge–Furman, *More than two thirds of the zeros of the Riemann zeta function
  are simple and on the critical line*, arXiv:2608.13637v2, Appendix A:
  https://arxiv.org/html/2608.13637v2

The last two primary sources were retrieved on 2026-10-05. Literature status,
scalar computer algebra, finite Lean proofs, and remaining analytic providers
are separate claims throughout this report.

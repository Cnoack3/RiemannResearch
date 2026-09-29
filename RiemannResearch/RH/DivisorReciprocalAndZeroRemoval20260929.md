# Signed divisor aggregates and removal of Weil-transform zeros

This continuation starts at `f8cd5fac3b5d8300757cd4312b1e79260b688887`.
It combines the actual Pareto projections, Balazard's reciprocal-charge sum
rule, certified common-period divisor-Abel values, and the residual dilation
identity. A separate analytic result supplies an integral-defined operation
that removes one transform zero while preserving the smooth Weil test class.
There is no claim of mathematical novelty or of a proof of RH.

## 1. A single finite arithmetic statistic

Stage `n` spans conductors `2,...,n+1`. Write

\[
r_n=\mathbf1-P_n\mathbf1,\qquad
r=\mathbf1-P_V\mathbf1,\qquad D=\|r\|^2.
\]

The correction is \(\kappa_{n,d}=c_{n,d}+\mu(d)=L_d(r_n)\), where
\(L_d=\operatorname{mobiusDifferenceCLM}(d)\). Let
\[
v_{n,d}=\operatorname{correctionDivisorAbelValue}
 (n,d,\operatorname{correctionPeriodCutoff}(n,d)).
\]
These are the handoff's actual signed inverse-column/progression sums;
their potentially large certified cutoffs are unchanged. Define
\[
\boxed{S_n=\sum_{d=2}^{n}\frac{v_{n,d}}d.}
\]
The upper endpoint is `n`, not `n+1`, because the old-coordinate certified
error has hypothesis `d ≤ n`.

The new unconditional limit is
\[
\boxed{S_n\longrightarrow-r(1)
=-2D+\langle r,U_2r\rangle.}
\]
Here `U_2` is the existing integer-dilation operator with norm `sqrt 2`.
Consequently its limit lies in
\[
\boxed{[-(2+\sqrt2)D,\;-(2-\sqrt2)D].}
\]
The reciprocal correction limit and energy interval already existed in
`ReciprocalGramCorrection.lean`. The new result transfers them to the
certified finite divisor-progression statistic, including its growing head.

### Proof of the moving-head step

The established arithmetic vectors
\(R_N=\sum_{d=1}^N d^{-1}\operatorname{mobiusRieszHilbert}(d)\)
satisfy `norm R_N ≤ 7` and converge weakly to zero. For any strongly
convergent `f_N → f`,
\[
|\langle R_N,f_N-f\rangle|\le7\|f_N-f\|\to0.
\]
Thus \(\langle R_N,f_N\rangle\to0\). Removing the first charge gives
\[
\sum_{d=2}^N\frac{L_d(f_N)}d
=\langle R_N,f_N\rangle-f_N(1)\longrightarrow-f(1).
\]
Apply this to `f_N = r_(s(N))`, for any `s(N) → infinity`. In particular,
\(C_n=\sum_{d=2}^n\kappa_{n,d}/d\to-r(1)\).
This uses actual PNT and quotient-energy providers through
`BalazardReciprocalCharge.lean`; it does not interchange fixed-coordinate
limits with a growing inverse matrix.

### Proof of the finite progression transfer

For `2 ≤ d ≤ n`, the handoff proves
\(|v_{n,d}-\kappa_{n,d}|^2\le1/(n+1)\). Therefore
\[
\boxed{|S_n-C_n|\le\frac{H_n}{\sqrt{n+1}}\to0.}
\]
Absolute values here bound only the certified approximation errors. The
arithmetic progression values themselves retain their complete signs.
The bound is for approximation of `C_n`; it is not an effective bound for
`S_n+r(1)` because no rate of projection convergence is supplied.

The existing dilation identity
\(r(1)/2=D-\langle r,U_2r\rangle/2\), with
\(|\langle r,U_2r\rangle|\le\sqrt2D\), proves the displayed interval.

## 2. The exact RH boundary

If `D > 0`, the finite arithmetic statistic eventually satisfies
\[
S_n< -\tfrac12(2-\sqrt2)D<0.
\]
This is an unconditional implication about the actual residual. In
particular, `S_n → 0` is equivalent to `r = 0`.

One sufficient RH input is now the single one-sided statement
\[
\boxed{\forall\varepsilon>0\;\forall N\;
\exists n\ge N:\quad S_n>-\varepsilon.}
\]
Its proof would force the already-existing nonpositive limit to be zero,
then `r(1)=0`, then `r=0`, and hence RH by the established forward density
implication. **Open:** no provider of this arithmetic lower estimate was
obtained. It is a conditional research reduction, not a proof of its premise.
No unformalized RH-to-density converse is used.

## 3. An unconditional growing-coefficient estimate

Subtracting adjacent moving reciprocal sums gives, for every `s(N) → infinity`,
\[
\frac{\kappa_{s(N),N+1}}{N+1}\to0.
\]
In particular both the terminal correction and the terminal optimal
coefficient are sublinear:
\[
\frac{\kappa_{N,N+1}}{N+1}\to0,\qquad
\frac{c_{N,N+1}}{N+1}\to0.
\]
For arbitrary `s`, the symbol `correction(s(N),N+1)` is the continuous
coefficient functional; it is a present inverse-Gram coordinate whenever
`N+1 ≤ s(N)+1`. The terminal specialization is always present for `N ≥ 1`.
Sublinear control of a growing coordinate does not establish vanishing of
the fixed-coordinate corrections required for RH.

## 4. A genuine zero-removal operation for the Weil test class

Use the existing centered transform
\(F(s)=\int_{\mathbb R} f(x)e^{-(s-1/2)x}\,dx\).
If `f` is smooth with every derivative superexponentially decaying and
`F(z)=0`, define the actual function
\[
g(x)=e^{(z-1/2)x}\int_{-\infty}^{x}
 e^{-(z-1/2)t}f(t)\,dt.
\]
The zero moment supplies an equal opposite-tail expression. For a zero-mean
integrable function with \(|f(x)|\le Ce^{-a|x|}\), the primitive satisfies
\[
\left|\int_{-\infty}^{x} f(t)\,dt\right|
\le(C/a)e^{-a|x|}.
\]
Exponential twisting preserves superexponential decay. The fundamental
theorem of calculus and derivative recursion preserve the full smooth
test class. Thus the new transform `G` satisfies, for every complex `s`,
\[
\boxed{F(s)=(s-z)G(s).}
\]
Every distinct zero of `F` remains a zero of `G`, and `G(z)=F'(z)`.
Hence a simple transform zero becomes a nonzero evaluation of an admissible
test. This is an actual integral-defined construction, not an assumed
meromorphic quotient or an assertion that Weil positivity holds.

**Still open in this continuation:** the complete multiplicity-sensitive
construction of a negative Weil witness at a hypothetical off-line pair,
and any unconditional arithmetic positivity estimate excluding it.
The completed Nyman family remains Weil-null before zero removal.

## 5. Sources and verification boundary

The reciprocal-charge ingredient follows the project's already formalized
version of Michel Balazard, *An arithmetical function related to
Báez-Duarte's criterion for the Riemann hypothesis*, Propositions 6–7:
https://arxiv.org/abs/1812.04309.
The density context is Luis Báez-Duarte's natural-dilation criterion:
https://arxiv.org/abs/math/0202141.
The new assembly and elementary zero-removal argument were developed in
this continuation. Wolfram was used only for finite algebra and Gaussian
transform sanity checks, never as a proof oracle.

Principal endpoints are `divisorReciprocalStatistic_tendsto`,
`divisorReciprocalStatistic_error_le`,
`divisorReciprocalStatistic_eventually_negative`,
`riemannHypothesis_of_divisorReciprocalStatistic_cofinal_lower`,
`correction_terminal_div_tendsto_zero`,
`coefficient_terminal_div_tendsto_zero`, `removeTransformZero_properties`,
and `SmoothSuperexponentialDecay.removeTransformZero`.

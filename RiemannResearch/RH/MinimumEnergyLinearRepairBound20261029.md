# Linear-in-head complete norm bound for the existing repair operator

Paper proof, 29 October 2026. This improves the head-growth exponent of the
paper estimate in `ExactHeadRepairAndConductorGrowth20261029.md` and improves
its numerical upper bound for H >= 2. It has not been submitted to Lean.
It supplies an explicit finite operator-norm bound, not accurate input approximants.

Write Z = zeta(2), and let T = `repairOperator H p` from
`QSquarefreeQuantitativeRepair.lean`. Assume H >= 1 and H < p <= 2H. No
squarefreeness is needed for this operator-norm estimate. Squarefreeness of p
and of the input support is needed separately for squarefree legality.

The result is

\[
 \boxed{\|T\|_{\mathrm{op}}\le17H,\qquad
 \|qOne-\operatorname{repaired}(H,p,f)\|_Q
 \le18H\|qOne-f\|_Q.}
\]

The second inequality follows from the already verified `repaired_error_le`.
The first is proved for every Hilbert input, so it is an actual operator bound.

## Coefficient notation and norm

Let x be any Q-Hilbert vector, e(k) its physical sequence, with e(0)=0, and
epsilon = ||x||_Q. Then

\[
 \sum_{k\ge1}\frac{|e(k)|^2}{k^2}=Z\varepsilon^2.
\]

Set Delta e(k)=e(k)-e(k-1), and let

\[
 a_d=-\sum_{k\mid d}\mu(d/k)\Delta e(k),\qquad
 \eta=e(1)-\sum_{d=2}^{H}\frac{a_d}{d}.
\]

The literal existing operator formula is

\[
 Tx=\sum_{d=2}^{H}a_d g_d+p\eta g_p.
\]

The signs are the ones in `coefficient_eq_charge` and `repairOperator_apply`.
All bounds below use absolute values only to estimate this actual signed vector.

## The residue part

Since |mu| <= 1,

\[
 \begin{aligned}
 \sum_{d=2}^{H}\frac{|a_d|}{\sqrt d}
 &\le\sum_{k=1}^{H}\frac{|\Delta e(k)|}{\sqrt k}
       \sum_{m\le H/k}\frac1{\sqrt m}\\
 &\le2\sqrt H\sum_{k=1}^{H}\frac{|\Delta e(k)|}{k}\\
 &\le4\sqrt H\sum_{k=1}^{H}\frac{|e(k)|}{k}\\
 &\le4H\sqrt Z\,\varepsilon.
 \end{aligned}
\]

The first inequality harmlessly inserts the d=1 contribution. The second uses
sum_{m<=M} m^(-1/2) <= 2 sqrt(M), obtained by integration on (0,M]. In the third,
reindexing e(k-1) gives weight 1/(k+1) <= 1/k. The last inequality is finite
Cauchy--Schwarz; this is the step that avoids the extra factor sqrt(H) in the
older pointwise-error proof.

The complete atom estimate, with its infinite tail included, is

\[
 \|g_d\|_Q\le\sqrt{\frac2{Zd}}\qquad(d\ge2).
\]

For completeness, the atom estimate follows from g_d(d)=0, g_d(n)=n/d
for 1 <= n < d, and |g_d(n)| <= 1 afterwards:
\[
 Z\|g_d\|_Q^2
 \le\frac{d-1}{d^2}+\sum_{n>d}\frac1{n^2}
 \le\frac{d-1}{d^2}+\frac1d<\frac2d.
\]
The tail bound uses the integral of x^(-2) from d to infinity.

Consequently the residue part has norm at most 4 sqrt(2) H epsilon.

## The slope correction

Write h_M = sum_{m=1}^M 1/m and w_k = h_floor(H/k)/k for 1 <= k <= H.
The sequence w_k is nonnegative and nonincreasing. Therefore

\[
 \begin{aligned}
 \sum_{d=2}^{H}\frac{|a_d|}{d}
 &\le\sum_{k=1}^{H}|\Delta e(k)|w_k\\
 &\le2\sum_{k=1}^{H}|e(k)|w_k\\
 &\le2\sqrt Z\,\varepsilon
        \left(\sum_{k=1}^{H}h_{\lfloor H/k\rfloor}^{\,2}\right)^{1/2}.
 \end{aligned}
\]

Here is a complete elementary bound for the last sum. For M >= 1,
h_M <= 1+log M. The function phi(x)=(1+log(H/x))^2 is decreasing on (0,H].
Hence

\[
 \sum_{k=1}^{H}h_{\lfloor H/k\rfloor}^{\,2}
 \le\sum_{k=1}^{H}(1+\log(H/k))^2
 \le\int_0^H(1+\log(H/x))^2\,dx=5H.
\]

The improper integral is finite, and the substitution x=H exp(-t) evaluates it
as H int_0^infty (1+t)^2 exp(-t) dt = 5H. Thus

\[
 |\eta|\le\sqrt Z(1+2\sqrt{5H})\varepsilon,
\]

where |e(1)| <= sqrt(Z) epsilon is the coordinate-one bound. Applying the full
atom bound again gives

\[
 \|p\eta g_p\|_Q
 \le\sqrt{2p}(1+2\sqrt{5H})\varepsilon.
\]

## Assemble the operator estimate

For arbitrary p > H, the preceding proof gives

\[
 \|T\|_{\mathrm{op}}
 \le4\sqrt2\,H+\sqrt{2p}(1+2\sqrt{5H}).
\]

If p <= 2H and H >= 1, this is at most

\[
 (2+4\sqrt2+4\sqrt5)H <17H.
\]

The deliberately rational constant 17 follows from sqrt(2)<3/2 and
sqrt(5)<9/4. Thus 1+||T|| <= 18H. No prime-gap theorem is part of this norm
estimate. Bertrand's postulate can supply a prime H<p<2H when H>=2; p=2
handles H=1. A composite squarefree anchor in this interval works equally well.

## Consequence for the exact-head energy target

Suppose f is a finite squarefree legal vector, p is squarefree, and

\[
 \|qOne-f\|_Q\le\frac1{72H^2}.
\]

The existing repair is finite legal and exact through H. The new bound gives
||qOne-repaired|| <= 1/(4H), and therefore

\[
 \|\operatorname{repaired}\|_Q^2
 \le(1+1/(4H))^2
 \le1+\frac9{16H}
 \le1+\frac5{8H}.
\]

This replaces the older paper input tolerance 1/(60 H^(5/2)) by
1/(72 H^2), a weaker accuracy requirement for H >= 2. At H=1 the new
constants are stricter; 17H is also larger than 15 H^(3/2) there.
It does not show that such accurate raw legal inputs exist for
unbounded H. That existence remains the RH-related approximation problem.
The proof gives an unconditional finite repair bound, not a cofinal energy
provider and not a proof of RH.

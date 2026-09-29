# The limiting inverse-Gram correction encodes off-line zeros

Status: rigorous paper consequence, not a newly checked Lean theorem and not a
claim of mathematical novelty. It combines the project's exact coefficient
functional with Abel summation and the bounded discrete Mellin functional.

Let \(H=\ell^2(1/[n(n+1)])\), with physical coordinate zero anchored at zero.
Let \(V\) be the closed span of \(g_d(n)=(n\bmod d)/d\), \(d\ge2\).
Write \(F=P_V1\), \(r=1-F\), and \(D=\|r\|_H^2\).
For every positive integer d put

\[
\ell_d=\sum_{k\mid d}\mu(d/k)[r(k)-r(k-1)].
\]

For d≥2 this is exactly the already identified limit of the finite
inverse-Gram correction \(c_{N,d}+\mu(d)\). At d=1 it equals r(1).

## Exact Abel--Mellin identity

Define

\[
A_f(s)=\sum_{k\ge1}f(k)[k^{-s}-(k+1)^{-s}]
      =s\int_1^\infty f(\lfloor x\rfloor)x^{-s-1}\,dx.
\]

For \(\sigma=\Re s>1/2\) this is a continuous functional on H and

\[
|A_f(s)|\le\frac{|s|}{\sqrt{2\sigma-1}}\|f\|_H.
\]

Indeed the H norm is exactly the L² norm of \(f(\lfloor x\rfloor)\)
against \(x^{-2}dx\). Cauchy--Schwarz leaves the integral
\(\int_1^\infty x^{-2\sigma}dx=(2\sigma-1)^{-1}\).
This also gives local uniform convergence and analyticity of A_f on that
half-plane, by differentiating on compact subsets or uniform convergence of
finite physical truncations.

For \(\Re s>3/2\), absolute convergence and divisor reindexing give

\[
\boxed{
\sum_{d\ge1}\frac{\ell_d}{d^s}
=\frac1{\zeta(s)}\sum_{k\ge1}\frac{r(k)-r(k-1)}{k^s}
=\frac{A_r(s)}{\zeta(s)}.
}
\]

The second equality is exact summation by parts. Its terminal term tends to
zero: \(|r(k)|\le\|r\|_H\sqrt{k(k+1)}\) and \(\sigma>3/2\).
Thus the signed correction Dirichlet series has a meromorphic continuation
to \(\Re s>1/2\), given by \(A_r(s)/\zeta(s)\).

If the series is taken only over legal conductors d≥2, subtract r(1) from the
right side. This constant does not change any poles.

## No zero cancellation in this quotient

The exact legal-atom identity is

\[
A_{g_d}(s)=\zeta(s)(d^{-1}-d^{-s}).
\]

Initially this follows for \(\Re s>1\) from
\(g_d(k)-g_d(k-1)=d^{-1}-1_{d\mid k}\); it continues analytically to
\(\Re s>1/2\). The apparent pole at s=1 cancels.

Every finite legal synthesis therefore has Mellin numerator divisible by
ζ. Strong H convergence \(F_N\to F\) makes \(A_{F_N}\to A_F\) locally
uniform in the half-plane. Consequently, at every zero ρ of ζ in
\(\Re\rho>1/2\), of any multiplicity m, A_F vanishes to at least order m.
This follows also by continuity of the first m−1 derivative evaluation
functionals. Since A_1(s)=1, we have

\[
A_r(s)=1-A_F(s),\qquad A_r(\rho)=1.
\]

It follows that

\[
\boxed{
\frac{A_r(s)}{\zeta(s)}-\frac1{\zeta(s)}
=-\frac{A_F(s)}{\zeta(s)}
\quad\text{is holomorphic at every such }\rho.
}
\]

Every off-line zero in the right half-plane is therefore a genuine pole of
the continued correction Dirichlet series, with exactly the same principal
part as \(1/\zeta(s)\), including multiplicities. At a simple zero the residue
is precisely \(1/\zeta'(\rho)\).

This supplies an exact spectral overlap of the signed-tail and inverse-Gram
routes with the zero side of Weil's formula. It does not prove that the poles
are absent: holomorphy of this continued correction series throughout the
half-plane is itself an RH-strength assertion. At the level of zeros, the
bound above gives the usual necessary obstruction

\[
D\ge\frac{2\Re\rho-1}{|\rho|^2}.
\]

The non-cancellation conclusion is stronger information than merely saying
that a quotient might have poles at ζ zeros: it identifies their exact
principal parts from the limiting inverse-Gram correction sequence.

## Locally uniform convergence of exact inverse-Gram polynomials

For the actual finite orthogonal projection
\(F_N=\sum_{d=2}^N c_{N,d}g_d\), define the entire function

\[
P_N(s)=\sum_{d=2}^N c_{N,d}(d^{-s}-d^{-1}).
\]

Every coefficient is the actual full-Pareto inverse-Gram coefficient.
There is the exact identity

\[
A_{F_N}(s)=-\zeta(s)P_N(s).
\]

Unconditionally, \(P_N\) converges locally uniformly throughout
\(\Re s>1/2\) to a holomorphic function P. To see this away from ζ zeros,
divide the locally uniform convergence of A_{F_N} by ζ. Around an individual
zero, choose a small closed disk in the half-plane whose boundary contains
no zeros. On that boundary the entire differences P_N−P_M tend uniformly to
zero; the maximum-modulus principle gives the same bound throughout the
disk. The local uniform limit is therefore holomorphic also at the zero.
At s=1 use the analytic reciprocal of ζ, which vanishes there. These local
arguments cover each compact subset.

In fact the proof gives a dimension-independent stability bound. For every
compact \(K\subset\{\Re s>1/2\}\), there is a finite constant C_K such that

\[
\boxed{\sup_{s\in K}|P_N(s)-P_M(s)|
   \le C_K\|F_N-F_M\|_H.}
\]

Away from zeros one can use the supremum of
\(|s|/(|\zeta(s)|\sqrt{2\Re s-1})\). In each zero disk use its zero-free
boundary supremum and the maximum-modulus principle. A finite covering of K
gives C_K. This uniformly controls signed Dirichlet contractions of the actual
inverse-Gram coefficients, including at multiple off-line zeros, without
controlling a growing matrix operator norm.

Consequently, the actual correction continuation takes the particularly
transparent exact form

\[
\boxed{\mathcal C_\infty(s)=\frac1{\zeta(s)}+P(s).}
\]

For Re(s)>3/2 it equals the ordinary absolutely convergent series
\(\sum_{d\ge1}\ell_dd^{-s}\). Its finite-stage counterpart is
\(\mathcal C_N(s)=1/\zeta(s)+P_N(s)\): the d=1 term is
\(1-F_N(1)\), the terms 2≤d≤N are \(c_{N,d}+\mu(d)\), and the full
remaining tail is \(\mu(d)\) for d>N. The tail has not been dropped.
Every finite stage and the limit have exactly the reciprocal-zeta principal
parts. For the legal-conductor series subtract the respective d=1 term.

This also supplies a local-uniform proof of all multiplicity statements
without differentiating an infinite Hilbert expansion term by term.

## Explicit higher-jet bound and repository target

The derivative continuity used above has an explicit estimate. Write
\(M_f(s)=A_f(s)/s\). For every nonnegative integer j and σ>1/2,

\[
M_f^{(j)}(s)=(-1)^j\int_1^\infty
   f(\lfloor x\rfloor)x^{-s-1}(\log x)^j\,dx,
\]
\[
\boxed{
|M_f^{(j)}(s)|\le
 \sqrt{\frac{(2j)!}{(2\sigma-1)^{2j+1}}}\,\|f\|_H.
}
\]

The squared L² norm of the derivative kernel is exactly
\(\int_1^\infty x^{-2\sigma}(\log x)^{2j}dx
=(2j)!/(2\sigma-1)^{2j+1}\), by x=exp(t). Local domination justifies
all derivatives. These are continuous linear functionals of f, so they
annihilate the Hilbert closure whenever they annihilate every legal atom.
At a zero ρ of multiplicity m with Reρ>1/2, for every j<m,

\[
\forall f\in V,\quad M_f^{(j)}(\rho)=0,
\qquad
M_r^{(j)}(\rho)=\frac{(-1)^j j!}{\rho^{j+1}}.
\]

This proves on paper exactly the currently open
`ClosedSpaceMellinMultiplicityTarget` in
`RiemannResearch/RH/ResidualMellinZeroConditions.lean`.
That file already verifies the j=0 value. The derivative closure and
principal-part statement here remain to be formalized. In contrast,
`DampedDivisorLSeries.lean` treats a different damped divisor sequence and
only its common half-plane of absolute convergence; it does not establish
this limiting-correction continuation.

The analytic ingredients are already stronger than that open target's
original commentary suggests: `ParetoMellinFiniteEnergy.lean` proves
`paretoMellin_analyticOnNhd` for every H vector, and
`paretoMellin_tendstoUniformlyOn_of_tendsto` proves uniform Mellin convergence
on each stricter half-plane Re(s)>σ>1/2. Thus the new formal step needed for
the target is preservation of the finite zero jets under this locally uniform
holomorphic limit, followed by identification of the actual correction series.
The bound and paper argument above supply that preservation directly.

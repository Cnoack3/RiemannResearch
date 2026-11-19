# Mellin comparison and the actual-zero quadratic-phase attempt

Research date: 18 November 2026.

## Status and scope

This is an attempt at the actual-zero side of the proposed Mellin-DPP
comparison. It proves analytic bounds and identifies an explicit residual
asymptotic still needed. It does not prove Montgomery pair correlation or
the Riemann Hypothesis.

The only new Lean formalizations in this change are the gamma-drift
declarations listed in THEOREM_CATALOG_MESOSCOPIC_GAMMA_20261118.md.
The analytic arguments here use established published inputs and are
written proofs, not claims of Lean verification.

All zero sums below count occurrences with multiplicity. Off-line zeros
with the same ordinate are separate occurrences. No RH is assumed unless
explicitly stated.

## 1. Normalization and the modular observation

Put a_T=log(T)/(2*pi), and let gamma_j range over T < gamma_j <= 2T.
Let N_T=N(2T)-N(T), and define
\[
 Z_T(\xi)=\sum_j e^{i\xi\gamma_j},\qquad
 \nu_T(d\alpha)=\frac{|Z_T(\alpha\log T)|^2}{N_T}\,d\alpha.
\]
For every real xi,
\[
 |Z_T(\xi)|^2-N_T
   =\sum_{j\ne k}\cos(\xi(\gamma_j-\gamma_k)).
\]
Thus these tests require only phases modulo 2*pi. An integer lift is not
a missing input.

For an even Schwartz test f, Fourier inversion gives
\[
 \frac1{N_T}\sum_{j\ne k}f(a_T(\gamma_j-\gamma_k))
 =\int_{\mathbb R}\widehat f(\alpha)
     \left(\frac{|Z_T(\alpha\log T)|^2}{N_T}-1\right)d\alpha.
\]
The desired all-pair spectral limit is
\[
 \nu_T\ \longrightarrow\ \delta_0+\min(|\alpha|,1)\,d\alpha
\]
against these tests. This is a distributional assertion, not pointwise
convergence of a raw periodogram.

The Mellin projection kernel is a separate determinantal model. Its
established analytic sine-kernel limit supplies the comparison law; it
does not identify the law of the actual zero ordinates.

## 2. An actual quadratic estimate at the correct normalization

Fujii's fixed-width count moment bounds imply the following, uniformly in
large T, all A>0, and all real b:
\[
 \boxed{\ \int_{b-A}^{b+A}\nu_T(d\alpha)\ll 1+A.\ }
\]

Here is the reduction. Write x_j=a_T(gamma_j-T), and
\[
 G_T(r)=\#\{(j,k):|x_j-x_k|\le r\}.
\]
The exact triangle identity is
\[
 \int_{\mathbb R}\#\{j:x_j\in(v,v+2]\}^2\,dv
 =\sum_{j,k}(2-|x_j-x_k|)_+.
\]
The integral is O(N_T), by the unconditional actual-count second moment
on a slightly enlarged dyadic height interval. It bounds G_T(1).
If n_k counts x_j in the kth unit cell, then sum n_k^2 <= G_T(1).
Cauchy–Schwarz on each integer cell shift therefore gives
\[
 G_T(r)\ll N_T(1+r).
\]
The Gaussian Fourier identity now gives exactly
\[
 \int_{\mathbb R}e^{-\pi(\alpha-b)^2/A^2}\nu_T(d\alpha)
 =\frac A{N_T}\sum_{j,k}
   e^{-\pi A^2(x_j-x_k)^2}e^{2\pi ib(x_j-x_k)}.
\]
Taking absolute values on the right and integrating the Gaussian against
dG_T(r) bounds this by C(1+A). On the requested interval the Gaussian is
at least exp(-pi), proving the assertion.

Consequently the measures are uniformly bounded on translated unit
frequency intervals. For every Schwartz g,
\[
 \sup_{T\ge T_0}\int_{|\alpha|>M}|g(\alpha)|\,\nu_T(d\alpha)
 \longrightarrow0.
\]
The missing issue is the value of the limiting measure on compact bands;
uncontrolled frequency tails are not an obstruction for Schwartz tests.

Published input: Fujii's microscopic count moments, also stated as
Lemma 2.2 in [Lam-Nov]. Lemma 2.3 there proves a stronger family of local
pair-row moment bounds.

## 3. The coherent atom can be identified

Let nu_{T_j} converge vaguely to a positive locally finite measure mu.
Such subsequences exist by the preceding bound. Then
\[
 \boxed{\mu(\{0\})=1.}
\]

For the lower bound, Riemann–von Mangoldt implies
\[
 \frac{Z_T(z/T)}{N_T}\longrightarrow F(z)=\int_1^2e^{izv}\,dv
\]
uniformly on compact z-intervals. Changing variables
alpha=z/(T log T) gives
\[
 \nu_T([-M/(T\log T),M/(T\log T)])
 \longrightarrow \frac1{2\pi}\int_{-M}^M|F(z)|^2\,dz.
\]
Testing compact continuous cutoffs equal to one near zero, then shrinking
their supports, proves that mu({0}) is at least this last quantity.
Plancherel and M -> infinity give the lower bound one.

For the upper bound define
\[
 H_R(\alpha)=\left(\frac{\sin(\pi R\alpha)}{\pi\alpha}\right)^2.
\]
Fourier inversion gives the exact identity
\[
 \int H_R\,d\nu_T
 =\frac1{N_T}\sum_{j,k}(R-|a_T(\gamma_j-\gamma_k)|)_+.
\]
For fixed R>0 this equals
\[
 \frac{a_T T}{N_T}\,\mathbb E[C_{T,R}^2]+o_T(1),
 \quad C_{T,R}=N(U+R/a_T)-N(U),\quad U\sim{\rm Unif}[T,2T].
\]
The endpoint strips contribute O(R log^2 T/N_T)=o(1).
The mean is R+o(1). Fujii's second moment [GLSS, Proposition 2] implies
\[
 \limsup_T\int H_R\,d\nu_T\le R^2+C\log(2+R).
\]
The unit-band bound and H_R(alpha)<=1/(pi^2 alpha^2) allow passage to mu.
Since H_R(0)=R^2 and H_R>=0,
\[
 \mu(\{0\})\le1+C\log(2+R)/R^2.
\]
Let R tend to infinity.

In particular sigma=mu-delta_0 is positive and
\[
 \int H_R\,d\sigma\ll\log(2+R).
\]
Taking R=1/(2 epsilon) yields the additional bound
\[
 \boxed{\sigma([-\epsilon,\epsilon])
       \ll\epsilon^2\log(2+1/\epsilon).}
\]
For the sine prediction this mass is exactly epsilon^2 when epsilon<1.
The logarithmic loss and the values on other compact bands remain.

## 4. Exact prime-polynomial decomposition of the variance

Use the classical argument function
\[
 \mathsf S(t)=\pi^{-1}\arg\zeta(1/2+it)
\]
with its standard continuous-path convention. Set h=R/a_T and
\[
 P_{T,R}(t)=-\frac2\pi\sum_{2\le n\le T}
  \frac{\Lambda(n)}{\sqrt n\log n}
  \sin(h\log n/2)\cos((t+h/2)\log n),
\]
\[
 E_{T,R}(t)=\mathsf S(t+h)-\mathsf S(t)-P_{T,R}(t).
\]
Every cosine here is a modular prime-power phase. These are exact
definitions; no small-remainder assertion is built into E.

Let <F>_T=T^{-1}integral_T^{2T} F(t) dt. Then exactly
\[
 \langle(\Delta_h\mathsf S)^2\rangle_T
  =\langle P^2\rangle_T+
     2\langle PE\rangle_T+\langle E^2\rangle_T.                 (1)
\]
If G is the exact smooth term in N=G+S and
d(t)=G(t+h)-G(t)-R, the full centered count square is exactly
\[
 \langle(C-R)^2\rangle_T
 =\langle P^2\rangle_T+2\langle PE\rangle_T+\langle E^2\rangle_T
   +2\langle(P+E)d\rangle_T+\langle d^2\rangle_T.              (2)
\]
For fixed R the last two terms tend to zero by the smooth-count estimate
and bounded actual second moments. The mean tends to R, so centering by
the actual mean makes no difference in the fixed-width limit.

### Evaluation through the endpoint cutoff n<=T

Put c_n=Lambda(n)/(sqrt(n)log(n))*sin(h log(n)/2) and
D(t)=sum_{n<=T}c_n n^{-it}. Montgomery–Vaughan [Lubinsky, (1.4)] gives
\[
 \langle |D(t+h/2)|^2\rangle_T
  =\sum c_n^2+O(T^{-1}\sum n c_n^2).
\]
The error tends to zero even at cutoff T:
\[
 \sum_{n\le T}n c_n^2
 \le\sum_{p^k\le T}1/k^2\ll T/\log T.
\]
The additional real-part-square term is also negligible:
\[
 |\langle D(t+h/2)^2\rangle_T|
 \le\frac2{T\log4}\left(\sum|c_n|\right)^2
 \ll(\log T)^{-2}.
\]
Here sum_{p<=T}p^{-1/2} << sqrt(T)/log T, and the higher prime-power
sum is O(log log T). Thus
\[
 \langle P^2\rangle_T=\frac2{\pi^2}\sum c_n^2+o(1).
\]
For fixed R the higher powers contribute O(h^2), because
sum_{p,k>=2}(log p)^2/p^k is finite. Partial summation with the prime
number theorem evaluates the remaining diagonal:
\[
 \boxed{\langle P^2\rangle_T\longrightarrow
 A_R=\frac1{\pi^2}\int_0^1
       \frac{1-\cos(2\pi R\alpha)}{\alpha}\,d\alpha.}          (3)
\]

This evaluates P itself. It does not say E tends to zero.

## 5. A genuine bound for the residual, and the missing limit

Selberg's unconditional approximation, stated as Theorem 8, equation
(10.5), in [Goldston], is
\[
 \int_0^Y\left|\mathsf S(t)+\frac1\pi
    \sum_{p\le Y^{1/k}}\frac{\sin(t\log p)}{\sqrt p}
            \right|^{2k}dt\ll_k Y.
\]
Take k=1 and Y=3T. Changing the prime cutoff from 3T to T has normalized
mean-square cost O(1/log T), by Montgomery–Vaughan. Adding prime powers
has bounded cost. Therefore, for
\[
 H_T(t)=-\frac1\pi\sum_{2\le n\le T}
       \frac{\Lambda(n)\sin(t\log n)}{\sqrt n\log n},
 \qquad B_T(t)=\mathsf S(t)-H_T(t),
\]
one has T^{-1}integral_T^{2T+1}|B_T(t)|^2 dt << 1.
Since E(t)=B_T(t+h)-B_T(t),
\[
 \boxed{\langle E^2\rangle_T\ll1\quad(0<h\le1).}
\]
Define the signed correction
\[
 \Gamma_T(R)=2\langle PE\rangle_T+\langle E^2\rangle_T.
\]
Cauchy–Schwarz supplies the genuine estimate
\[
 |\Gamma_T(R)|\ll1+\sqrt{\langle P^2\rangle_T}
             \ll1+\sqrt{\log(2+R)}.
\]
It bounds the correction without identifying its limit.

For the unit-intensity sine process,
\[
 V_{\sin}(R)=R-2\int_0^R(R-r)
                   \left(\frac{\sin\pi r}{\pi r}\right)^2dr
 =\int_{\mathbb R}H_R(\alpha)\min(|\alpha|,1)d\alpha.
\]
Splitting the Fourier integral at one gives exactly
\[
 V_{\sin}(R)=A_R+B_R,\qquad
 B_R=\frac1{\pi^2}\int_1^\infty
                \frac{1-\cos(2\pi R\alpha)}{\alpha^2}d\alpha.
\]
Equations (1)--(3) show that the fixed-width comparison is equivalent to
\[
 \boxed{\Gamma_T(R)\longrightarrow B_R\quad\text{for each fixed }R>0.}
                                                                    (4)
\]
The covariance must remain signed. Replacing (4) by a claim only about
<E^2> requires a separate proof that <PE> tends to zero.

At R=1,
A_1=0.2469859270943188,
B_1=0.0971766664197194,
V_sin(1)=0.3441625935140382.
These values follow from
\[
 A_R=\frac{\gamma_E+\log(2\pi R)-{\rm Ci}(2\pi R)}{\pi^2},
\quad
 B_R=\frac{1-\cos z+z(\pi/2-{\rm Si}(z))}{\pi^2},
\quad z=2\pi R.
\]
The required residual is substantial even for a window of one mean
spacing. An O(1) remainder does not establish (4).

## 6. What can already be transferred in growing windows

Fujii's unconditional estimate, stated unambiguously in [GLSS,
Proposition 2, (5.6)], gives
\[
 \int_0^T(\mathsf S(t+u)-\mathsf S(t))^2dt
 =\frac T{\pi^2}\log(2+u a_T)
       +O(T\sqrt{\log(2+u a_T)}),\qquad0<u\le1.
\]
Subtract at heights 2T and T with the same u=R/a_T. The change in the
logarithmic main term is O(1/log T). On [T,2T] the smooth-count drift is
O(R/log T). Applying Cauchy–Schwarz to the exact drift terms proves,
uniformly for 1<=R<=a_T,
\[
 \langle(C_{T,R}-R)^2\rangle_T
 =\pi^{-2}\log(2+R)+O(\sqrt{\log(2+R)}).
\]
The actual variance differs by the squared mean error, which is bounded
in this range. Therefore
\[
 \frac{\operatorname{Var} C_{T,R_T}}{V_{\sin}(R_T)}
 \longrightarrow1
 \quad\text{if }R_T\to\infty,\ R_T\le a_T.
\]
Maples–Rodgers, Theorem 1.2, proves a larger unconditional class of
mesoscopic BV-statistic variance limits and CLTs when the variance
diverges. It does not give this fixed-width absolute comparison.

For factorial moments retain the exact mean correction:
\[
 \mathbb E[C(C-1)]-(R^2-R)
 =\mathbb E[(C-R)^2]+(2R-1)(\mathbb EC-R).
\]
The extra term is O(R^2/log T), so R_T=log log T is a safe explicit
choice for matching the logarithmic variance correction. Agreement
relative to R_T^2 alone would discard this information.

The Mellin model's moving-center estimate also extends uniformly to
such slow growing windows: after a gauge, the unfolded kernel differs
from the sine kernel by O(1/log T) on 0<=x,y<=R_T, provided the physical
offset 2*pi*R_T/log T stays bounded. This follows from the same integral
from center U to L, with L=floor(T^2), uniformly T<=U<=2T. The effective
band length log(L/U)/log T differs from one by O(1/log T).
The resulting count variance and factorial moment errors are
O((R_T+R_T^2)/log T)=o(1) at R_T=log log T.
Thus the actual side, not the model error, limits the comparison.

## 7. What the modular and complex-zero publications do and do not supply

FMZ [Theorem 1 and Corollary 1.1] evaluates smooth tests of a fixed
prime-log frequency vector, including a secondary arithmetic bias.
Its quantifiers do not permit silently replacing that vector by
frequencies of order log T and squaring a sum at N_T normalization.

BGSTB [Theorem 1] gives an unconditional Montgomery formula on Fourier
support at most one for complex-zero differences, with the weight
4/(4-(rho-rho')^2). It is not the actual-ordinate phase energy when RH
is not assumed. Lamzouri's September 2026 paper, Lemma 3.2, includes an
exact device to remove this weight for smooth tests: replace g by
g-g''/[4(log T)^2]. That leaves the complex-to-ordinate issue intact.

Ford–Zaharescu [Lemma 2] records the uniform Selberg density estimate
\[
 N(1/2+u,T)\ll T\log T\,e^{-cu\log T}
\]
for an absolute c>0. Reflection and tail integration give
\[
 \sum_{0<\gamma\le T}(\beta-1/2)^2
 \ll T\log T\int_0^\infty u e^{-cu\log T}du
 \ll T/\log T.
\]
This improves a bound with a needless (log log T)^2 factor. However,
at xi=alpha log T the scaled average displacement square is only O(1),
not o(1). Symmetric displacements beta-1/2=+/-c/log T are compatible
with such a bound and multiply paired complex phases by cosh(c alpha).
Frequency integration does not remove that multiplier.

Lamzouri's 10 November 2026 preprint [Proposition 3.2] provides a new
useful input: deleting a reflection-invariant fraction delta of zeros
changes the relevant normalized complex correlation by at most
\[
 O_g\left(\delta^{\kappa_\theta}+(\log T)^{-1/2}\right),\quad
 \kappa_\theta=1/8-7\theta/32>0,\quad 1/2<\theta<4/7,
\]
for nonnegative even smooth Fourier tests supported in [-theta,theta].
Its Lemma 2.3 controls all fixed moments of local actual-ordinate pair
rows. These are substantive quantitative uniformity statements.

Taking the exceptional set to be all off-line zeros yields a
restricted-support actual-ordinate transfer if their fraction tends to
zero. That density-one hypothesis is not proved by the paper.
A thin-box argument yields a weaker sufficient horizontal condition.
Here use the cumulative zero list 0<gamma<=T and define
\[
 \epsilon_T=\frac{(\log T)^2}{N(T)}
                \sum_{0<\gamma\le T}(\beta-1/2)^2,
 \qquad
 {\cal P}_T(g)=\frac1{N(T)}
       \sum_{0<\gamma,\gamma'\le T}
           \widehat g(a_T(\gamma-\gamma')).
\]
For a fixed nonnegative even smooth test \(g\) supported inside
\([-\theta,\theta]\), the centered comparison now gives, for every fixed
\(0<\kappa<1-7\theta/4\),
\[
 \left|{\cal P}_T(g)-g(0)-\int |\alpha|g(\alpha)\,d\alpha\right|
 \ll_{g,\theta,\kappa}
    \min(1,\epsilon_T)^\kappa+(\log T)^{-1/2}.               \tag{5}
\]
Here \(0<\theta<4/7\). The normalizer and the range of positive-height
zero occurrences are those displayed above. To see the gain over optimizing
a hard deletion threshold, weight each row by
\(m_i=\min(1,(\log T)^2(\beta_i-1/2)^2)\). Reflection cancels the linear
term of the tested kernel when both marks are small. On the remaining
pairs their combined truncated marks are at least one. Hölder with the
local row moments and integration of the Selberg tail give the stated
power. Removing the Lorentz weight costs \(O_g(1/\log T)\). The constants
can depend on the distance of \(\kappa\) from its strict endpoint.

With \(\epsilon_T\ll(\log T)^{-p}\), the same comparison also tends to
zero throughout \(4/7\le\theta<2/3\) when \(p>6\theta/(2-3\theta)\).
For the endpoint \(\theta=4/7\), this condition is \(p>12\).
The proof and the piecewise remainder powers are in
[Sparse density bounds for the Montgomery pair statistic](SparsePairDensityBounds20261119.md).

Thus the sufficient strengthening is precisely
\[
 \sum_{0<\gamma\le T}(\beta-1/2)^2=o(T/\log T).
\]
The present density estimate yields O, not little-o. This is a
**conditional research reduction**: the little-o hypothesis is **Open**
in this attempt. Even if discharged, the Fourier support restriction
would remain. The paper's unconditional positive-proportion small-gap
theorem is an inequality; it does not give the missing variance
equality (4).

## 8. Uniform integrability and next analytic obligation

For every fixed R, Fujii's higher moments give a uniform fourth-moment
bound for C_{T,R}. Hence
\[
 \mathbb E[C_{T,R}^2\,1_{C_{T,R}>M}]
 \le M^{-2}\mathbb E[C_{T,R}^4]\ll_R M^{-2}.
\]
Thus convergence of the actual count law to the sine count law would
transfer second moments. Rare large counts are controlled already.

The next substantive task is (4), or identification of the non-atomic
measure in Section 3. The present attempt evaluates the prime term,
controls the exact residual, establishes the central atom, and obtains
leading mesoscopic agreement. It does not identify the residual
covariance at fixed R.

## References

- [Goldston] D. A. Goldston, Notes on Pair Correlation of Zeros and Prime
  Numbers, Theorem 8 and (10.5).
  https://arxiv.org/pdf/math/0412313
- [Lubinsky] D. S. Lubinsky, Uniform Mean Value Estimates and Discrete
  Hilbert Inequalities via Orthogonal Dirichlet Series, (1.4) for the
  Montgomery–Vaughan mean-value theorem.
  https://lubinsky.math.gatech.edu/Research%20papers/DirichletMeanValueJan2014Rohrs.pdf
- [GLSS] D. A. Goldston, J. Lee, J. Schettler, A. I. Suriajaya,
  Pair Correlation Conjecture for the Zeros of the Riemann Zeta-function I:
  Simple and Critical Zeros, Propositions 1 and 2.
  https://arxiv.org/pdf/2503.15449
  https://doi.org/10.1112/mtk.70127
- [Maples–Rodgers] K. Maples, B. Rodgers, Bootstrapped zero density
  estimates and a central limit theorem for the zeros of the zeta
  function, Theorem 1.2, Proposition 2.5.
  https://arxiv.org/pdf/1404.3080
- [FMZ] K. Ford, X. Meng, A. Zaharescu, Simultaneous Distribution of
  the Fractional Parts of Riemann Zeta Zeros, Theorem 1.
  https://arxiv.org/pdf/1511.06814
- [FZ] K. Ford, A. Zaharescu, On the distribution of imaginary parts
  of zeros of the Riemann zeta function, Lemma 2 and (3.8).
  https://arxiv.org/pdf/math/0405459
- [BGSTB] S. A. C. Baluyot, D. A. Goldston, A. I. Suriajaya,
  C. L. Turnage-Butterbaugh, An unconditional Montgomery theorem for
  pair correlation of zeros of the Riemann zeta-function, Theorem 1.
  https://arxiv.org/pdf/2306.04799
- [Lam-Sep] Y. Lamzouri, A new proof that more than 2/3 of the zeros of
  the Riemann zeta function are simple and on the critical line,
  Lemma 3.2. September 2026 preprint.
  https://arxiv.org/pdf/2609.02882
- [Lam-Nov] Y. Lamzouri, The distribution of small gaps between zeros
  of the Riemann zeta function, Lemmas 2.2–2.3 and Proposition 3.2.
  10 November 2026 preprint.
  https://arxiv.org/pdf/2611.14486
- [Rodgers] B. Rodgers, Tail bounds for counts of zeros and eigenvalues,
  and an application to ratios. The stronger tail theorem assumes RH;
  the paper separately records weaker unconditional tail control.
  https://arxiv.org/pdf/1502.05658

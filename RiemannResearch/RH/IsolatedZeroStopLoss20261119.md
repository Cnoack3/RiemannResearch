# Two-neighbor isolation from Conrey's stop-loss bound

For every fixed $0<c\le 10^{-5}$, the resulting asymptotic lower proportion is **0.6724913656**. Kim's November 2026 preprint gives 0.672468 in the same range. The new figure combines Kim's isolation transfer with Conrey's longer mollifier and a newly verified threshold and slope. [Kim, Theorem 1.1 and Proposition 4.2](https://hexagonmath.org/pdf/2611.00318v1) · [Conrey, J. reine angew. Math. 399 (1989), §5](https://maths.dur.ac.uk/users/herbert.gangl/morethan2_5.PDF)

## Counting convention

List the positive ordinates in increasing order, counting analytic multiplicities. A member with $\gamma_n\le T$ and $n\ge2$ qualifies when **both** neighboring gaps in the full infinite list strictly exceed $2\pi c/\log T$. Its successor is tested even if it lies above $T$. An off-line zero shares its ordinate with its reflection and cannot qualify. A higher-multiplicity zero cannot qualify either. A lower bound for the number of simple critical-line zeros by itself leaves these two gaps uncontrolled. [Kim, equations (1.1)–(1.2)](https://hexagonmath.org/pdf/2611.00318v1)

For $T>1$, give each zero copy below or at $T$ mass $1/N(T)$, put $X=|\beta-1/2|\log T$, and set $S_T(u)=\mathbb E[(X-u)_+]$. Let $D_T(a)$ be the corresponding mean of $((\beta-1/2)\log T/(2\pi)-a)_+$ restricted to $\beta>1/2$, with the same denominator $N(T)$. Analytic-multiplicity-preserving reflection gives the finite identity $S_T(2\pi a)=4\pi D_T(a)$ for $a\ge0$. A factor of two accounts for the left half-plane. The remaining $2\pi$ comes from changing the displacement units.

The fixed-threshold Conrey consequence yields $\limsup S_T(u)\le F(u)$, where $F(u)=\log[(1-e^{-22u/7})/(1-e^{-8u/7})]$ for $u>0$. The height limit is taken with each mollifier length exponent strictly below $4/7$. Here $u=2\pi a$ is fixed. [Derivation of the global-height estimate](OptimizedHorizontalMoments20261119.md)

## Majorant and coefficient

Set $H(y)=1-4M(y)^2/(1+M(2y))$, with

$$
M(y)=\frac{\cosh(\pi y)+\sqrt{2}\,\pi y\cot(1/\sqrt{2})\sinh(\pi y)}
              {1+2\pi^2y^2}.
$$

For $a=303/250$ and $\ell=7061/10000$, the finite interval calculation proves $H(y)<\ell(y-a)_+$ on $0\le y\le3$. For an interval $[b,e]$ it takes the upper bound $1-4M(b)^2/(1+M(2e))$ and the lower bound $\ell(b-a)_+$. Monotonicity of $M$ follows from its representation as the integral of the positive Montgomery–Taylor density times $\cosh(2\pi uy)$. Exact rational subdivision plus outward-rounded mpmath interval arithmetic separates these bounds on 28,449 intervals, to maximum bisection depth 23. On $y\ge3$, $H\le1<\ell(3-a)$. The finite strict margins and uniform convergence of the transforms on $[0,6]$ give the same non-strict positive-part majorant after sufficiently small smoothing in Kim's proof. [Kim, Lemma 5.1 and §5](https://hexagonmath.org/pdf/2611.00318v1) · [Interval verification](BoundCertificateReplays20261119.md#verify_isolation_profilepy)

Apply Proposition 4.2 and take the smoothing limit. For each $0<c\le1/(4\pi)$ the lower proportion is at least

$$
\frac32-\frac{\cot(1/\sqrt2)}{\sqrt2}
-\frac{\ell}{4\pi}F(2\pi a)-6\pi^2c^2.
$$

At $c=10^{-5}$ the interval replay puts this between 0.6724913656 and 0.6724913657. Keeping Kim's original $a=6/5,\ \ell=663/1000$ and substituting the same profile gives 0.6724911466569586. Wolfram Language independently evaluates the new expression as 0.6724913656447573973696462343749242538597. The parameters certify a gain within the one-piece mollifier and Montgomery–Taylor construction. The proof does not establish global optimality among isolation methods. [Lamzouri's original isolation argument](https://arxiv.org/abs/2610.26841v2) · [Kim's certificate and reproducibility record](https://doi.org/10.5281/zenodo.24126375)

For Lamzouri's local-height threshold $2\pi c/\log\gamma_n$, choose any $c'>c$ below $1/(4\pi)$. Every Kim-isolated zero at parameter $c'$ with $\gamma_n\ge T^{c/c'}$ also passes the local test. Riemann–von Mangoldt gives $N(T^{c/c'})/N(T)\to0$ at fixed $c,c'$. Letting $c'\downarrow c$ gives the same continuous lower-bound formula in the interior of the range, including $0<c\le10^{-5}$. [Lamzouri, Definition 1.1](https://arxiv.org/abs/2610.26841v2)

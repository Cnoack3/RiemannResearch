---
title: "A realistic path to ordinate pair correlation"
subtitle: "Exact counting identities, prime mean squares, and the signed residual"
date: "11 October 2026"
geometry: "margin=1in"
fontsize: 11pt
colorlinks: true
---

This continuation executes five connected workstreams: exact count moments;
quantitative transfer from triangle transforms to pair counts; the complete
prime-polynomial mean square; an explicit residual retaining horizontal zero
coordinates; and unconditional bounds on that residual. The finite results
are separated from the analytic limit still required for the conjecture.
No Riemann Hypothesis or simplicity assumption is used.

The central conclusion is a concrete reduction. Once the prime mean square
is evaluated, ordinate pair correlation is equivalent to identifying the
limiting **signed covariance plus residual energy** for every fixed window
size. The residual cannot be discarded: below we prove it has a positive
contribution for sufficiently small windows, independently of pair correlation.

# 1. Exact counting moments, including both boundaries

Let $I$ be a finite set of occurrence labels, let $x_i\in\mathbb R$, let
$a\le b$, and let $h>0$. Repeated ordinates have different labels. Put
$C_h(t)=\sum_i\mathbf1_{t<x_i\le t+h}$ and $y_+=\max(y,0)$.
For a pair set $\ell_{ij}=\max(x_i,x_j)-h$ and
$r_{ij}=\min(x_i,x_j)$. Its clipped overlap has length

$$
K_{a,b,h}(x_i,x_j)=\bigl(\min(b,r_{ij})-\max(a,\ell_{ij})\bigr)_+.
$$

Its full length and the two discarded parts give the exact equality

$$
\begin{aligned}
K_{a,b,h}(x_i,x_j)
={}&(h-|x_i-x_j|)_+\\
&-(\min(a,r_{ij})-\ell_{ij})_+
 -(r_{ij}-\max(b,\ell_{ij}))_+.
\end{aligned}
\tag{1.1}
$$

Therefore

$$
\boxed{\int_a^b C_h(t)^2dt=\sum_{i,j}K_{a,b,h}(x_i,x_j).}
\tag{1.2}
$$

Likewise, $\int_a^b C_h(t)dt=\sum_iK_{a,b,h}(x_i,x_i)$.
These identities hold for every positive $h$, even when a window is longer
than the interval of integration.

**Proof.** Up to endpoints of measure zero, the indicator for occurrence $i$
is that of $[x_i-h,x_i)$. The intersection for $i,j$ is the interval from
$\ell_{ij}$ to $r_{ij}$ when this is nonempty. Decompose it into its portions
left of $a$, between $a$ and $b$, and right of $b$. Their lengths are exactly
(1.1). Expand the finite square and integrate term by term. No pair, including
a pair of different occurrences with the same ordinate, has been removed.

## The actual-zero specialization

Let $N=N(T)$ count all nontrivial zeta-zero occurrences with
$0<\gamma_j\le T$, with analytic multiplicity. For sufficiently large $T$,
$N>0$. Set

$$
\rho_T=N(T)/T,\qquad x_j=\rho_T\gamma_j,
\qquad h=\lambda/\rho_T\quad(\lambda>0).
$$

Use the capped forward count

$$
C_T(t;\lambda)=N(\min(t+h,T))-N(t),\qquad0\le t\le T.
$$

For this finite sample the upper boundary term is zero, while the lower one
is explicit:

$$
\begin{aligned}
\int_0^T C_T(t;\lambda)dt
 &=hN-\sum_j(h-\gamma_j)_+,\\
\int_0^T C_T(t;\lambda)^2dt
 &=\sum_{j,k}(h-|\gamma_j-\gamma_k|)_+
   -\sum_{j,k}(h-\max(\gamma_j,\gamma_k))_+.
\end{aligned}
\tag{1.3}
$$

Since the positive ordinates are bounded away from zero and $h\to0$, for each
fixed $\lambda$ the lower terms eventually vanish. Define

$$
A_T(\lambda)=\frac1N\sum_{j,k}(\lambda-|x_j-x_k|)_+,
\qquad V_T(\lambda)=\frac1T\int_0^T(C_T(t;\lambda)-\lambda)^2dt.
$$

Using $\rho_T=N/T$, (1.3) then gives the **exact** equalities

$$
\boxed{\frac1T\int_0^T C_Tdt=\lambda,\qquad
\frac1T\int_0^T C_T^2dt=A_T(\lambda),\qquad
A_T(\lambda)=\lambda^2+V_T(\lambda).}
\tag{1.4}
$$

Clipping at $T$ is part of the definition, not an omitted error.

# 2. Triangle transforms determine the local pair law

For any $N\ge1$ real numbers define $d_{jk}=|x_j-x_k|$ and

$$
q_N=\frac1N\#\{(j,k):d_{jk}=0\},\qquad
B_N(\lambda)=\frac1N\#\{(j,k):0<d_{jk}\le\lambda\}.
$$

Let $D_N(\lambda)=N^{-1}\#\{(j,k):j\ne k,\ d_{jk}\le\lambda\}$.
Then $q_N\ge1$ and $D_N=B_N+q_N-1$. An index diagonal and an
ordinate collision are different notions.

Each hinge $(\lambda-d)_+$ is convex. Thus $A_N$ is continuous, convex,
and piecewise linear, with right derivative

$$
A'_{N,+}(\lambda)=q_N+B_N(\lambda)=1+D_N(\lambda).
$$

For $0<\varepsilon<\lambda$ its finite secants satisfy

$$
\frac{A_N(\lambda)-A_N(\lambda-\varepsilon)}\varepsilon
\le A'_{N,+}(\lambda)
\le\frac{A_N(\lambda+\varepsilon)-A_N(\lambda)}\varepsilon.
\tag{2.1}
$$

More precisely, for $a<b$, the secant lies between the inclusive threshold
mass at $a$ and the strict threshold mass at $b$. This convention retains
pairs lying exactly at a threshold. Also

$$
q_N\varepsilon\le A_N(\varepsilon),\qquad\varepsilon>0.
\tag{2.2}
$$

## The target and quantitative transfer

Write $s(u)=\sin(\pi u)/(\pi u)$ with $s(0)=1$, and $r(u)=1-s(u)^2$.
The target is

$$
A_*(\lambda)=\lambda+2\int_0^\lambda(\lambda-u)r(u)du
=\lambda^2+V_*(\lambda),
$$
$$
V_*(\lambda)=\lambda-2\int_0^\lambda(\lambda-u)s(u)^2du.
\tag{2.3}
$$

It has $A_*'=1+B_*$, where $B_*(\lambda)=2\int_0^\lambda r(u)du$,
and $0\le A_*''\le2$. The elementary Fourier identity
$s(u)^2=\int_{-1}^1(1-|v|)\cos(2\pi uv)dv$ and
$1-\cos y\le y^2/2$ imply $r(u)\le\pi^2u^2/3$. Consequently

$$
0\le A_*(\varepsilon)-\varepsilon\le\pi^2\varepsilon^4/18,
\qquad
0\le q_N-1\le\frac{|A_N(\varepsilon)-A_*(\varepsilon)|}\varepsilon
 +\frac{\pi^2\varepsilon^3}{18}.
\tag{2.4}
$$

If $|A_N-A_*|\le\eta$ at $\lambda-\varepsilon,\lambda,\lambda+\varepsilon$,
(2.1) and $0\le A_*''\le2$ give

$$
\boxed{|D_N(\lambda)-B_*(\lambda)|\le\varepsilon+2\eta/\varepsilon.}
\tag{2.5}
$$

For strictly positive gaps, therefore,

$$
B_* -\varepsilon-2\eta/\varepsilon-(q_N-1)
\le B_N\le B_*+\varepsilon+2\eta/\varepsilon.
\tag{2.6}
$$

**Proof of the transfer.** Each model secant differs from $A_*'(\lambda)$
by at most $\varepsilon$. Replacing the two endpoint values by $A_N$
changes the secant by at most $2\eta/\varepsilon$. Apply (2.1), subtract
one, and then subtract the nonnegative collision excess when required.

If $A_T(\lambda)\to A_*(\lambda)$ for every fixed $\lambda>0$, (2.4), first
at fixed $\varepsilon$ and then as $\varepsilon\downarrow0$, gives $q_T\to1$.
Equations (2.5)--(2.6), taking $T\to\infty$ before
$\varepsilon\downarrow0$, give the one-sided ordinate PCC:

$$
\boxed{\frac1{N(T)}\#\{(j,k):0<\rho_T(\gamma_j-\gamma_k)\le\lambda\}
\longrightarrow\int_0^\lambda r(u)du.}
\tag{2.7}
$$

Evenness supplies the factor of two between absolute and one-sided gaps.
The monotonicity of these counting functions and continuity of their limit
also give uniform convergence on compact positive $\lambda$ intervals.

Equivalently, the measures $N^{-1}\sum_{j\ne k}\delta_{x_j-x_k}$ converge
vaguely to $r(u)du$: interval-count convergence and locally bounded mass
imply convergence for compactly supported continuous tests. Conversely,
testing vague convergence against $(\lambda-|u|)_+$ recovers $A_T\to A_*$.
Thus (1.4) makes fixed-window variance convergence an exact criterion for the
local pair law. It also implies density-one simple critical zeros: the number
of occurrences sharing their ordinate with another is at most $N(q_T-1)$,
and reflection forces every off-line zero to share its ordinate. It does
not exclude a finite or zero-density exceptional set.

# 3. Prime mean square: all signed terms and a cutoff reaching $T$

For $X\ge2$ define

$$
P_X(t,h)=-\frac1\pi\sum_{2\le n\le X}
\frac{\Lambda(n)}{\sqrt n\log n}
[\sin((t+h)\log n)-\sin(t\log n)].
\tag{3.1}
$$

Let $M=\lfloor X\rfloor$ and
$b_n=\Lambda(n)\sin(h\log n/2)/(\sqrt n\log n)$.
Then $P_X=-(2/\pi)\sum b_n\cos((t+h/2)\log n)$.
Define the normalized cosine kernel

$$
J_T(v)=\frac1T\int_0^T\cos((t+h/2)v)dt
=\begin{cases}1,&v=0,\\
\dfrac{\sin((T+h/2)v)-\sin((h/2)v)}{Tv},&v\ne0.
\end{cases}
$$

Finite expansion and product-to-sum give the complete equality

$$
\boxed{\|P_X\|_T^2=D_X+E_-+E_+,\quad
D_X=\frac2{\pi^2}\sum_{n=2}^M b_n^2,}
\tag{3.2}
$$
$$
E_-=\frac2{\pi^2}\sum_{n\ne m}b_nb_mJ_T(\log(n/m)),\qquad
E_+=\frac2{\pi^2}\sum_{n,m}b_nb_mJ_T(\log(nm)).
$$

Here $\|f\|_T^2=T^{-1}\int_0^T f(t)^2dt$; all sums run from $2$ to $M$.
The signs of $b_n$ and of both remainders are retained. The sum-frequency
diagonal is included in $E_+$.

## Explicit elementary error

Let $H_0=0$, $H_j=\sum_{k=1}^j1/k$, and
$R_M=\max_{2\le n\le M}(H_{n-2}+H_{M-n})$. Since
$|J_T(v)|\le2/(T|v|)$ for $v\ne0$ and
$|\log(n/m)|\ge|n-m|/M$,

$$
\boxed{|E_-+E_+|\le D_X
\left[\frac{2MR_M}{T}+\frac{2(M-1)}{T\log4}\right].}
\tag{3.3}
$$

Indeed $|b_nb_m|\le(b_n^2+b_m^2)/2$ bounds the difference-frequency
sum by $R_M\sum b_n^2$, while $(\sum|b_n|)^2\le(M-1)\sum b_n^2$
bounds the sum-frequency sum. This proves a finite error with no
asymptotic or zero-statistics input.

## The arithmetic diagonal and its endpoint

For $n=p^k$, $b_n^2=(k^2p^k)^{-1}\sin^2(hk\log p/2)$. Hence

$$
0\le\sum_{k\ge2,\ p^k\le X}b_{p^k}^2
\le\frac{h^2}{4}\sum_p\frac{(\log p)^2}{p(p-1)}=O(h^2).
\tag{3.4}
$$

The displayed series converges by comparison with
$\sum_{n\ge2}(\log n)^2/[n(n-1)]$.
Writing $L=\log T$ and $c_T=L/(2\pi\rho_T)=1+O(1/L)$, the prime part is
exactly $\sum_{p\le X}p^{-1}\sin^2(\pi\lambda c_T\log p/L)$.
For fixed $0<a<b$, PNT and partial summation give

$$
\sum_{T^a<p\le T^b}\frac1p\longrightarrow\log(b/a).
$$

Thus the prime reciprocal measures in logarithmic coordinates converge to
$du/u$ away from zero. At the lower endpoint, use the vanishing of the
sine test and the Chebyshev bound to obtain

$$
\sum_{p\le T^\delta}\frac1p\sin^2(\pi\lambda c_T\log p/L)
\ll_\lambda\delta^2+L^{-2}.
$$

The limiting integral below $\delta$ satisfies the same $O_\lambda(\delta^2)$
bound. First take $T\to\infty$, then $\delta\downarrow0$. Equation (3.4)
therefore proves, for fixed $\theta>0$ and $X=T^\theta$,

$$
D_X\longrightarrow I_\theta(\lambda)
=\frac2{\pi^2}\int_0^\theta\frac{\sin^2(\pi\lambda u)}u du.
\tag{3.5}
$$

For $0<\theta<1$, (3.3) now proves $\|P_X\|_T^2\to I_\theta$.

## The classical sharpening reaches $\theta=1$

Montgomery--Vaughan's mean-value theorem gives

$$
\int_0^T\left|\sum a_n n^{it}\right|^2dt
=T\sum|a_n|^2+O\left(\sum n|a_n|^2\right)
$$

with an absolute constant [MV, Corollary 3, (1.11)]. Applied to
$a_n=b_n e^{ih\log n/2}$ it bounds exactly $E_-$. The elementary bound
for $E_+$ still applies. Prime-power support and partial summation give,
uniformly in $h$,

$$
\sum n b_n^2\ll X/\log X,\qquad
\sum|b_n|\ll\sqrt X/\log X.
$$

For the first, primes contribute at most $\pi(X)$ and higher powers at most
$\sum_{k\ge2}\pi(X^{1/k})/k^2=O(\sqrt X)$. For the second, primes contribute
$O(\sqrt X/\log X)$, squares $O(\log\log X)$, and powers of order at least
three a convergent series. Consequently

$$
\boxed{|E_-+E_+|\ll\frac{X}{T\log X},\qquad
\|P_{T^\theta}\|_T^2\longrightarrow I_\theta(\lambda)\quad(0<\theta\le1).}
\tag{3.6}
$$

This is an unconditional theorem about this chosen polynomial. At $X=T$ it
has error $O(1/\log T)$ apart from the PNT diagonal convergence. It does
not assert an approximation to zero counts or extend a known PCC support
range. The same argument permits $X/(T\log X)\to0$ with
$\log X/\log T\to1$, for example $X=T\log T/\log\log T$.

# 4. An exact residual with horizontal coordinates retained

Set $Z_T=C_T-\lambda$. Let $\vartheta(t)$ be the continuous Riemann--Siegel
phase and $S(t)$ the standard argument term in Riemann--von Mangoldt.
The exact formula $N(t)=1+\vartheta(t)/\pi+S(t)$ away from ordinates gives

$$
Z_T=\Delta_hS+m_T-B_T,
\quad m_T=\Delta_h\vartheta/\pi-\lambda,
\quad B_T=N(t+h)-N(\min(t+h,T)).
\tag{4.1}
$$

The endpoint spill $B_T$ is nonnegative and supported on $[T-h,T]$.
The unconditional local zero bound and Stirling's formula imply

$$
\|B_T\|_T^2\ll_\lambda\frac{\log T}{T},\qquad
\|m_T\|_T=O_\lambda(1/\log T).
\tag{4.2}
$$

For detail, $N(T+h)-N(T)\ll\log T$, so the spill contributes at most
$h\log^2T/T$. Also, for $t\ge1$,
$m_T(t)=\frac h{2\pi}(\log(t/T)+1)
+O(h/(1+t)+h\log T/T)$. Its square integrates using
$\int_0^1(\log u+1)^2du=1$. The bounded initial interval contributes
$O_\lambda(1/T)$. Thus $\|Z_T-\Delta_hS\|_T=o_\lambda(1)$.

## A contour representation of the actual residual

Fix $c>1$ and set

$$
\xi(s)=\tfrac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s),\qquad
G(s)=\frac1s+\frac1{s-1}-\frac12\log\pi+\frac12\psi(s/2).
$$

For $t>0$ and $t,t+h$ not zero ordinates, apply the argument principle to
$\xi$ on the rectangle with real sides $1-c,c$ and horizontal sides
$t,t+h$. There are no poles. Put $F=\xi'/\xi$. Functional symmetry and
conjugation give $F(1-c+iu)=-\overline{F(c+iu)}$. The two vertical
sides of the positively oriented contour therefore contribute
$2i\int_t^{t+h}\Re F(c+iu)du$. On a horizontal side the real parts
cancel by the same symmetry, and the imaginary parts double the integral
from $1/2$ to $c$. Hence

$$
\Delta_hN(t)=\frac1\pi\int_t^{t+h}\Re F(c+iu)du
-\frac1\pi\Im\Delta_h\int_{1/2}^c F(\sigma+it)d\sigma.
\tag{4.3}
$$

The right-side prime series is absolutely convergent. Define

$$
P_{c,h}(t)=-\frac1\pi\sum_{n\ge2}\frac{\Lambda(n)}{n^c\log n}
[\sin((t+h)\log n)-\sin(t\log n)],
$$
$$
G_{c,h}(t)=\frac1\pi\int_t^{t+h}\Re G(c+iu)du.
$$

The canonical product gives
$F(s)=B+\sum_\rho m_\rho[(s-\rho)^{-1}+\rho^{-1}]$.
Subtract the two heights before summing: the constant and compensation terms
cancel. With $\rho=\beta+i\gamma$ define

$$
K_{c,h}(\beta,y)=\frac1\pi\int_{1/2}^c
\left[\frac{y+h}{(\sigma-\beta)^2+(y+h)^2}
-\frac{y}{(\sigma-\beta)^2+y^2}\right]d\sigma.
$$

Then

$$
\boxed{\Delta_hN(t)=P_{c,h}(t)+G_{c,h}(t)
+\sum_\rho m_\rho K_{c,h}(\beta,t-\gamma).}
\tag{4.4}
$$

Here $\sum_\rho m_\rho$ runs over distinct zero locations with their
analytic multiplicities, including positive and negative ordinates. For fixed $t,h,c$, the
subtracted resolvents are uniformly $O(h/\gamma^2)$ for sufficiently large
$|\gamma|$. Riemann--von Mangoldt implies
$\sum_\rho m_\rho/(1+\gamma^2)<\infty$, so this series converges absolutely
and its integration is justified. Near zeros the two heights avoid the
singularity by assumption; the exceptional set of $t$ has measure zero.
Every $\beta$ is retained. The canonical product and functional symmetry
are classical inputs [DLMF]; (4.3)--(4.4) are the deductions used here.

For any chosen finite $P_X$ in (3.1) the actual residual is therefore

$$
\boxed{R_{T,X}=P_{c,h}-P_X+G_{c,h}-\lambda-B_T
+\sum_\rho m_\rho K_{c,h}(\beta,t-\gamma),\quad Z_T=P_X+R_{T,X}.}
\tag{4.5}
$$

Equivalently $R_{T,X}=\Delta_hS-P_X+m_T-B_T$. This formula identifies
all of the actual remainder, including horizontal and endpoint contributions.
It supplies no smallness claim. In fact, for fixed $c>1$,
$\|P_{c,h}\|_\infty\le(h/\pi)\sum\Lambda(n)n^{-c}=O_c(h)\to0$;
this convergent prime series cannot itself carry microscopic variance.
Moving the prime representation toward the critical line with usable uniform
estimates remains the Selberg-type analytic task. The exact contour formula
is not being described as a new Selberg approximation theorem.

# 5. Rigorous fixed-window bounds and the precise remaining limit

The unconditional Selberg--Fujii theorem, as reproduced in [GLSS,
Proposition 2, (5.6)], states for $0<h\le1$, with $L_T=\log T/(2\pi)$,

$$
\frac1T\int_0^T(\Delta_hS)^2dt
=\frac1{\pi^2}\log(2+hL_T)
+O(\sqrt{\log(2+hL_T)}).
$$

Since $hL_T=\lambda+O_\lambda(1/\log T)$, (4.2) gives

$$
\boxed{V_T(\lambda)=\frac1{\pi^2}\log(2+\lambda)
+O(\sqrt{\log(2+\lambda)})+o_\lambda(1)=O_\lambda(1).}
\tag{5.1}
$$

The $O$ term stays bounded, rather than tending to zero, when $\lambda$ is
fixed. It therefore does not identify $V_*(\lambda)$.


This input also closes the converse to Section 2 for the conventional
strictly positive-gap PCC statement. The exact identity is
$A_T(\lambda)=q_T\lambda+\int_0^\lambda B_T(u)du$.
If positive-gap PCC holds, its monotone counts are bounded on $[0,\lambda]$;
dominated convergence gives
$\int_0^\lambda B_T(u)du\to A_*(\lambda)-\lambda$.
Hence $q_T-1=(V_T(\lambda)-V_*(\lambda))/\lambda+o(1)$.
Using (5.1), $V_*\ge0$, and the absolute constant in Fujii's bound gives
$\limsup(q_T-1)\ll\log(2+\lambda)/\lambda$. First take $T\to\infty$
for fixed $\lambda$, then $\lambda\to\infty$: this proves $q_T\to1$.
Thus conventional positive-gap PCC also implies triangle convergence for
actual zeta zeros. This converse uses Fujii; the deterministic direction
from triangle convergence in Section 2 requires no such analytic input.

There is also an exact lower bound unavailable from sign-free residual
estimates. Write $r_\lambda=\lambda-\lfloor\lambda\rfloor$. Since the
count is integer-valued,
$(C_T-\lfloor\lambda\rfloor)(C_T-\lfloor\lambda\rfloor-1)\ge0$.
Average, use its exact mean $\lambda$, and obtain

$$
\boxed{V_T(\lambda)\ge r_\lambda(1-r_\lambda).}
\tag{5.2}
$$

## Local compactness is now available

For the positive even pair measures including the diagonal,
$\mu_T=N^{-1}\sum_{j,k}\delta_{\rho_T(\gamma_j-\gamma_k)}$,
(1.4)--(5.1) bound every triangle transform. For $a>0$,

$$
\mu_T([-a,a])\le A_T(2a)/a=O_a(1).
$$

Thus every sequence $T\to\infty$ has a subsequence with a vague limit,
a positive even Radon measure $\mu\ge\delta_0$. Every such limit satisfies
$\int(\lambda-|u|)_+d\mu\ge\lambda^2$. Identification of these limits,
not existence of a limiting subsequence, is the task left by (5.1).

## A positive lower bound for the signed residual contribution

Define $\langle f,g\rangle_T=T^{-1}\int_0^Tfg$ and

$$
\mathcal E_{T,\theta}(\lambda)
=2\langle P_{T^\theta},R_{T,T^\theta}\rangle_T
 +\|R_{T,T^\theta}\|_T^2.
$$

The complete equality, before any bound, is

$$
\boxed{V_T=\|P_{T^\theta}\|_T^2+\mathcal E_{T,\theta}.}
\tag{5.3}
$$

Combining (3.6) with (5.2) proves, unconditionally for $0<\theta\le1$,

$$
\liminf_{T\to\infty}\mathcal E_{T,\theta}(\lambda)
\ge r_\lambda(1-r_\lambda)-I_\theta(\lambda).
\tag{5.4}
$$

Since $I_\theta(\lambda)\le\theta^2\lambda^2$, for $0<\lambda<1$
this gives the concrete inequality

$$
\boxed{\liminf_{T\to\infty}\mathcal E_{T,\theta}(\lambda)
\ge\lambda-(1+\theta^2)\lambda^2,
\quad0<\theta\le1.}
\tag{5.5}
$$

It is strictly positive for $0<\lambda<1/(1+\theta^2)$. At $\theta=1$
it reads $\liminf\mathcal E_{T,1}\ge\lambda-2\lambda^2>0$ for
$0<\lambda<1/2$. This is a genuine bound on the actual residual; PCC is
not assumed to derive it. The reverse triangle inequality likewise yields

$$
\liminf\|R_{T,T^\theta}\|_T
\ge\max\{0,\sqrt{r_\lambda(1-r_\lambda)}-\sqrt{I_\theta(\lambda)}\}.
$$

Fujii supplies an upper bound for $\mathcal E_{T,\theta}$ by subtracting
$I_\theta+o(1)$ from (5.1). It also gives $\|R\|_T=O_{\lambda,\theta}(1)$.
These bounds retain the signed expression; they do not identify its limit.

## The remaining provider, with an exact target

Fourier transformation of the interval indicator and of $s^2$ gives

$$
V_*(\lambda)=\frac2{\pi^2}\left[
\int_0^1\frac{\sin^2(\pi\lambda u)}u du
+\int_1^\infty\frac{\sin^2(\pi\lambda u)}{u^2}du\right].
\tag{5.6}
$$

For completeness, the covariance distribution is $\delta_0-s(u)^2du$,
whose Fourier transform is $1-(1-|u|)_+=\min(|u|,1)$. The squared Fourier
transform of an interval of length $\lambda$ is
$\sin^2(\pi\lambda u)/(\pi^2u^2)$. Integrate their product, use evenness,
and separate $0<u<1$ from $u>1$. This proves (5.6) and agrees with (2.3).

Given (3.6), the exact remaining target for any fixed $0<\theta\le1$ is

$$
\boxed{\mathcal E_{T,\theta}(\lambda)
\longrightarrow V_*(\lambda)-I_\theta(\lambda)
\quad\text{for every fixed }\lambda>0.}
\tag{5.7}
$$

At the now justified cutoff $X=T$, it simplifies to

$$
\boxed{2\langle P_T,R_{T,T}\rangle_T+\|R_{T,T}\|_T^2
\longrightarrow\frac2{\pi^2}\int_1^\infty
\frac{\sin^2(\pi\lambda u)}{u^2}du.}
\tag{5.8}
$$

The right side is strictly positive. Proving (5.8) for every fixed $\lambda$
would establish variance convergence and, by Section 2, ordinate PCC. It is
**open in this work**. A boundedness estimate or $\|R\|_T\to0$ does not
supply it. The next analytic work is to evaluate this signed quadratic
quantity using (4.5), with sufficient uniform control to retain the
horizontal zero contribution and the mixed prime--residual term.

# Verification scope and research ledger

The accompanying Lean development treats exact finite window overlaps and
moments, the centered-variance algebra, finite hinge convexity and secants,
quantitative transfer of three energy errors, and the signed mean square of
finite cosine polynomials. It uses occurrence labels, so repeated ordinates
are permitted. The actual-zero specialization uses the repository's genuine
multiplicity-copy type, with its displayed support and mean assumptions.

PNT diagonal convergence, Montgomery--Vaughan's mean-value theorem, the
contour/canonical-product argument, Fujii's moment input, vague compactness,
and the asymptotic PCC transfer in this note are **paper mathematics**; they
are not claimed to have been formalized by these finite Lean modules.
The only domain-specific PCC provider (5.7), equivalently (5.8), remains
Open. The full Selberg-type approximation with a usable uniform microscopic
remainder is also Open as a provider; (4.4) establishes an exact contour
identity only.

The final verification job and publication commit are recorded in the
accompanying verification ledger once the checkpoint finishes.

# References

**[MV]** H. L. Montgomery and R. C. Vaughan, *Hilbert's Inequality*,
J. London Math. Soc. (2) 8 (1974), 73--82, Corollary 3, equation (1.11).
[Author-hosted paper](https://personal.science.psu.edu/rcv4/personal/Publications/s2-8-1-73.pdf).
This supports the mean-value input in Section 3, not a zero-count
approximation.

**[GLSS]** D. A. Goldston, J. Lee, J. Schettler, A. I. Suriajaya,
*Pair Correlation Conjecture for the Zeros of the Riemann Zeta-function I:
Simple and Critical Zeros*, arXiv:2503.15449v4 (2026), Sections 3, 5--7.
[Paper](https://arxiv.org/html/2503.15449v4).
Proposition 2 explicitly reproduces the unconditional Selberg--Fujii moment
input used here and references the original Fujii and Tsang proofs.
Its fixed-scale error is not a PCC asymptotic.

**[DLMF]** NIST Digital Library of Mathematical Functions, equations
[25.2.12](https://dlmf.nist.gov/25.2.E12),
[25.4.3](https://dlmf.nist.gov/25.4.E3), and
[25.4.4](https://dlmf.nist.gov/25.4.E4).
These support the canonical product, completed-zeta definition, and
functional symmetry used to derive the explicit contour identity.

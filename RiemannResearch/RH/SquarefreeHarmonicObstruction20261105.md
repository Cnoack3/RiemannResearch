# Sharp two-sign harmonic growth in the squarefree span

Let $g_m(n)=\{n/m\}$, let $Q(n)=1/(\zeta(2)n^2)$ on positive integers, and let $V$ be the closed real span in $L^2(Q)$ of the $g_m$ with $m\ge2$ squarefree. Write
$$
 S_\pm(v;X)=\sum_{1\le n\le X}\frac{(\pm v(n))_+}{n},\qquad
 h(v;X)=\min(S_+(v;X),S_-(v;X)).
$$
Bagchi's Remark 8 gives the squarefree dictionary underlying this test. The construction concerns arbitrary elements of that dictionary's closed span. A counterexample to a proposed bound for the specific projection displacement would require its normal equations. [Bagchi (2006)](https://arxiv.org/pdf/math/0607733)

**Theorem (paper proof).** For every $\beta>1/2$ there is a single $v\in V$ and positive constants $c,C,X_0$, depending on $\beta$, such that for every $X\ge X_0$,
$$
 c\,\frac{\sqrt X}{(\log X)^\beta}
 \le h(v;X)\le C\,\frac{\sqrt X}{(\log X)^\beta}.
$$
One can prescribe any positive upper bound on $\|v\|_Q$ by rescaling. Every example satisfies the squarefree radical increment identities. For every fixed $\delta>0$ both signed portions of the full-profile absolute first moment in the agenda diverge. The exponent threshold $1/2$ is sharp for this all-large-$X$ lower bound even in the ambient space.

## Four residues

Set $t_m=2g_{2m}-g_m$. Writing $n=qm+r$ with $0\le r<m$ gives $t_m(n)=q\bmod 2$. For each prime $p>6$, set
$$
 s_p=t_p-t_{3p}=2g_{2p}-g_p-2g_{6p}+g_{3p}.
$$
All four conductors are squarefree. In each period of length $6p$ the values of $s_p$ on the six successive half-open intervals of length $p$ are $0,1,0,0,-1,0$. In particular, $s_p$ vanishes for $n<p$, is $1$ on $[p,2p)$, and is $-1$ on $[4p,5p)$. The companion Lean module contains the residue formulas and finite-span membership.

## An element of the closed span

Choose an integer $K\ge 12$ with $\sqrt{K/2}\ge 4\,2^\beta$. By Bertrand's postulate, for each $k\ge1$ choose a prime $p_k\in[K^k,2K^k]$. Put
$$
 A_k=\frac{\sqrt{p_k}}{k^\beta},\qquad
 v(n)=\sum_{k\ge1} A_k s_{p_k}(n).
$$
Then $K/2\le p_{k+1}/p_k\le2K$, and $A_{k+1}/A_k\ge\sqrt{K/2}\,(k/(k+1))^\beta\ge4$. In particular $\sum_{i<k}A_i\le A_k/3$. The series at each physical site is finite. [A formalized proof of Bertrand's postulate](https://doi.org/10.6092/ISSN.1972-5787/3406)

For $p_k\le n<p_{k+1}$, the absolute value of any partial sum is at most $4A_k/3$. The square of this dominating function has finite $Q$-mass:
$$
 \frac{16}{9\zeta(2)}
 \sum_{k\ge1}A_k^2\!\!\sum_{p_k\le n<p_{k+1}}\! n^{-2}
 \le \frac{16}{9\zeta(2)}\sum_{k\ge1}\frac{A_k^2}{p_k-1}
 \le \frac{32}{9\zeta(2)}\sum_{k\ge1}k^{-2\beta}.
$$
Here $\sum_{n\ge p}n^{-2}\le\int_{p-1}^\infty t^{-2}\,dt$. Dominated convergence gives convergence in $L^2(Q)$ of the finite legal partial sums to $v$. Consequently $v\in V$. For each $m\ge2$ the map $v\mapsto\Delta v(m)-\Delta v(\operatorname{rad}m)$ is a finite linear combination of continuous coordinate evaluations. Every partial sum annihilates this functional by the repository's squarefree difference theorem, so their limit also does.

## Quantitative estimates for the two signs

Since $p_{k+1}>5p_k$, future pulses vanish throughout both designated intervals. Earlier pulses have total amplitude at most $A_k/3$. Hence $v(n)\ge 2A_k/3$ on $[p_k,2p_k)$ and $v(n)\le-2A_k/3$ on $[4p_k,5p_k)$. These intervals each have $p_k$ sites and therefore
$$
 S_+(v;5p_k)\ge A_k/3,\qquad S_-(v;5p_k)\ge 2A_k/15.
$$
For $5p_k\le X<5p_{k+1}$, monotonicity gives $h(v;X)\ge2A_k/15$. As $X<10Kp_k$ and $\log X\ge k\log K$, this proves the lower estimate with $c=2(\log K)^\beta/(15\sqrt{10K})$.

For $p_k\le X<p_{k+1}$, the harmonic mass of $[p_i,p_{i+1})$ is at most $1+\log(2K)$. Thus the total absolute prefix is at most $(16/9)(1+\log(2K))A_k$. Here $p_k\le X$, and $\log X\le (k+1)\log K+\log 2\le (2\log K+\log 2)k$. These inequalities yield the upper estimate, for example with $C=(16/9)(1+\log(2K))(2\log K+\log2)^\beta$.

For a fixed $\delta>0$, $H_\delta(n)=o(\log n)$ implies $e^{-H_\delta(n)}\ge n^{-1/4}$ for all sufficiently large $n$. On each designated interval for $p_k$, the corresponding sign contributes at least
$$
 (5p_k)^{-1/4}\cdot \frac{2A_k}{15}
 = \frac{2}{15\,5^{1/4}}\,\frac{p_k^{1/4}}{k^\beta}
$$
to its own weighted moment. This grows without bound and all terms of each series are nonnegative.

## Sharpness of the logarithmic threshold

For arbitrary $v\in L^2(Q)$, set
$$
 a_j^2=\sum_{2^j\le n<2^{j+1}}\frac{|v(n)|^2}{n^2}, \qquad
 \sum_{j\ge0}a_j^2=\zeta(2)\|v\|_Q^2.
$$
The inequality $2h\le S_++S_-$ and Cauchy–Schwarz on each dyadic interval give
$$
 2^{1-J/2}h(v;2^{J+1}-1)
 \le \sum_{j=0}^J 2^{-(J-j)/2}a_j .
$$
Write $k_i=2^{-i/2}$ and $L=\sum_{i\ge0}k_i=(1-2^{-1/2})^{-1}$. Weighted Cauchy–Schwarz bounds the square of the right-hand side by $L\sum_{j=0}^J k_{J-j}a_j^2$. Summing over $J$ and exchanging nonnegative terms gives
$$
 \sum_{J\ge0}2^{-J}h(v;2^{J+1}-1)^2
 \le \frac{\zeta(2)}{4(1-2^{-1/2})^2}\|v\|_Q^2.
$$
An all-large-$X$ lower bound $h(v;X)\ge c\sqrt{X/\log X}$ with $c>0$ would make this series dominate a positive multiple of the harmonic series. This proves impossibility at $\beta=1/2$ and hence for smaller $\beta$.

The example simultaneously satisfies membership in $V$, arbitrarily small $Q$-energy after rescaling, sublinear growth, and all the exact radical differences. Deriving a uniform polylogarithmic conclusion for the actual displacement requires information beyond these properties.

## A normal equation which separates the example from the actual displacement

For $p>6$ prime let $E_{p,r}=\{n:\lfloor n/p\rfloor\equiv r \pmod 6\}$. The signed pulse is exactly $\mathbf 1_{E_{p,1}}-\mathbf 1_{E_{p,4}}$. For every $f\in V^{\perp_Q}$,
$$
 \sum_{n\in E_{p,1}} Q(n) f(n)
 =\sum_{n\in E_{p,4}} Q(n) f(n).
$$
Both sums converge absolutely by Cauchy–Schwarz and $Q(\mathbb N)=1$. This applies in particular to $r_Q$ and $w=B_0r_P-d$. The latter yields the actual-displacement identity
$$
 \langle s_p,d\rangle_Q = \langle B_0 s_p,r_P\rangle_Q .
$$
Since $s_p$ vanishes for $n<p$ and $|s_p|\le1$, Cauchy–Schwarz and the inverse-square tail give
$$
 |\langle s_p,d\rangle_Q|
 \le \frac{\|\mathbf1_{[p,\infty)} r_P\|_Q}
 {(p+1)\sqrt{\zeta(2)(p-1)}} = o(p^{-3/2}).
$$

One can arrange that the counterexample substantially violates this condition. Enlarge $K$ above so that $q=K/2\ge4096$. For $p=p_k$ the own-scale term in the unnormalized pairing $\zeta(2)\langle s_p,v\rangle_Q$ is $A_k\sum s_p(n)^2/n^2$. The combined absolute contribution of earlier pulses is at most one third of this, since $|s_p|=s_p^2$ and $\sum_{i<k} A_i\le A_k/3$. The positive plateau alone gives $\sum s_p(n)^2/n^2\ge 1/(4p)$. All later pulses contribute in absolute value at most
$$
 \sum_{i>k}\frac{A_i}{p_i-1}
 \le \frac{2 A_k}{p_k}\sum_{m\ge1}q^{-m/2}
 =\frac{2 A_k}{p_k(\sqrt q-1)}.
$$
The first step also justifies absolute convergence of the series of pairings. Consequently,
$$
 \zeta(2)\langle s_{p_k},v\rangle_Q
 \ \ge\ \left(\frac16-\frac{2}{63}\right)\frac{A_k}{p_k}
 \ \ge\ \frac{A_k}{8p_k}.
$$
These pairings have a lower bound of order $p_k^{-1/2}(\log p_k)^{-\beta}$ and hence violate the normal-equation estimate. This exhibits a specific projection constraint that supplies information beyond radical increments.

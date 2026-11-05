# Recursive prime carries, composite charge cancellation, and the LCM blocks

The target for the limiting matched projection displacement is
$$
\sup_j\sum_{L_{M_j}\le n<L_{M_{j+1}}}\frac{|d(n)|^8}{n^2}<\infty,
\qquad L_M=\operatorname{lcm}(1,\ldots,M).
$$
Take distinct increasing endpoints, $d=f_Q-f_P$, and $Q(n)=1/(\zeta(2)n^2)$. The physical differences and charges are $x(n)=d(n)-d(n-1)$ and $b_m=\sum_{a\mid m}\mu(m/a)x(a)$ with $d(0)=0$. The previous [all-order decomposition and RH criteria](AllOrderCarryAndDifferenceResearch20261105.md) give the context. This note uses a prime in each step that is coprime to the parent. The earlier note covers repeated factors separately.

## The local floor and its two composite charges

Put $g_r(n)=\{n/r\}$, $D_k=p_1\cdots p_k$. Choose integers $u_k,v_k$ with $u_k p_k+v_kD_{k-1}=1$. Then
$$
S_k=u_k g_{D_{k-1}}+v_k g_{p_k},\qquad
g_{D_k}=\{S_k\}=S_k-C_k,\qquad C_k=\lfloor S_k\rfloor.
$$
The constants are integers, so inserting or removing an inner fractional part does not change the terminal fractional part. If the integer part is retained, each earlier $C_i$ is multiplied by $\prod_{i<j\le k}u_j$. The total transported integer is exactly the floor of the fully expanded prime argument.

At every composite $D>1$, Möbius inversion gives
$$
 b_D(C_k)=\mathbf1_{D=D_k}-u_k\mathbf1_{D=D_{k-1}}.
$$
This formula has a parent term that is absent in the direct decomposition from all prime atoms to one composite. For any finite tree of such steps choose a single parent $r(m)$ for each child $m$. With real weights $w_m$ the exact charge of the total carry at $D$ is
$$
\mathbf1_{D\text{ in the edge set}}w_D-
\sum_{m:\,r(m)=D}u_mw_m .
$$
Thus a nonzero incoming charge at an internal node cancels exactly when the signed child weights sum to it. A finite leaf retains its own coefficient. The formula for a truncated tree specifies the boundary to be estimated before taking an infinite limit.

[Finite path and terminal fractional part](QRecursivePrimeCarry.lean) · [Composite charge on a tree](QRecursiveCarryDetection.lean).

## A recursive chain with genuine cancellation at infinitely many composites

Let $p_k$ denote the $k$th prime, $D_k=\prod_{i=1}^k p_i$, and choose Bézout integers $u_k p_k+v_k D_{k-1}=1$ for $k\ge2$. Write $g_q(n)=\{n/q\}$. The actual integer floor carry is
$$C_k=u_k g_{D_{k-1}}+v_k g_{p_k}-g_{D_k}.$$
Take $(u_2,v_2)=(1,-1)$, $w_2=1$, and define $w_k=w_{k-1}/u_k$ for $k\ge3$. Since $u_k$ is a nonzero integer, $|w_k|\le1$. Directly summing gives
$$\sum_{k=2}^K w_k C_k=g_2+\sum_{k=2}^K w_k v_k g_{p_k}-w_K g_{D_K}.$$
The boundary tends to zero in $Q$ since $\|g_D\|_Q\ll D^{-1/2}$. This norm bound follows by splitting the defining series at $D$: for $n<D$ the ratio $g_D(n)/n$ equals $1/D$, and for $n\ge D$ it is at most $1/n$. For $k\ge3$, the Bézout equality gives
$$|w_kv_k|=|w_k-w_{k-1}p_k|/D_{k-1}\le (1+p_k)/D_{k-1}.$$
Bertrand's bound $p_k<2p_{k-1}$ and $D_{k-2}\ge 2^{k-2}$ make this summable. In fact the carry series converges absolutely in $Q$: the three terms in $\|w_k C_k\|_Q$ are bounded respectively by $O(D_{k-1}^{-1/2})$, $O(|w_kv_k|)$, and $O(D_k^{-1/2})$. The limit is a prime-atom series with the physical Möbius charges $b_D$ zero at every composite $D$. Its prime detector $b_2$ equals $-1$, so its limit is nonzero. Thus infinitely many nonzero floor carries can genuinely cancel at every composite. This constructs selected coefficients. It gives no estimate for the actual matched displacement's coefficients.

For arbitrary exact normalized chains with $p_k\ge2$ and $|w_k|\le1$, the two series in the identity converge absolutely at each fixed site, including when there is no comparison of consecutive prime sizes. The reciprocal Bézout equation bounds $|w_kv_k g_{p_k}(n)|$ by $2n/D_{k-1}$. Each boundary term is at most $n/D_k$. This gives geometric bounds on both series. [Infinite path identity at each site](QInfiniteRecursiveCarry.lean).

For the first four edges, a signed choice gives the following exact values.

| Parent | New prime | Target | $u_k$ | $v_k$ | $w_k$ |
|---:|---:|---:|---:|---:|---:|
| 2 | 3 | 6 | 1 | −1 | 1 |
| 6 | 5 | 30 | −1 | 1 | −1 |
| 30 | 7 | 210 | 13 | −3 | −1/13 |
| 210 | 11 | 2310 | −19 | 1 | 1/247 |

Wolfram checked the displayed synthesis on all 2310 sites of a full period, with maximum exact error zero. The charges of the four-edge sum at $2,6,30,210,2310$ are respectively $-1,0,0,0,1/247$. Each new edge transports the preceding composite charge to the next conductor.

One can even evaluate the prime sum at each fixed physical site with a finite tail error from the reciprocal certificate. If $n<p_{K+1}$ then for $k>K$, $g_{p_k}(n)=n/p_k$. The Bézout recurrence yields $w_kv_k/p_k=w_k/D_k-w_{k-1}/D_{k-1}$, so the tail equals $-n w_K/D_K$. Thus the partial carry series already equals its pointwise limit wherever all the subsequent parent and prime conductors are larger than $n$; each subsequent floor carry is zero there.

## Positive digits and the signed subtree sums of the actual displacement

With $D$ the parent and $r=Dp$ the child, use the normalized quotient digit
$$
 h_r(n)=\frac{\lfloor n/D\rfloor\bmod p}{p},\qquad
 g_r(n)=\frac{g_D(n)}p+h_r(n).
$$
As a function of a physical site, $h_r(n)=0$ when $n<D$ and $0\le h_r(n)\le\min(1,n/r)$. Under uniform CRT, condition on the complete residue modulo $D$. The $p$ possible lifts have digits $0,1,\ldots,p-1$, each occurring once. Iteration gives independent uniform digits on any fixed prime chain under product Haar. The physical measure has separate weights at the individual integers. Direct summation there gives
$$
\frac{1}{768r}\le \sum_{n\ge1}\frac{h_r(n)^8}{n^2}\le\frac3r\qquad(p\ge2).
$$
For the lower bound use $D\lceil p/2\rceil\le n<Dp$, so $h_r(n)\ge1/2$ on at least $r/3$ integers. For the upper bound split at $r$ and use the displayed sitewise bound. [Physical digit estimates](QRecursiveDigitBounds.lean).

Order each squarefree integer's primes increasingly to fix its finite path from the root $1$. With $r\preceq m$ denoting a non-root prefix, telescoping the residues gives
$$
g_m(n)=\frac1m\sum_{1<r\preceq m}r h_r(n).
$$
In particular, for the actual signed charges and finite horizon $H$,
$$
\sum_{m\le H} b_m g_m(n)=\sum_{2\le r\le H}r T_r(H) h_r(n),
\qquad T_r(H)=\sum_{\substack{m\le H\\r\preceq m}}\frac{b_m}{m}
$$
with zero understood at unused nodes. Balazard's reciprocal-charge theorem and the finite floor reconstruction give $d(n)=-\lim_H\sum_{m\le H}b_m g_m(n)$ at every fixed site. [Balazard, Proposition 7](https://doi.org/10.1007/978-3-030-61887-2_3) · [Physical transfer](QHeadSlopeLimit.lean).

Consequently a one-sided condition can retain actual cancellation inside the subtrees. If some $\sigma\in\{-1,1\}$ and arbitrarily large $H$ satisfy
$$
\sum_{2\le r\le H} r\,(-\sigma T_r(H))_+\le C ,
$$
then $\sigma d(n)\le C$ at every site since $0\le h_r(n)\le1$. The one-sided bounded-displacement theorem implies RH. A special case is a common sign $\sigma T_r(H)\ge0$ at all nodes of each good horizon. These conditions are open for the actual coefficients. [One-sided implication](QDifferenceLimits.lean).

A global absolute-value estimate from the digit eighth moment and Minkowski would use $\sum_r r^{7/8}|T_r(H)|$. For any $s>0$ it satisfies
$$
\frac1{1+2^{-s}}\sum_{2\le m\le H} m^{s-1}|b_m|
\le \sum_{2\le r\le H}r^s|T_r(H)|
\le \frac1{1-2^{-s}}\sum_{2\le m\le H}m^{s-1}|b_m|.
$$
The left inequality uses $b_r/r=T_r-\sum_{c\text{ child of }r}T_c$ and $c\ge2r$. The right one sums the geometric ancestor weights along each path. Thus a uniform absolute budget at $s=7/8$ asks precisely for convergence of $\sum_{m>1}|b_m|/m^{1/8}$. This quantifies the cost of taking absolute values before exploiting the signs.

## Canonical GCD recursion for the actual charges

Let $Q(N=n)=1/(\zeta(2)n^2)$, $x_n=d(n)-d(n-1)$, and $b=\mu*x$ in divisor convolution. The repository gives $b_m=0$ off the squarefree integers and $x\in L^2(Q)$. In particular $x_n=\sum_{m\mid n}b_m$, and
$$
 \sum_m |b_m|/m^2
 \le \zeta(2)\sum_n |x_n|/n^2<\infty .
$$
For a squarefree $S$, let $\mathcal F_S=\sigma(\mathbf1_{p\mid N}:p\mid S)$. For $a\mid S$ define
$$
   \alpha_a(S)=\sum_{(m,S)=a}b_m(a/m)^2.
$$
These coefficients are absolutely convergent. The prime divisibility indicators are independent under $Q$, with means $p^{-2}$, since $Q(k\mid N)=k^{-2}$. Conditional on the retained indicators, a squarefree $m$ divides $N$ with probability $\mathbf1_{a\mid N}(a/m)^2$, $a=(m,S)$. The absolute bound above allows conditional expectation to pass through the divisor expansion in $L^1(Q)$. Thus at every site
$$
  x_S(n):=\mathbb E_Q[x_N\mid\mathcal F_S](n)
  =\sum_{a\mid(n,S)}\alpha_a(S).
$$
For a new prime $p\nmid S$, split each fiber according as $p\mid m$ or $p\nmid m$. This gives
$$
 \alpha_a(S)=\alpha_a(Sp)+p^{-2}\alpha_{ap}(Sp), \qquad
 \sum_{a\mid S}\frac{|\alpha_a(S)-b_a|}{a^2}
 \le\sum_{m\nmid S}\frac{|b_m|}{m^2}.
$$
For increasing primorials the right side tends to zero. In particular each fixed coefficient is recovered. Moreover $x_S\to x$ in $L^2(Q)$ by martingale convergence since $x$ is radical-measurable. Directly, $\|x_S-x\|_{L^1(Q)}\le2\sum_{m\nmid S}|b_m|/m^2$.

### The drift after integrating

Writing $g_a(n)=\{n/a\}$ gives the exact physical antiderivative
$$
 \sum_{k=1}^n x_S(k)
 = \sum_{a\mid S}\alpha_a(S)\lfloor n/a\rfloor
 = n\theta_S-\sum_{a\mid S}\alpha_a(S)g_a(n), \qquad
 \theta_S=\sum_{a\mid S}\frac{\alpha_a(S)}a
 =\sum_m b_m\frac{(m,S)}{m^2}.
$$
The last infinite sum is absolute for each fixed $S$. The finite residue sum is bounded in $n$, so whenever $\theta_S\ne0$ this antiderivative has infinite $L^2(Q)$ norm. For example, for the single legal atom $d=g_p$ with $p\nmid S$, $x_n=1/p-\mathbf1_{p\mid n}$ and $x_S\equiv1/p-1/p^2$. Once $p\mid S$, $x_S=x$ and the drift vanishes. This example isolates the change from the prime divisibility probability $1/p^2$ under $Q$ to the frequency $1/p$ in a physical antiderivative. Subtracting $n\theta_S$ gives a legal combination of squarefree residues at each stage. Convergence of those corrected primitives in the requested moving-block eighth moments requires an estimate beyond the derivative martingale.

**Status.** Lean verifies the recursive floor identities, local and tree charge detection, infinite fixed-site identity for normalized chains, and the physical upper eighth-moment bound for one digit. The consecutive-prime construction, its convergence in the physical Hilbert space, the one-sided subtree criterion, and the conditional-expectation derivation above have paper proofs. For the actual projection, the stated one-sided subtree estimate and the uniform LCM-block estimate remain open.

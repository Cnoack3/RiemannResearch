# Displacement moments and signed tails

Let $Z=\zeta(2)$, $q(n)=1/(Zn^2)$, $d=f_Q-f_P$, and $w=Br_P-d$. For a physical vector $u$, let $b_u(n)=q(n)u(n)$ and $T_u(m)=\sum_{n\ge m}b_u(n)$ for $m\ge1$. The Lean definition sets the auxiliary coordinate $T_u(0)=0$.

## Lean declarations

| Declaration | Conclusion |
|---|---|
| `QSignedTailRigidity.mean_zero_of_summable_signedTail` | A squarefree annihilator with summable signed tails has zero mean. |
| `QSquarefreeDisplacementRigidity.residual_zero_iff_summable_displacement_signedTail` | The actual squarefree residual vanishes exactly when $\sum_m|T_d(m)|<\infty$. |
| `QSquarefreeDisplacementRigidity.riemannHypothesis_of_summable_displacement_signedTail` | The signed-tail condition on $d$ implies Mathlib RH. |
| `QSquarefreeDisplacementRigidity.riemannHypothesis_of_summable_displacement_prefix` | $\sum_{N\ge1}|\sum_{n\le N}d(n)|/N^2<\infty$ implies RH. |
| `QSignedTailRigidity.squarefree_absolute_moment_of_one_sided` | A prime-remainder comparison bounds the absolute power moment of a squarefree annihilator by $4/a$ times either one-sided moment for $0<a\le1$. |
| `QSquarefreeDisplacementRigidity.displacement_absolute_power_moment_of_one_sided` | Finiteness of either one-sided power moment of the actual displacement implies finiteness of its absolute moment. |
| `QSquarefreeDisplacementRigidity.riemannHypothesis_of_one_sided_displacement_harmonic_moment` | Finiteness of either $\sum_n d(n)^+/n$ or $\sum_n d(n)^-/n$ implies RH. |
| `QSquarefreeDisplacementRigidity.riemannHypothesis_of_eventual_displacement_sign` | Eventual nonnegativity or eventual nonpositivity of $d$ implies RH. |

The normalization by $Z$ cancels in every summability condition. The implication from RH back to squarefree closure is supplied on paper by Bagchi's Remark 8. The residual-zero equivalence in the table is internal to the project.

## Proof of the signed-tail criterion

Take $L=Y!$ and the finite sieve $F_Y(n)=-\sum_{k\mid L}\mu(k)g_k(n)$. Its coefficients have squarefree support. At positive sites its difference is exactly
$$
F_Y(n)-F_Y(n-1)=\mathbf 1_{\gcd(n,L)=1}-\sum_{k\mid L}\frac{\mu(k)}{k}.
$$
Each difference has magnitude at most one and tends to $\mathbf 1_{n=1}$. At fixed $Y$ the primitive $F_Y$ is bounded. Discrete summation by parts applied to the annihilator $w$ gives
$$
\sum_{m\ge1}T_w(m)\big(F_Y(m)-F_Y(m-1)\big)=0.
$$
If $T_w$ is summable, dominated convergence gives $T_w(1)=0$. The faithful-witness identity then forces the residual to vanish. The reciprocal term always satisfies
$$
\sum_m |T_{Br_P}(m)|
\le\sum_n n q(n)\frac{|r_P(n)|}{n+1}
\le\sum_n q(n)|r_P(n)|<\infty.
$$
The remaining hypothesis is exactly the one on $T_d$. For the prefix criterion, the checked Abel summation argument is in `QSignedPhysicalPrefix.lean`.

The order of the sums matters. The scalar sequence $v(n)=(-1)^n n^{1/3}$ belongs to $L^2(Q)$. Its signed tails are $O(m^{-5/3})$ by the alternating-series estimate, whereas its absolute power moments in (A) diverge for $\alpha\ge2/3$. Conversely, $v(n)=1$ has finite absolute power moments at every $\alpha<1$ and signed tails comparable to $1/m$. These examples compare the hypotheses on the ambient space.

## Positive prime tests

For $0<a\le1$, choose primes $j+1<p_j\le 2(j+1)$ and set $h(j)=(j+1)^{a-1}$. At stage $J$ put the coefficient $h(j)-h(j+1)$ at $p_j$ for $j<J$, and the remaining coefficient $h(J)$ at $p_J$. The resulting nonnegative sum $U_J(n)$ of remainders $n\bmod p_j$ satisfies
$$
n^a\le U_J(n)\quad(1\le n\le J+1),\qquad
0\le U_J(n)\le \frac{2}{a}n^a\quad(n\ge1).
$$
For the lower bound the terms telescope starting at $j=n-1$. For the upper bound use $n\bmod p_j\le2\min(n,j+1)$ and $a\sum_{k=1}^n k^{a-1}\le n^a$. A prime-orthogonal charge $b$ satisfies $\sum b_n U_J(n)=0$. The exact identity $\sum |b_n|U_J(n)=2\sum(\epsilon b_n)^+U_J(n)$, where $\epsilon=1$ or $-1$, yields
$$
\sum |b_n|n^a\le\frac4a\sum(\epsilon b_n)^+n^a
$$
whenever the right side is finite. Apply this to $w$. The charge of $Br_P$ has finite absolute first moment, so the finiteness implication transfers to $d$. The quantitative constant above applies directly to the annihilator.

## A power rate for the note's canonical exact heads (paper proof)

Assume $\zeta$ is zero-free in $\Re z>\theta$, where $1/2\le\theta<1$. For $\theta<\alpha<1$ and $0<\delta<\alpha-\theta$, the exact heads obey
$$
\sup_{n\ge1} n^{-\alpha}|1-E_N(n)|\ll_{\theta,\alpha,\delta}N^{-\delta}.
$$
The heads are legal when $N+1$ is prime. Choose $\theta<c<\sigma<\alpha$ with $\sigma-c>\delta$. Put $U_N(z)=\sum_{k\le N}\mu(k)k^{-z}$ and $R=1/\zeta$, with $R(1)=0$. Lemma 1 of Báez-Duarte (Balazard–Saias) bounds all tails $R(c+it)-U_j(c+it)$ for $j\ge N$ by $O_\eta((1+|t|)^\eta)$ for every fixed $\eta>0$. Summation by parts against the decreasing real weights $k^{-(\sigma-c)}$ gives
$$
|R(\sigma+it)-U_N(\sigma+it)|\ll_\eta N^{-(\sigma-c)}(1+|t|)^\eta.
$$
At $1$ the same argument gives $|m_N|=|U_N(1)|\ll N^{-(1-c)}$. The complete signed identity on $z=\sigma+it$ is
$$
T(1-E_N)(z)=\frac{\zeta(z)}z\left[R(z)-U_N(z)+(N+1)^{1-z}m_N\right],
\qquad T f(z)=\int_1^\infty f(\lfloor x\rfloor)x^{-z-1}\,dx.
$$
The assumption on $\zeta$ gives $|\zeta(\sigma+it)|\ll_\eta (1+|t|)^\eta$ on this interior line, as in equation (6) of the note. Choose finite $p\ge2$ with $\sigma+1/p\le\alpha$, then take $2\eta<1/p$. The transform has $L^{p/(p-1)}(dt)$ norm $O(N^{-(\sigma-c)})$. Inverse Hausdorff–Young in $\log x$ gives the same order for the $L^p(dx/x)$ norm of $x^{-\sigma}(1-E_N(\lfloor x\rfloor))$. Integration over a single cell $[n,n+1)$ bounds the coordinate by $O(n^{\sigma+1/p}N^{-(\sigma-c)})$.

Pairing the legal heads with $w$ proves (A). The checked positive-test argument allows a moment on either sign of $d$ and hence a pointwise $O(n^\beta)$ bound on either sign for $\beta<1-\theta$. The external all-moduli boundary $87338196661320751993/10^{20}$, specialized at modulus one, permits $\beta=0.1266$. This last implication combines the external result and the paper argument with the internal moment comparison.

## Cofinal one-sided moments (original derivation)

Let $d=f_Q-f_P$ be the physical displacement in the attached note, and put
$$
H(X)=\min_{\sigma\in\{-1,1\}}\sum_{n\le X}\frac{(\sigma d(n))_+}{n},\qquad x_+=\max(x,0).
$$
It suffices that $H(X)\le C(\log X)^B$ along any unbounded sequence of integers, for some fixed $B,C\ge0$. The sign may change with the cutoff. More generally, suppose $|M(t)|\ll t e^{-a\Phi(t)}$, where $a>0$ and $\Phi(t)=(\log t)^{3/5}(\log\log t)^{-1/5}$ for large $t$. Then
$$
 \liminf_{X\to\infty}\frac{\log(2+H(X))}{\Phi(X)}<2^{-3/5}a
 \quad\Longrightarrow\quad \mathrm{RH}.
$$

**Proof.** Write $Z=\zeta(2)$, $w=Br_P-d$, $b_n=w(n)/(Zn^2)$, $m=\sum b_n$ and $C_w=\|w\|_Q/\sqrt Z$. Define $S_\sigma(X)=\sum_{n\le X}n(\sigma b_n)_+$. Since $Br_P(n)=r_P(n)/(n+1)$, the positive-part Lipschitz inequality gives
$$
 \left|Z S_\sigma(X)-\sum_{n\le X}\frac{(-\sigma d(n))_+}{n}\right|
 \le\sum_{n\ge1}\frac{|r_P(n)|}{n(n+1)}<\infty .
$$
Cauchy–Schwarz also gives $\sum_{n>X}|b_n|\le C_w/\sqrt X$. Orthogonality of $w$ to each prime atom gives the exact equality $\sum b_n(n\bmod p)=0$. For the canonical legal head $E_N$ with $N+1$ prime, set $D_N=1-E_N$. Then $m=\sum b_nD_N(n)$, $D_N(n)=0$ on $1\le n\le N$, and $|D_N(n)|\le3N$ everywhere.

Choose integers $N<Y\le X$ and $\delta\ge0$ with $|D_N(n)|\le\delta n$ for $n\le Y$. Put $L=\lceil\log_2(X/Y)\rceil$. By Bertrand's postulate choose primes $Y<q\le2Y$ and $2^{k+1}Y<p_k\le2^{k+2}Y$ for $0\le k<L$. Form
$$
 T(n)=\delta(n\bmod q)+\sum_{k<L}\frac{3N}{2^kY}(n\bmod p_k).
$$
For $n\le Y$ the first residue equals $n$. On $2^kY<n\le2^{k+1}Y$ the $k$-th term exceeds $3N$. Thus $T\ge |D_N|$ through $X$, while everywhere $T(n)\le (\delta+6N/Y)n$ and $T(n)\le2\delta Y+12NL$. The exact identity $\sum |b_n|T(n)=2\sum(\sigma b_n)_+T(n)$, followed by the complete tail bound, yields
$$
 |m|\le 2(\delta+6N/Y)\min_\sigma S_\sigma(X)
       +(4\delta Y+24NL+3N)C_w/\sqrt X. \tag{1}
$$

For all-log savings, fix $K>B$ and use $|M(t)|/t\ll(\log t)^{-K-2}$. The Abel tail formula for $m_N=\sum_{k\le N}\mu(k)/k$ gives $|m_N|\ll(\log N)^{-K-1}$. If $N<n\le Y$, write $J=\lfloor n/(N+1)\rfloor$. The exact defect is $\sum_{j\le J}M(n/j)+J((N+1)m_N-M(N))$. Since $n/j\ge N$, this proves
$$
 \frac{|D_N(n)|}{n}\le \bigl(2+\log(Y/N)\bigr)\sup_{t\ge N}|M(t)|/t+|m_N|.
$$
Take $N=p-1\asymp \sqrt X/(\log X)^2$ by Bertrand and $Y=\lceil N(\log N)^K\rceil$. Then $Y<X$ eventually, $\delta\ll(\log N)^{-K}$, $\delta Y=O(N)$, and $L=O(\log X)$. Both terms in (1) tend to zero along the chosen cutoffs.

For the VK estimate, choose $0<a'<a$ and use $Y=\lceil N e^{a'\Phi(N)}\rceil$ with the same $N$. Abel summation gives $|m_N|\ll e^{-a''\Phi(N)}$ for every $a''<a$. Indeed for $a'<a''<a$ the residual tail integral after extracting $e^{-a''\Phi(N)}$ is bounded by $\int^\infty e^{-(a-a'')\Phi(e^v)}\,dv<\infty$. The defect estimate now gives $\delta\ll e^{-a'\Phi(N)}$. The far term in (1) tends to zero as before. Since $\Phi(N)/\Phi(X)\to 2^{-3/5}$, choose $a'$ and cutoffs on which the near term tends to zero. In either case $m=0$. The faithful-witness identity gives $r_Q=0$, hence RH.

The same proof uses the project's unconditional $\Psi(t)=((6+\log t)\log(6+\log t))^{1/11}$ with threshold $2^{-1/11}a_0$, for any coefficient $a_0>0$ in its ordinary Mertens estimate. The proof above uses dyadic prime tests. The Lean proof below gives the polylogarithmic and VK implications by a different finite construction. [Exact floor identity](https://github.com/Cnoack3/RiemannResearch/blob/434b3b19364a2ffbb4fb9ea7e3114e0db2557182/RiemannResearch/RH/CanonicalMobiusWindowCancellation.lean) · [Unconditional Mertens estimate](https://github.com/Cnoack3/RiemannResearch/blob/434b3b19364a2ffbb4fb9ea7e3114e0db2557182/RiemannResearch/NumberTheory/PrimeNumberTheorem/MertensStretchedDecay.lean) · [Faithful witness](https://github.com/Cnoack3/RiemannResearch/blob/434b3b19364a2ffbb4fb9ea7e3114e0db2557182/RiemannResearch/RH/QSquarefreeDisplacementRigidity.lean).


## Cofinal harmonic prefixes in Lean

For the actual projection displacement let
$$
 H(X)=\min_{\sigma\in\{-1,1\}}\sum_{n=1}^X\frac{\max(\sigma d(n),0)}{n}.
$$
A cofinal bound means that every starting cutoff has a later good cutoff. Both the cutoff and the sign can depend on the starting point. The infrequent good cutoffs suffice because the estimates control a single scalar, the mean of the faithful witness.

| Lean declaration | Exact scope |
|---|---|
| `riemannHypothesis_of_cofinal_harmonic_polylog` | For fixed real $B,C\ge0$, cofinally $H(X)\le C(\log X)^B$ implies Mathlib RH. The all-logarithmic Mertens estimate is proved in the repository. |
| `residual_zero_iff_fixed_cofinal_harmonic_polylog` | The same cofinal bound, for each fixed $B,C\ge0$, is equivalent to vanishing of the actual squarefree residual. |
| `minimumHarmonicPrefix_div_log_tendsto_of_not_RH` | If RH fails, $H(X)/(\log X)^B\to+\infty$ for every fixed $B\ge0$. This is a limit along all integer cutoffs. |
| `riemannHypothesis_iff_fixed_cofinal_harmonic_polylog` | The converse from RH uses the repository's explicit Báez-Duarte approximation input. Bagchi's Remark 8 gives the corresponding published squarefree result. |
| `riemannHypothesis_of_liminf_vk_harmonic_prefix` | With the ordinary Mertens input $\lvert M(x)\rvert\le Cxe^{-a\Phi(x)}$ eventually, $a>0$, the extended lower limit of $\log(2+H(X))/\Phi(X)$ below $2^{-3/5}a$ implies RH. |
| `riemannHypothesis_of_leeLeong_liminf_harmonic_prefix` | The same conclusion uses Lee and Leong's printed estimate as the named Lean proposition `LeeLeongMertensEstimate`. |
| `minimumHarmonicPrefix_div_sqrt_tendsto_zero` | The actual displacement satisfies $H(X)=o(\sqrt X)$ unconditionally. The proof also bounds the full absolute harmonic prefix of every complete-Q vector. |
| `exists_ordinary_mertens_rate_and_sharp_cofinal_stretched_RH` | Lean supplies ordinary Mertens constants $a_0>0$ and $C\ge0$ and the displacement implication at the corresponding threshold $2^{-1/11}a_0$. The profile is $\Psi(X)=((6+\log X)\log(6+\log X))^{1/11}$. The project proves the ordinary Mertens input internally. |

The proof begins with the complete identities
$$
 m=\sum_n b_nD_N(n),\qquad 0=\sum_n b_n(n\bmod p).
$$
Here $w=Br_P-d$, $b_n=q(n)w(n)$, $m=\langle1,w\rangle_Q$, and $D_N=1-E_N$ at positive sites. The first equality holds for legal Möbius heads, the second for every prime. Smoothing gives a finite constant $S$ with $\sum_{n\le X} n(-\sigma b_n)_+\le S+H(X)/\zeta(2)$ when $\sigma$ realizes the minimum. Write $T_w(X)=\sum_{n>X}|b_n|$. The complete-Q norm gives $T_w(X)\le (\lVert w\rVert_Q^2+2/\zeta(2))/\sqrt{X+1}$.

For the polylogarithmic implication it suffices to use a single balanced prime probe at each legal head. The internal Mertens theorem gives, for every natural $A$, every sufficiently large $N$, and every site $n$,
$$
 |D_N(n)|\le n/(6+\log N)^A,\qquad |D_N(n)|\le 3N.
$$
Move a good cutoff down to $k^8$, choose a legal head $N\in[k,2k]$, and choose a prime between $k^4$ and $2k^4$. Monotonicity of both harmonic masses and comparability of the logarithms preserve the bound. The three terms in the witness estimate are then bounded by a constant times $(1+H(k^8))/(6+\log k)^A$, $(6+\log k)^{-A}$, and $1/k$. Taking $A>B$ gives $m=0$.

For the VK coefficient, a finite positive mixture of balanced prime remainders uses the decreasing weights $h(j)=\min(\delta,K/(j+1))$, where $|D_N(n)|\le\min(\delta n,K)$, $K=3N$. For every $X$ it yields
$$
 |m|\le 2\delta(S+H(X)/\zeta(2))+K(1+2\mathcal H_{X+1})T_w(X),\qquad
 \mathcal H_j=\sum_{i=1}^j\frac1i.
$$
Choose $X^\theta\le N\le4X^\theta$ with $0<\theta<1/2$. The far term is $O(X^{\theta-1/2}\log X)$. If the ordinary Mertens estimate has coefficient $a$, the global slope is eventually at most $e^{-c\Phi(N)}$ for each $0<c<a$. The comparison $\Phi(N)\ge\theta^{3/5}\Phi(X)$ gives every coefficient below $2^{-3/5}a$. Lean uses an extended nonnegative real lower limit so that growth to positive infinity has its usual meaning.

The arithmetic transfer also gives an estimate uniform in both the head and the site. Suppose $N\ge1$, $0<\varepsilon\le1$, $\varepsilon(1+\log(1/\varepsilon))\le1/2$, and $|M(y)|\le\varepsilon y$ for every $y\ge N$. The exact jump $M(p)-M(p-1)=-1$ at a Bertrand prime $N<p\le2N$ gives $1/(4N)\le\varepsilon$. The finite harmonic window then gives $|D_N(n)|\le16\varepsilon(1+\log(1/\varepsilon))n$ for every site. This is `QMertensFirstMoment.abs_defect_le_pure_mertens_entropy_slope`.

The actual arithmetic obligation is to bound one signed harmonic prefix along arbitrarily large cutoffs. Walfisz's ordinary Mertens estimate and Lee and Leong's explicit version control the Möbius heads. The displacement bound is a separate hypothesis.

**Sources.** S. Gerhold, *Asymptotic estimates for some number-theoretic power series*, Acta Arith. 142 (2010), equation (2), records Walfisz's estimate. E. S. Lee and N. Leong, *New explicit bounds for Mertens function and the reciprocal of the Riemann zeta-function*, Theorem 1.1, gives the explicit ordinary Mertens input. B. Bagchi, Remark 8, gives the squarefree converse under RH. [Gerhold](https://fam.tuwien.ac.at/~sgerhold/pub_files/papers/mu_ogf.pdf) · [Lee–Leong](https://arxiv.org/html/2208.06141v5) · [Bagchi](https://arxiv.org/pdf/math/0607733).

### What squarefree legality alone can force

There is a squarefree-legal Hilbert vector $u$ with $|u(n)|=O(n^{1/4})$ for which **both** signed harmonic prefixes have order $X^{1/4}$ at every sufficiently large cutoff. This separates the extra projection equations for the actual displacement from its Hilbert norm, growth and radical jump identities. The argument below is a paper proof.

Put $Q_0=2^{16}$, choose $p_1=2$, and use Bertrand's theorem to choose primes recursively with $Q_0p_j<p_{j+1}\le 2Q_0p_j$. Write $g_p(n)=(n\bmod p)/p$, $a=1/4$, and set
$$
 u(n)=\sum_{j\ge1}(-1)^j p_j^a g_{p_j}(n).
$$
Splitting $\sum_{n\ge1}g_p(n)^2/n^2$ at $p$ bounds it by $3/p$. Hence $\sum_jp_j^a\|g_{p_j}\|_Q<\infty$ and $u$ belongs to the closure of the squarefree span. Splitting the pointwise series at $p_j=n$ in the bound $g_{p_j}(n)\le\min(1,n/p_j)$ gives $|u(n)|\ll n^a$ by geometric summation. Subtracting at two successive sites gives the exact identity
$$
 \Delta u(n)=\sum_j (-1)^j p_j^{a-1}-\sum_{p_j\mid n}(-1)^j p_j^a,
$$
so $\Delta u(n)=\Delta u(\operatorname{rad}n)$ for every $n\ge1$.

Take $p_j/2\le n\le3p_j/4$. The $j$-th term has magnitude at least $p_j^a/2$, while the sum of the absolute values of all other terms is at most
$$
 p_j^a\left(\frac1{Q_0^a-1}+\frac1{Q_0^{1-a}-1}\right)<\frac18p_j^a.
$$
The sign on the interval is $(-1)^j$, and its harmonic mass is at least a fixed positive multiple of $p_j^a$. If $p_j\le X<p_{j+1}$, the intervals for $p_j$ and $p_{j-1}$ supply opposite signs and $X<(2Q_0)^2p_{j-1}$. Thus each sign has harmonic mass $\gg X^a$. The matching upper bound follows from $|u(n)|\ll n^a$.

## Sources

- B. Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the Riemann hypothesis*, Remark 8, for squarefree closure under RH. <https://doi.org/10.1007/BF02829783>
- L. Báez-Duarte, *A strengthening of the Nyman–Beurling criterion for the Riemann hypothesis*, Lemma 1, equation (2.1), for the vertical estimate on twisted Möbius tails. <https://www.bdim.eu/item?id=RLIN_2003_9_14_1_5_0>
- QuasiRiemannTracker, merged all-moduli Dirichlet proof, PR 102, for the explicit half-plane. <https://github.com/GTimG/QuasiRiemannTracker/pull/102>

## Open obligations

For the actual $d$, prove the signed-tail summability, the signed-prefix summability, a sufficient one-sided moment, or its required growth estimate. A full project formalization of the zero-free-half-plane to exact-head power rate also remains open.

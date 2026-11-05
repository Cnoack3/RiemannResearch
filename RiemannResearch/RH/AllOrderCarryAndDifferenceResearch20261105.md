# Squarefree carries of arbitrary order and the physical increments of the displacement

The proposed inequality for the **limiting** displacement is
$$
\boxed{\quad \sup_j\sum_{L_{M_j}\le n<L_{M_{j+1}}}\frac{|d(n)|^8}{n^2}<\infty,\qquad L_M=\operatorname{lcm}(1,\ldots,M).\quad}
$$
Take strictly increasing distinct LCM endpoints. Here $d=f_Q-f_P$ is the difference of the two projections of the constant $1$ onto the closed squarefree span $V$. Both use $g_m(n)=(n\bmod m)/m$, with $Q(n)=1/[Zn^2]$, $Z=\zeta(2)$, and $P(n)=1/[n(n+1)]$. Anchor $d,d_N$ and the uncentered atoms at zero. Centered periodic packets retain their periodic value at zero. At stage $N$ the largest permitted conductor is $N+1$, and $d_N=f_{Q,N}-f_{P,N}$. The separate aligned finite-stage target is $\liminf_N\sum_{n\le N}|d_N(n)|^8/n^2<\infty$.

The block bound implies every physical moment of order $0<q<8$. Indeed its $j$th contribution is at most $C^{q/8}(2/L_{M_j})^{1-q/8}$ by Hölder, and consecutive strict LCM endpoints at least double. The resulting RH argument uses the conjugate-exponent approximation specified in [the LCM criterion](QLcmDisplacementCriterion.lean). The paper input uses J. Lee's published approximation and a strict zero-free margin reported in B. Liu's preprint. The project's eighth-moment route retains its approximation hypothesis. The increment and one-sided harmonic criteria below use the project's existing Mertens-based implications directly. [Lee's result as recorded by Báez-Duarte](https://arxiv.org/pdf/math/0011254) · [Liu, Theorem 27.1, preprint](https://arxiv.org/html/2610.12234v2) · [Bagchi, squarefree criterion](https://arxiv.org/abs/math/0607733)

## 1. Consequence of the proposed increment limit

Put $x_n=d(n)-d(n-1)$ and $b_m=\sum_{a\mid m}\mu(m/a)x_a$. The existing Lean radical recurrence gives $x_n=x_{\operatorname{rad} n}$ for $n\ge2$. Hence $x_{r^k}=x_r$ for every $r\ge2$, $k\ge1$. **If $x_n\to0$ in the ordinary physical index, then $x_r=0$ at every $r\ge2$.** Writing $c=d(1)$, this gives $d(n)=c$ for all $n\ge1$ and $b_m=c\mu(m)$, including $b_1=c$. Indeed the sole surviving jump is at $1$. Boundedness of the actual $d$ forces the limiting residual to vanish, and hence $c=0$ and RH follows. Even an unspecified finite limit forces this conclusion because $d(n)/n\to0$. [Existing Lean implication from unscaled differences](QSquarefreePrimeLocalTests.lean). Hilbert membership gives $d(n)/n\to0$ and $x_n/n\to0$; the decay of the unscaled $x_n$ remains an independent premise. [Radical recurrence](QSquarefreeDisplacementRegularity.lean) · [Bounded-displacement criterion](QSquarefreeDisplacementRigidity.lean)

One-sided decay suffices as well. If $\limsup x_n\le0$, recurrence gives $x_n\le0$ for every $n\ge2$. Then $d$ is nonincreasing and one strict sign support is finite, so the repository's sign-count theorem gives RH. Reverse all signs for $\liminf x_n\ge0$. Another sufficient premise permits any fixed finite exceptional set of primes $S$. If $x_n\to0$ on integers with a prime divisor outside $S$, all other possible nonzero jumps occur on $S$-smooth numbers, with amplitudes in a finite set by recurrence. There are at most $\prod_{p\in S}(1+\log n/\log p)$ such numbers through $n$. The resulting polylogarithmic displacement satisfies the established Mertens criterion. [Sign-count criterion](QDisplacementSignCounts.lean)

The stage index matters. At $N=2$ a rational interval computation on the two-conductor Gram system gives $0.0144<\Delta d_2(2^k)<0.0152$ for every $k\ge1$. The $Q$ and $P$ Gram entries were enclosed by rounding $10^5$ terms down at scale $10^{12}$, with an upper allowance $10^5/10^{12}+10^{-5}$ per entry. Thus decay cannot be inferred by holding this first nontrivial stage fixed and sending the site to infinity.

## 2. A single integer carry with any number of prime factors

For squarefree $m=\prod_{p\in S}p$, choose integers $a_p$ with $\sum_{p\mid m}a_p(m/p)=1$. Reduction modulo $m$ gives the identity
$$
g_m=\sum_{p\mid m}a_pg_p-C_m,\qquad C_m=\left\lfloor\sum_{p\mid m}a_pg_p\right\rfloor .
$$
For example, with $\{x\}=x-\lfloor x\rfloor$,
$$
g_{210}=\{g_2+g_3-2g_5-3g_7\},\qquad
g_{2310}=\{g_2-g_3-2g_5+g_7+g_{11}\}.
$$
The signed reciprocal sums are $1/210$ and $1/2310$. Wolfram checked the fractional-part identities at every site of both periods.

For $r=|S|$ let $u_p=[(m/p)^{-1}]_p/p\in(0,1)$. Their sum is $k+1/m$. Subtract $1$ from the $k$ largest values to obtain $w_p=a_p/p$ in an interval of length at most one, of mean $1/(rm)$. This gives
$$
\sum_{p\mid m}w_p^2\le \lfloor r^2/4\rfloor/r+1/(rm^2).
$$
Indeed the sum of squared deviations from the mean is convex on each translated unit cube. At its vertices the squared deviation sum is $s(r-s)/r$ for $s$ upper coordinates. The resulting bounds for four and five primes are $1+1/(4m^2)$ and $6/5+1/(5m^2)$.

Write $E_N=\|1-f_{P,N}\|_P^2$ and $e_s=E_N-Zs\langle g_s,d_N\rangle_Q$. For each included prime and product, the exact matched response is
$$
Z\langle C_m,d_N\rangle_Q=(e_m-e_*)/m-\sum_{p\mid m}w_p(e_p-e_*)
$$
for **any** anchor $e_*$. Every common term cancels since $\sum w_p=1/m$. Moreover $C_m(n)=0$ for $n<\min_{p\mid m}p$. The matched equation $d_N=\Pi_N B(1-f_{P,N})$, $Bf(n)=f(n)/(n+1)$, confines its forcing to that physical tail. This controls a row for each product. To reconstruct the displacement the signed rows must be solved together.

## 3. Each pure squarefree interaction has a signed prefix

Set $F_D=g_D-(D-1)/(2D)$ and use the counting probability on each finite projection of the infinite CRT product $\prod_p\mathbb Z/p$. Conditioning $F_D$ on the residue modulo $s\mid D$ gives $(s/D)F_s$. Accordingly
$$
 I_D=\frac1D\sum_{s\mid D}\mu(D/s)s F_s,\qquad F_D=\sum_{1<q\mid D}(q/D)I_q .
$$
For squarefree $D>1$ integrating over any one of its prime coordinates annihilates $I_D$. Four primes give $4+6+4+1=15$ nonconstant interactions, and five give $5+10+10+5+1=31$. With $c_D(n)=\sum_{s\mid(D,n)}s\mu(D/s)$,
$$
 -D\Delta I_D(n)=c_D(n)=\prod_{p\mid D}(p\mathbf1_{p\mid n}-1)\qquad (n\ge1).
$$

Let $e(t)=\exp(2\pi i t)$. With $r_s=t\bmod s$ the exact prefix is
$$
\sum_{n=0}^{t-1}I_D(n)
=-\frac1{2D}\sum_{s\mid D}\mu(D/s)r_s(s-r_s)
=-\frac1{2D}\sum_{a\in(\mathbb Z/D)^\times}\left|\sum_{j<t} e(aj/D)\right|^2
\in[-D/8,0].
$$
The first equality sums a full period and a remainder. For the second, Parseval for $[0,t)$ modulo $s$ gives $r_s(s-r_s)$ for the sum of the squares over all nonconstant frequencies. Divisor inversion selects the primitive frequencies at $D$. Their total is at most $r_D(D-r_D)$. Equivalently the square sum is the positive semidefinite quadratic form $\sum_{i,j<t}c_D(i-j)$; the prime contrasts give a real Gram factorization. Partial summation on $D\mid A,B$, $0<A<B$, gives
$$
 -\tfrac D8(A^{-2}-B^{-2})\le\sum_{A\le n<B}I_D(n)n^{-2}\le0 .
$$
A second partial summation yields a leading term. If $v_n=n^{-2}-(n+1)^{-2}$, the mean of the signed prefix over one period is $-J_2(D)/(12D)$ by the frequency formula; its centered primitive has magnitude at most $D^2/8$, by periodicity and the first bound. Consequently
$$
\left|\sum_{A\le n<B}I_D(n)n^{-2}+\frac{J_2(D)}{12D}(A^{-2}-B^{-2})\right|\le\frac{D^2}{8}(v_A-v_B).
$$
These estimates concern signed first moments. The Haar variance is $J_2(D)/(12D^2)=\prod_{p\mid D}(1-p^{-2})/12\ge1/[12\zeta(2)]$, by orthogonality and inversion of $\operatorname{Var}(F_D)=(1-D^{-2})/12$. Therefore the eighth moment of the individual pure interaction has a positive lower bound even at high order. For even $D$, all primitive frequencies are odd, so the prefix attains its minimum $-J_2(D)/(6D)$ at $D/2$. The values follow either from the divisor triangles or the primitive cosecant-square sum.

| $D$ | Prime count | Haar variance (exact, Wolfram) | Minimum prefix (exact, Wolfram) |
|---:|---:|---:|---:|
| 210 | 4 | $64/1225$ | $-768/35$ |
| 2310 | 5 | $1536/29645$ | $-18432/77$ |

The repository also proves vanishing linear log-test moments of its continuous Pareto packet through degree $\omega(D)-2$. This kills degrees $0,1,2$ at four primes and $0,1,2,3$ at five. [Pareto log moments](RamanujanOrdinaryMomentsProof.lean) · [Vaidyanathan, primitive-period Fourier spaces, IEEE Transactions on Signal Processing (2014)](https://doi.org/10.1109/TSP.2014.2331617)

## 4. What the signed sums of the actual charges control

The actual law satisfies $Q(p\mid n)=p^{-2}$, independently over distinct primes. This is independence of divisibility bits. For the periodic packets use their periodic value $I_D(0)$ at the backward-difference boundary. On these coordinates,
$$
 \mathbb E_Q|\Delta I_D(N)|^h=D^{-h}\prod_{p\mid D}\big[1-p^{-2}+(p-1)^h p^{-2}\big],\qquad h>0.
$$
In particular the second moment is $2^{\omega(D)}\varphi(D)/D^3$. Write $J_2(s)=s^2\prod_{p\mid s}(1-p^{-2})$. The jumps of the actual $d$ have an **infinite physical GCD expansion**
$$
 \boxed{\quad\mathbb E_Q|x_N|^2=\sum_{s\ {\rm squarefree}}J_2(s)
 \left|\sum_{s\mid m}\frac{b_m}{m^2}\right|^2.\quad}
$$
Here $s=1$ is included. To justify the exchange, $d\in L^2(Q)$ implies $\sum |x_n|^2/n^2<\infty$ by the shift estimate. For $\sigma>3/2$,
$$
 \sum_m |b_m|m^{-\sigma}\le\zeta(\sigma)\sum_n |x_n|n^{-\sigma}
 \le\zeta(\sigma)\sqrt{\zeta(2\sigma-2)}\left(\sum_n |x_n|^2/n^2\right)^{1/2}.
$$
Let $W_s=\prod_{p\mid s}(p^2\mathbf1_{p\mid N}-1)$ for squarefree $s$. Independence gives $\mathbb E_Q[W_s\mathbf1_{m\mid N}]=\mathbf1_{s\mid m}J_2(s)/m^2$ for squarefree $m$; the actual $b_m$ are supported there. Now use $x_N=\sum_{m\mid N}b_m$, absolute convergence at $\sigma=2$, and boundedness of fixed $W_s$. The normalized products form an orthonormal basis on the radical-measurable subspace by finite-coordinate approximation, so Parseval gives the formula. [Divisor basis](QDivisorWaveletDensity.lean) · [Balazard, Propositions 7 and 9, Springer](https://doi.org/10.1007/978-3-030-61887-2_3)

The integrated displacement uses **one fewer reciprocal power**. Put $A_s(H)=\sum_{s\mid m\le H}b_m/m$ and $R_s=sI_s+\varphi(s)/2=\sum_{a\mid s}\mu(s/a)a g_a$. Finite arithmetic identities give, for $1\le n\le H$,
$$
 x_n=A_1(H)+\sum_{2\le s\le H}A_s(H)c_s(n),\qquad
 d(n)=nA_1(H)-\sum_{2\le s\le H}A_s(H)R_s(n).
$$
Balazard's scalar theorem, already formalized in the Pareto realization, gives $A_1(H)\to0$ for every $L^2(Q)$ input by the Q/P transfer. For each **fixed** pair $L,t$ it removes the scalar from the finite translation formula, giving the naturally ordered limit
$$
d(L+t)-d(t)=\lim_{H\to\infty}\sum_{m\le H}b_m\left(
\mathbf1_{(L\bmod m)+(t\bmod m)\ge m}-(L\bmod m)/m\right).
$$
If $L=L_M$, every squarefree $m$ whose prime factors are at most $M$ drops out exactly. The cutoff may be chosen for the entire finite block by taking a maximum over its sites. This conclusion supplies no bound as the block moves.

At the matched stage $H=N+1$ the charges of $d_N$ are finitely supported and its scalar is exactly zero. Let $G_{sr}=\langle R_s,R_r\rangle_Q$ on the squarefree conductors $2\le r,s\le H$, and set $e_1=E_N$. The physical contrast normal equations are
$$
 Z\sum_r G_{sr} A_r(H;d_N)=\sum_{a\mid s}\mu(s/a)e_a,\qquad s>1.
$$
Indeed $d_N=-\sum_r A_r R_r$. Also $Z\langle R_s,d_N\rangle_Q=\sum_{a\mid s}\mu(s/a)(E_N-e_a)$ and $\sum_{a\mid s}\mu(s/a)=0$. This is a signed, coupled physical Gram system. The Haar diagonal weights and the $m^{-2}$ Parseval row do not replace it. [Matched physical normal equation](QSquarefreeFiniteDisplacement.lean)

## 5. A fixed nonconstant packet can diverge even in the legal closure (paper)

Fix squarefree $q>1$, including a product of four or five primes. Let $S_M$ contain $M\le m<2M$ such that $q\mid m$ and both $m,m+1$ are squarefree. Its asymptotic density is
$$
\rho_q=\prod_{p\mid q}(p-1)/p^2\prod_{p\nmid q}(1-2/p^2)>0.
$$
For a fixed finite prime cutoff $y$ containing the factors of $q$, CRT gives the truncated product. Larger prime squares eliminate at most $2M\sum_{p>y}p^{-2}+O(\sqrt M)$ sites by a union bound, since $p^2\le2M$ for an offending square. Take $M\to\infty$ followed by $y\to\infty$. [Dietmann and Marmon, squarefree twins, Bulletin of the London Mathematical Society (2014)](https://doi.org/10.1112/blms/bdu038)

For $M$ large define
$$
 F_M=|S_M|^{-1}\sum_{m\in S_M}[(m+1)g_{m+1}-m g_m].
$$
For $e\ge2$ the only charges of $g_e$ are $b_1=1/e$ and $b_e=-1$. Hence $A_q(H;F_M)=|S_M\cap[1,H]|/|S_M|$, a nonnegative step rising to one. Meanwhile $|F_M(n)|\ll M$. Each summand also equals $m(\lfloor n/m\rfloor-\lfloor n/(m+1)\rfloor)-\lfloor n/(m+1)\rfloor$. After extending the nonnegative difference to all $m\in[M,2M)$ and telescoping, the absolute numerator is bounded by $3M\lfloor n/M\rfloor$. Thus
$$
 |F_M(n)|/n\ll_q\min\{1/M,M/n\},\qquad
 |\langle F_M,F_L\rangle_Q|\ll_q(M/L)[1+\log(L/M)]\quad(L\ge M).
$$
For the second estimate split the sum at $M^2$ and $L^2$. On $M=2^j$ the Gram bound has summable diagonals, so $\|\sum_j u_jF_{2^j}\|_Q^2\ll_q\sum_j|u_j|^2$ for every finite sequence by $2|u_iu_j|\le|u_i|^2+|u_j|^2$. Hence $v=\sum_{j\ge j_0}j^{-1}F_{2^j}$ converges in $V$. Since every fixed $b_m$ is continuous on $L^2(Q)$, and only one bin can be partially cut, **$A_q(H;v)\sim\log\log H$**. This is a counterexample for general legal vectors. By uniform boundedness and Baire, the set of vectors in $V$ with unbounded packets at *every* squarefree $q>1$ is residual: for each $q$ the sets $\{v:\sup_H|A_q(H;v)|\le K\}$ are closed with empty interior; take the countable intersection of their complements. The special target-$1$ matched normal equations therefore matter for the actual $d$.

## 6. A sufficient one-sided charge estimate (paper)

Fix $\varepsilon\in\{-1,1\}$ and $c_m=(-\varepsilon b_m)_+$. Integer division gives the exact formula
$$
 d(tn)-t d(n)=\sum_{m\le tn}b_m\left\lfloor t(n\bmod m)/m\right\rfloor .
$$
Divide by $t$. Since $d(tn)/t\to0$ for fixed $n$ and the carry weight is between $0$ and $g_m(n)$ after division,
$$
 \varepsilon d(n)\le\sum_m c_m g_m(n)
 \le C(n)+n\sum_{m>n}c_m/m,\qquad C(y)=\sum_{m\le y}c_m.
$$
This uses a finite signed inequality and a bound by a nonnegative series. If $C(y)\ll(1+\log y)^E$, dyadic splitting bounds the tail by $\sum_{k\ge0}2^{-k}C(2^{k+1}n)\ll_E(1+\log n)^E$. Thus the positive harmonic prefix of $\varepsilon d$ is $O((1+\log X)^{E+1})$, which gives RH by the existing one-sided harmonic criterion. Only one sign of the actual charges needs this estimate. [Cofinal harmonic criterion](QCofinalDisplacementMoments.lean)

**Status.** The reciprocal scalar, radical recurrence, matched projection identity, and implications from boundedness or a one-sided harmonic bound are established repository results. The accompanying Lean modules extend the finite packet, matched carry and conditional increment calculations; their checked declarations are listed in the theorem catalog. The infinite physical Parseval identity, balanced coefficient bound, legal diverging-packet construction and polylogarithmic deduction above include their paper proofs. The unscaled increment premise, the one-sided charge estimate and the uniform moving-block inequality have not been established for the actual displacement.

# The aligned eighth moment of the two finite projections

The open inequality is
$$
\liminf_{N\to\infty} S_N<\infty,\qquad
S_N=\sum_{n=1}^N\frac{|f_{Q,N}(n)-f_{P,N}(n)|^8}{n^2}.
$$
Both fits project $1$ onto the full span of $g_m(n)=(n\bmod m)/m$ for squarefree $2\le m\le N+1$. Write $Z=\zeta(2)$, $Q(k)=1/(Zk^2)$, $P(k)=1/[k(k+1)]$, $d_N=f_{Q,N}-f_{P,N}$ and $r_N=1-f_{P,N}$. Distinguish $E_N=\|r_N\|_P^2$, $R_N=\|r_N\|_Q^2$ and $e_N=\|1-f_{Q,N}\|_Q^2$. The following estimates leave the displayed liminf open.

## Estimates after solving the projection equations

Let $u_{N,k}$ be the repository's ordered, $Q$-orthogonalized physical evaluation vectors. The index is the first possible physical site $k=1,\ldots,N+1$. A redundant vector is zero. Put
$$
D_N(n)=\sum_{k=1}^{N+1}\frac{|u_{N,k}(n)|^2}{(k+1)^2},
\qquad U_N=\sum_{n\le N}D_N(n)^4/n^2.
$$
Write $\Pi_N$ for the $Q$ projection onto the finite stage. The exact normal equation $d_N=\Pi_N B r_N$, with $Bf(n)=f(n)/(n+1)$, gives $\langle d_N,u\rangle_Q=\langle Br_N,u\rangle_Q$ for every stage vector. The repository's weighted Bessel inequality gives
$$
\sum_k(k+1)^2|\langle d_N,u_{N,k}\rangle_Q|^2\le R_N.
$$
Expanding $d_N$ in that basis and applying Cauchy–Schwarz gives $|d_N(n)|^2\le R_ND_N(n)$. Thus
$$
S_N\le R_N^4 U_N\le (9/8)^4 e_N^4 U_N.
$$
All three inequalities are unconditional. A cofinal bound for $e_N^4 U_N$ would suffice for the original question. All its inputs come from the single $Q$ Gram matrix and the $Q$ projection of $1$. [Lean declarations](QFiniteEighthReconstruction.lean)

A paper refinement separates the contribution of later basis vectors. On $2^j\le n<2^{j+1}$, let $v_j$ be the sum of the terms of the expansion of $d_N$ with onset $k\ge2^{3j/4}$. Set $a_k=\langle d_N,u_{N,k}\rangle_Q$ and $b_j=2^{3j/2}\sum_{k\ge2^{3j/4}}a_k^2$. Point evaluation and the Hilbert norm give
$$
\sum_{2^j\le n<2^{j+1}}|v_j(n)|^8/n^2\le64Z^4 b_j^4,
\qquad
\sum_j b_j\le(1-2^{-3/2})^{-1}\sum_k k^2a_k^2.
$$
For the first bound use $|v_j(n)|\le\sqrt Z\,n\|v_j\|_Q$ on six factors and sum the remaining square. For the second bound interchange the two nonnegative sums. Thus the eighth norm of the late contribution is bounded uniformly, since $R_N\le9e_N/8\le9/8$. An upper bound for the **early** contribution on those same shells suffices. This localizes the outstanding estimate after solving the Gram system.

## A sharper estimate using both projections

Let $K^\nu_n$ represent evaluation at site $n$ in the stage for the $\nu$ inner product. Define
$$
h_n=(Q/P)K^Q_n-K^P_n .
$$
For every stage vector $v$, its $P$ pairing with $h_n$ equals $v(n)-v(n)=0$. Consequently the P-orthogonal residual $r_N$ obeys the exact identity $d_N(n)=\langle r_N,h_n\rangle_P$. If $H_N(n)=\|h_n\|_P^2$ then
$$
 S_N\le E_N^4\sum_{n\le N}H_N(n)^4/n^2.
$$
For a fixed site the Cauchy–Schwarz factor $\sqrt{H_N(n)}$ is the norm of the functional on the full $P$-orthogonal complement. The actual residual is a particular vector in that complement. [Exact pairing, norm bound and conditional RH theorem](QFiniteParetoDualKernel.lean)

For numerical evaluation let $a_n=(g_m(n))_m$ and $G_w=\sum_k w(k)a_ka_k^t$. Use the unnormalized weights $\mu(k)=k^{-2}$ and $\nu(k)=k^{-3}$. Then $K_n^Q(k)=Z a_k^tG_\mu^{-1}a_n$. Orthogonality gives the exact matrix expression
$$
H_N(n)=a_n^t\left[G_\mu^{-1}(G_\mu+G_\nu)G_\mu^{-1}-G_P^{-1}\right]a_n .
$$
Here $\mu^2/P=\mu+\nu$. Subtraction of $G_P^{-1}$ removes the component within the Pareto stage. This matrix formula is a paper derivation using real arithmetic.

## Testing the estimates

The sums below use the unnormalized physical output weights $1/n^2$. $R_N$, $E_N$ and the evaluation vectors retain their respective probability normalizations. Values are floating-point diagnostics.

| $N$ | Actual $S_N$ | $U_N$ | $R_N^4 U_N$ | Matched kernel bound |
|---:|---:|---:|---:|---:|
| 20 | $1.37890\,10^{-15}$ | 0.19539 | $2.93377\,10^{-9}$ | $4.81070\,10^{-13}$ |
| 100 | $2.14277\,10^{-15}$ | 0.31736 | $6.50769\,10^{-10}$ | $1.42148\,10^{-13}$ |
| 200 | $4.14111\,10^{-15}$ | 0.39664 | $4.55263\,10^{-10}$ | $1.84742\,10^{-13}$ |
| 256 | $6.55955\,10^{-15}$ | 0.48032 | $4.04116\,10^{-10}$ | $2.51915\,10^{-13}$ |

For each Gram entry sum over residues $1\le r\le L=\operatorname{lcm}(a,b)$. The progression masses for $\mu$, $P$, $\nu$ are respectively $\psi_1(r/L)/L^2$, $[\psi((r+1)/L)-\psi(r/L)]/L$, and $-\psi_2(r/L)/(2L^3)$. Solve the two full Gram systems before evaluating the aligned head. Compute the ordered physical basis by Gram–Schmidt on the evaluation rows after whitening with the $Q$ Gram matrix. Wolfram independently reproduced the small-stage full-period values at 28-digit working precision, and the matched kernel bound at stage 20 at 32 digits. In the full scan through 256, the largest $S_N$ over $65\le N\le128$ occurred at $N=95$ and was $7.19\times10^{-14}$, larger than the four displayed sample values. For example, split the input at $T=10$ at $N=20$. Solving the truncated low- and high-conductor right-hand sides separately gave moments $4.4342\,10^{-11}$ and $3.7921\,10^{-11}$. Their combined fit had moment $2.0624\,10^{-15}$. The signs in the coupled system matter. The table gives no asymptotic upper bound.

## What the full Gram right-hand sides control

For every included conductor write $b_m=\langle g_m,d_N\rangle_Q$, $u_m=Zm b_m$. The exact signed deficit and the resulting individual and simultaneous bounds are
$$
E_N-u_m=\sum_{k\ge m}P(k)r_N(k)\frac{m\lfloor k/m\rfloor}{k},
\qquad |E_N-u_m|\le \|\mathbf1_{k\ge m}r_N\|_P/\sqrt m,
\qquad \sum_{m\ \mathrm{included}}|E_N-u_m|^2\le4E_N.
$$
The last inequality applies to any selection of included conductors. It follows from the discrete dual Hardy inequality applied with $a_k=r_N(k)/(k+1)$ and the triangular kernel $[1-(k\bmod m)/k]/k$. The kernel vanishes for $k<m$ and is bounded by $1/k$. Adjacent included rows additionally satisfy $m^2|u_m-u_{m+1}|^2\le H_m E_N$, where $H_m=\sum_{j\le m}1/j$. [Lean declarations](QFiniteForcingData.lean) · [E. T. Copson, J. London Math. Soc. (1927)](https://doi.org/10.1112/jlms/s1-2.1.9)

There is a quantitative obstruction to passing from an arbitrary small vector of scaled Gram data to a small eighth norm. Take $p\ge3$ prime with $p-1$ squarefree. Set $v_p=g_p-\Pi_{p-2}g_p$ and work at the aligned stage $N=p$. For odd such $p$, $p+1$ is divisible by 4, so $g_p$ is the last included atom. Every old Gram datum of $v_p$ vanishes. The new one is $\langle g_p,v_p\rangle_Q=\|v_p\|_Q^2$. The adjacent-conductor comparison and the exceptional jump at $p$ give
$$
 Zp^2\|v_p\|_Q^2\le2H_{p-1},
 \qquad S_p(v_p)^{1/8}\ge\frac{1}{3p^{1/4}}.
$$
Consequently the operator that reconstructs a stage vector from its scaled Gram data $\{Zm\langle g_m,v\rangle_Q\}_m$ has norm at least $p^{3/4}/(6H_{p-1})$ from Euclidean norm to the physical eighth norm on the stage head. Mirsky's theorem supplies arbitrarily large such primes on paper. The finite estimates are formalized. These test vectors differ from the matched displacements, which obey additional signed equations. [Lean declarations](QPrimeForcingObstruction.lean) · [Mirsky (1949)](https://www.jstor.org/stable/2305811)

## A finite lower bound for the actual eighth moment

For every integer $N\ge1$,
$$
 E_N\le \max\{(800/N)^{1/3}, (10\,4^8\,8^7S_N)^{1/9}\}.
$$
If $NE_N^3\ge800$, then $S_N\ge E_N^9/(10\,4^8\,8^7)$.

**Paper proof.** Write $E=E_N\le1$. Under the hypothesis $NE^3\ge 800$ choose a prime $p$ between $\lceil4/E\rceil$ and $2\lceil4/E\rceil$ by Bertrand. Thus $4/E\le p\le10/E$, $p\le N$, and $NE\ge8p^2$. Orthogonality under both measures gives
$$
 Zp\langle g_p,d_N\rangle_Q=E-\mathbb E_P\left[r_{P,N}(n)\frac{p\lfloor n/p\rfloor}{n}\right]
 \ge E-\sqrt{E/p}\ge E/2.
$$
Indeed the multiplier is between zero and one, supported on $n\ge p$, a set of $P$-mass $1/p$. From $d_N=\Pi_N B r_{P,N}$, $\|B\|\le1/2$, and $ZQ\le2P$, one gets $\sqrt Z\|d_N\|_Q\le\sqrt{E/2}$. Since $0\le g_p\le1$ and $\sum_{n>N}n^{-2}\le1/N$, the absolute raw pairing from $n>N$ is at most $\sqrt{E/(2N)}\le E/(4p)$. The raw pairing on $n\le N$ is therefore at least $E/(4p)$. Splitting at $p$ and using $\sum_{1\le n<p} n^{-6/7}\le7p^{1/7}$ gives $\sum g_p(n)^{8/7}/n^2\le8/p$. Hölder implies $E/(4p)\le S_N^{1/8}(8/p)^{7/8}$. Taking eighth powers and using $p\le10/E$ proves the estimate.

The same pairing and $\|g_p\|_Q^2\le2/(Zp)$ give $\|d_N\|_Q^2\ge E_N^3/(80Z)$. Burnol's Theorem 1.3 (*Advances in Mathematics* 170 (2002), 56–70, https://doi.org/10.1006/aima.2001.2066), applied to the squarefree trial space as a subspace of the unrestricted dilation space, gives $E_N\gg1/\log(N+1)$. Consequently, unconditionally,
$$
 \|d_N\|_Q^2\gg(\log(N+1))^{-3},\qquad S_N\gg(\log(N+1))^{-9}.
$$
The lower estimate restricts rates of decay. It does not preclude a bounded liminf. The same Burnol input and $|ZA_{N,T}-E_N|\le\sqrt{E_N/(T+1)}$ yield $ZA_{N,T}/E_N=1+O(\sqrt{\log(N+1)/(T+1)})$, so the retained high-conductor scalar is eventually positive when $T/\log N\to\infty$.

## Two other sufficient tests

* A fixed number of sites can be omitted on each good stage. They may move with $N$ and their contributions can have arbitrary size. Equivalently, for the resulting RH implication it suffices that $\liminf_N\sum_{n\le N}\min\{1,|d_N(n)|^8/n^2\}<\infty$. Passing to fixed physical heads proves summability of the capped series of the limit. Its terms therefore tend to zero, so eventually the cap is inactive. Both criteria still have the arithmetic premise below. [Capped and trimmed tests](QFiniteEighthCapped.lean)
* For each fixed positive squarefree site $k$, including 1, it suffices to bound the aligned eighth moments of $K^Q_{N,k}$ on a cofinal set of stages. Both that set and the bound may depend on $k$. The difference of the limiting projection of the site representer and the site representer itself is an $L^8$ annihilator. Subcritical approximation makes its mean zero and hence the limiting residual vanishes at $k$. The squarefree-radical identity for its first differences then gives zero at all sites by strong induction. [Squarefree column criterion](QFiniteColumnEighth.lean)

## The centered input and the signed inverse Gram response

Put $r_N=1-f_{P,N}$. The two normal equations give $\Pi_N r_N=\Pi_N B r_N=d_N$.
Consequently $\Pi_N[(1+a)B-aI]r_N=d_N$ for every real $a$. Choose $a=(2T+3)^{-1}$ and
let $u_{N,T}=\Pi_N[(1+a)B-aI]({\bf1}_{n\le T}r_N)$. Above $T$ the multiplier
ranges from $a$ at $T+1$ to $-a$ in the limit. These two endpoints also give
the minimax lower bound over every affine shift. Lean proves
$$
 (2T+3)\|d_N-u_{N,T}\|_Q\le\|{\bf1}_{n>T}r_N\|_Q .
$$
If $T_N\to\infty$ and $N^6\le(2T_N+3)^8$, then the aligned eighth moment of the
error tends to zero. Finite Minkowski gives a vanishing difference of the two
eighth roots and an equivalence of their cofinal boundedness tests. One possible
choice is $T_N=\lceil N^{3/4}/2\rceil$. On the retained sites the centered
source is $B[(1-an)r_N]$ with $0\le 1-an\le1$, so it uses the same Schur matrix.
[Centering and aligned equivalence](QFiniteEighthCentered.lean)

For $T<d_0\le N+1$ squarefree, use the anchor $d_0g_{d_0}$ and low contrasts
$d g_d-d_0g_{d_0}$ for squarefree $2\le d\le T$. Write $b$ for the original
truncated right-hand side in this basis and $Z=\zeta(2)$. Its signed entries are
$$
 Zb_0=\sum_{k\le T}P(k)r_N(k),\qquad
 Zb_d=-\sum_{d\le k\le T}P(k)r_N(k)\frac{d\lfloor k/d\rfloor}{k}.
$$
The anchor takes Hardy row 1. Each low contrast takes its own row, yielding
$\sum_i(Zb_i)^2\le4\sum_{k\le T}P(k)r_N(k)^2\le4$. For any cutoff $D_N\to\infty$
the squared mass of the contrast coefficients indexed by $d>D_N$ tends to zero,
uniformly with respect to the choice of the retained heads and anchors. The
proof uses the actual residual tail. [Signed input estimates](QFiniteSchurForcingData.lean)

Let $G$ be the full screened Schur Gram matrix and $e(n)$ the physical
evaluation vector of that screened family at $n$. The original truncated
output obeys the signed identity $\widetilde d_{N,T}(n)=(e(n)^\top G^{-1})b$.
Its complete Hilbert energy satisfies
$Z\,b^\top G^{-1}b=Z\|\widetilde d_{N,T}\|_Q^2\le1/2$.
The same row $e(n)^\top G^{-1}$ applies after the input taper. In either
case $Z^2|u(n)|^2\le4\|e(n)^\top G^{-1}\|_2^2$. Write $\ell(n)=e(n)^\top G^{-1}$.
Keeping the signed pairing gives the sufficient condition
$$
 \exists C<\infty,\quad
 \sum_{n\le N}\frac{|\ell(n)b_{N,T_N}|^8}{n^2}\le C
 \quad\text{for arbitrarily large legal stages }N.
$$
Here $T_N$ can tend to infinity arbitrarily slowly. This criterion still uses the
physical $L^{8/7}$ approximation. [Inverse-Gram identities and signed RH criterion](QFiniteSchurEighth.lean)

### Why an estimate for arbitrary Schur inputs fails

Let $R_{N,T,d_0}=\sum_{n\le N}\|\ell(n)\|_2^8/n^2$. Take low squarefree
conductors $q<p\le T$, with $p$ prime. The functional
$x\mapsto x(1)-x(p)+x(p-1)$ annihilates the screened anchor and every low
basis vector except the $p$ contrast, on which it equals $p$. Consequently,
on the unit input supported at $p$, one of those three evaluations has
absolute value at least $p(G^{-1})_{pp}/3$. The minimum-vector variational
identity gives
$$
 (G^{-1})_{pp}\,\|p g_p-q g_q\|_Q^2\ge 1,\qquad
 R_{N,T,d_0}\, 3^8\|p g_p-q g_q\|_Q^{16}\ge p^6 .
$$
The latter inequality holds for every $N\ge T$ and $d_0>T$. Telescoping the
adjacent-conductor harmonic estimate gives
$\|p g_p-q g_q\|_Q\le(p-q)\sqrt{2(1+\log p)/Z}$.
Elementary prime distribution supplies arbitrarily large pairs with $p-q\le p^{1/4}$.
The lower bound then grows at least as a constant times $p^2/(1+\log p)^8$.
After fixing a pair the estimate holds for every $T\ge p$.
Thus this row sum diverges along every diverging retained head, uniformly
over the larger stages and anchors. The counterexample uses a free Schur input.
The open inequality concerns only the specific $b_{N,T}$ above, which consists
of signed averages of one Pareto projection residual.
[Finite obstruction and divergence](QFiniteSchurRowObstruction.lean)

### A test that uses both projections

Let $K_N(n,\cdot)$ represent evaluation at $n$ on the stage in $L^2(Q)$.
In $L^2(P)$ form
$$
 U_{N,T,n}(k)={\bf1}_{1\le k\le T}\frac{K_N(n,k)}{k},\qquad
 D_{N,T,n}=U_{N,T,n}-\Pi_N^P U_{N,T,n}.
$$
Moving the two orthogonal projections across their respective inner products gives
$$
 Z\widetilde d_{N,T}(n)
 =\langle r_N,D_{N,T,n}\rangle_P
 =\langle1,D_{N,T,n}\rangle_P
 =\mathbb E_P D_{N,T,n}.
$$
Write $E_N=\|r_N\|_P^2$. Cauchy–Schwarz now retains the actual squared projection
error as well as the best Pareto approximation to every kernel. In particular,
$$
 Z^8\sum_{n\le N}\frac{|\widetilde d_{N,T}(n)|^8}{n^2}
 \le E_N^4\sum_{n\le N}\frac{\|D_{N,T,n}\|_P^8}{n^2}.
$$
The right side involves only the two finite projection matrices and their full
weights. Its cofinal boundedness is sufficient for RH given the subcritical
approximation, for any $T_N\to\infty$. The signed mean in the identity can
allow further cancellation within each $D_{N,T,n}$.

There is an unconditional first moment, $\sum_n Q(n)\|U_{N,T,n}\|_P^2\le Z$
uniformly in $N,T$. This follows by interchanging the finite retained inputs
with the output sum and bounding each complete squared evaluation column by
$Z$. Orthogonal decomposition also gives $\|D_{N,T,n}\|_P^2
=\|U_{N,T,n}\|_P^2-\|\Pi_N^P U_{N,T,n}\|_P^2$. The cofinal bound for the
fourth power of this squared norm after multiplying by $E_N^4$ is open.
[Physical forcing kernel and Pareto projection](QFinitePhysicalForcingKernel.lean)

### Numerical checks outside Lean

All numbers below use complete progression masses in the two Gram systems
and the physical output cutoff $n\le N$. Each peak share is the fraction of
the actual matched moment contributed by its maximizing site.

| $N$ | $S_N$ | Peak site | Peak share |
|---:|---:|---:|---:|
| 105 | $1.75402\times10^{-15}$ | 95 | 81.36% |
| 140 | $3.82782\times10^{-15}$ | 95 | 54.35% |
| 193 | $2.39468\times10^{-15}$ | 114 | 41.04% |
| 215 | $3.07300\times10^{-15}$ | 215 | 27.66% |
| 260 | $6.49340\times10^{-15}$ | 221 | 35.91% |

Stages 214 and 215 have the same 132 legal conductors because 216 is nonsquarefree.
Their projection vectors are identical. The extra physical term raises the moment
from $2.22288\times10^{-15}$ to $3.07300\times10^{-15}$, moving the maximizing site
from 114 to 215. This is an observed change of the output head alone.

At stage 105 a second calculation evaluated each progression by 16 direct terms
and an extended-precision Euler–Maclaurin tail through $B_{14}$, followed by
iterative refinement. It agreed with the digamma/trigamma computation of $S_{105}$
to relative error $7.5\times10^{-12}$.

For the original uncentered truncation at $N=215,T=57$, split its right-hand
side on the original residue atoms at $m=T$. Solve each part using the same
complete $Q$ Gram matrix. The aligned moments of the low and high responses
were respectively $1.28152\times10^{-9}$ and $8.98925\times10^{-10}$.
The moment of their signed sum was $5.86980\times10^{-15}$. The corresponding
untruncated matched moment was $3.07300\times10^{-15}$. These finite values
explain why bounding the two responses separately loses information.

The following diagnostics evaluate the improved Pareto upper bound for exactly
this same truncated fit. The three columns on the right successively use the
full variance, project the kernel off the Pareto stage and retain the actual
residual energy, and measure the signed output. Upper bounds are divided by
$Z^8$ so each column has the units of the unnormalized physical moment.

| $N$ | $T$ | $Z^{-8}\sum\|U_n\|_P^8/n^2$ | $Z^{-8}E_N^4\sum\|D_n\|_P^8/n^2$ | Truncated signed moment |
|---:|---:|---:|---:|---:|
| 105 | 33 | 0.0837766 | $2.21528\times10^{-13}$ | $4.51200\times10^{-15}$ |
| 215 | 57 | 0.0929477 | $3.38928\times10^{-13}$ | $5.86980\times10^{-15}$ |
| 260 | 65 | 0.0979060 | $3.23709\times10^{-13}$ | $9.41516\times10^{-15}$ |

For each kernel row let $u$ be its retained physical values and $P_T$ the
diagonal matrix of their Pareto masses. With $X_T$ the matrix of atoms on the
retained sites, set $v=X_T^\top P_Tu$. The calculation uses
$\|D_n\|_P^2=u^\top P_T u-v^\top G_P^{-1}v$ with the **complete** Pareto Gram
matrix. The table gives floating-point comparisons at these stages.

## Arithmetic status

The repository's square-root-log Mertens estimate already proves the separate implication $\log(2+|d(n)|)=o(\sqrt{\log n})\Rightarrow\mathrm{RH}$. Here $d=f_Q-f_P$ is the limit. The eighth-moment implication takes the explicit Lean premise `HasSubcriticalApproximation`: $1$ can be approximated in $L^{8/7}(Q)$ by vectors of the squarefree Hilbert closure. On paper the arithmetic inputs are J. Lee's theorem for the natural Möbius approximation (1996), recorded by Báez-Duarte at (1.12), (1.17), and Liu's preprint reporting a zero-free boundary strictly below $7/8$. Liu documents a separate Lean verification of its zeta conclusion. The project now identifies the full Lebesgue integral for Lee’s exact centered Möbius sums with their Pareto moment and transfers its convergence to the named physical approximation, using the original finite legal witnesses. The implication from the zero-free half-plane to convergence of that integral is open in this project. [Lean transfer](QFiniteEighthLee.lean). Bagchi's remark following the discrete criterion identifies the squarefree specialization. [Báez-Duarte](https://arxiv.org/pdf/math/0011254) · [Liu, October 2026, Part IV and verification appendix](https://arxiv.org/html/2610.12234v2) · [Bagchi](https://arxiv.org/abs/math/0607733)

The analytic premise has mathematical content. For a putative zero $\rho$ of real part $\sigma>7/8$, the Mellin functional on the step realization is bounded on $L^{8/7}(P)$, since $\|t^{\rho-1}\|_{L^8(0,1)}=(8\sigma-7)^{-1/8}$. It vanishes on every squarefree atom by the Mellin identity, extends to the closure, and takes $1$ to $1/\rho$. Thus every candidate must have $L^{8/7}(P)$ error at least $(8\sigma-7)^{1/8}/|\rho|$. Norm equivalence transfers this obstruction to $Q$. [Repository Mellin identities](QMellinTransfer.lean)

The open task is a cofinal upper bound for the actual fits. A concrete target is the fourth-power sum of their squared norms multiplied by $E_N^4$. For the weaker RH implication one can even cap each term of this upper bound at 1, by the capped criterion and monotonicity. Write $\Pi_N$ for the $Q$ projection onto the finite stage. The exact normal equations, sharp cancellation in the kernel, and alignment of the output cutoff all survive in this target.

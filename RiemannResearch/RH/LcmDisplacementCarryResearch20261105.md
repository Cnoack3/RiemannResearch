# Eighth moments on LCM blocks and signed CRT carries

Write $L_M=\operatorname{lcm}(1,\ldots,M)$ and take increasing $M_j$ with distinct $A_j=L_{M_j}$. The proposed inequality concerns the actual limiting displacement $d=f_Q-f_P$:
$$
\sup_j B_j(d)<\infty,\qquad B_j(v)=\sum_{A_j\le n<A_{j+1}} |v(n)|^8/n^2 .
$$
The same question for $B_j(d_{M_j-1})$ has an unconditional affirmative answer. The two quantifiers lead to different problems. The Hilbert law is $Q(n)=1/(Zn^2)$, $Z=\zeta(2)$, and the other projection uses $P(n)=1/[n(n+1)]$. Both projections at stage $N$ use the squarefree atoms $g_m(n)=(n\bmod m)/m$ for $2\le m\le N+1$.

## The criterion and its arithmetic input

Each strict LCM jump at least doubles the modulus. A block beginning at $A$ has reciprocal-square mass at most $2/A$. If $B_j(d)\le C$, finite Hölder bounds its $q$-mass for $0<q<8$ by $C^{q/8}(2/A_j)^{1-q/8}$. The right side is summable in $j$. In particular $q=7999/1000$ has conjugate $p=7999/6999$, with $1/p=6999/7999>0.874975$. A common $C$ and arbitrarily late qualifying stages **for each fixed block** suffice because $d_N\to d$ at every physical site. Individual qualifying sequences may depend on the block. Passing to sparser endpoints only groups nonnegative masses: every elementary LCM block is contained in a selected block beyond the finite initial prefix.

For the paper implication, J. Lee's natural approximation converges in $L^p$ for $1<p<1/\theta$ under a zero-free half-plane $\Re s>\theta$. On each cell $(1/(n+1),1/n]$ the centered continuous generators equal $g_m(n)$ almost everywhere. The cells have lengths $P(n)$, $Q/P$ is bounded, and the Möbius coefficients vanish at nonsquarefree conductors. Thus Lee supplies a physical squarefree approximation. Liu's October 2026 arXiv preprint reports $\theta=0.874957019420\ldots$. The strict margin matters because block interpolation loses the endpoint $8$. The current project takes the resulting approximation at $p$ as a hypothesis. Hölder against the actual $L^q$ annihilator $B r_P-d$, with $Bv(n)=v(n)/(n+1)$, then forces the positive witness identity to vanish. The existing capacity implication gives Mathlib's RH. Conversely, Bagchi's RH direction gives $1$ in the squarefree closure and hence $d=0$. This gives a paper equivalence with the proposed bound.

The same interpolation allows $B_j(d)\ll A_j^\delta$ for $0\le\delta<8(1-\theta)-1$: choose $1/(1-\theta)<q<8/(1+\delta)$. With the reported $\theta$ the admissible upper limit is about $0.00034384$. This extra slack is a paper corollary.

Sources: J. Lee, *Convergence and the Riemann Hypothesis*, Commun. Korean Math. Soc. 11 (1996), 57–62, as recorded in [Báez-Duarte, §1, (1.12), (1.17)](https://arxiv.org/pdf/math/0011254); [B. Liu, v2, Theorem 27.1](https://arxiv.org/html/2610.12234v2); [B. Bagchi, squarefree specialization, Remarks 4 and 8](https://arxiv.org/html/math/0607733v1).

## Exact supporting conductors for the limiting displacement

Set $d(0)=0$, $\Delta d(k)=d(k)-d(k-1)$ and $b_m=\sum_{k\mid m}\mu(m/k)\Delta d(k)$. The repository's finite-head inversion gives $d(n)=\sum_{m\le n}b_m\lfloor n/m\rfloor$. Squarefree compatibility of the actual $d$ forces $b_m=0$ at each nonsquarefree conductor. With $L=L_M$ the resulting **finite signed identity** is
$$
d(L+t)=d(L)+d(t)+\sum_{\substack{m\le L+t\ \mathrm{squarefree}\\
\exists p\mid m\ \mathrm{prime},\ p>M}} b_m\,
\mathbf1_{(L\bmod m)+(t\bmod m)\ge m}.
$$
Every squarefree product formed from primes through $M$ divides $L$, regardless of the size of the product. Its translation carry vanishes identically. This holds for $d$ itself at each integer and uses no uniform CRT extension or interchange of an infinite sum. The surviving sum and the two boundary values still enter the eighth power.

### Exact covariance and cancellation of the translation carries

Use $L=L_M=\operatorname{lcm}(1,\dots,M)$ and define
$X_m(t)=\mathbf1_{\{(t\bmod m)+(L\bmod m)\ge m\}}-(L\bmod m)/m$.
This concerns the binary *translation* carry in the limiting displacement identity.
The Bézout pair-atom carry is a distinct object.

For $g=(m,n)$, $r=L\bmod g$, with $t$ uniform modulo $P=\operatorname{lcm}(m,n)$,
\[
\mathbb E_P X_mX_n=\frac{r(g-r)}{mn}.
\]
Indeed, fixing $s=t\bmod g$, CRT gives independent, uniform choices in the
two fibers over $s$. Writing $L\bmod m=ug+r$, the top $ug+r$ residues
modulo $m$ contain $u+\mathbf1_{\{s\ge g-r\}}$ residues in this fiber.
The conditional mean of $X_m$ is $(g\mathbf1_{\{s\ge g-r\}}-r)/m$,
and similarly for $n$. Averaging the product proves the identity, including
$m=n$. Thus distinct squarefree conductors sharing no prime above $M$ have
exactly zero centered covariance. When they share a rough prime covariance
can be positive; its sign need not give cancellation for coefficients of the
same sign. With $L=60$, Wolfram exact arithmetic returns $2/49$ for $(14,21)$,
$0$ for $(14,22)$, and $4/245$ for $(21,35)$. Exhaustive exact tests over
$0\le L\le 8$ and $1\le m,n\le13$ gave maximum error zero (1,521 triples).

The pattern extends to moments of finite collections. Take squarefree
$m_1,\ldots,m_k$ and uniform $t$ modulo their lcm. Condition on all prime
residues for $p\le M$ occurring in these moduli. Collections whose sets
of primes above $M$ are disjoint are then conditionally independent by CRT.
The conditional mean of each individual centered $X_m$ is zero: the product
$d$ of its old prime divisors divides $L$, and each old fiber contains
exactly $(L\bmod m)/d$ of the top $L\bmod m$ residues. Consequently
\[
\mathbb E\prod_{i=1}^k X_{m_i}=0
\quad\text{if some }m_i\text{ has no prime above }M\text{ shared by another }m_j.
\]
The indices include repetitions. An all-old conductor has $X_m=0$ identically.
For a finite signed sum, this removes every isolated index in the complete-period
centered eighth-moment expansion. The surviving tuples have no isolated indices. The uncentered formula also contains a deterministic term evaluated below.

A quantified distinction between complete-period means and physical shell sums:
for a tuple of up to eight moduli let $Y(t)=\prod_i X_{m_i}(t)$ and
$P'=\operatorname{lcm}_i m_i$. For $L\ge1$ and any $T$,
\[
\left|\sum_{t<T}\frac{Y(t)-\mathbb E_{P'}Y}{(L+t)^2}\right|
\le\frac{2P'}{L^2}.
\]
Subtracting the period mean gives a sequence bounded by $2$ with zero period
sum, hence partial sums bounded by $2P'$. Finite summation by parts against
the decreasing weights yields the stated bound. This can be useful for short
conductors; it does not control tuples with lcm far larger than the shell start
or the total signed sum with the actual Möbius charges.

The deterministic means combine *exactly* with the endpoint, at no error.
For any fixed finite horizon $H\ge L+t$ put $a_m=\operatorname{mobiusDifference}_m(d)$,
including $a_1=d(1)$, and $s_H=\sum_{1\le m\le H}a_m/m$. Then
\[
d(L)+\sum_{m\le H}a_m\frac{L\bmod m}{m}
  =\sum_{m\le H}a_m\left(\lfloor L/m\rfloor+\frac{L\bmod m}{m}\right)
  =L s_H,
\qquad
d(L+t)=d(t)+L s_H+\sum_{m\le H}a_m X_m(t).
\]
For $H\ge1$ this is the repository's slope
$\operatorname{headCharge}(H-1,\mathrm{displacement})$, since the canonical
atom coefficient at $m\ge2$ is $-a_m$. In particular the unrestricted
deterministic term is a single scalar rather than one absolute bound per
modulus. One cannot discard or separately pass the two terms to infinity
without an estimate.

One can also see a second type of cancellation, this time *among signed
coefficients*. Write a finite centered sum as $S_H(t)=\sum_{m\le H}a_m X_m(t)$
and use normalized counting measure on the full lcm cycle of the moduli
with nonzero coefficients. Its mean is zero. At the reduced nonzero frequency
$b/k$ the normalized Fourier coefficient (negative exponent convention) is
\[
\widehat S_H(b/k)=
 \underbrace{\sum_{u=1}^L e^{2\pi i bu/k}}_{D_L(b/k)}
 \underbrace{\sum_{\substack{m\le H\\k\mid m}}\frac{a_m}{m}}_{A_k(H)}.
\]
Indeed a modulus $m$ contributes only when $k\mid m$, and then its top
$L\bmod m$ residues $-1,-2,\dots,-(L\bmod m)$ give precisely $D_L(b/k)/m$;
the extra complete $k$-cycles sum to zero. This proof uses no infinite
Fourier expansion. Parseval gives the signed packet identity
\[
\mathbb E |S_H|^2=
 \sum_{k=2}^{H}|A_k(H)|^2
 \sum_{\substack{1\le b<k\\(b,k)=1}}
 \frac{\sin^2(\pi b L/k)}{\sin^2(\pi b/k)}.
\]
All frequencies with $k\mid L$ vanish identically. Conductors whose primitive
packet $A_k(H)$ cancels vanish as well. Since $a_m=0$ for nonsquarefree $m$
for the displacement, the remaining frequencies must themselves have
squarefree conductor with at least one prime above $M$. For example $L=60$,
$a_{14}=2$, $a_{21}=-3$ gives $A_7=2/14-3/21=0$ *despite both shared-prime
carries being nonzero*; the complete-cycle variance is $10/7$. This example
illustrates exact cancellation without asserting that the actual displacement
has these particular charges. For the eighth norm, finite-group
Hausdorff–Young gives $\|S_H\|_8\le
(\sum_{k,b}|D_L(b/k) A_k(H)|^{8/7})^{7/8}$ on the full cycle. Control of
these quantities for growing $H$ and their short, physically weighted block
counterparts is still needed.

Wolfram checked this signed example exactly over all 42 residue classes:
the variance was $10/7$ and the sum of $S_H$ inside *each* of the seven
residue classes modulo $7$ was zero, verifying annihilation of every
nonzero frequency of conductor $7$.

## Prime atoms and the two kinds of carry

For distinct primes and $aq+bp=1$, the integer-valued Bézout carry is $C_{p,q}=a g_p+b g_q-g_{pq}$. Equivalently, put $u=[q^{-1}n]_p/p$, $v=[p^{-1}n]_q/q$, with least nonnegative residues. Then $g_{pq}=u+v-\mathbf1_{u+v\ge1}$. The latter formula permutes each prime coordinate, so its binary carry differs from the Bézout carry by one-coordinate integer terms.

Uniform product (Haar) measure on the infinite product $\prod_p\mathbb Z/p\mathbb Z$ makes the coordinates independent. Subtracting the two conditional means and restoring the common mean gives the interaction
$$
I_{p,q}=g_{pq}-g_p/q-g_q/p-(p-1)(q-1)/(2pq).
$$
It has both conditional means zero. Two distinct pair interactions are orthogonal even if they share one prime. Orthogonal variance decomposition gives $\mathbb E_H I_{p,q}^2=(1-p^{-2})(1-q^{-2})/12$. Its eighth moment is consequently at least the fourth power of this variance. Wolfram checked the conditional means and variance on small complete periods, including $p=3,q=5$, where the variance is $16/225$ and the mean binary carry is $4/15$.

There is also cancellation under the actual reciprocal-square weight. For $pq\mid A,B$, $0<A<B$,
$$
-\frac{pq}{8}(A^{-2}-B^{-2})
\le\sum_{n=A}^{B-1}I_{p,q}(n)/n^2\le0.
$$
Indeed the prefix through $t-1$ equals $[-r(pq-r)+u(p-u)+v(q-v)]/(2pq)$ for $r=t\bmod pq$, $u=t\bmod p$, $v=t\bmod q$. It lies in $[-pq/8,0]$ and vanishes at both endpoints. Apply summation by parts. At $(p,q,A,B)=(3,5,15,30)$ the weighted sum is approximately $-0.00342478$. This is a signed first-moment estimate. The atomic law $Q$ on integers and the Haar product give different expectations.

For the actual matched projections put $E_N=\|r_{P,N}\|_P^2$ and $e_m=E_N-Zm\langle g_m,d_N\rangle_Q$. Then
$$
Zpq\langle C_{p,q},d_N\rangle_Q=e_{pq}-aqe_p-bpe_q .
$$
All copies of $E_N$ cancel because $aq+bp=1$. For included $p,q,pq$ the defining equations identify each $e_m$ with a signed Pareto residual tail. The carry vanishes below $s=\min(p,q)$, and the multiplier in the matched equation $d_N=\Pi_N B r_{P,N}$ gives
$$
(s+1)|\langle C_{p,q},d_N\rangle_Q|
\le \|C_{p,q}\|_Q\,\|\mathbf1_{[s,\infty)}r_{P,N}\|_Q .
$$

### A gain when the two prime conductors are close

Let \(P(k)=1/[k(k+1)]\) for \(k\ge1\), \(D_m(k)=m\lfloor k/m\rfloor/k\), and \(r_N\) be the finite Pareto residual. For included conductors the repository's signed forcing formula reads \(e_m=\langle D_m,r_N\rangle_P\). Given \(p<q\) and \(\delta=q-p\), the following bound uses the distance between the conductors:
\[
 |e_p-e_q|\le \left( \zeta(3/2)\frac{\sqrt\delta}{p}+
 \frac{\delta}{q^{3/2}}\right)
 \|\mathbf1_{k\ge p}r_N\|_P .
\]
Indeed, counting integer thresholds gives the exact identity
\[
 D_p(k)-D_q(k)=\frac p k\sum_{j\ge1}\mathbf1_{[jp,jq)}(k)
               -\frac{\delta}{k}\left\lfloor k/q\right\rfloor .
\]
The \(j\)-th interval contains \(j\delta\) integers. On it the squared integrand, including its weight, is at most \(p^2/(jp)^4\). The sum of the individual norms is therefore at most \(\zeta(3/2)\sqrt{\delta}/p\). The last term is bounded by \(\delta/q\) and vanishes below \(q\); the Pareto mass on \(k\ge q\) is \(1/q\). Minkowski and Cauchy–Schwarz give the result. For \(q\le2p\), the first interval alone gives \(\|D_p-D_q\|_P^2\ge p^2\delta/q^4\ge\delta/(16p^2)\); the square-root scale cannot be improved for arbitrary unit residuals.

For coprime \(p,q\), choose the centered inverse \(a\) with \(aq+bp=1\) and \(|a|\le p/2\). In the normalized carry identity the coefficient of this difference is \(-a/p\), so the estimate improves the carry's physical forcing for close primes. The next step is to control these signed rows *together* through the full Gram system, including distant prime factors and conductors with three or more factors. The estimate above is a paper proof; it does not bound the eighth moment of the projected displacement.

## What the finite cutoff already supplies

Take $F=\sum_{2\le m\le M}c_mg_m$. With $F(0)=0$, inversion gives $c_m=-\sum_{k\mid m}\mu(m/k)\Delta F(k)$ for $m>1$. Thus
$$
\|F\|_\infty\le\sum_m|c_m|\le M\sum_{k\le M}|\Delta F(k)|/k
\le 2\sqrt Z\,M^{3/2}\|F\|_Q .
$$
The last estimate is Cauchy–Schwarz applied separately to $F(k)$ and $F(k-1)$. The matched displacements have uniformly bounded $Q$-norm by the finite energy comparison. Hence their eighth-power mass beyond $L_M$ is $O(M^{12}/L_M)$ for the stage with maximal conductor $M$. This gives summability over all $M$ by [Farhi's LCM bound](https://arxiv.org/abs/0906.2295). The Lean module instead combines existing coercivity with the pinned Mathlib inequality $2^M\le(M+1)L_M$ to obtain summability uniformly over arbitrary finite block lengths.

The squarefree period $R_M=\prod_{p\le M}p$ divides $L_M$. For a nonnegative $R$-periodic profile $H$ and multiples $A,B$ of $R$, summing complete periods gives the two-sided comparison
$$
\frac{1}{1+R/A}\le
\frac{\sum_{A\le n<B}H(n)/n^2}{(1/A-1/B)\mathbb E_H[H]}
\le1+R/A
$$
when the denominator is positive. Compare the individual weights on $[a,a+R)$ with $1/[a(a+R)]$ and telescope. Such a complete-period argument applies directly to the fitted atoms at this cutoff. Later conductors can have periods longer than the entire physical block.

One can see why the special projection equations are needed even using only prime atoms. For each block choose a prime $2A_j<p_j<4A_j$ by Bertrand's theorem. Since $\|g_p\|_Q^2\ll1/p$ by splitting at $p$, the series $F=\sum_j p_j^{1/4}g_{p_j}$ converges in the closed legal span. On $[A_j,2A_j)$ its nonnegative $j$-th term is at least $p_j^{1/4}/4$, so $B_j(F)\gg A_j$. This example also satisfies $F(n)=o(n)$, as every physical $L^2(Q)$ vector does. Legality, the prime-coordinate representation, and sublinear growth together permit unbounded block moments.


### A polynomial physical cutoff from all CRT interactions (paper proof)

Let $v=\sum_{2\le m\le M}c_mg_m$ with squarefree conductors; set other $c_m$ to zero. Write $H$ for product Haar measure on the prime residue coordinates. For every $\epsilon>0$ and integer $X\ge1$,
\[
 \|v\|_{L^8(H)}^8\ll_\epsilon M^{8+\epsilon}\|v\|_{2,Q}^8,\qquad
 \sum_{n\ge X}\frac{|v(n)|^8}{n^2}
 \ll_\epsilon M^{8+\epsilon}\|v\|_{2,Q}^8
          \left(\frac1X+\frac{M^8}{X^2}\right).
\]
In particular $X\ge M^{8+\delta}$ gives a vanishing far tail for any uniformly $Q$-bounded family of legal fits and any fixed $\delta>0$. The physical upper estimate applies to arbitrary cutoffs, including those below the full primorial period. The estimate covers all stages $M\le X^{1/8-\eta}$ for fixed $0<\eta<1/8$.

**Coefficient estimates.** Extend $v(0)=0$, put $f(r)=v(r)-v(r-1)$, and temporarily set $c_1=-v(1)$. The consecutive residue differences give $c_m=-\sum_{d\mid m}\mu(d)f(m/d)$ for every $m\le M$, including $m=1$. Write $H_M=\sum_{d\le M}1/d$. Minkowski for the dilations in this formula and the triangle inequality for differences give
\[
 \left(\sum_{m\le M}c_m^2/m^2\right)^{1/2}
 \le H_M\left(\sum_{r\le M}|f(r)|^2/r^2\right)^{1/2}
 \le 2\sqrt{\zeta(2)}H_M\|v\|_{2,Q}.
\]
Summing the signed formula telescopes to $\sum_{m\le M} c_m=-\sum_{d\le M}\mu(d)v(\lfloor M/d\rfloor)$. Since $|v(r)|\le\sqrt{\zeta(2)}r\|v\|_{2,Q}$, the full sum is $O(MH_M\|v\|_{2,Q})$. In fact $\mathbb E_H v=\frac12\sum_{m\le M}c_m$ with this virtual $c_1$ convention.

**All carry orders.** Put $F_s=g_s-\mathbb E_Hg_s$ and $I_t=\sum_{s\mid t}\mu(t/s)(s/t)F_s$ for squarefree $t>1$. Integration over any prime $p\mid t$ kills $I_t$: for $p\mid s$, averaging $F_s$ over the $p$ coordinate gives $F_{s/p}/p$, and the two divisor terms cancel. Inverting the divisor sum gives $v-\mathbb E_Hv=\sum_{t>1} b_t I_t$ with $b_t=\sum_{k\le M/t}c_{tk}/k$. Cauchy–Schwarz with weights $1/k$ and then interchanging sums yield $\sum_{t>1}b_t^2\le H_M^2\sum_{m\le M}c_m^2$.

For terms of order $r=\omega(t)$, randomly color every prime uniformly with one of $r$ colors. A term uses every color with probability $r!/r^r$. Minkowski bounds the full degree-$r$ sum by $r^r/r!$ times the largest norm of a sum restricted to such terms. For a fixed coloring, condition on all color groups except the first. The contributions grouped by the index of the first color are independent centered variables. Conditional symmetrization introduces independent signs at cost $2$ in norm. Repeat in all groups, retaining the earlier signs. Conditional on the CRT coordinates, the resulting sum is an $r$-fold Rademacher chaos with coefficients $b_t I_t$. Iteration of $\|\sum_i a_i\varepsilon_i\|_8\le105^{1/8}(\sum_i a_i^2)^{1/2}$ gives the bound $105^{r/8}(\sum_t |b_t I_t|^2)^{1/2}$; Minkowski in $L^4$ justifies interchanging the next $L^8$ norm and the square sum. Since $\|I_t\|_\infty\le \frac12\prod_{p\mid t}(1+1/p)\le (3/2)^r$ and $r^r/r!\le e^r$, the degree-$r$ bound is $C^r(\sum_{\omega(t)=r}b_t^2)^{1/2}$ for an absolute $C$. The largest possible $r$ is $o(\log M)$ since $(r+1)!\le t$. Summing in $r$ costs $M^{o(1)}$. The coefficient estimates and the separate mean bound prove the Haar estimate.

**Transfer to physical intervals.** The finite Fourier frequencies of $v^4$ are rational fractions with reduced denominator at most $M^4$, since a product of four atoms has period dividing the product of its four conductors. After collecting equal frequencies, distinct ones are separated on the circle by at least $M^{-8}$. For any interval of $Y$ consecutive integers, the dual large sieve and Parseval on the finite CRT period give
\[
 \sum_{n\text{ in interval}}|v(n)|^8
 \le (Y+M^8)\sum_\alpha|\widehat{v^4}(\alpha)|^2
 =(Y+M^8)\mathbb E_H |v|^8.
\]
Apply this on $[2^jX,2^{j+1}X)$, divide by $(2^jX)^2$, and sum. The separation estimate uses the classical large sieve; the coefficient and Haar estimates above are paper deductions for this dictionary. [Montgomery and Vaughan, *The large sieve*, Mathematika 20 (1973), 119–134](https://doi.org/10.1112/S0025579300004708)

**Sharpness for general legal vectors.** Infinitely many $m,m+1$ are both squarefree, since the squarefree density $6/\pi^2$ exceeds $1/2$. Take the legal vector
\[
 v_m=((m+1)g_{m+1}-m g_m)/\sqrt{H_m}.
\]
The repository's complete adjacent-residue estimate gives $\|v_m\|_P^2\le1$, hence $\|v_m\|_Q^2\le2/\zeta(2)$. The CRT coordinates modulo $m$ and $m+1$ are independent under Haar, so
\[
 \operatorname{Var}_H(v_m)=[m^2-1+(m+1)^2-1]/(12H_m).
\]
In particular $\mathbb E_H|v_m|^8\ge(\operatorname{Var}_H v_m)^4\gg m^8/(\log m)^4$. For $2<\alpha<8$ and $X=\lceil m^\alpha\rceil$, the interval $[X,2X)$ contains at least $X/(2m(m+1))$ complete periods eventually. Consequently its physical eighth moment exceeds a constant times $m^{8-\alpha}/(\log m)^4$, which diverges. Every proposed universal cutoff exponent below $8$ fails, by taking $\alpha$ strictly between the larger of that exponent and $2$, and $8$. This lower example concerns general bounded legal vectors. [Complete adjacent-residue estimate](AdjacentResidueHarmonic.lean)

## What the actual Gram fits do on a fixed block

For a finite fit $F=\sum c_mg_m$, the translation $F(L+t)-F(t)=-\sum c_mX_m(t)$ is exact for every $t$, by direct subtraction of residues. Write $K_{mn}=r(g-r)/(mn)$ as above. The full-period variance of this translation is $c^\mathsf{T}Kc$. The comparison $|c|^\mathsf{T}K|c|$ makes all the charges have the same sign and keeps their magnitudes. The ratios below therefore test cancellation in the **actual finite fitted charges**.

| Physical block | Stage $N$ | $B_j(d_N)$ | Signed variance / same-sign variance |
|---|---:|---:|---:|
| $[60,420)$ | 4 | $1.057\times10^{-17}$ | both zero |
| $[60,420)$ | 30 | $5.536\times10^{-15}$ | 0.368 |
| $[60,420)$ | 100 | $1.034\times10^{-13}$ | 0.218 |
| $[60,420)$ | 256 | $1.806\times10^{-14}$ | 0.188 |
| $[420,840)$ | 6 | $3.162\times10^{-17}$ | both zero |
| $[420,840)$ | 100 | $7.673\times10^{-15}$ | 0.290 |
| $[420,840)$ | 256 | $1.994\times10^{-14}$ | 0.190 |

For each pair of atom conductors $m,n$ with period $R=\operatorname{lcm}(m,n)$, the Gram entries used full residue sums. Each class $r=1,\dots,R$ has unnormalized $Q$ mass $\psi_1(r/R)/R^2$ and $P$ mass $[\psi((r+1)/R)-\psi(r/R)]/R$. Solving the two Gram systems for the projection of the constant and subtracting the coefficient vectors gives $c$. These values are floating-point experiments. The variance and the eighth-moment columns use different measures and different functions. Numerically there is signed cancellation on the complete period, and the physical eighth moment on a fixed block changes as more conductors enter.

## Remaining estimate

On the block beginning at $A_j=L_{M_j}$, the available unconditional estimates even allow a conductor cutoff $K_j\le A_j^{1/8-\eta}$ for fixed $0<\eta<1/8$. The unresolved estimate is
$$
\sup_j\sum_{A_j\le n<A_{j+1}}
\frac{|d(n)-d_{K_j-1}(n)|^8}{n^2}<\infty.
$$
By the triangle inequality for each finite weighted eighth norm and the uniform estimate on the cutoff fit this is equivalent to the proposed uniform bound for $d$. The finite translation formulas locate precisely which rough primes can contribute. The Fourier formula identifies signed sums of Möbius charges over their multiples. Establishing sufficient control for those charges on a physical interval shorter than their common period is still open.

Lean modules: [block interpolation](QLcmShellMoment.lean), [conjugate moments](QSubcriticalDisplacementMoment.lean), [actual and fixed-block criteria](QLcmDisplacementCriterion.lean), [frozen fits](QFrozenConductorBlocks.lean), [signed physical interaction](QCRTPairCarryBlocks.lean), [matched carry](QMatchedCRTCarry.lean), and [finite translation and slope](QDisplacementTranslationCarry.lean). The Haar covariance, Fourier packets, large-sieve refinement, lower examples, and numerical experiments above are paper arguments or computations.

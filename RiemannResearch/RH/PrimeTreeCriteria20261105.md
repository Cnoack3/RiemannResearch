# Reading the squarefree prime tree upward

For the matched displacement $d=f_Q-f_P$, set $b_m=(\mu*\Delta d)(m)$ with the project's anchored first difference. An upward sufficient inequality is
$$
 \exists\sigma\in\{-1,1\},\ C\ge0\quad
 \forall n\ge1\quad \liminf_{H\to\infty}B_{\sigma}(H,n)\le C.
$$
Here $B_\sigma$ is the sitewise pruned budget defined below. The distinction between finding one common $C$ and obtaining a finite answer at each site is essential. The results here identify the actual estimates to try. They give no unconditional proof of this inequality or of RH.

## Down the tree and back up

Use the squarefree integers as vertices, with root $1$. A child of $r$ appends a prime greater than its largest prime. Thus $30$ has parent $6$ and $210$ has parent $30$. Larger primes can always be appended; a squarefree conductor appears exactly once. One descending CRT step can be written in a representation-independent way. Put $a_r(n)=n\bmod r$ and $g_r(n)=a_r(n)/r$. At $r=Dp$ the normalized atom has the exact positive-digit expansion
$$
 g_{Dp}(n)=\frac{g_D(n)+j_{D,p}(n)}{p},\qquad
 j_{D,p}(n)=\lfloor n/D\rfloor\bmod p.
$$
Indeed $a_{Dp}=a_D+D j_{D,p}$. For $\gcd(D,p)=1$ this digit equals $((a_p-a_D)D^{-1}\bmod p)$. This incorporates the next prime's CRT residue and fixes an integer representative. The digit is distinct from the signed floor of a chosen Bézout lift. The earlier [recursive carry formalization](QRecursivePrimeCarry.lean) tracks those signed floors.

In the opposite direction, let $w_m=b_m/m$ and $T_r(H)=\sum_{m\le H:r\preceq m}w_m$. Write $D(r)$ for the parent and $a_r-a_{D(r)}=\delta_r(n)$. For $2\le r\le H$,
$$
 T_r(H)=w_r+\sum_{c\le H:D(c)=r}T_c(H).
$$
Consequently each leaf starts with its own weight, and a parent adds its own weight to the signed values returned by its children. This determines the finite upward sum uniquely. Every test $f$ satisfies the discrete summation by parts identity
$$
 \sum_{2\le r\le H}(f(r)-f(D(r)))T_r(H)
 =\sum_{1\le m\le H}(f(m)-f(1))w_m.
$$
With $f(r)=a_r(n)$ and $H\ge n$, the left side is exactly
$$
 n A(H)-d(n),\qquad A(H)=\sum_{m\le H}w_m .
$$
The repository's reciprocal-charge theorem gives $A(H)\to0$. Thus each signed tree observation tends to $-d(n)$ at fixed $n$. The tree's signed readout tends to zero at every physical integer exactly when the limiting projection residual vanishes. Using Báez-Duarte's published approximation theorem this is equivalent to RH. The Lean statement for the converse receives that theorem as an explicit parameter. [Báez-Duarte, Theorem 2, (3.1)](https://www.bdim.eu/item?fmt=pdf&id=RLIN_2003_9_14_1_5_0)

## Exact finite-head pruning

Fix a physical head $N$ and $n\le N$. Internal edges $r\le N$ keep their original digits. For a crossing $k=D(r)\le N<r$, every child has the same digit $u_k(n)=n-(n\bmod k)=k\lfloor n/k\rfloor$. All edges with both endpoints above $N$ have digit zero throughout the head. Define
$$
 F_k(H,N)=\sum_{N<r\le H:D(r)=k}T_r(H).
$$
The exact pruned evaluation and its one-sided upper bound are
$$
 \begin{aligned}
 S_H(n)&=\sum_{2\le r\le\min(N,H)}\delta_r(n)T_r(H)
    +\sum_{k\le N}u_k(n)F_k(H,N),\\
 -\sigma S_H(n)&\le
 \underbrace{\sum_{2\le r\le\min(N,H)}\delta_r(n)[-\sigma T_r(H)]_+
    +\sum_{k\le N}u_k(n)[-\sigma F_k(H,N)]_+}_{B_\sigma(H,N,n)} .
 \end{aligned}
$$
In the opening inequality $B_\sigma(H,n)=B_\sigma(H,n,n)$. Taking positive parts after adding siblings always gives a smaller or equal budget. At $n=N=7$, crossings $6\to30$ and $6\to42$ have digit $6$. If their subtree masses are $+1,-1$, their signed sum and pooled cost both vanish, while their separate one-sided costs sum to $6$. This illustration uses freely chosen weights.

For the actual projection the root criterion can be approached through the two matched finite projections $d_j$. For each fixed $(H,N,n)$, their pruned budgets converge to the actual budget. Hence a sufficient target involving only finite Gram systems is a fixed sign $\sigma$ and constant $C$ such that, for every $n$, arbitrarily large $H$ admit arbitrarily large $j$ satisfying $B_\sigma^{(j)}(H,n,n)\le C$. The two indices have different roles. Numerical samples or a single diagonal require additional uniform estimates.

There is also an exact worst-site test for a nonnegative unpooled edge cost. At $L-1$ for $L=\operatorname{lcm}(1,\dots,H)$, every digit simultaneously equals its maximum $r-D(r)$. For a signed sum this leaves room for cancellation; taking absolute values at each edge uses it up. See [simultaneous saturation](LCMDigitSaturation.lean).

## Formal sources and status

- [Prefix recursion and signed summation by parts](PrefixExpansion.lean), [finite and fixed-site identities](QPrimeSubtreeBudget.lean), [head pruning](PrefixPruning.lean), [finite-projection transfer](QTreeFiniteFits.lean).
- [Local escape](PrefixNoEscape.lean), [prime-coordinate topology](TreeConeTopology.lean), [projection tree equivalences](TreeRHCrit.lean). The published Báez-Duarte input is explicit in the direction from RH. The sufficient tree conditions imply RH internally.
- [Euler tree equivalence](TreeEulerCriterion.lean) and [finite prime deletion](TreeEulerPruning.lean) give a Lean equivalence to Mathlib's RiemannHypothesis with no domain-specific assumption. The initial germ uses signed leaf sums only in the half-plane of absolute convergence.
- [Mertens transfer for the prime-2 subtree](../NumberTheory/PrimeNumberTheorem/RoughMertensSubtree.lean). The root-to-subtree equivalence is internal. The RH-to-Mertens analytic equivalence is an explicit published input in this module.

## A Mertens example that isolates the missing cancellation

Use the test weights $b_m=\mu(m)$ in the reciprocal tree. Write $U(x)=\sum_{n\le x}\mu(n)/n$. The classical prime number theorem (also the available project Mertens bound by partial summation and the Euler product) gives $U(x)\to0$. For fixed $y$ the reciprocal sum restricted to integers with no prime factor at most $y$ equals
$$
 \sum_{a:\,P^+(a)\le y}\frac1a U(x/a).
$$
This follows by convolution with the indicator of integers made only from primes at most $y$; take $U(t)=0$ for $t<1$. The reciprocal weights sum to $\prod_{p\le y}(1-p^{-1})^{-1}<\infty$, so dominated convergence makes this sum tend to zero. Taking $y=P^+(r)$ and multiplying by $\mu(r)/r$ shows that every fixed nonroot subtree has limit zero. Nevertheless, at $r=2$, for any finite child conductor cutoff $K$ the sum over children larger than $K$ tends to $-\mu(2)/2=1/2$. This is an explicit example of signed mass going out through successively different children. It uses ordinary Möbius test weights; verifying the local tail condition for the matched projection remains open. Tao proves the reciprocal limit for arbitrary prime semigroups, with the uniform bound $|T_r(H;\mu)|\le1/r$. [Tao, Bull. Aust. Math. Soc. 81 (2010)](https://doi.org/10.1017/S0004972709000884)

## Pooling crossing siblings on the actual finite displacement projections

For \(H=N+1\), take every squarefree conductor \(2\le m\le H\). Set \(g_m(n)=(n\bmod m)/m\) and use the constant target \(1\) for the first Gram row. The two Gram matrices have entries \(\sum_{n\ge1}g_a(n)g_b(n)w(n)\) with \(w_Q(n)=1/n^2\) and \(w_P(n)=1/[n(n+1)]\). Solve the normal equations for the projection of 1 in each norm. If \(c_m=c^Q_m-c^P_m\), the fitted displacement is \(d_N(n)=\sum_{m\ge2}c_mg_m(n)\). Its floor coefficients are \(b_1=\sum c_m/m\) and \(b_m=-c_m\) for \(m\ge2\). Their reciprocal sum through \(H\) vanishes exactly.

Set \(T_r=\sum_{r\preceq m\le H}b_m/m\). The unpooled column takes the positive part of each adverse subtree coefficient before summing its nonnegative digit at sites \(1\le n\le X\). The pooled column first groups all crossing children \(r>X\) of each parent \(D\le X\), which have identical digits at these sites. Both columns sum the resulting site bounds with weight \(1/n\). Each row uses the same sign \(\sigma=-1\) in all three columns, chosen by minimizing the pooled expense over the two signs. The final column evaluates \(\sum_{n\le X}\max(0,\sigma d_N(n))/n\) directly.

| Stage \(N\) | Head \(X\) | Unpooled | Pooled | Direct physical side |
|---:|---:|---:|---:|---:|
| 30 | 20 | .151245 | .141219 | .005541 |
| 60 | 40 | .275036 | .275036 | .008468 |
| 100 | 40 | .328773 | .328181 | .007594 |
| 256 | 40 | .388531 | .387506 | .006538 |
| 256 | 80 | .609874 | .607781 | .008107 |
| 256 | 256 | 1.031694 | 1.031694 | .016307 |

The pooled budget decreased by 6.63% in the first row and 0.264% at \((256,40)\). At \((256,256)\) there is only one possible crossing conductor, so grouping gives equality. The physical sums are much smaller in every row, showing cancellation beyond this sibling pooling. These are finite-stage diagnostics. Passing to \(d\) with uniform growth control requires an estimate across the cutoff parameters.

The Python calculation sums the infinite Gram entries over residue classes. For period \(L=\operatorname{lcm}(a,b)\) and residue \(1\le j\le L\), the exact weights are \(\psi_1(j/L)/L^2\) and \([\psi((j+1)/L)-\psi(j/L)]/L\), respectively. NumPy/SciPy used IEEE binary64 and positive-definite solves. The largest 2-norm condition number in the table is \(8.92\times10^4\). The maximum pointwise difference between signed tree reconstruction and independent basis evaluation within these rows was \(9.72\times 10^{-17}\). A separate Wolfram evaluation at 40-digit working precision recomputed every Gram entry, fit, subtree charge and harmonic sum for \((N,X)=(30,20)\). It gave \(0.1512446701189377,\ 0.1412187240857271,\ 0.005540838964071880\), agreeing with the binary64 computation within \(2.1\times10^{-14}\). This is a numerical cross-check of the first row.

## The topology of increasing prime prefixes

For the matched displacement, write $b_m=(\mu*\Delta d)(m)$, supported on positive squarefree integers, and set
$$
 T_r(H)=\sum_{\substack{m\le H\\r\preceq m}}\frac{b_m}{m}.
$$
Here $r\preceq m$ means that the increasing list of prime factors of $r$ is an initial segment of that of $m$. The empty prefix has product $1$. This note uses three spaces because the relevant test functions distinguish different limits.

### The prime-coordinate space

Enumerate the primes $p_1,p_2,\ldots$. Put $K=\{0,1\}^{\mathcal P}$, with distance $2^{-j}$ if $p_j$ is the first prime on which two distinct masks differ. A finite support is a squarefree vertex and an infinite support is an infinite ray. The supports of squarefree integers are dense. This is compact by a diagonal subsequence argument. Fixing any finite list of bits defines a clopen set. These sets form a basis. This is the usual Cantor-space construction, as in A. S. Kechris, *Classical Descriptive Set Theory*, Springer GTM 156 1995, §2, https://doi.org/10.1007/978-1-4612-4190-4.

For $r>1$, the cone $[r]$ fixes *every* prime coordinate through $P^+(r)$, according to the support of $r$. Set $[1]=K$. Every cone is homeomorphic to $K$ since the remaining coordinates are free. The cone partitions as
$$
 [r]=\{r\}\ \sqcup\!\bigsqcup_{p>P^+(r)}[rp],
$$
where $P^+(1)=1$. A neighborhood of the stopping point $r$ contains all but finitely many child cones. Conversely, discarding finitely many child cones from $[r]$ gives a neighborhood of $r$. Thus $[r]$ is the one-point compactification of the disjoint topological sum of its child cones. Each child cone is clopen and $\{r\}$ is closed. In particular $rp_j\to r$ for primes tending to infinity. The prefix relation is stronger than divisibility. For example $[15]$ fixes the bits $2\mapsto0,3\mapsto1,5\mapsto1$, and excludes $30$.

### What the physical observations see

The physical tests are $F_n(m)=m\{n/m\}=n\bmod m$ for positive squarefree $m$. On $K$, $p_j\to1$, but $F_2(1)=0$ and $F_2(p_j)=2$ eventually. More generally $F_n(rp_j)=n$ eventually, while $F_n(r)=n\bmod r$. The failure occurs for each finite stop $r\le n$.

There is an exact identification of the topology generated by the physical observations. Its compactification is the one-point compactification $D^*=D\cup\{\infty\}$ of discrete positive squarefree indices. On it, define $F_n(\infty)=n$ because $F_n(m)=n$ for $m>n$. Conversely all finite singleton indicators come from the observations. With $F_0=0$,
$$
 1-F_k(m)+F_{k-1}(m)=m\mathbf 1_{m\mid k},\qquad
 r\mathbf 1_{m=r}=\sum_{k\mid r}\mu(r/k)\,[1-F_k(m)+F_{k-1}(m)].
$$
At infinity both sides of the second identity vanish. Therefore the $F_n$ separate all points of $D^*$, including infinity. Their joint evaluation embeds compact $D^*$ homeomorphically into a Hausdorff product, and $D$ is dense in its image.

The closure of $m\mapsto(\operatorname{supp}(m),1/m)$ in $K\times[0,1]$ realizes both sets of tests. It consists of one isolated point for each squarefree index and all of $K\times\{0\}$. At a positive height this follows from discreteness of the reciprocal indices. To approach $(S,0)$, prescribe the first $j$ prime bits of $S$ and append one extra prime larger than both $j$ and $p_j$. Every $F_n$ equals $n$ on the boundary, and every prime bit extends by the first coordinate. These tests separate points of the closure, giving the compactification generated by both families. In particular $rp_j$ tends here to $(\operatorname{supp}(r),0)$, which the tests distinguish from the isolated vertex $(\operatorname{supp}(r),1/r)$.

### Which limiting operations are justified

The repository's theorem `Pareto.qSequence_mobiusDifference_absolute_mass` gives $\sum |b_m|/m^2<\infty$. Hence $\sum (b_m/m^2)\delta_{\operatorname{supp}(m)}$ defines a finite signed Borel measure on $K$, and all its cone masses and all their countable child sums are absolutely convergent. The charges in $T_r(H)$ instead have weight $1/m$. The multiplier $m$ is unbounded on the index space. Passing from the damped masses to the actual tree readout needs an additional estimate.

Two other natural probability measures on $K$ illuminate the distinction between finite stops and infinite rays. Under the pushforward of the zeta-two law $\mathbb P(N=n)=n^{-2}/\zeta(2)$ by prime support, the prime bits are independent Bernoulli variables with probabilities $1/p^2$. Indeed the probability that all primes in $S$ divide $N$ is $\prod_{p\in S}p^{-2}$ for every finite $S$. This law has mass one on finite supports. In contrast, under uniform Haar residues in $\prod_p\mathbb Z/p\mathbb Z$, prime-divisibility indicators are independent with probabilities $1/p$. Since $\sum_p1/p=\infty$, the second Borel–Cantelli lemma gives infinite support almost surely. Neither product law specifies the signed subtree charges $b_m/m$.

### A local upward criterion allowing cancellation

For every nonempty prefix $r$ and all $H\ge r$, finite disjointness gives
$$
 T_r(H)=\frac{b_r}{r}+\sum_{\substack{p>P^+(r)\\ rp\le H}} T_{rp}(H).
$$
The following two conditions on the actual charge are together equivalent to vanishing of the matched displacement and, using the published approximation equivalence, to RH.
$$
 \begin{split}
 &T_r(H)\longrightarrow0 \quad\text{for every nonempty prefix }r,\\
 &\lim_{P\to\infty}\limsup_{H\to\infty}
 \left|\sum_{\substack{p>\max(P,P^+(r))\\ rp\le H}} T_{rp}(H)\right|=0
 \quad\text{for every nonempty prefix }r .
 \end{split}
$$
Indeed fix $P$. The finitely many child terms with $p\le P$ tend to zero. The identity forces the remaining signed sum to converge to $-b_r/r$. The second condition gives $b_r=0$. Then finite divisor reconstruction $d(n)=\sum_{m\le n} b_m\lfloor n/m\rfloor$ leaves $d(n)=n b_1$, and the project's $\sum |d(n)|^2/n^2<\infty$ forces $b_1=0$. Conversely, when $d=0$ every charge is zero. This argument identifies the exact escaping mass to estimate. The conditions are a reformulation, and their verification for the actual displacement remains open.

Comparing $r p_j$ with $r$ gives an explicit signed-measure counterexample to an inference based only on compactness. The bounded-variation measures $\delta_{r p_j}-\delta_r$ tend weakly to zero in prime coordinates, although the physical $F_r$-readout is $r$ eventually. In the other direction, for primes $p_j,q_j\to\infty$ with $p_j$ odd, $\delta_{2q_j}-\delta_{p_j}$ eventually vanishes on each physical test while its integral against the even cylinder equals $1$. Both examples use general signed data. The finite-head pruning theorem avoids both unjustified interchanges by consolidating crossing sibling masses before taking a limit.

## A fixed Möbius subtree is an RH criterion

\[
\boxed{\quad \forall\varepsilon>0\quad\exists C_{r,\varepsilon}<\infty\quad\forall X\ge1,\qquad
\left|\sum_{\substack{m\le X\\r\preceq m}}\mu(m)\right|
\le C_{r,\varepsilon} X^{1/2+\varepsilon}.\quad}
\]

Here \(r\) is **any one fixed squarefree vertex**, including the root \(r=1\). The quantifier on \(r\) matters. The criterion above is equivalent to RH for every choice of that single vertex. The tree is the same ordered-prime tree as for the carries. The weighting here is the ordinary Möbius function. The displacement tree instead places the repository's matched charges \(b_m/m\) at the vertices. The arithmetic criterion below allows no substitution of one family of charges for the other without a proof.

### The signed descendant sum

Write the primes of a squarefree number in increasing order. A child appends a strictly larger prime, so a path visits each of the initial products. Write \(r\preceq m\) when the factors of \(r\) form the initial segment of the factors of \(m\). Put \(y=P^+(r)\), with \(P^+(1)=1\), and \(P_y=\prod_{p\le y}p\). For integer \(x\ge0\) define

\[
 F(x,y)=\sum_{n\le x,\ (n,P_y)=1}\mu(n),\qquad M(x)=F(x,1).
\]

All sums start at 1. Every descendant of \(r\) has the unique form \(rk\) with all prime factors of \(k\) greater than \(y\). Consequently

\[
 S_r(X):=\sum_{\substack{m\le X\\r\preceq m}}\mu(m)=\mu(r)F(\lfloor X/r\rfloor,y).
\]

At \(r=6,X=42\) the descendants are \(6,30,42\). The signs are \(+,-,-\). Deleting the common prefix \(2,3\) leaves \(1,5,7\) and gives \(S_6(42)=F(7,3)=-1\).

### Reading upward and pruning terminal children

For \(x\ge1\), partition the nontrivial terms of \(F(x,y)\) by their least prime \(p\). Every remaining prime is greater than \(p\), and adjoining \(p\) reverses the sign. The root term is \(\mu(1)=1\). Therefore

\[
F(x,y)=1-\sum_{y<p\le x}F(\lfloor x/p\rfloor,p).
\]

If \(p>\sqrt x\), the child has no further vertices at this cutoff, so its suffix sum equals 1. Set \(z=\min\{x,\max(y,\lfloor\sqrt x\rfloor)\}\). All terminal children in this range can be counted in one operation, giving the exact formula

\[
 F(x,y)=1-\sum_{y<p\le\sqrt x} F(\lfloor x/p\rfloor,p)-[\pi(x)-\pi(z)].
\]

Define \(F(0,y)=0\). Wolfram checked this pruned formula against direct Möbius enumeration for every \(1\le x\le80\) and \(0\le y\le15\). Further exact results are

| \(X\) | \(M(X)\) | \(S_6(X)\) |
|---:|---:|---:|
| 42 | −2 | −1 |
| 100 | 1 | −3 |
| 2310 | −1 | −33 |

### Why one fixed subtree is enough

Separate the small and large prime factors uniquely. Write \(a\) for the product of the primes at most \(y\) that divide a squarefree integer. Summing first over \(a\) gives

\[
 M(x)=\sum_{a\mid P_y}\mu(a)F(\lfloor x/a\rfloor,y).
\]

The inverse uses **all powers** of the primes in \(P_y\). Put \(\mathcal S_y=\{a\ge1:p\mid a\Rightarrow p\le y\text{ for every prime }p\}\). Then

\[
 F(x,y)=\sum_{a\in\mathcal S_y,\ a\le x}M(\lfloor x/a\rfloor).
\]

To check the inverse, swap the two finite sums and fix the product \(n\). Its coefficient is \(\sum_{a\mid n,\ a\in\mathcal S_y}\mu(n/a)\). At each prime at most \(y\) dividing \(n\), the two potentially nonzero choices for the exponent in \(n/a\) cancel; if no such prime divides \(n\), the coefficient is \(\mu(n)\).

For any fixed \(\sigma>0\), a bound \(|F(x,y)|\le Cx^\sigma\) transfers to \(M\) with constant \(C\prod_{p\le y}(1+p^{-\sigma})\). A bound \(|M(x)|\le Cx^\sigma\) transfers to \(F\) with constant \(C\prod_{p\le y}(1-p^{-\sigma})^{-1}\). Finally \(S_r(rx)=\mu(r)F(x,y)\) recovers every integer cutoff. Combining these facts with Littlewood's classical criterion gives the stated RH equivalence. Titchmarsh, *The Theory of the Riemann Zeta-function*, second edition, Theorem 14.25(c). See the published [Hu, Kaneko, Martin and Schildkraut paper](https://www.cambridge.org/core/journals/mathematical-proceedings-of-the-cambridge-philosophical-society/article/on-a-mertenstype-conjecture-for-number-fields/B01C7628DF4D57CAE8410901FD6A9321), §1.

There is a companion analytic interpretation. For \(\Re s>1\), absolute convergence and the Euler product give

\[
 \sum_{r\preceq m}\frac{\mu(m)}{m^s}
 =\frac{\mu(r)r^{-s}}{\zeta(s)\prod_{p\le P^+(r)}(1-p^{-s})}.
\]

For fixed \(r\), the finite product has no zeros on \(\Re s>0\), and the numerator has no zeros anywhere. Every zero of \(\zeta\) in \(\Re s>1/2\) gives a pole of each fixed subtree transform with exactly the same order. Thus RH also means that the transform of any one fixed subtree extends holomorphically throughout that half-plane. The pole of \(\zeta\) at 1 gives a zero of the continued subtree transform. This is analytic continuation of the function initially defined in \(\Re s>1\).

### A sharp limitation on pruning estimates

For prime \(p\), set \(X=p^3\) and choose the moving subtree rooted at \(p\). The only vertices below this cutoff are \(p\) and \(pq\) with \(p<q\le p^2\) prime. Indeed, any two additional primes would both exceed \(p\). Hence

\[
 S_p(p^3)=\pi(p^2)-\pi(p)-1\sim \frac{p^2}{2\log p}
 = \frac{3}{2}\frac{X^{2/3}}{\log X}.
\]

The asymptotic uses the prime number theorem. Thus a common bound \(C_\varepsilon X^{1/2+\varepsilon}\) on **all moving subtrees** is false for every \(0<\varepsilon<1/6\). Wolfram gives the exact charges 150, 1,225, and 79,660 at \(p=31,101,1009\). Already at the root the terminal range \(\sqrt X<p\le X\) contributes \(-[\pi(X)-\pi(\sqrt X)]\) of order \(X/\log X\). A valid upward proof must retain signed cancellation between terminal and deeper children. Taking absolute values first would lose more than the whole RH budget.

The repository's unconditional \(M(X)\ll X\exp[-c\sqrt{\log X}]\) controls the ordinary profile but is asymptotically larger than \(X^{1/2+\varepsilon}\) for each fixed \(0<\varepsilon<1/2\). The fixed-prefix transfer carries the known scale between root and subtree. An improvement to the RH exponent still requires independent arithmetic cancellation.

### A reciprocal Möbius example where limiting children lose mass

Use vertex charges \(\mu(m)/m\) and let \(T_r(H)\) be the resulting signed mass under a fixed prefix. For each such \(r\),

\[
T_r(H)=\frac{\mu(r)}{r}\sum_{k\le H/r,\ (k,P_y)=1}\frac{\mu(k)}k\longrightarrow0,
\qquad y=P^+(r).
\]

For a proof, let \(A(t)=\sum_{n\le t}\mu(n)/n\), which is bounded and tends to zero by the prime number theorem. The finite convolution used above rewrites the rough reciprocal sum as \(\sum_{a\in\mathcal S_y}A(\lfloor H/(ra)\rfloor)/a\), with \(A(0)=0\). Dominated convergence applies because \(\sum_{a\in\mathcal S_y}a^{-1}=\prod_{p\le y}(1-p^{-1})^{-1}<\infty\). This fixed-prefix limit is also a special case of [Terence Tao, *Bull. Aust. Math. Soc.* 81 (2010)](https://doi.org/10.1017/S0004972709000884).

Yet for every \(H\ge2\), the partition into the vertex 2 and its children gives

\[
T_2(H)=-\tfrac12+\sum_{2<p\le H/2}T_{2p}(H).
\]

The child sum therefore tends to \(+1/2\), whereas the sum of the individual child limits is zero. Removing any fixed finite set of children leaves the same limiting \(+1/2\). This explicitly exhibits the lack of uniform tail control when interchanging a growing child sum with its cutoff limit. The example uses the ordinary reciprocal Möbius coefficients.

### Lean boundary

The module `RoughMertensSubtree.lean` specializes the quantitative transfer to the branch \(r=2\). Its starting theorem in the repository, `M_nat_eq_oddMertensPrefix_sub`, is the exact parity-pruning identity \(M(x)=F(x,2)-F(\lfloor x/2\rfloor,2)\). With \(B_q(f)\) denoting \(\exists C\ge0,\ \forall j\ge0,\ \forall n<2^j,\ |f(n)|\le Cq^j\) (that is, for all integers \(j\ge0\) and \(0\le n<2^j\)), its theorem `root_iff_twoBranch` transfers \(B_q\) in both directions at every \(q>1\). For \(q=2^\sigma\), this is exactly an \(O(x^\sigma)\) bound by taking the smallest \(j\) with \(x<2^j\). The final RH statement in the module names Littlewood's classical analytic equivalence as its one hypothesis. The all-prefix finite-Euler-factor proof and the prime-cube obstruction above are paper arguments. [Repository parity identity](https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/NumberTheory/PrimeNumberTheorem/MertensOddSquareSieve.lean)

## Reading upward with Taylor coefficients

The signed tree has an exact numerical RH criterion. Set $P_0(x)=1$ and, for integers $k\ge1$, define

$$
P_k(x)=\sum_{j=1}^k {k-1\choose j-1}\frac{(-x)^j}{j!},\qquad
A_k=\sum_{m\ge1}\frac{\mu(m)}{m^2}P_k(3\log m).
$$

Only squarefree nodes contribute. Each fixed coefficient is absolutely summable. On a disk about zero the finite signed prime-tree products converge to $1/\zeta(\phi(z))$ for $\phi(z)=(2+z)/(1-z)=2+3z/(1-z)$. To find the coefficient $A_k$ of this germ, write each summand as $m^{-2}\exp(-3\log(m)z/(1-z))$. The Laguerre generating function gives $[z^k]\exp(-xz/(1-z))=P_k(x)=L_k^{(-1)}(x)$. Interchanging the expansion with the sum follows from locally uniform absolute convergence whenever $\Re\phi>1$. A disk of radius $1/8$ around zero suffices, since $|\phi(z)-2|\le3/7$ there. The map $\phi$ sends the unit disk bijectively to $\Re s>1/2$. Cauchy–Hadamard and uniqueness of holomorphic continuation give

$$
\mathrm{RH}\quad\Longleftrightarrow\quad\limsup_{k\to\infty}|A_k|^{1/k}\le1
\quad\Longleftrightarrow\quad
\forall\,0<r<1,\quad\sup_{k\ge0}r^k|A_k|<\infty .
$$

For fixed $k\ge1$ and integer $N\ge e^{k/2}$, either (i) truncate to $m\le N$, or (ii) keep the complete finite prime tree with all primes $p\le N$ and all their squarefree products. In either case the omitted terms are among $m>N$, so the approximation $A_{k,N}$ satisfies

$$
|A_k-A_{k,N}|\le \frac1N\sum_{j=1}^k {k-1\choose j-1}3^j
       \sum_{i=0}^j\frac{(\log N)^i}{i!}.
$$

Indeed $x^{-2}(\log x)^j$ is decreasing for $x\ge e^{j/2}$, and its integral from $N$ to infinity is $j!N^{-1}\sum_{i=0}^j (\log N)^i/i!$. For $k=0$ the bound is $1/N$. These estimates certify individual coefficients. The RH criterion requires growth control as $k$ varies. This coefficient criterion is an analytic corollary of the Lean extension theorem, proved here on paper.

[DLMF 25.2.11, Euler product](https://dlmf.nist.gov/25.2.E11), [DLMF 18.12.13, Laguerre generating function](https://dlmf.nist.gov/18.12.E13).

The Wolfram Language kernel gave the following independent check. The middle column uses direct derivatives of $1/\zeta(\phi(z))$ at zero divided by $k!$. The last column sums the squarefree terms with $m\le10{,}000$.

| $k$ | Taylor coefficient | Finite node sum |
|---:|---:|---:|
| 0 | 0.607927101854 | 0.607926897331 |
| 1 | 1.039484204105 | 1.039489869351 |
| 2 | −0.491469772816 | −0.491542562178 |

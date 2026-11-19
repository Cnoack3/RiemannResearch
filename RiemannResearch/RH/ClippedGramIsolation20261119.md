# Isolation with eight- and ten-point Gram certificates

For each fixed $0<c\le 10^{-5}$, a lower bound for the proportion of zeros isolated on both sides in the full multiplicity-counted array is **0.6736373773** using the ten-point certificate. The eight-point certificate separately gives **0.6735364025**. Kim's preprint reports 0.672468 for the same statistic and range. Here the frame certificate is used on a subset already known to be isolated. The argument bounds the complement by its own spectral contribution. [Kim, Theorem 1.1 and Proposition 3.1](https://hexagonmath.org/pdf/2611.00318v1) · [Knausgård, §5](https://arxiv.org/html/2610.08965v1) · [Verified ten-point submission](https://www.riemannzeta.fun/submissions/bakken-ten-hw-one-unit)

The fixed-gap refinement gives 0.673637381 at the same cutoff and retains quantitative proportions through 0.61485 of mean spacing, with a further pair-energy-only refinement through 0.61701890. It uses the trace inequality proved here. [Fixed-gap isolation](FixedGapIsolation20261119.md)

## A trace inequality

Use $\varphi_2(t)=t^2-(t-2)_+^2$ and $g(t)=4-(2-t)_+^2$ for $t\ge0$. Let $P$ be positive semidefinite and $Q=B_s+B_w-Z$, where the three summands before their signs are positive semidefinite. Assume $\operatorname{rank}B_s\le r$ and write $B_w=\sum_i u_i u_i^*$. Then

$$
\operatorname{tr}(P+Q)^2\ \ge\
\operatorname{tr}\varphi_2(P)+4\operatorname{tr}Q-4r-\sum_i g(\|u_i\|^2).
\tag{1}
$$

Write $Q=Q_+-Q_-$ for its spectral parts. The nonnegative cross term $\operatorname{tr}(P Q_+)$ and $Q_-Q_+=0$ give $\operatorname{tr}(P+Q)^2\ge\operatorname{tr}(P-Q_-)^2+\operatorname{tr}Q_+^2$. Completing the square with $(P-2I)_+$ gives $\operatorname{tr}(P-Q_-)^2\ge\operatorname{tr}\varphi_2(P)-4\operatorname{tr}Q_-$. For the remaining term, $t^2\ge4t-g(t)$, and $0\le g\le4$. In decreasing order, the eigenvalues after position $r$ obey $\lambda_{r+i}(Q_+)\le\lambda_i(B_w)$ by Loewner monotonicity and Weyl's rank inequality. For $r$ exceeding the dimension the tail is empty. The Gram matrix of the vectors $u_i$ has the same nonzero eigenvalues as $B_w$ and diagonal $\|u_i\|^2$. Jensen on its spectral resolution, using the concavity of $g$ and $g(0)=0$, yields $\operatorname{tr}g(B_w)\le\sum_i g(\|u_i\|^2)$. Summing in these inequalities proves (1). [Knausgård, Lemma 2.1](https://arxiv.org/html/2610.08965v1)

## What each nonisolated group costs

Represent the zeros as Kim's finite conjugation-invariant multiset, with the real coordinate equal to the normalized ordinate. Start with simple real points that are at distance greater than $2c$ from every other simple real point. Of these retain in $P$ exactly the points also $c$-isolated from the full finite array. Every omitted member of this first set is assigned to one repeated real point or one reflected nonreal pair within distance $c$ of its real coordinate. At most one member can be assigned to each such group. Partition the remaining simple real points into consecutive pairs and triples, with every successive gap at most $2c$, in each maximal cluster. Denote by $n$ the number retained in $P$ and by $N$ the cardinality with multiplicity. The finite isolated count is at least $n$. [Kim, proof of Proposition 3.1](https://hexagonmath.org/pdf/2611.00318v1)

Write $e=\pi^2 c^2\le1/16$, and let $m$ denote a group's total number of occurrences. For each group remove its negative frame term and retain the top eigenpart of its positive frame in $B_s$. Its remaining positive eigenparts contribute the vectors $u_i$ in (1). Its signed trace equals $m$. In the table, the baseline contribution sought for each group is $2m$ and the rank allowance is one per group. The elementary estimate $K(t)\ge1-\pi^2t^2/2$ follows from the probability density on $[-1/2,1/2]$. [Kim, equations (3.7)–(3.13)](https://hexagonmath.org/pdf/2611.00318v1)

| Group | Trace in the remaining positive eigenparts | Loss below $2m$ |
|---|---|---|
| Two simple real points | $1-K(\Delta)\le2e$ | At most $8e$ |
| Three simple real points | At most $2[1-(1-2e)^2]\le8e$, by projecting on the middle point | Zero, since $4m-4-32e\ge2m$ |
| Repeated real point | Zero without an assignment, at most $e$ with one, by projecting on the repeated point | Zero |
| Reflected pair without an assignment | Zero | Zero |
| Reflected pair of individual multiplicity at least two with an assignment | One eigenvalue at most one | Zero, since $m\ge5$ and $g(1)=3$ |

For a reflected pair of individual multiplicity one with an assigned simple point, $m=3$. Put $M(y)=\int f(u)\cosh(2\pi yu)\,du$, $A=1+M(2y)$, and write the canonical reflected frame as $2gg^*-2hh^*$. For zero ordinate offset, the positive part before subtracting $2hh^*$ is $2gg^*+\phi\phi^*$. Its $2$-by-$2$ Gram matrix has diagonal $(A,1)$ and off-diagonal entry $\sqrt2 M(y)$. Its smaller eigenvalue is

$$
w(y)=\frac{A+1-\sqrt{(A-1)^2+8M(y)^2}}{2}.
$$

At ordinate distance at most $c$, the off-diagonal magnitude is at least $(1-e/2)\sqrt2 M(y)$. With $k$ its squared normalized magnitude, $0\le k\le1$, this lowers $k$ by at most $e$ from the value at zero offset. The smaller eigenvalue as a function of $k$ has derivative $-A/\sqrt{(A-1)^2+4Ak}$, of magnitude at most $2$ since $A\ge2$. As $g$ is $4$-Lipschitz, the group's loss below $2m$ is at most $[g(w(y))-2]_++8e$. The total gap losses across disjoint groups are at most $4eN$, using $8e$ for a two-copy group and at most $8e$ for a charged three-copy group.

Consequently the full pair energy $S=\operatorname{tr}(P+Q)^2$ satisfies

$$
S\ge\operatorname{tr}\varphi_2(P)+2(N-n)
-\sum_{\text{distinct right zeros }z}[g(w(|\Im z|))-2]_+-4\pi^2c^2N .
\tag{2}
$$

## Converting the window certificates to an isolation proportion

For each window let $x,b$ certify $\operatorname{tr}\varphi_2(P)\ge(1+x)n-b\,\operatorname{span}-\omega(\varepsilon)n-O(1)$ for the normalized smoothed window, with $\omega(\varepsilon)\to0$. Knausgård's (5.2) explicitly quantifies over every finite real set, permitting the retained points above. For the ten-point window, the pinned formal source supplies the same implication through its finite matrix theorem matching_defect_bound_n, W10_B and cert_AM. Its score function is $\Psi(t)=\varphi_2(t)-2t+1$, so its trace is $\operatorname{tr}\varphi_2(P)-n$ for the normalized Gram with trace $n$. The separated bound in that file is $1253/650<2$. Multiplying by the reciprocal cutoff mass preserves the cap $2$ for all sufficiently small fixed smoothings. The difference of Fourier entries is bounded uniformly by the $L^1$ distance of the densities. These are the hypotheses of matching_defect_bound_n; the coefficient of its smoothing error for a ten-point frame is $36$. [Knausgård, (3.1), (5.2), Propositions 5.2–5.3](https://arxiv.org/html/2610.08965v1) · [Pinned ten-point Lean source at a3cc59d](https://github.com/josusanmartin/riemann/blob/a3cc59dd21fadc2177cc01ea4fad3226b814f20d/submissions/bakken-ten-hw-one-unit/proof/Solution.lean)

Let $h\le2-C(f)$ bound the window energy coefficient. The strict numerical majorant is $g(w(y))-2<\ell(y-a)_+$ on $[0,3]$, while $w\le1$ and $\ell(3-a)>1$ take care of the rest. The positive-part majorant holds for all sufficiently small smoothings because the Laplace transforms converge uniformly on $[0,6]$ and the compact majorant has a finite strict margin. The sum over distinct right zeros in (2) is bounded by its multiplicity-counted counterpart. Its normalized stop-loss cost is at most $\ell F(2\pi a)/(4\pi)$ by the finite reflection identity. The retained span is at most $T\log T/(2\pi)=N(T)+o(N(T))$. The finite count loses at most two possible isolated members on returning to the infinite-neighbor convention. Taking the height limit at fixed smoothing and then the smoothing limit gives

$$
\liminf_{T\to\infty}\frac{B_0(T,c)}{N(T)}
\ge \frac{h-b-\ell F(2\pi a)/(4\pi)-4\pi^2c^2}{1-x}.
\tag{3}
$$

| Source window | Reward $x$ | Span charge $b$ | $h$ | $(a,\ell)$ | Certified lower bound at $c=10^{-5}$ |
|---|---:|---:|---:|---:|---:|
| Eight points | $8722/10^6$ | $4389/10^6$ | $2-1327947272845/10^{12}$ | $(1439/1000,7358/10000)$ | $0.6735364025$ |
| Ten points | $78629501063688385648757192860/D$ | $39745053312603427868508160000/D$ | $67206299948881203266318003264831248651423598405947/10^{50}$ | $(36/25,7348/10000)$ | $0.6736373773$ |

Here $D=8388608000000000000000000000000$. The eight-point energy certificate tightens the paper's outward rounding by evaluating the same expression at its fixed coefficients. For both windows the interval replay independently evaluates this energy and recomputes the transform from the actual window coefficients. On $[u,v]$ it substitutes the upper bound $A(v)$ and lower bound $M(u)$ into $w$, which increases with the former argument and decreases with the latter. The eight-point replay covers 10,730 rational intervals and the ten-point replay covers 10,811, both to maximum bisection depth 20. The ten-point value at the stated parameter is 0.6736373773645649378456577045864655841. The external window interaction certificates and Kim's analytic pair-energy asymptotic remain explicit inputs. The numeric replay verifies the new majorants and the arithmetic of (3); its interval computations are outside Lean's kernel. [Numerical replay](BoundCertificateReplays20261119.md#verify_isolation_profilepy) · [Fixed-threshold stop-loss and height limits](OptimizedHorizontalMoments20261119.md) · [Montgomery–Taylor comparison and local-height conversion](IsolatedZeroStopLoss20261119.md)

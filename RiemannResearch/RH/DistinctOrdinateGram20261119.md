# Distinct positive ordinates and full-array collisions

Let $D(T)=\#\{\gamma:0<\gamma\le T,\;\zeta(\beta+i\gamma)=0,\ 0<\beta<1\}$ and let $N(T)$ count all nontrivial zero occurrences in the same window. Thus a reflected off-line pair contributes one to $D(T)$, and every other zero at that same height also shares this one ordinate. The new lower bounds for $\liminf D(T)/N(T)$ are **0.83392118** from the Montgomery–Taylor window and **0.83449280** from the ten-point window. Both use the fixed-strike Conrey stop-loss input. Only the ten-point result needs the external interaction certificate. The Lean consumer uses the cardinality of the image of the actual height cutoff under the imaginary-coordinate map. The finite-frame/energy estimate and the independent numerical certificate are scoped hypotheses. [Lean consumer](../Analysis/ActualDistinctOrdinateGram.lean) · [Numerical replay](BoundCertificateReplays20261119.md#verify_distinct_ordinatespy)

The verified ten-point distinct-critical-line proportion, approximately $0.67363929$, is a lower bound for this ordinate proportion by inclusion. Knausgård's $0.83900459$ counts distinct complex numbers, which can share an ordinate. The new estimates compare to the critical-line inclusion and do not improve the cited complex-distinct count. In the repository's Langer phase-frame criterion they allow every dimension $d\le T^\beta$ with $\beta$ strictly below the indicated ordinate proportion, given the separate Langer input. [Knausgård, Theorems 1.1 and 1.3](https://arxiv.org/html/2610.08965v1) · [Ten-point source](https://www.riemannzeta.fun/submissions/bakken-ten-hw-one-unit) · [Actual distinct ordinates](../Analysis/ActualDistinctOrdinateProportion.lean)

Two research-platform manuscripts dated November 18, 2026 supply further comparators. Paper 179 Theorem 1 gives 0.67385611 for simple critical-line zeros and hence for distinct ordinates by inclusion. Paper 178 gives 0.840002554868691 for distinct complex zeros and 0.680005109737382 for simple zeros at any real part. A horizontal reflection pair can contain two distinct simple complex zeros at the same height. These source numbers use different counted sets. [Paper 179, Theorem 1](https://rstation.ai/problems/riemann_hypothesis/papers/179) · [Paper 178, Theorem 1](https://rstation.ai/problems/riemann_hypothesis/papers/178)

## Exact finite counting at coincident heights

Normalize heights by $\log T/(2\pi)$ as in Kim. At each distinct height let $n_r$ be the number of critical-line copies and $r$ the number of right-half-plane copies. Reflection supplies the same number on the left. The group multiplicity is $m=2r+n_r$. A singleton has $n_r=1$, $r=0$. Let $n$ count those singleton groups and $D$ all height groups. The exact excess multiplicity of nonsingleton groups is
$$
 n=2D-N+\sum_{m\ge2}(m-2).
\tag{1}
$$
All real duplicates and all off-line pairs at a fixed height belong to that one group, even when their real parts differ. The singleton-block interaction applies only after excluding every height with more than one occurrence. The positive contributions of the remaining groups are analyzed with one strong rank per occupied height. [Full signed frames](ClippedGramIsolation20261119.md) · [Kim's common-ordinate decomposition](https://hexagonmath.org/pdf/2611.00318v1)

For an even probability density $f$ on $[-1/2,1/2]$ define $M(y)=\int f(t)\cosh(2\pi yt)\,dt$. At a group at height $x$, factoring out the common phase of its frame, a critical-line copy gives the unit vector $1$. A right copy and its reflection contribute the positive vector $v_y=\sqrt2\cosh(2\pi yt)$ and a negative frame. Their signed trace equals two. Write
$$
 A_y=\lVert v_y\rVert^2=1+M(2y),\quad
 B_{y,z}=\langle v_y,v_z\rangle=M(y+z)+M(y-z),\quad
 g(t)=4-(2-t)_+^2 .
$$
In the finite spectral inequality from the companion note put the $n$ singleton frames in $P$. Each other height contributes its strongest positive rank to $B_s$ and its remaining positive eigenparts to $B_w$. If the singleton window has interaction reward $x_0$ and span charge $b$, then, up to its smoothing error,
$$
 S \ge (1+x_0)n-b\,\mathrm{span}+4(N-n)-4(D-n)-\sum_{\rm weak}g(w)
   =4N-4D+(1+x_0)n-b\,\mathrm{span}-\sum_{\rm weak}g(w).
\tag{2}
$$
Discard the nonnegative $x_0\sum(m-2)$ in (1); the remaining group-specific slack is $m-2$ per nonsingleton. This integer credit matters when bounding the weak prices.

## Three spectral prices cover every collision

Fix a trial height $z$. In each group with many copies, compress its positive frame onto $v_z^\perp$, including the common ordinate phase in the test vector. Interlacing bounds every positive eigenvalue after the largest by the corresponding eigenvalue of this compression. The Gram of the projected vectors has the same nonzero spectrum. Jensen for the concave increasing $g$, with $g(0)=0$, bounds its trace price by the sum of the prices of squared projected vector norms. A real copy has price $h_0=g(1-2M(z)^2/A_z)$; a right copy has price $h_z(y)=g(A_y-B_{y,z}^2/A_z)$. The numerical certificate gives $h_0<1$. Define $L=\min(4/3,1+(1-h_0)/2)$.

- For $r\ge3$, the budget $m-2$ is at least $4r/3+n_r$. For $r=2$ and $n_r\ge1$, it is $2+n_r$, which covers $n_r h_0+rL$. Both types have total unabsorbed price bounded by $\sum_{\rm right}[h_z(y)-L]_+$.
- For $r=1$ and $n_r=j\ge1$ the positive part is a two-vector Gram, with diagonal entries $(A_y,j)$ and off-diagonal $\sqrt{2j}\,M(y)$. Denote its smaller eigenvalue by $w_j(y)$. The slack is $j$. When $j\ge4$, $g(w_j)\le4\le j$. Otherwise the additional signed cost is $g(w_j(y))-j$.
- For $r=2$ and $n_r=0$, order the horizontal positions $0\le u\le y$. The two-vector Gram has diagonal $(A_u,A_y)$ and off-diagonal $B_{u,y}$. The signed cost is $g(w(u,y))-2$ for its smaller eigenvalue $w(u,y)$. Charge it to the larger horizontal position. For pure real groups and for $r=1,n_r=0$ the positive rank is one, so there is no weak price.

For both chosen windows all three signed quantities are bounded by $\ell(y-a)_+$ at every permitted $y$ and $u$. In the third case, charging all right copies their nonnegative majorant only enlarges the upper bound. Equations (1)–(2) now give
$$
 S\ge(3-x_0)N-2(1-x_0)D-b\,\mathrm{span}
   -\ell\sum_{\rm right}(y-a)_+ - o_\varepsilon(1)N-O(1).
\tag{3}
$$
The MT window has $x_0=b=0$ by convex Jensen on the singleton Gram. The ten-point constants $x_0,b$ are those in the pinned interaction certificate, applied to the distinct singleton heights. The span is at most $T\log T/(2\pi)=N(T)+o(N(T))$. The unweighted pair energy has the same asymptotic as in the companion note. [Eight- and ten-point input audit](ClippedGramIsolation20261119.md) · [Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh, Acta Arithmetica (2024)](https://doi.org/10.4064/aa230612-20-3)

## Directed numerical and asymptotic certification

For each scalar Gram with diagonals $a_1,a_2$ and nonnegative off-diagonal $q$, its smaller eigenvalue is $(a_1+a_2-\sqrt{(a_1-a_2)^2+4q^2})/2$. This value increases in either diagonal and decreases in $q$. For $0\le y\le2$, $A_y$, $M(y)$ and $B_{y,z}$ increase in $y$ by their cosh integral representations. These monotonicities provide directed bounds on each scalar interval. On the two-dimensional domain $0\le u\le y\le2$, a rectangle $[u_0,u_1]\times[y_0,y_1]$ uses the upper diagonals $A_{u_1},A_{y_1}$ and lower off-diagonal $M(u_0+y_0)+M(\max(0,y_0-u_1))$ after clipping the empty corner. The finite cover has strictly positive margins. For $y\ge2$, every signed price is at most three and $\ell(2-a)>3$. Uniform convergence of smoothed Laplace transforms on the required compact argument interval preserves all prices and majorants. The scalar tail bound applies to every smoothed density.

Let $H$ be the certified lower bound for $2-C(f)$ and $F(t)=\log[(1-e^{-22t/7})/(1-e^{-8t/7})]$. Apply the finite reflection identity and fixed Conrey strike to (3), first passing to large heights and then removing the smoothing. The lower ordinate proportion is
$$
 \frac{1+H-x_0-b-\ell F(2\pi a)/(4\pi)}{2(1-x_0)} .
$$

| Window | $z$ | $a$ | $\ell$ | Scalar intervals | Triangle boxes | Directed value, rounded down |
|---|---:|---:|---:|---:|---:|---:|
| Montgomery–Taylor | $0.640$ | $0.795$ | $17.62$ | 1,593 | 1,086 | $0.83392118$ |
| Ten points | $0.641$ | $0.797$ | $17.69$ | 1,950 | 1,061 | $0.83449280$ |

The corresponding full values start at $0.8339211845848170926$ and $0.8344928087481432319$. The result keeps the complex-distinct, critical-line and all-ordinate counts separate throughout. [Directed verification](BoundCertificateReplays20261119.md#verify_distinct_ordinatespy) · [Conrey stop-loss profile](OptimizedHorizontalMoments20261119.md)

## If microscopic horizontal displacement vanishes

The Lean source defines the multiplicity of each actual ordinate as the cardinality of its fibre in the type of zero occurrences. It proves that every represented height has positive multiplicity, that the fibre multiplicities sum to $N(T)$, the exact singleton partition (1), and the per-group slack inequality for reflected groups with at least three pairs or two pairs plus at least one real copy.

If the full mean of $(\log T)|\beta-1/2|$ tends to zero, the finite reflection identity implies that all fixed-strike right-hand prices in (3) tend to zero. The general source-supported ordinate bound then becomes
$$
 \frac{1+H-x_0-b}{2(1-x_0)} .
$$
For the ten-point window this is exactly $(1+\kappa_{10})/2=0.83681964408330198\ldots$. The Montgomery–Taylor limit is $(1+\kappa_{\rm MT})/2=0.836250351839\ldots$. The vanishing hypothesis is stronger than the presently known upper bounds for that mean. The finite frame/energy input and angular prices remain explicit hypotheses. [Microscopic mean consumer](../Analysis/ActualDistinctOrdinateGram.lean) · [Finite reflection](IsolatedZeroStopLoss20261119.md)

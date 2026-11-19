# Fixed-gap isolation in the full zero array

Let $B_0(T,c)$ count occurrences at positive ordinates at or below $T$ whose two adjacent gaps in the full infinite list exceed $2\pi c/\log T$. The denominator $N(T)$ counts all zeros with analytic multiplicity. Every qualifying zero is simple and on the critical line. Each row gives a lower bound for $\liminf B_0(T,c)/N(T)$ for every fixed $0<c\le C$. [Kim, Theorem 1.1 and definitions](https://hexagonmath.org/pdf/2611.00318v1)

| Window | $C$ | Strike $a$ | Slope $\ell$ | Certified lower bound | Rational intervals |
|---|---:|---:|---:|---:|---:|
| Eight points | $10^{-5}$ | $1.439$ | $0.7358$ | $0.673536406$ | 11,205 |
| Ten points | $10^{-5}$ | $1.440$ | $0.7348$ | $0.673637381$ | 11,311 |
| Ten points | $0.0831944$ | $1.455$ | $0.6912$ | $2/3$ | 3,552 |
| Ten points | $1/6+10^{-8}$ | $1.519$ | $0.5529$ | $0.64455851$ | 3,028 |
| Ten points | $1/4+10^{-8}$ | $1.148$ | $0.8426$ | $0.60369938$ | 2,110 |
| Tuned cosine | $1/3+10^{-8}$ | $0.841$ | $1.4688$ | $0.53929888$ | 1,505 |
| Tuned cosine | $2/5+10^{-8}$ | $0.695$ | $1.8296$ | $0.46427262$ | 1,177 |
| Tuned cosine | $9/20+10^{-8}$ | $0.622$ | $1.9507$ | $0.38986860$ | 995 |
| Tuned cosine | $1/2+10^{-8}$ | $0.574$ | $1.9559$ | $0.29675518$ | 774 |
| Tuned cosine | $11/20+10^{-8}$ | $0.546$ | $1.8460$ | $0.18242429$ | 760 |
| Tuned cosine | $3/5+10^{-8}$ | $0.539$ | $1.6910$ | $0.04520996$ | 690 |
| Tuned cosine | $0.61485$ | $0.540$ | $1.6314$ | $0.00001338$ | 678 |

These figures are new in this repository. The local Lean theorem checks their implication for actual zeta-zero counts from the explicit finite-frame and pair-energy input, the Conrey stop-loss input and the numerical certificate. The small-gap windows use the indicated interaction certificates. Knausgård's preprint records a finite computation outside the kernel. The ten-point public submission provides a pinned Lean source. The tuned windows use ordinary Jensen on the isolated block. The new fixed-gap argument has no peer-review record. [Source windows and finite spectral lemma](ClippedGramIsolation20261119.md) · [Conditional Lean consumer](../Analysis/ActualGramTwoNeighborIsolation.lean) · [Directed numerical replay](BoundCertificateReplays20261119.md#verify_fixed_gap_isolationpy) · [Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh, Acta Arithmetica (2024)](https://doi.org/10.4064/aa230612-20-3)

At half mean spacing and above, the two-frequency extremizers give sharper proportions using the pair-energy input alone. They extend positivity to $0.61701890$ and give an upper ceiling of $0.61701891$ for this variational coefficient. [Sharp extremizing windows](VariationalIsolation20261119.md)

## The finite groups

Use Kim's conjugation-invariant finite multiset of normalized zeros. Its real coordinate is the ordinate up to an overall sign. The absolute imaginary coordinate is $y=|\beta-1/2|\log T/(2\pi)$. Use the specified even, positive unit-mass density $f$ on $[-1/2,1/2]$, initially smoothed. Define

$$
M(y)=\int f(t)\cosh(2\pi yt)\,dt,\qquad
J(y,v)=\int f(t)\cosh(2\pi yt)\cos(2\pi vt)\,dt,\qquad K(v)=J(0,v).
$$

Fix $0<c\le C\le1$ and set $k=K(C)$, $d=K(2C)$ and $p=1-k^2$. The certificates show $k,d>0$ and $K(v)\ge d$ for $0\le v\le2C$. For every $y\ge0$, $J(y,v)$ decreases on $[0,1]$ since $t\sin(2\pi vt)\ge0$ there. At any offset of magnitude at most $C$ the mixed-frame inner-product magnitude is bounded below by $J_C(y)=\max(J(y,C),0)$.

Arrange the simple real points by coordinate and split at successive gaps greater than $c$. Partition each nonsingleton cluster into consecutive pairs and triples. Retain each singleton at distance greater than $c$ from every other ordinate in the full finite multiset. Assign each remaining singleton to one obstructing repeated real point or reflected pair with real coordinate within $c$. Each obstruction receives at most two assignments because singleton coordinates are separated by more than $c$. Write $n$ for the retained singleton count and $N$ for the number of all occurrences. The infinite-neighbor count is at least $n-2$ after accounting for the ends of the finite list. [Kim, proof of Proposition 3.1](https://hexagonmath.org/pdf/2611.00318v1)

Use the trace inequality (1) in the companion note, with $\varphi_2(t)=t^2-(t-2)_+^2$ and $g(t)=4-(2-t)_+^2$ on $t\ge0$. In its positive part $P$ include the isolated singleton frame and every pure simple-real pair. In $Q$ include the remaining groups. Pinch the Gram matrix of $P$ onto the isolated block and the separate two-by-two blocks. The trace of the convex $\varphi_2$ decreases under pinching, by Jensen on the spectral resolution of each compressed block. The nonzero spectrum of a frame and its Gram agree and $\varphi_2(0)=0$. A pair at distance $\Delta\le c$ has eigenvalues $1\pm K(\Delta)\in[0,2]$, so contributes at least $2+2K(C)^2=4-2p$. Its loss below $2$ per occurrence is at most $p$ per occurrence. [Finite spectral trace inequality](ClippedGramIsolation20261119.md)

Each group in $Q$ has signed trace $m_g$, its number of occurrences. Designate one strong rank-one part and bound the remaining positive eigenweights $w_j$ with the price $g$. The trace inequality then assigns the contribution $4m_g-4-\sum_j g(w_j)$, to be compared with $(2-p)m_g$.

- For a simple-real triple, every adjacent Gram entry is at least $k$ and the other off-diagonal entry is at least $d$. The symmetric matrix with entries exactly $k,d$ has a positive top eigenvector with eigenvalue $1+(d+\sqrt{d^2+8k^2})/2$. Evaluating its Rayleigh quotient against the actual Gram bounds the actual top eigenvalue below by that number. Thus the two weak eigenvalues have total at most $t_0=2-(d+\sqrt{d^2+8k^2})/2$. They lie in $[0,2]$ since the full trace is three. Cauchy–Schwarz and monotonicity give a combined price at most $4t_0-t_0^2/2<2+3p$, with the final inequality checked for each row.
- For a repeated real point with $j=0,1,2$ assigned singletons, projection onto its central frame leaves trace at most $jp$. The weak positive rank is at most $j$. Concavity and monotonicity bound the price by $jg(p)$. As $g(p)-2\le p$ on $[0,1]$ and $m_g\ge2+j$, the budget $2m_g-4+m_gp$ covers this cost.
- A reflected pair without assignments has positive rank one. When the underlying multiplicity $m\ge2$ and $j=1,2$ singletons are assigned, the residual positive rank is at most $j$. Its price is at most $4j\le2(2m+j)-4$. Each such group reaches the unpenalized baseline $2m_g$.

For a reflected pair of underlying multiplicity one write its signed frame as $2uu^*-2vv^*$, with $A=2\lVert u\rVert^2=1+M(2y)$. With one assignment its positive Gram has diagonal $(A,1)$ and off-diagonal magnitude at least $\sqrt2 J_C(y)$. Its weak eigenvalue is at most
$$
w_1(y)=(A+1-\sqrt{(A-1)^2+8J_C(y)^2})/2 .
$$

With two assignments, put $s=K(\Delta)\ge d>0$ for the inner product of their frames. Their sum and difference directions have eigenweights $1+s$ and $1-s$. Keep the difference direction among the weak vectors and combine the positively weighted sum with $2uu^*$. The resulting Gram has smaller diagonal $1+s\le2$. The off-diagonal magnitude is at least $2J_C(y)$ because the two inner products have summed real part at least $2J(y,C)$ in the center's phase convention. Its smaller eigenvalue increases with the smaller diagonal holding the other entries fixed and decreases with the off-diagonal magnitude. It is at most
$$
w_2(y)=(A+2-\sqrt{(A-2)^2+16J_C(y)^2})/2 .
$$
Both comparison matrices are positive semidefinite by $2J_C(y)^2\le A$, from Cauchy–Schwarz and $2\cosh^2 v=1+\cosh(2v)$. We have $0\le w_1\le1$ and $0\le w_2\le2$. Nonorthogonal weak decompositions across different groups are allowed by the concave trace inequality on the Gram of all weak vectors. [Kim's signed frames, equations (3.7)–(3.13)](https://hexagonmath.org/pdf/2611.00318v1)

The assigned group has three or four occurrences respectively, which already contribute $3p$ or $4p$ to the gap budget. Its additional signed price is bounded by the corresponding term in
$$
\psi_C(y)=\max\{g(w_1(y))-2-3p,\;g(w_2(y))+g(1-K(2C))-4-4p\}.
$$
One may further cap the first signed term by $1-3p$ and the second by $2(1-d^2)-4p$, as proved in the variational note. The Lean definition uses these caps; the fixed-profile replay certifies the larger uncapped envelope displayed above. After summing over the disjoint groups and overcounting each nonreal price by all right-half-plane copies, the full energy $S=\operatorname{tr}(P+Q)^2$ satisfies
$$
S \ge \operatorname{tr}\varphi_2(P_{\rm isolated})+(2-p)(N-n)-
      \sum_{\text{right copies}} [\psi_C(y)]_+ .
\tag{1}
$$

## Transfer to the actual zeros

Let $x,b,h$ be the isolated block's interaction reward, span charge and lower bound for $2-C(f)$, where $C(f)$ is the pair-energy coefficient. For the smoothed window, the source gives $\operatorname{tr}\varphi_2(P_{\rm isolated})\ge(1+x)n-b\,\mathrm{span}-o_\varepsilon(1)n-O(1)$ on this subset. Its span is at most $T\log T/(2\pi)=N(T)+o(N(T))$. For fixed smoothing the full pair energy per copy tends to the corresponding smoothed coefficient. [Knausgård, (3.1) and (5.2)](https://arxiv.org/html/2610.08965v1) · [Pinned ten-point source](https://github.com/josusanmartin/riemann/blob/a3cc59dd21fadc2177cc01ea4fad3226b814f20d/submissions/bakken-ten-hw-one-unit/proof/Solution.lean)

For each row the rational certificate gives $\psi_C(y)<\ell(y-a)_+$ on $[0,4]$ with a uniform margin from the finite cover. On $[4,\infty)$ the signed prices are bounded by $1-3p$ and $g(1-K(2C))-4p$, both strictly below $\ell(4-a)$. The normalized smoothed densities approximate $f$ in $L^1$, so their $M,J$ converge uniformly on the required compact arguments $0\le y\le8$. Also $p_\varepsilon\to p$. The tail estimates require only the unit mass and real kernel values and persist after sufficiently small smoothing. On $[0,1]$ monotonicity of $K$ is automatic for every smoothing. When $2C>1$, the strict negative derivative on $[1,2C]$ persists because $K_\varepsilon'$ converges uniformly there, with error bounded by $\pi\lVert f_\varepsilon-f\rVert_1$. All other admissibility inequalities are strict. Take the height limit at fixed smoothing, followed by the smoothing limit.

The finite reflection identity and Conrey's stop-loss profile $F(u)=\log[(1-e^{-22u/7})/(1-e^{-8u/7})]$ bound the normalized right-copy price by $\ell F(2\pi a)/(4\pi)$ in the limit. The certificate verifies $1-x-p>0$. Rearranging (1) gives
$$
\liminf_{T\to\infty} B_0(T,c)/N(T)\ge
 \frac{h-b-p-\ell F(2\pi a)/(4\pi)}{1-x-p}.
\tag{2}
$$
On a rational interval $[u,v]$, substitute the upper diagonal $1+M(2v)$ and lower mixed entry $\max(0,J(u,C)+\min(0,\cos(\pi C))[M(v)-M(u)])$ in both eigenvalue formulas. This mixed bound follows by integrating the nonnegative cosh increment and using $\cos(2\pi Ct)\ge\cos(\pi C)$. Cap the two eigenvalue bounds by their smaller diagonals $1,2$. For $2C>1$, monotonicity of $K$ beyond one is checked on 128 rational subdivisions. The derivative at every point is at most the secant slope plus $\pi^2 h_0/2$ on an interval of width $h_0$, since $|K''|\le\pi^2$. Each upper bound is strictly negative. The replay verifies positivity of the tuned windows, the angular and price inequalities and the final outward rounding. The maximum cover depth is 21. [Directed interval replay](BoundCertificateReplays20261119.md#verify_fixed_gap_isolationpy) · [Finite reflection](IsolatedZeroStopLoss20261119.md) · [Conrey profile](OptimizedHorizontalMoments20261119.md)

## Choosing the tuned windows

Use $f=f_{\rm MT}+\sum_{j=1}^8 v_j\cos(2\pi jt)$ with the exact integer-over-10,000 coefficients in the replay. The Montgomery–Taylor density is $\cos(\sqrt2\,t)/(\sqrt2\sin(1/\sqrt2))$. Its minimum exceeds $\sum|v_j|$ in each row, so $f>0$ and all perturbations have zero integral. Jensen gives $\operatorname{tr}\varphi_2(P_{\rm isolated})\ge n$ since the isolated Gram has unit diagonal. These windows therefore use $x=b=0$.

The unconditional pair-energy coefficient on this support is
$$
C(f)=\int f(t)^2dt+\iint |s-t|f(s)f(t)\,ds\,dt .
$$
Montgomery–Taylor stationarity kills the linear term for every mean-zero perturbation. The cosine modes diagonalize the quadratic part with $d_j=1/2-1/(4\pi^2j^2)$, by twice integrating $(|x|)''=2\delta_0$ or elementary cosine integration. Thus $h=2-C_{\rm MT}-\sum d_jv_j^2$ exactly. Write $K_0=K_{\rm MT}(C)$ and $u_j=\int\cos(2\pi jt)\cos(2\pi Ct)dt$. Omitting the off-line price, (2) becomes $1-(C(f)-1)/K(C)^2$. Cauchy–Schwarz gives the exact optimum for this surrogate in the chosen span,
$$
\sup_v\frac{(K_0+\sum u_jv_j)^2}{C_{\rm MT}-1+\sum d_jv_j^2}
 =\frac{K_0^2}{C_{\rm MT}-1}+\sum\frac{u_j^2}{d_j},
 \qquad v_j=\frac{(C_{\rm MT}-1)u_j}{K_0d_j}.
$$
The numerical selection perturbed the common scale along this direction to account for the off-line term, then rounded each coefficient. The bound uses the replayed rational coefficients. [Pair-energy method and extremal density](https://arxiv.org/html/2610.08965v1) · [Original unconditional Montgomery theorem](https://doi.org/10.4064/aa230612-20-3)

## Comparison and consecutive gaps

Kim gives $0.672468$ for the same two-neighbor statistic at $c\le10^{-5}$. Lamzouri gives $0.5087$ at the local-height cutoff $c=1/6$. At any row with $C>c$, the local test at $\gamma_n\ge T^{c/C}$ follows from the common-height test at $C$, and Riemann–von Mangoldt gives $N(T^{c/C})/N(T)\to0$. This transfers the stated coefficients with an explicit $10^{-8}$ margin to their indicated local fractions of mean spacing. [Kim, Theorem 1.1](https://hexagonmath.org/pdf/2611.00318v1) · [Lamzouri, Theorem 1.1](https://arxiv.org/abs/2610.26841v2)

Angón–Ross–Tang–Zhao count finite-list strings of consecutive gaps allowing equality. At $c=1/4$ they give $0.3450014$, $0.1812517$ and $0.0175021$ for two, three and four. Our two-gap lower density is $0.60369938$. Write $w_k$ for the number of starting positions for $k$ consecutive strict gaps with both ends inside the cut. We have $w_2\ge B_0-2$. Translating the $k$-run starting positions by $k$, the union with the $l$-run starts lies in the same $N$ positions. Each element of the intersection yields a $(k+l)$-run after translating back. Thus $w_k+w_l\le N+w_{k+l}$. Iteration gives $mB_0\le w_{2m}+(m-1)N+2m$ for every positive integer $m$. Both three and four consecutive gaps have lower density at least **0.20739876** at quarter mean spacing. Both five and six have lower density at least **0.020912143** at $10^{-5}$. Kim's pre-existing bound already gives a positive six-gap proportion $0.017404$ by this transfer. [Angón–Ross–Tang–Zhao, Theorem 1 and definitions](https://arxiv.org/html/2610.22927v2) · [Checked finite-to-asymptotic transfer on sorted actual copies](../Analysis/ActualConsecutiveModerateGaps.lean)

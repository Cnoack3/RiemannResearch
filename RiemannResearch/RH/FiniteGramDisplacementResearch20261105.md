# Testing one finite Gram pair per physical window

For each $M$, project $1$ onto the span of the squarefree $g_m(n)=\{n/m\}$ with $2\le m\le M+1$ in two metrics, $Q(n)=1/(\zeta(2)n^2)$ and $P(n)=1/[n(n+1)]$. Write $d_M=f_{Q,M}-f_{P,M}$. These are two finite linear systems with full weighted inner products. Bagchi's Remark 8 identifies the squarefree dictionary, and his final section describes the Gram method for the original single-metric problem. [Bagchi (2006)](https://arxiv.org/pdf/math/0607733)

Put
$$
h(u;X)=\min_{\epsilon=\pm1}\sum_{n=1}^X\frac{\max(\epsilon u(n),0)}n .
$$
**Finite sufficient condition for RH.** If for some fixed $C,E\ge0$ there are arbitrarily large integers $k$ such that
$$
h(d_{2k^4};k^8)\le C(\log k)^E,
$$
then RH holds. More generally, the same implication holds with stage $M(k)$ whenever $M(k)\ge2k^4$ eventually. The sign may depend on $k$. The finite cutoffs and the proofs of the Möbius estimates used here are internal to the Lean development. The growth bound for these Gram solutions is open. [Finite probe theorem](QFiniteHarmonicProbe.lean)

## Why one conductor cutoff suffices

Use the finite Pareto residual $u_M=1-f_{P,M}$ and witness $w_M=B_0u_M-d_M$. The finite normal equations give $w_M\perp_Q V_M$. The projection convergence gives $u_M\to r_P$ and $w_M\to w$ in $L^2(Q)$. Their norms are uniformly bounded.

Fix $k$ and $M\ge2k^4$. Bertrand's postulate supplies $N\in[k,2k]$ with $N+1$ prime and a prime $k^4<p\le2k^4$. The exact-head Möbius trial $v_N$ and the prime atom $g_p$ both belong to $V_M$. With $D_N=1-v_N$ and $b_M(n)=Q(n)w_M(n)$, finite orthogonality gives the exact pairings
$$
\sum_n b_M(n)D_N(n)=\langle1,w_M\rangle_Q,\qquad
\sum_n b_M(n)(n\bmod p)=0 .
$$
This is where the finite stage earns its place in the theorem. Fixed-window convergence of $d_M$ alone gives no numerical rate on a growing window.

For an integer $A>E$, put $\delta_k=(6+\log k)^{-A}$. At all sufficiently large $k$ the proved Möbius slope bound gives $|D_N(n)|\le\delta_k n$ for every $n$. The global bound $|D_N(n)|\le3N$ controls the far tail. The cheaper sign of $d_M$ bounds the corresponding positive prefix of signed charge by
$$
\|u_M\|_Q+h(d_M;k^8)/\zeta(2).
$$
For example, on paper the elementary bound $\sum_{n>Y}|b_M(n)|\le \|w_M\|_Q/\sqrt{\zeta(2)Y}$ yields
$$
|\langle 1,w_M\rangle_Q|
\le 2\delta_k\bigl(\|u_M\|_Q+h(d_M;k^8)/\zeta(2)\bigr)
  +2\delta_k\|w_M\|_Q/\sqrt{\zeta(2)}
  +6\|w_M\|_Q/(k\sqrt{\zeta(2)}).
$$
The Lean version uses the repository's square-norm tail estimate with $\|w_M\|_Q^2+2/\zeta(2)$ in its tail constants. Both bounds tend to zero along the hypothesized heads. Strong convergence gives $\langle1,w\rangle_Q=0$, and the faithful witness identity gives RH. [Finite mean bound and cofinal limit](QFiniteHarmonicProbe.lean)

## Reduction to one Pareto solve

At a prime $p$, take the $P$ projection at stage $p$ and define the one signed entry $a_p=\langle g_p,1-f_{P,p}\rangle_Q$. Along the primes, $\zeta(2)p a_p$ converges to the limiting squared $P$ distance. Thus it suffices to establish $p a_p\to0$ along an unbounded subsequence. This needs one $P$ solve and one $Q$ row per prime. The sharp comparison with the finite residual and Burnol's logarithmic lower bound give $a_p>0$ for every sufficiently large prime. A test looking for infinitely many nonpositive entries is thereby excluded. [Exact identity and signed limit](QFiniteSingleResidueTest.lean) · [Burnol comparison and proof](SingleResidueBurnolResearch20261105.md)

For a matrix formulation, let $G$ be the finite Pareto Gram matrix, $b$ its correlations with 1, $q$ the row of $Q$ correlations with $g_p$, and $t=\langle g_p,1\rangle_Q$. Then $a_p=t-qG^{-1}b$, equivalently the determinant of the bordered matrix with rows $(G,b)$ and $(q,t)$ divided by $\det G$. The dictionary with one copy of each squarefree conductor is linearly independent. In a vanishing combination, first differences at 1 give $\sum_m c_m/m=0$, and first differences at each conductor determine its coefficient in ascending order. Thus $G$ is positive definite. The remaining size estimate is an arithmetic assertion about these explicit entries.

## Other reductions and the scope of the counterexample

- A uniform unit budget has an exact converse at the residual level. The limiting residual is zero if and only if arbitrarily large $K$ admit some $M\ge K$ with $h(d_M;K)\le1$. [Finite prefix](QFiniteHarmonicPrefix.lean)
- For the original centered iteration, $X\le9^j$ gives $|h(d;X)-h(u_j;X)|\le\sqrt{61\zeta(2)/7200}$. Restarting the degree-two Chebyshev polynomial gives an error factor $17^{-k}$ after $2k$ feedback evaluations. Alternatively, project only the first $N$ coordinates of the actual Pareto residual. The signed remainder is $\Pi B_0(1_{\{n>N\}}r_P)$, and its prefix error tends to zero uniformly through $(N+2)^2$. This latter approximation still uses the infinite projector and residual. [Prefix](QResolventHarmonicPrefix.lean) · [Chebyshev](QDisplacementChebyshevResolvent.lean) · [Projected head](QDisplacementProjectedHead.lean) · [Golub and Varga (1961), §2](https://www.math.kent.edu/~varga/pub/paper_17.pdf)
- Squarefree-span membership and the radical difference identities permit $h(v;X)\asymp\sqrt X/(\log X)^\beta$ at every sufficiently large $X$ for each $\beta>1/2$. The infinite construction and sharp threshold are paper proofs. Lean proves the pulse formulas, finite-span membership, energy and prefix bounds, exact block balance, and the decay of signed pairings for the actual displacement against bounded legal tail tests. [Counterexample](SquarefreeHarmonicObstruction20261105.md) · [Pulse equations](SquarefreePulseEquations.lean) · [Tail tests](QDisplacementTailTests.lean)
- The exact implicit cutoff of Lee and Leong crosses the previously excluded pointwise endpoint. The Lean theorem takes the specialized published arithmetic proposition as an argument. A bound on the actual displacement is still required. [Analytic proof](MertensImplicitTruncationResearch20261105.md) · [Implicit input](MertensImplicitTruncation.lean) · [Dyadic tests](MertensDyadicDisplacement.lean)
- Complete rational enclosures give $h(d_{32};256)=0.025862657507$ to absolute error $10^{-12}$. The separate twelve-row experiment measures the prescribed finite resolvent iterates. [Computations, scripts, and error bounds](FiniteGramDisplacementExperiment20261105.md)

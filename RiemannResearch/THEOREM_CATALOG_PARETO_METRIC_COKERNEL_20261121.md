# The metric cokernel of the Pareto mixed inclusion

[Lean source](RH/MixedConductorMetricCokernel.lean)

Let $C:V\to\mathbb R$ be the legal mean and let $s(a)=au$ be its screened section,
where $u=P_{M^\perp}J_2/\log 2$. The scalar line has its usual absolute value
and $V$ has its inherited Pareto norm. Write $E=\|1-P_V1\|_P^2$.

## Established identities

For every bounded real-linear $F:V\to Y$ vanishing on $M$, the unique factor
through $C$ is $\bar F=F\circ s$. Its operator norm satisfies

$$
  \|\bar F\|=\|F\|\,\|u\|_P,\qquad
  s^*s=\|u\|_P^2 I_{\mathbb R},\qquad \|u\|_P^2=\frac{1}{1-E}.
$$

| Lean declaration | Conclusion |
| --- | --- |
| `norm_descend_legalPacketMean` | Exact norm of the factor in every real normed target |
| `legalMeanFactorizationBound_iff` | Every contraction killing $M$ factors with norm at most $K$ exactly when $\|u\|_P\le K$ |
| `screenedMeanSection_adjoint_comp_self` | The Gram operator of $s$ is $\|u\|_P^2 I$ |
| `screenedMeanSection_isometry_iff_adjoint` | The section is isometric exactly when $C^*=s$ |
| `algebraMap_isometry_iff_contractive_cokernel` | The algebra's scalar map is isometric exactly when $C$ is a cokernel among contractions |
| `legalMean_contractive_cokernel_iff_naturalApproximation` | The norm-one universal property is equivalent to discrete Nyman–Beurling approximation |

The map $F=sC$ is the orthogonal projection onto $V\cap M^\perp$. It kills
$M$ and has norm one. Its unique factor is $s$, which witnesses sharpness.

In the quotient $V/M$, the class with mean $a$ has quotient norm $|a|\,\|u\|_P$.
The fiber estimate `legalPacketMean_fiber_bound` gives the lower bound and the representative
$s(a)$ attains it. Thus $C$ identifies the quotient isometrically with the usual real line
exactly when $\|u\|_P=1$.

## Open condition

Establish $\|u\|_P\le1$ for the original section. Its mean already gives
$1\le\|u\|_P$. Equality is equivalent to $u=1$ and to $1\in V$.
The implication from the norm-one universal property to RH is checked by
`riemannHypothesis_of_legalMean_contractive_cokernel`. The reverse implication
uses the published RH-to-natural-approximation theorem. See [Bagchi, Theorem 1](https://arxiv.org/abs/math/0607733).

## Decomposing the mixed ideal by conductor

Write $\mathcal I=\{q\ge2:q\text{ has at least two distinct prime divisors}\}$.
For $S\subseteq\mathcal I$, set $K_S=\overline{\operatorname{span}}\{J_q:q\in S\}$
and let $P_S$ be its orthogonal projection inside $M$. Then

$$
M=K_S\oplus^\perp
 \overline{\operatorname{span}}\{J_q-P_SJ_q:q\in\mathcal I\setminus S\}.
$$

The two arrows in the split exact sequence are inclusion of $K_S$ and
orthogonal projection onto the second summand. Their adjoints give the retraction
and section. Taking $S=\{q:\omega(q)=2\}$ separates the raw packets with exactly
two distinct prime divisors from the screened packets with at least three.

In increasing conductor order, put $H_{<q}=\operatorname{span}\{J_r:r\in\mathcal I,\ r<q\}$.
Finite packet independence makes every $d_q=J_q-P_{H_{<q}}J_q$ nonzero. The vectors
$e_q=d_q/\|d_q\|_P$ form a Hilbert basis of $M$. Every partition of these modes gives
a binary biproduct. The lattice of all real subspaces of $M$ is order-isomorphic to the
ideals of the screened algebra contained in $M$. This correspondence preserves closedness
in both directions.

For the parity packet, the energy of the first mode and the complete sum are

$$
 |\langle J_2,e_6\rangle_P|^2=
 \frac{(\log 2-\pi/(2\sqrt3))^2}{\pi/\sqrt3},
 \qquad
 \sum_{q\in\mathcal I}|\langle J_2,e_q\rangle_P|^2
 =\log 2-\frac{(\log 2)^2}{1-E}.
$$

The remaining arithmetic equality is attainment of $\log 2-(\log 2)^2$ by this sum,
equivalently $1\in V$. The basis and both biproduct constructions are unconditional.

[Hilbert basis and Parseval](RH/MixedConductorHilbertBasis.lean) ·
[Split exact sequences and ideals](RH/MixedConductorBlockSplitting.lean)

## Strict filtration by the number of prime divisors

Put $F_r=\overline{\operatorname{span}}\{J_q:q\in\mathcal I,\ \omega(q)\le r\}$ and
$D_r=F_r\cap F_{r-1}^{\perp}$, where $\omega(q)$ counts distinct prime divisors.
Then $F_1=0$, each $F_{r-1}\subsetneq F_r$ for $r\ge2$, and
$M=\widehat{\bigoplus}_{r\ge2}D_r$. The projection onto $D_r$ is
$P_{F_r}-P_{F_{r-1}}$. The vector partial sums and their squared norms converge
in the original Pareto metric. Each inclusion $F_{r-1}\hookrightarrow F_r$
belongs to a split short exact sequence with categorical cokernel $D_r$.

The continuous Möbius difference $\Delta_q$ vanishes on $F_{r-1}$ whenever
$\omega(q)=r$ and has value $-q$ on $J_q$. In particular
$\Delta_{30}(J_{30}-P_{F_2}J_{30})=-30$. This detects a nonzero three-prime
component after screening against the entire closed two-prime space.

[Strictness, norm convergence, and categorical quotients](RH/MixedConductorPrimeSupport.lean)

## Snake boundary of the centered mean diagram

The morphism from the legal mean sequence to the ambient mean sequence has vertical
maps $M\hookrightarrow 1^\perp$, $v\mapsto v-C(v)1$, and $0:\mathbb R\to\mathbb R$.
Both rows split. Mathlib's module snake lemma gives exactness of
$0\to V\cap\mathbb R1\xrightarrow{C}\mathbb R\xrightarrow{\partial}1^\perp/M$.
For every legal lift $v$ of $a$, the boundary is $[v-a1]=a[u-1]$.

The orthogonality $u-1\perp M$ gives the exact identities
```math
\|\partial\|_{\mathrm{op}}=\|u-1\|_P,\qquad
\|\partial\|_{\mathrm{op}}^2=\|u\|_P^2-1=\frac{E}{1-E},
\qquad E=\operatorname{dist}_P(1,V)^2 .
```
The boundary vanishes exactly when $1\in V$. In the other branch it is injective,
has range $\mathbb R[u-1]$ of dimension one, and $E>0$ bounds every legal squared
approximation error from below. The minimum norm on the mean-one fiber is $\|u\|_P>1$.

**Open.** Decide whether $\partial=0$. Lean proves that vanishing implies RH.
The converse direction uses the RH-to-natural-approximation implication of
Báez-Duarte's Theorem 1.1 as an explicit hypothesis.

[Centered mean diagram, snake boundary, and norm dichotomy](RH/CenteredMeanSnake.lean)

## The internal and ambient mean quotients

Put $1_V=P_V1$. For $v\in V$, the inner product $\langle v,1_V\rangle_P$
equals $C(v)$. Since $1_V=u/\|u\|_P^2$, both $(\mathbb R1_V)^{\perp_V}$ and
$(\mathbb Ru)^{\perp_V}$ equal $M$. Their quotient by $M$ is zero. On $V$, $P_{M^\perp}v=C(v)u$ has kernel $M$ and range $\mathbb Ru$.
The ambient constant decomposes as $1=u/\|u\|_P^2+P_{V^\perp}1$.

With $a=1_H-P_V1_H$, the theorem `screenedLine_eq_projectedOne_line` gives
$\mathbb Ru=\mathbb R1_V$ in the ambient space. The residual is orthogonal to $M$
and $\mathbb Ru$. The theorem `limitResidual_mean_and_screened_norm` gives its exact mean.

$$
\langle a,1_H\rangle_P=\|a\|_P^2=1-\frac{1}{\|u\|_P^2}.
$$

The line and residual criteria, including `screenedLine_eq_one_line_iff_residual_mean_zero`, give

$$
\mathbb Ru=\mathbb R1_H
\quad\Longleftrightarrow\quad a=0
\quad\Longleftrightarrow\quad 1_H\in V
\quad\Longleftrightarrow\quad \langle a,1_H\rangle_P=0.
$$

Proving that this mean vanishes is open.

The linear equivalence `boundaryTargetEquivLegalQuotient` sends
$x+M\mapsto x+V$ on $1^{\perp_H}/M$. Its inverse sends $h+V$ to
$[h-\langle h,1\rangle_Pu]$. Under this equivalence $\partial(a)$ becomes
$-a(1+V)$. The ambient quotient is zero exactly when $V=H$, equivalently
$1\in V$, by `boundaryTarget_subsingleton_iff_one_mem`.

In $H$, `mixedClosure_eq_closedSpace_inf_one_orthogonal` gives $M=V\cap 1_H^\perp$.
The defect $u-1$ lies in $1_H^\perp\cap M^\perp$. If $1_H^\perp\subseteq M$,
then $u-1\in M\cap M^\perp=\{0\}$. Conversely, scaled dilation differences of a legal
constant put every coordinate point mass in $V$, so $V=H$. The theorem
`boundary_eq_zero_iff_mixedClosure_eq_one_orthogonal` composes these equivalences.

$$
\partial=0\quad\Longleftrightarrow\quad 1\in V\quad\Longleftrightarrow\quad V=H
\quad\Longleftrightarrow\quad M=1_H^\perp.
$$

The inclusion $1_H^\perp\subseteq M$ remains open.

[Quotient equivalence and rank-one projection](RH/CenteredMeanQuotients.lean)

## Finite Möbius tests for the ambient mean-zero space

Set $L=\log 2$, $z=J_2-L1$ and $F_k=\overline{\operatorname{span}}\{J_q:q\in\mathcal I,\ \omega(q)\le k\}$. The constant is legal exactly when $z\in M$. Write $p=P_MJ_2$, $D_j=F_{j+1}\cap F_j^\perp$, and take the projections onto $D_j$ and $F_k$ inside $M$. The finite Parseval identity retains both residual terms.

$$
L-L^2=L^2\|\partial\|^2+
\sum_{j=0}^{k-1}\|P_{D_j}p\|^2+\|p-P_{F_k}p\|^2.
$$

The last term tends to zero by the support filtration. The first term is precisely the ambient defect.

### A finite matrix and its exact cost

Use rows $2\le m\le H$ and columns $q\in\mathcal I$ with $q\le B$. Put

$$
A_{mq}=-m\,\mathbf1_{m\mid q}\,\mu(q/m),\qquad
t_m=-2\,\mathbf1_{m=2}-L\mu(m),\qquad
G_{qr}=\langle J_q,J_r\rangle_P.
$$

The incidence entry is zero when $m$ does not divide $q$. Each entry of $G$ is the sum of packet products over one common period, weighted by its **complete Pareto progression masses**. This is a finite formula that retains the infinite physical tail. For any row weights $a$, the squared norm of the projection of $\sum_m a_m R_m$ onto the packet window is $(A^\top a)^\top G^{-1}(A^\top a)$, where $R_m$ represents the continuous Möbius difference of order $m$.

Choose a prime $s_H>H+1$ and take $B_H=s_H(H+1)$. The finite head interpolation theorem gives linear independence of the projected rows. In particular $K_H=AG^{-1}A^\top$ is positive definite and

$$
E_H=t^\top K_H^{-1}t
=\min_{Ac=t}c^\top Gc.
$$

For the minimizing packet vector $x_H$ and every feasible packet vector $y$, the complete norm satisfies $\|y\|^2=E_H+\|y-x_H\|^2$. The construction also covers the empty row set. A fresh prime certifies feasibility of the full window. At $H=2$, the single column $J_6$ with coefficient $(L-2)/2$ gives the explicit unconditional estimate

$$
E_2\le \frac{(2-L)^2}{4}\frac{\pi}{\sqrt3}.
$$

**Conditional research reduction.** Fix the schedule in advance, for example the least prime $s_H>H+1$. A single bound $E_H\le C$ along arbitrarily large heads implies $1_H^\perp\subseteq M$ and hence RH. Equivalently at each finite stage the rank-one matrix inequality is $tt^\top\preceq C K_H$. This condition tests signed arithmetic rows. The proof uses totality of the Möbius Riesz tests in the ambient space. The ambient inclusion is equivalent in Lean to the repository's Nyman–Beurling approximation condition. Its implication to RH is kernel-checked. The reverse RH implication in the quotient development takes Báez-Duarte's published theorem as a parameter. Necessity of this specified cutoff schedule for that approximation is unproved.

When the schedule itself may be chosen separately at each head, existence of a uniformly bounded schedule is equivalent to $\partial=0$. For the reverse implication, $z\in M$ gives finite mixed approximants within unit norm distance that match its full physical head. Taking the prime large enough to include each approximant gives $E_H\le(\|z\|_P+1)^2$. This use of membership explains the role of prescribing $s_H$ in the arithmetic problem.

**Open.** Establish $\liminf_{H\to\infty}E_H<\infty$ for a prescribed schedule. Finite positive definiteness and solvability give a separate finite bound at each head. The existing sublinear complete squared-error estimate for centered parity uses freely chosen mixed cutoffs and supplies $o(H)$.

### Two restrictions on a possible proof

For every fixed $k$, some $\delta_k>0$ satisfies $\|z-y\|_P^2\ge\delta_k$ throughout $F_k$. A squarefree order $m>2$ with $\omega(m)>k$ annihilates the stage and has target $-L\mu(m)$. Centering the Riesz test reduces its squared norm by $\mu(m)^2$. At $m=30$ the exact dual squared norm is $2652$, so $\|z-y\|_P^2\ge L^2/2651$ throughout the closed two-prime stage.

If all columns used are $J_{sd}$ for one fresh prime $s\nmid d$, their weighted sum has the form $v=D_s f-f$ for the Pareto dilation. At $s>2$, even matching just the order-two observation forces

$$
14\|v\|_P^2\ge (\sqrt{s}-1)^2(2-L)^2.
$$

Thus the standard fresh-prime columns used to show solvability have growing cost. The full window also contains columns outside that restricted family.

| Lean declaration | Conclusion |
| --- | --- |
| `parity_variance_eq_boundary_add_layers` | Exact boundary and finite-layer remainder |
| `captured_eq_projection`, `windowGram_entry` | Exact projected test energy from the complete CRT Gram |
| `headGram_posDef`, `headCost_minimum` | Unconditional positive definiteness and least-energy interpolation |
| `boundary_eq_zero_iff_exists_bounded_headCost` | Equivalence when the prime schedule can follow the approximants |
| `headCost_two_le` | Explicit upper bound at the first nonempty head |
| `one_orthogonal_le_mixedClosure_of_cofinal_headCost` | Conditional ambient inclusion from cofinally bounded cost |
| `fixed_support_positive_floor`, `two_prime_error_floor` | Obstruction at any fixed support level and its order-thirty certificate |
| `fresh_packet_combination`, `fresh_dilation_cost_floor` | Quantitative obstruction for a single fresh prime |

[Finite Möbius matrices and the ambient inclusion](RH/MixedMobiusWindow.lean) · [Support and fresh-prime lower bounds](RH/MixedParitySupportBounds.lean) · [Finite head interpolation](RH/MixedConductorHead.lean) · [Sublinear centered parity fits](RH/ParetoMixedCenteredParityHeads.lean)

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

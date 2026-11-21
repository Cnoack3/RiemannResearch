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

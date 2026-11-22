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

## The Von-Mangoldt Pattern and squarefree CRT

For a finite set of primes $S$, put $q_S=\prod_{p\in S}p$. For $T\subseteq S$, reduction from $q_S$ to $q_T$ forgets precisely the coordinates in $S\setminus T$. The CRT equivalences give a natural isomorphism of contravariant diagrams in commutative rings. Each residue ring, with its prime projections, satisfies the categorical product universal property.

$$
\mathbb Z/q_S\mathbb Z \;\simeq\; \prod_{p\in S}\mathbb Z/p\mathbb Z.
$$

At the point $m$ the local contrast on the $p$-coordinate is $p\mathbf1_{p\mid m}-1$. Their product is the Ramanujan sum. Summing the jumps reconstructs the integrated packet whenever $q_S>1$

$$
J_{q_S}(n)=-\sum_{m=1}^{n}\prod_{p\in S}(p\mathbf1_{p\mid m}-1).
$$

[Ramanujan contrasts](RH/QRamanujanContrastGram.lean) · [Packet jumps](RH/ParetoPacketGreenGram.lean) · [Reconstruction from the categorical CRT coordinates](RH/PrimeSupportAlgebraDescent.lean)

For a mixed conductor $q$ with at least two distinct prime divisors, let $\omega(q)$ count its distinct prime divisors. Let $I_k$ be the closed span in $V$ of the mixed packets with at most $k$ distinct prime divisors. Then

$$
 C(J_q)=0,\qquad J_q\in I_k \;\Longleftrightarrow\; \omega(q)\le k.
$$

When $k<\omega(q)$, the continuous Möbius coordinate at $q$ kills $I_k$ and takes the value $-q$ on $J_q$. The reverse implication follows from the generators of $I_k$. Thus $J_{30}$ first occurs at stage three. The conductor $12=2^2\cdot3$ gives a mean-zero packet at stage two outside the closed span of squarefree mixed packets. For $q=p^a$ with $a\ge1$, one has $C(J_q)=\log p$ and $P_{M^\perp}J_q=(\log p)u$.

[Squarefree CRT and its product cone](CategoryTheory/SquarefreeResidueCRT.lean) · [Packet entry and prime-power screening](RH/PrimeSupportAlgebraDescent.lean) · [Packet expectations](RH/ParetoResidueMean.lean) · [The conductor twelve](RH/MixedOrthogonalMean.lean) · [Full and squarefree tower completions](RH/ConductorTowerCompletions.lean)

## The centered snake sequence

Let $H$ be the Pareto space, $Z=\ker C_H$ its ambient mean-zero subspace, and $c(v)=v-C(v)\mathbf1_H$ for $v\in V$. The vertical maps between the two split mean sequences are inclusion $M\to Z$, centering $c:V\to H$, and the zero endomorphism of $\mathbb R$. Identifying the scalar term with the algebra quotient $V/M$ gives the exact sequence in real modules

$$
0\longrightarrow V\cap\mathbb R\mathbf1_H\longrightarrow V/M
\xrightarrow{\delta} Z/M\longrightarrow H/c(V)
\longrightarrow\mathbb R\longrightarrow 0.
$$

The connecting map sends $[v]$ to $[c(v)]$. Its pullback to $V/I_k$ sends the algebra unit to $[u-\mathbf1_H]$ for every $k$. Under $Z/M\simeq H/V$ this becomes the class of $-(\mathbf1_H-P_V\mathbf1_H)$. The transition $V/I_n\to V/I_k$ for $n\le k$ gives a short exact sequence with kernel $I_k/I_n$. Compatible continuous maps from the stages into a Hausdorff algebra descend uniquely through $V/M$.

Let $j:V\hookrightarrow H$ be inclusion. The screened and ambient square-zero products use the chosen mean-one vectors $u$ and $\mathbf1_H$, respectively. Expanding them gives the vector identity

$$
j(x\star_V y)-j(x)\star_H j(y)=C(x)C(y)(\mathbf1_H-u).
$$

On $J_q,J_r$ the scalar is $\Lambda(q)\Lambda(r)$. A mixed input gives automatic agreement. At $q=2,r=3$ the scalar is $(\log 2)(\log 3)\ne0$, so agreement on that pair is equivalent to $u=\mathbf1_H$. The screened product has $J_6\star_VJ_6=0$ while the pointwise square of $J_6$ has value one at site one. Proving the two-prime agreement, equivalently $\delta(1)=0$, remains open here. [The screened square at conductor six](RH/MixedConductorSquareZero.lean)

[Split rows and connecting map](RH/CenteredMeanSnake.lean) · [Long exact sequence](RH/CenteredMeanLongExact.lean) · [Hausdorff algebra descent](RH/PrimeSupportAlgebraDescent.lean) · [Product identity and two-prime test](RH/CenteredMeanRHCriteria.lean) · [Snake lemma, Stacks Project, Tag 07JV](https://stacks.math.columbia.edu/tag/07JV)

## Which formulations reach RH in Lean

The declaration `categoricalMean_tfae` groups thirteen conditions equivalent to $\mathbf1_H\in V$. They include vanishing of the snake boundary, zero residual energy, existence of a contractive mean section, arbitrarily small parity quotient norm, the Gram determinant limit, natural approximation, and agreement of the two products on $J_2,J_3$. Each implies mathlib's `RiemannHypothesis`. The reverse direction in `stageUnit_zero_iff_riemannHypothesis` takes `RiemannHypothesis → BaezDuarte.NaturalApproximation` as an explicit premise. Báez-Duarte's discrete theorem supplies the published reference for that implication. [Formal statements](RH/CenteredMeanRHCriteria.lean) · [Báez-Duarte, 2003](https://www.bdim.eu/item?id=RLIN_2003_9_14_1_5_0) · [Bagchi, Theorem 1](https://arxiv.org/abs/math/0607733)

The declaration `analyticRiemannHypothesis_tfae` collects six two-way criteria whose Lean statements require no additional premise.

| Criterion | Lean source |
| --- | --- |
| Every finite distinct family of right-half-strip zeros satisfies the unit-budget Mellin product bound | [Finite Mellin products](RH/MixedConductorMetricLifting.lean) |
| Each off-line Cauchy mixture has nonzero residue pairing at scale two | [Cauchy detection](RH/CauchyAnnihilatorRH.lean) |
| The damped horizontal second energy of the actual zeros vanishes | [Zero energy](Analysis/ActualZeroSecondEnergy.lean) |
| Uniform Selberg density holds for an unbounded set of slopes | [Cofinal slopes](Analysis/ActualSelbergSlopeRH.lean) |
| The specified Taylor disks for the logarithmic derivative of $\xi$ exist at rational centers for every rational radius below one half | [Rational Taylor disks](RH/XiTaylorDiskRadius.lean) |
| The cofinal sharp Weil integrals satisfy the specified polynomial upper bound | [Sharp Weil bound](Analysis/MontgomerySharpWeilSeparator.lean) |

On November 22, 2026, Lean checked the transitive axiom dependencies of the 70 exported declarations in the four modules and the two packet lemmas made public. The audit allowed only `propext`, `Classical.choice`, and `Quot.sound`. [Axiom audit](https://app.buildbuddy.io/invocation/c3221973-f53f-490a-80f1-225528588406)

## A single prime-power covariance

Write $d=u-1$. For every $v\in V$ the signed identity is
$\langle v,d\rangle_P=C(v)\|d\|_P^2$. In particular
$\langle J_q,d\rangle_P=\Lambda(q)\|d\|_P^2$ for all $q\ge2$.
For any fixed prime power, nonpositivity of this pairing is equivalent to
$1\in V$. At conductor two the pairing integrates $u-1$ over the odd sites
against the original Pareto law.

**Conditional research reduction.** The theorem
`riemannHypothesis_of_parity_pairing_nonpos` derives RH from the single
inequality $\langle J_2,u-1\rangle_P\le0$. **Open.** Prove this inequality,
or prove that the finite pairings tend to zero. Each finite pairing is
strictly positive and equals $(\log 2)\|u_N-1\|_P^2$.

In the second draft (November 22), centered parity is $g=J_2/\log 2-1$.
Its full screening equals $d$, so $g\in M$ is equivalent to $1\in V$.
The dilated odd blocks $A_m=\{n:\lfloor n/m\rfloor\text{ is odd}\}$ have
mass $(\log 2)/m$. Their conditional mean of $d$ equals $\|d\|_P^2$ at every scale.

Theorem `screened_displacement_scaled_tail_identity` splits the scaled physical
tail energy into $(\log 2)\|d\|_P^4$ and the complete squared remainder.
Theorem `screenedTwo_eq_one_iff_cofinal_small_scaled_tail` identifies arbitrarily
small cofinal scaled tails with vanishing of $d$. **Open.** Establish
$\liminf_{m\to\infty}m\sum_{n\ge m}w_n d(n)^2=0$ for this screened vector.
For finite mixed fits made from one dilation, `centered_parity_single_dilation_error_lower`
bounds the error below by $(\sqrt m-1)\|y\|_P-\|g\|_P$ for the fit $y-D_m y$.

[Signed identities and finite-cutoff proofs](RH/ParetoPrimePowerCovariance.lean)

## Möbius coordinates of the mixed projection

Use $d=1-u$, $\ell=\log 2$, and $L_b$ for the continuous Möbius difference
functional of conductor $b$. For every $b>1$, the actual mixed projection satisfies

$$L_b(P_M J_2)+2{\bf1}_{b=2}+\ell\mu(b)=\ell L_b(d).$$

The coordinates above one determine a vector of finite Pareto norm, so all the
left sides vanish simultaneously exactly when $d=0$. At $b=6$, the centered
Riesz vector has squared norm $92-1=91$, giving
$|L_6(P_M J_2)+\ell|^2\le91\ell^2\|d\|_P^2$.

**Conditional research reduction.** Prove the simultaneous mixed projection
charge identities. The precise equalities constitute the premise in
`screenedTwo_eq_one_iff_mixed_projection_charges`. **Open.**

[Mixed projection charge identities and the conductor-six bound](RH/ScreenedParityMobiusCoordinates.lean)

## Exact Mellin obstruction for the two-prime covariance

Write $G$ for the full covariance of $J_2,J_3$ minus the inner product of
their projections onto the mixed space. If $E$ is the squared distance of
the constant to the legal space, then
$G=(\log 2)(\log 3)E/(1-E)$. For a finite family of distinct zeros with
real parts greater than $1/2$, `two_three_covariance_finite_zero_remainder`
expresses $E$ as the sum of the Mellin interpolation energy and the complete
squared interpolation remainder. For any such zero $z$, the single-zero
consequence reads
$$
(\log 2)(\log 3)(2\Re z-1)\le |1-z|^2G.
$$
The vanishing of $G$ remains open.

[Finite-zero remainder and single-zero covariance bound](RH/MixedConductorPolarizedParseval.lean)

## Decomposing the mixed ideal by conductor

Write $\mathcal I=\{q\ge2:q\text{ has at least two distinct prime divisors}\}$.

Let $M_{\mathrm{sf}}$ denote the closed span of the squarefree composite packets.
The functional $L(f)=f(4)-f(3)-f(2)+f(1)$ has $L(J_q)=0$ when $4\nmid q$
and $L(J_q)=-4\mu(q/4)$ otherwise. The pair $(C,L)$ vanishes on $M_{\mathrm{sf}}$
and takes values $(\log 2,0)$ and $(0,4)$ on $J_2$ and $J_{12}$.
`squarefreeMixed_two_twelve_independent` proves independence of these cosets in
$V/M_{\mathrm{sf}}$, and `squarefreeMixedPacketClosure_lt_mixedClosure` gives
$M_{\mathrm{sf}}\subsetneq M$. The rank-one quotient in this paper is $V/M$.

The residual $J_{12}-P_{M_{\mathrm{sf}}}J_{12}$ witnesses
`mean_not_injOn_legal_squarefreeMixedOrthogonal`. For the full mixed closure,
`mixedOrthogonalMean_injective_iff_full_capture_saturation` identifies ambient
injectivity with $\|P_MJ_2\|_P^2=\log 2-(\log 2)^2$. **Open.** Establish the
reverse bound independently. [LaTeX section](RH/ParetoVonMangoldtReduction.tex.md)

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

## Global Parseval identity and the filtered parity deficit

Let $L_k=F_{k+1}\cap F_k^\perp$, $m=P_Mv$ and $A_N(m)=\sum_{k<N}\|P_{L_k}m\|_P^2$.
The scalar coordinate of $v$ is $C(v)$ in the line with norm $|a|\|u\|_P$.
For every legal $v$ and every cutoff $N$,
\[
 \|v\|_P^2=|C(v)|^2\|u\|_P^2+A_N(m)+\|m-P_{F_N}m\|_P^2 .
\]
The last term tends to zero. Reconstruction converges in the original norm.
The isometric equivalence uses the screened line with its inherited norm and
the external Hilbert sum of the $L_k$. Its coordinate maps are $v\mapsto C(v)u$
and $v\mapsto P_{L_k}m$. Synthesis adds the scalar vector to the convergent mixed sum.
The theorem `support_energy_eq_conductor_basis` identifies the total layer energy
with the existing conductor-ordered Hilbert-basis sum.

For $p=P_M(J_2/\log 2)$ the finite deficit splits exactly as
\[
 (\log 2)^{-1}-1-A_N(p)=\|u-1\|_P^2+\|p-P_{F_N}p\|_P^2 .
\]
Thus saturation along these support stages is equivalent to $\|u\|_P=1$.
The theorem `norm_one_iff_forall_support_capture` expresses this as one cutoff per positive tolerance.
Whether saturation holds remains open. Any Möbius coordinate above the cutoff
bounds the omitted norm from below. Each $N\ge1$ misses a unit vector in $L_N$,
so convergence of the truncations on $M$ is strong and fails in operator norm.

| Lean declaration | Conclusion |
| --- | --- |
| `legal_support_energy_remainder` and `legal_support_parseval` | Finite and infinite weighted identities on the legal space |
| `legalSupportEquiv` and `legalSupportEquiv_symm_apply` | Isometric equivalence and synthesis formula |
| `supportCoordinate_tail_bound` and `exists_unit_missed_by_support_cutoff` | Finite-stage lower bounds and the obstruction to uniform convergence |
| `parity_support_deficit` and `parity_support_saturation_iff_norm_one` | Exact parity deficit and the norm-one obligation |

For a comparison of successive layer rows the left vertical map is inclusion
and the right one is zero. Truncating the middle map to the old stage preserves
the sections and gives zero boundary. Taking the natural middle inclusion
gives the identity $L_k\to L_k$ when the left cokernel is identified via its
layer projection. This map is nonzero for $k\ge1$. The declarations
`truncatedLayerBoundary_eq_zero` and `successiveLayerBoundary_eq_id` compute
both maps using mathlib's module snake lemma.

[Global Parseval and the parity deficit](RH/MixedConductorGlobalParseval.lean) ·
[Connecting maps of the layer tower](RH/MixedConductorSupportSnake.lean)

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

## The mean restricted to the ambient mixed complement

Write $C(h)=\langle\mathbf1,h\rangle_P$ for $h\in M^\perp$ and
$K=M^\perp\cap\mathbf1^\perp$. The constant gives a section, so $C$ is
surjective and $M^\perp/K\cong\mathbb R$. The restricted mean is injective on
$V\cap M^\perp=\mathbb Ru$. On the whole mixed complement the following
conditions are equivalent.

$$
C|_{M^\perp}\text{ is injective}
\quad\Longleftrightarrow\quad M^\perp=\mathbb R\mathbf1
\quad\Longleftrightarrow\quad \mathbf1\in V
\quad\Longleftrightarrow\quad \mathbf1-u=0 .
$$

Taking orthogonal complements of $M\subseteq\mathbf1^\perp$ gives
$\mathbb R\mathbf1\subseteq M^\perp$. The exact ambient splitting is
$M^\perp=\mathbb R\mathbf1\oplus^\perp K$. The theorem
`mixedOrthogonal_inf_oneOrthogonal_eq_bot_iff_discrepancy_zero` gives
$K=\{0\}\iff\mathbf1-u=0$.

On $D=\operatorname{span}_{\mathbb R}\{\mathbf1,u\}$, `meanKer_on_one_screenedTwo_span`
gives $D\cap\ker C=\mathbb R d$ with $d=\mathbf1-u$. Indeed,
$C(a\mathbf1+bu)=a+b$. The theorem `discrepancy_mem_closedSpace_iff_zero`
applies injectivity on $V\cap M^\perp$ to prove $d\in V\iff d=0$.
The membership $d\in V$ remains open and is equivalent to $\mathbf1\in V$.

The von Mangoldt coefficient is the continuous linear functional
$T(h)=\langle u,h\rangle_P$. For the draft sign $d=\mathbf1-u$,
$(C-T)(h)=\langle d,h\rangle_P$, hence $T(d)=-\|d\|_P^2$.

**Established.** Every $h\in M^\perp$ bounded above or below on the positive
sites equals $C(h)\mathbf1$. Write $h=a\mathbf1+z$ with $z\in V^\perp$. For an
upper-bounded $z$, the dilation adjoints preserve its upper bound and its
membership in $V^\perp$. The one-sided mean estimate applies at each dilation,
and consecutive dilation means recover every coordinate of $z$. Negation gives
the lower-bounded case.

**Established.** Centering gives a continuous linear equivalence
$\Phi:V^\perp\to K$ with inverse $\Psi:K\to V^\perp$. Their formulas are
$\Phi(z)=z-C(z)\mathbf1$ and $\Psi(y)=y-\langle u,y\rangle_P\mathbf1$.
The inverse satisfies $\|\Psi(y)\|_P^2=\|y\|_P^2+\langle u,y\rangle_P^2$.

**Conditional research reduction.** If $K$ lies in one real line, linearity
of $\Psi$ puts $V^\perp$ in one real line, so the conjugate-zero criterion
gives RH. **Open.** Exclude a nonzero vector in $K$ unbounded in both directions.

[Ambient mean and packet coefficient](RH/MixedOrthogonalMean.lean) ·
[One-sided annihilator theorem](RH/ParetoAnnihilatorOneSided.lean)

## The density operator from the reciprocal blocks

Write $P$ for the $Q$-orthogonal projection onto a closed subspace $S$,
$A=PD|_S$, and $C=(I-P)D|_S$. The affine operator identity
$B=(I+D)/\zeta(2)$ determines every matrix entry of $B$ in the orthonormal
divisor basis. Positivity of $D$ gives $I_S+A\ge I_S$. Its bounded inverse
identifies $B(S)$ with the graph of $C(I_S+A)^{-1}$ over $S$.
For the full legal space $V$, the complementary components of this graph
are dense in $V^{\perp_Q}$ because $D(V)$ is dense in $L^2(Q)$.

[Density operator and graph theorem](RH/QDensityOperatorDecomposition.lean)

## Reciprocal images of affine squarefree packets

Use $D=\zeta(2)B-I$, so $Df(n)=f(n)/n$. For squarefree $q>1$ and
a new prime $p>q$ the integrated CRT identity reads
\[
D(J_{pq}+J_q)(n)=\frac{p}{n}J_q(\lfloor n/p\rfloor).
\]
It vanishes for $n<p$ and its absolute value is uniformly bounded in $p$.
Consequently $-DJ_{pq}\to DJ_q$ in the full zeta-two norm. If $M_{\rm sf}$
denotes finite mixed squarefree packet combinations and $z=J_2/\log 2$,
the squarefree reciprocal sieve now gives
$D(\mathbf1-z)\in\overline{D(M_{\rm sf})}$. This is an unconditional
mean-one affine approximation to $1/n$. A uniform bound on the original
affine trials would imply RH. For the full legal space the established
equality is $\overline{D(V)}=L^2(Q)$ and exact range equality
$D(V)=D(L^2(Q))$ would imply $V=L^2(Q)$ by injectivity.
[Affine squarefree reciprocal transfer](RH/SquarefreeAffineReciprocal.lean)

## Reconstruction from the density image in zeta-two space

Set $S=B(V)$, with $B=dQ/dP$. Its distinguished target is $b=B\mathbf1$.
Then $S=L^2(Q)$ if and only if $b\in S$, equivalently $P_S^Q b=b$.
There is also an unconditional reconstruction using only elements of $S$.
For $(Rh)(n)=h(n)/(n+1)$, the identity $\zeta(2)R(Bv)(n)=v(n)/n$
and full reciprocal density give $\overline{R(S)}=L^2(Q)$.
For squarefree conductors $a\ge2$, Möbius inversion gives the same finite
span for the integrated packets and the residues, before taking closure.
Consequently $Bf$ belongs to the closed zeta-two span of the twisted
squarefree residues exactly when the physical $f$ belongs to the Pareto
squarefree packet closure. This squarefree image omits $Br_4$.
Bagchi's Remark 8 gives the arithmetic criterion
$\mathrm{RH}\iff B\mathbf1\in B(V_{\rm sf})$. The sufficiency direction is
formalized without extra hypotheses. For necessity the Lean theorem takes
the published Möbius approximation from Báez-Duarte's Theorem 2 as an
explicit hypothesis.
[Bagchi, Remark 8](https://arxiv.org/pdf/math/0607733#page=9) ·
[Báez-Duarte, Theorem 2](https://www.bdim.eu/item?fmt=pdf&id=RLIN_2003_9_14_1_5_0)
[Reconstruction from the single density-image space](RH/QDensityImageReconstruction.lean)

## Mixed packets alone after the reciprocal multiplier

Let $V$ be the full legal closure in $L^2(Q)$, $M$ its closed mixed-conductor
subspace, $B=dQ/dP$, and $D=\zeta(2)B-I$, so $Df(n)=f(n)/n$.
For the raw legal remainder $r_a(n)=n\bmod a$, $C_P(r_a)=\log a$
and $\|Dr_a\|_Q\le1$. Thus for each $v\in V$ the corrected vector
$v-C_P(v)r_a/\log a$ lies in $M$ and its reciprocal image tends to $Dv$.
Full reciprocal totality gives
\[
\overline{D(M)}=\overline{M+B(M)}=L^2(Q).
\]
In particular the single family $J_q(n)/n$ at conductors with at least two
distinct prime factors has dense span. Full density of either pure family
$\{g_a\}$ or $\{Bg_a\}$ is equivalent to $B J_q\in V$ for **each mixed
conductor** $q$. The preservation assertion remains open and would imply RH.
[Mixed reciprocal density and the mixed-only test](RH/MixedReciprocalDensity.lean)

## Orthogonal tower of mean-one physical patches

Write $u$ for the screened mean-one vector and $M$ for the closed mixed
space. Let $K_n$ consist of the vectors in $M$ vanishing on positive sites
$1,\ldots,n$. With $K_0=M$, project the Riesz representer of site $n+1$
onto $K_n$ to obtain $g_{n+1}$. Finite mixed interpolation gives
$g_{n+1}\ne0$. The normalized direction $h_{n+1}=g_{n+1}/\|g_{n+1}\|^2$
has value one there, and
$K_n=\mathbb Rh_{n+1}\oplus^\perp K_{n+1}$. These lines span a dense
subspace of $M$.

The minimum-norm legal patch $a_n$ has mean one and physical values one on
$1,\ldots,n$. It starts at $a_0=u$ and satisfies
$a_{n+1}=a_n+(1-a_n(n+1))h_{n+1}$. Every feasible vector belongs to
$a_n+K_n$. If $D_n=|1-a_n(n+1)|^2/\|g_{n+1}\|^2$, then
$\|a_N-\mathbf1\|^2=\|u-\mathbf1\|^2+\sum_{n<N}D_n$.
The existing centered-parity trials give $\|a_N-\mathbf1\|^2=o(N)$.

**Open.** Prove the partial sums of $D_n$ are bounded along arbitrarily
large physical cutoffs. In Lean this is equivalent to $u=\mathbf1$ and
implies RH. If $u=\mathbf1$, every patch already equals $\mathbf1$.
[Orthogonal layers, finite minimizers and global criterion](RH/ParetoAffineHeadTower.lean)

## The same affine tower under the zeta-two law

The physical head constraints and the Pareto mean define the same affine sets.
In the zeta-two inner product, the Pareto mean is represented by
$w(k)=\zeta(2)k/(k+1)$. Orthogonally projecting the constant onto each
affine set gives its zeta-two minimizer $b_n$. Its squared distance increases
by $\|b_m-b_n\|_Q^2$ between stages $n\le m$ and is $o(n)$.

Write $\widehat b_n(r)$ for the full Jordan-normalized divisor coefficients.
Then $\widehat b_n(r)\to\mathbf1_{\{r=1\}}$ at each fixed conductor. More
precisely, the squared coefficient error is bounded by
\[
\frac{2J_2(r)}{\zeta(2)(n+1)}\,\|\mathbf1-b_n\|_Q^2 .
\]
On the Pareto mean-one fiber, the complete squared error is at most
$\zeta(2)(\zeta(2)-1)$ times the sum of the squares of the nonconstant
coefficients. A uniform bound for that sum at arbitrarily large physical
stages is equivalent to $u=\mathbf1$ and implies RH. Obtaining this bound
over all conductors remains open.
[Zeta-two projections and arithmetic coordinates](RH/ZetaTwoAffineHeadTower.lean)

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

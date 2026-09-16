> **Formalization status.** This is the informal source retained for provenance. The precise checked scope and remaining obligations are listed in [MinimalSeedsContinuationVerification20260916.md](MinimalSeedsContinuationVerification20260916.md). In particular, Section 12's analytic nonmembership theorem is not yet a Lean theorem, and the uniform bound needed for RH is unproved.

# How far can the two-seed criterion be reduced?

Date: 2026-09-14.

These are mathematical derivations from the conversation, not new Lean-verified declarations. The previously verified input is the equivalence of two-seed density and full remainder density in the actual Pareto Hilbert space. Combined with the established strong Báez-Duarte theorem, this gives the mathematical RH equivalence. The classical RH-to-full-density implication remains a formalization dependency in the Lean project.

No proof of RH, approximation rate, or uniform arithmetic norm estimate is claimed here. No novelty or priority claim is made.

## 1. Definitions and the previously established input

Let
\[
\mathcal H_P=\ell^2\!\left(\mathbb N_{\ge1},\frac1{n(n+1)}\right),
\qquad R_d(n)=n-d\lfloor n/d\rfloor.
\]
Extend sequences by value zero at index zero. Set
\[
D_mf(n)=m f(\lfloor n/m\rfloor),\qquad
g_{a,m}=R_{am}-R_m=D_mR_a.
\]
The two-seed space and full remainder space are
\[
V=\operatorname{span}_{\rm finite}\{g_{2,m},g_{3,m}:m\ge1\},\qquad
W=\operatorname{span}_{\rm finite}\{R_d:d\ge2\}.
\]
All spans and closures use real scalars unless otherwise stated. The established input is
\[
\mathrm{RH}\iff\overline W=\mathcal H_P
\iff\overline V=\mathcal H_P\iff1\in\overline V.
\tag{1.1}
\]
The classical full-family equivalence is [Bagchi, Theorem 1](https://arxiv.org/abs/math/0607733). His fractional-part sequences are nonzero scalar multiples of the remainders. The real formulation follows from the complex formulation by taking real parts of finite approximants.

Because positive-integer dilations preserve V and act boundedly, approximating the constant in V implies density of V. This fact must not be transferred automatically to a further subfamily whose span is no longer invariant under all dilations.

## 2. Information supplied by the reduction: the dual map

The established cocycle and joint-fixed-space results give
\[
(D_2-I)W\subseteq V,\qquad (D_3-I)W\subseteq V,
\qquad \ker(D_2^*-I)\cap\ker(D_3^*-I)=\mathbb R1.
\]
Consequently the bounded linear map
\[
J:V^\perp\longrightarrow W^\perp\oplus W^\perp,
\qquad J(h)=((D_2^*-I)h,(D_3^*-I)h)
\tag{2.1}
\]
is injective. Indeed, the cocycle puts both defects in W-perp. If both defects vanish, h is constant. Orthogonality to R_2, whose Pareto mean is log 2, then makes that constant zero.

Thus any nonzero two-seed annihilator explicitly produces a nonzero full-family annihilator through at least one adjoint defect. This explains why two seeds do not introduce an additional qualitative obstruction to density. Injectivity alone supplies no uniform inverse bound or rate of approximation.

## 3. A smaller exact dictionary: one generator at each dilation

Write uniquely
\[
m=2^a3^bu,\qquad (u,6)=1.
\]
Define
\[
h_m=
\begin{cases}
g_{2,m},&a\le b,\\
g_{3,m},&a>b.
\end{cases}
\tag{3.1}
\]

**Theorem 3.1.** The functions h_m form an algebraic basis of V. In particular,
\[
\operatorname{span}_{\rm finite}\{h_m:m\ge1\}=V.
\tag{3.2}
\]
This is an unconditional equality of finite spans, so (1.1) remains valid after replacing the two generators at each m by the single selected h_m.

Recovery of an omitted generator can require larger dilation indices. Equality of the unrestricted spans gives no automatic comparison of optimal variances under the same finite dilation budget.

**Spanning proof.** Regard each R_m as a vertex, and each h_m as the oriented edge from m to 2m or 3m prescribed by (3.1). The choice increments the smaller of the two exponents. Starting from 2^a3^bu, the path reaches 6^{max(a,b)}u and then follows
\[
6^ku\longrightarrow2\cdot6^ku\longrightarrow6^{k+1}u.
\]
Every pair of vertices with the same u therefore has paths meeting at a common finite vertex. If L is sufficiently large, telescoping along the selected path P(m,L) gives
\[
\sum_{n\in P(m,L)}h_n=R_{6^Lu}-R_m.
\]
Subtract the paths from m and pm, for p=2 or 3. Their difference is g_{p,m}. Every original generator is thus a finite signed sum of selected generators.

For example,
\[
h_1=R_2,\quad h_2=R_6-R_2,\quad h_3=R_6-R_3,
\qquad R_3=h_1+h_2-h_3.
\]

Independence follows from the continuous biorthogonal functionals constructed next. This is an algebraic basis; no Schauder-basis or uniformly bounded partial-sum assertion is being made.

## 4. Continuous coefficient functionals and forced limits

For any f in the Pareto space, define the finite-coordinate functional
\[
\alpha_d(f)=\sum_{e\mid d}\mu(d/e)\bigl(f(e)-f(e-1)\bigr).
\tag{4.1}
\]
Every coordinate evaluation is continuous, so every alpha_d is continuous. Möbius inversion gives the pointwise finite identity
\[
f(n)=\sum_{d\le n}\alpha_d(f)\lfloor n/d\rfloor.
\tag{4.2}
\]
In particular,
\[
\alpha_d(1)=\mu(d),\qquad
\alpha_d(R_e)=-d\,\mathbf1_{d=e}\quad(d,e>1).
\]
Also alpha_1(R_e)=1 for e>1. Thus the nonzero remainders are linearly independent.

Delete the selected edge h_m from its graph. Let C_m be the component on the side containing m, before that edge is traversed. It is finite: all its vertices have a directed path to m and are at most m. Define
\[
L_m(f)=\sum_{d\in C_m}\frac{\alpha_d(f)}d.
\tag{4.3}
\]
The selected graph is a forest: each vertex has one outgoing edge, increasing its integer label; a finite undirected cycle would force every vertex on that cycle to have an outgoing edge within it, hence a directed cycle.

For a selected edge h_n with upper endpoint t(n), direct computation gives, including d=1,
\[
\frac{\alpha_d(h_n)}d=\mathbf1_{d=n}-\mathbf1_{d=t(n)}.
\]
Summing over the finite cut yields
\[
L_m(h_n)=\delta_{mn}.
\tag{4.4}
\]
This proves independence, uniqueness of every finite h-expansion, and continuity of each individual coefficient.

If F_j=sum_m c_m^{(j)}h_m tends to 1 in the actual Pareto norm, then necessarily
\[
c_m^{(j)}\longrightarrow\ell_m:=L_m(1)
=\sum_{d\in C_m}\frac{\mu(d)}d
\quad\text{for each fixed }m.
\tag{4.5}
\]
This strengthens a redundant system of coefficient relations into an individually prescribed limit for every coordinate in a basis of original legal generators.

### Explicit coefficient targets

Write m=2^a3^bu with (u,6)=1. The finite cuts are:

- If a=b=k, C_m is the rectangle of indices u2^i3^j with 0<=i,j<=k.
- If a=b+1=k+1, the rectangle is 0<=i<=k+1, 0<=j<=k.
- If a<b, C_m consists of u2^i3^b with 0<=i<=a.
- If a>b+1, C_m consists of u2^a3^j with 0<=j<=b.

Using the values of the Möbius function on powers of 2 and 3 gives:

| Index \(m\) | Forced coefficient \(\ell_m\) |
|---|---:|
| \(u\) | \(\mu(u)/u\) |
| \(2u\) | \(\mu(u)/(2u)\) |
| \(3u\) | \(-\mu(u)/(3u)\) |
| \(6^k u,\ k\ge1\) | \(\mu(u)/(3u)\) |
| \(2\cdot6^k u,\ k\ge1\) | \(\mu(u)/(3u)\) |
| All other indices with rough part \(u\) | \(0\) |

All targets vanish when u is not squarefree.

### The forced formal series diverges in every order

For \(m=6^k\), \(k\ge1\), the target coefficient is \(\ell_m=1/3\), while \(h_m=D_mR_2\). The exact dilation norm and \(R_2^2=R_2\) give
\[
\|\ell_{6^k}h_{6^k}\|_{\mathcal H_P}^2
=\frac{6^k\log2}{9}\longrightarrow\infty.
\tag{4.6}
\]
Consequently the formal series \(\sum_m\ell_mh_m\) cannot converge in any enumeration: its individual terms do not tend to zero. No ordering of this dictionary is a Schauder basis of the whole Pareto Hilbert space, because continuity of the biorthogonal functionals would force these coefficients in an expansion of 1.

This does not contradict approximation by changing finite coefficient arrays. The statement that each fixed coefficient tends to \(\ell_m\) does not give a single norm-convergent series with those coefficients. A successful construction needs increasingly distant corrections whose contributions cancel in the full norm.

## 5. Further deletion and the exact candidate for a smallest subfamily

**Theorem 5.1 (finite deletion).** For any finite J, constant approximation using {h_m:m not in J} is possible exactly when constant approximation using all h_m is possible and ell_m=0 for every m in J.

Necessity follows by applying L_m. For sufficiency use the bounded finite-rank projection
\[
P_Jf=f-\sum_{m\in J}L_m(f)h_m.
\tag{5.1}
\]
It deletes precisely the selected coordinates. When all their targets vanish, P_J1=1, so applying P_J to approximants preserves convergence to 1.

A concrete deletion is h_4=R_12-R_4. Its cut is {4}, and
\[
L_4(f)=\frac{f(4)-f(3)-f(2)+f(1)}4,\qquad L_4(1)=0.
\]
Thus the dictionary with exactly one generator per dilation, and with h_4 omitted altogether, still gives an RH-equivalent constant-approximation criterion. The same is true after removing h_9 or any finite collection of zero-target indices.

Under RH, every h_m is nevertheless indispensable for density of the *whole Hilbert space*, because L_m annihilates the closed span of all the other h_n and takes value 1 on h_m. Removing h_4 preserves approximation of 1 while destroying full density. Its new span is no longer invariant under all integer dilations.

Define
\[
S_*:=\{m:\ell_m\ne0\}
=\left\{u,2u,3u,6^ku,2\cdot6^ku:
(u,6)=1,\ \mu(u)\ne0,\ k\ge1\right\}.
\tag{5.2}
\]

**Theorem 5.2 (unique possible inclusion-minimal target family).** Within subsets of the dictionary {h_m}, any inclusion-minimal family approximating 1 must be precisely {h_m:m in S_*}.

Indeed, every successful subfamily must contain all nonzero-target indices, by continuity of L_m. If a successful subfamily contains a zero-target index, the rank-one version of (5.1) removes it while retaining convergence. Such a family cannot be inclusion-minimal.

This identifies a precise further conjecture:
\[
\boxed{\mathrm{RH}\ \Longrightarrow\
1\in\overline{\operatorname{span}\{h_m:m\in S_*\}}.}
\tag{5.3}
\]
The reverse implication follows from containment in V. The forward implication is **unproved here**. Removing infinitely many individually removable coordinates requires a new limiting argument; continuity of each L_m separately does not control the infinite projection.

If RH holds and (5.3) fails, then no inclusion-minimal approximating subfamily exists within this dictionary: every successful subfamily has an individually removable element. This is why a smallest set under inclusion is a substantive question, rather than something guaranteed by algebraic independence.

## 6. Two fixed finite dilation templates are optimal

There is another, different meaning of size: the number of fixed finite legal functions whose *all integer dilates* may be used.

**Theorem 6.1 (single-template obstruction).** For every fixed finite remainder packet f in W,
\[
1\notin\overline{\operatorname{span}\{D_mf:m\ge1\}}.
\tag{6.1}
\]
This holds independently of RH and includes every fixed mixture of the 2- and 3-seeds.

**Proof.** The step-function Mellin functional is
\[
\mathcal M f(s)=\int_1^\infty f(\lfloor x\rfloor)x^{-s-1}\,dx.
\]
For Re s>1/2 it is continuous on the actual Pareto space, since
\[
|\mathcal Mh(s)|\le\frac{\|h\|_{\mathcal H_P}}{\sqrt{2\Re s-1}},
\qquad \mathcal M1(s)=\frac1s.
\tag{6.2}
\]
Write f=sum_{d in D}u_dR_d with D finite and put
\[
P_f(s)=\sum_{d\in D}u_d(1-d^{1-s}).
\]
Integrating the floor expansion first for Re s>1 and then continuing the analytic identity gives
\[
\mathcal Mf(s)=\frac{\zeta(s)}sP_f(s),\qquad \Re s>0,
\tag{6.3}
\]
with the singularity at s=1 removable. In particular P_f(1)=0.

If P_f is identically zero, any Mellin evaluation away from the pole already separates the target from all dilates. Otherwise choose epsilon in (0,1/2) such that P_f has no zero on the circle |s-1|=epsilon.

Simultaneous Diophantine approximation of the finitely many numbers log d/(2*pi) supplies T_j tending to infinity with d^(-iT_j) tending to 1 for every d in D. For completeness, Dirichlet approximation supplies arbitrarily accurate recurrent integer times; if these times have a bounded subsequence, one of them is an exact common period and its multiples provide unbounded recurrence instead. Therefore
\[
P_f(s+iT_j)\longrightarrow P_f(s)
\]
uniformly on each compact set. Rouché's theorem implies that, for large j, P_f has a zero s_j satisfying
\[
|s_j-(1+iT_j)|<\varepsilon.
\]
Thus Re s_j>1/2 and s_j is different from the pole 1. Equation (6.3) gives M f(s_j)=0.

The exact dilation identity
\[
\mathcal M(D_mf)(s)=m^{1-s}\mathcal Mf(s)
\tag{6.4}
\]
shows that the same continuous functional annihilates every dilate and its closed linear span. It does not annihilate 1. More quantitatively, every F in that closed span satisfies
\[
\boxed{\|F-1\|_{\mathcal H_P}^2
\ge\frac{2\Re s_j-1}{|s_j|^2}>0.}
\tag{6.5}
\]
This proves the theorem.

For a pure integer seed a>=2 the explicit extra zero is
\[
s_a=1+\frac{2\pi i}{\log a},
\]
so
\[
\|F-1\|^2\ge\frac1{1+(2\pi/\log a)^2}
\tag{6.6}
\]
for every combination of its dilates.

Combining Theorem 6.1 with (1.1), **under RH the minimum number of fixed finite legal dilation templates that can approximate 1 is exactly two**. The restriction to finite legal templates matters; an arbitrary Hilbert-space function is a different class of starting objects.

An immediate design restriction is that no fixed mixing ratio
\[
c_{2,m}=\alpha b_m,\qquad c_{3,m}=\beta b_m
\tag{6.7}
\]
can work across a sequence with fixed alpha,beta. These are exactly dilates of the single template alpha R_2+beta R_3. A successful method must allow the relative use of the seeds to vary with the dilation (or allow its template itself to vary with the approximation stage). The selected dictionary (3.1) does precisely this.

## 7. Arithmetic information: compensating coefficients must move to infinity

For F in V, use its unique physical remainder coordinates
\[
F=\sum_{d\ge2}r_d(F)R_d.
\]
They have finite support and satisfy r_d(F)=-alpha_d(F)/d. For each u>1 coprime to 6, every generator is an edge within one component, so
\[
\sum_{a,b\ge0}r_{2^a3^bu}(F)=0.
\tag{7.1}
\]
If F_j tends to 1 in Pareto norm, continuity of alpha_d forces
\[
r_d(F_j)\longrightarrow-\frac{\mu(d)}d.
\tag{7.2}
\]
For squarefree u>1 coprime to 6, the sum of these limiting coordinates in its component is
\[
-\frac{\mu(u)}u
\left(1-\frac12\right)\left(1-\frac13\right)
=-\frac{\mu(u)}{3u}\ne0.
\tag{7.3}
\]
Therefore the component sum in (7.1) cannot be passed through the limit. More explicitly, for any fixed A,B>=1,
\[
\sum_{\substack{a,b\ge0\\a>A\text{ or }b>B}}
r_{2^a3^bu}(F_j)\longrightarrow\frac{\mu(u)}{3u}.
\tag{7.4}
\]
The finite head tends to (7.3), and the total is zero. Equation (7.4) specifies the compensating coefficient sum outside every fixed exponent box.

For u=5 the limiting coefficients at 5,10,15,30 are respectively
\[
\frac15,-\frac1{10},-\frac1{15},\frac1{30},
\]
with total 1/15. Farther coefficients in that same component must carry total approaching -1/15.

This is useful information about any successful construction. Arbitrarily large powers of 2 or 3 are needed in every squarefree rough-root component. The outstanding analytic question is how these necessary corrections can have controlled full Pareto energy, retaining all signed mixed terms.

### Componentwise bounds cannot be substituted for the full norm

Let Q_u denote the algebraic projection selecting one rough-root component, for squarefree u>1. If F_j tends to 1, the local floor coefficients of Q_u F_j converge to those of
\[
q_u(n)=\mu(u)\left(
\lfloor n/u\rfloor-\lfloor n/(2u)\rfloor
-\lfloor n/(3u)\rfloor+\lfloor n/(6u)\rfloor\right).
\]
This grows as mu(u)*n/(3u)+O(1), so q_u does not belong to the Pareto Hilbert space. Fatou's lemma then gives
\[
\liminf_j\|Q_uF_j\|_{\mathcal H_P}^2=\infty.
\tag{7.5}
\]
Consequently, if constant approximation exists, even projection onto one such arithmetic component is unbounded in the Pareto norm. The algebraic decomposition into components is not an orthogonal Hilbert decomposition. Controlling separate components by absolute norms discards cancellations that a successful bounded full packet must exhibit.

## 8. Limits on restricting the dilation set

For the original two-seed coefficients,
\[
\alpha_d(F)=d\left(c_{2,d}+c_{3,d}
-\mathbf1_{2\mid d}c_{2,d/2}
-\mathbf1_{3\mid d}c_{3,d/3}\right).
\tag{8.1}
\]
When d is coprime to 6, approximation to 1 therefore requires
\[
c_{2,d}^{(j)}+c_{3,d}^{(j)}\longrightarrow\frac{\mu(d)}d.
\tag{8.2}
\]
Thus at least one of the two original generators at every squarefree dilation coprime to 6 must remain available. In particular, every prime p>=5 is required.

The necessary squarefree, coprime-to-6 set has natural density
\[
\frac13\prod_{p\ge5}(1-p^{-2})=\frac3{\pi^2}.
\tag{8.3}
\]
For example, this follows by inserting the squarefree indicator sum_{d^2|n}mu(d), counting integers coprime to 6, and using absolute convergence of the resulting reciprocal-square series. Thus a fixed density-zero set of allowed integer dilations cannot work with these two original primitive seeds. This concerns the union of dilation indices available across the sequence, not a requirement that each finite packet contain every such index.

### Squarefree dilations are insufficient

Fix u=5, or any squarefree u>1 coprime to 6. If only squarefree dilation indices are allowed, the endpoints in that component lie in the finite set
\[
S=u\{1,2,3,4,6,9,12,18\}.
\]
Every such packet has zero total remainder coefficient in S, hence
\[
L(F):=\sum_{d\in S}\frac{\alpha_d(F)}d=0.
\]
But L is continuous and
\[
L(1)=\sum_{d\in S}\frac{\mu(d)}d=\frac{\mu(u)}{3u}\ne0.
\]
This gives an unconditional positive approximation-error floor. The same proof rules out retaining only squarefree allowed Ramanujan conductors, with S=u{1,2,3,6}. Indeed B_d=sum_{e|d}mu(d/e)R_e, and squarefree d only introduces squarefree divisors; its component coefficient totals still vanish by legality.

The classical squarefree thinning in [Bagchi, Remark 4](https://arxiv.org/pdf/math/0607733) concerns constant approximation by the full residue family. It neither proves full density of that squarefree subfamily nor justifies transferring the same restriction to the two-seed dilation dictionary.

## 9. What “smallest” now means precisely

| Meaning of size | Conclusion |
|---|---|
| Fixed finite legal templates, with all integer dilates available | One never works; two suffice under RH. |
| Original generator choices at each m | One selected generator per m preserves V exactly. |
| Algebraic generation of all V | The h_m form a basis, so no one h_m can be deleted while keeping exactly V. |
| Density of the whole Pareto space | Under RH, the h_m are a minimal complete system, because their continuous biorthogonal functionals separate each element. |
| Approximation of the particular target 1 | Every finite collection of zero-target h_m may be deleted. S_* is the unique possible inclusion-minimal subfamily of this basis; whether it suffices under RH is unresolved here. |
| Cardinality of individual generators | Every working family must be infinite; a countable family suffices under RH. This gives little arithmetic guidance. |

For the last row, any finite family of finite legal packets has a common period Q and vanishes at every positive multiple of Q. Every linear combination consequently has squared error at least 1/[Q(Q+1)] against the constant. Equivalently, a finite-dimensional span is closed and cannot contain 1.

The most precise next thinning problem is (5.3). A quantitative route would establish uniform control of the projections deleting larger finite sets of zero-target coordinates, at least on a suitable actual approximating family. Such control must retain the full signed Pareto norm. The component obstruction (7.5) shows why a naive independent treatment of arithmetic components is inadequate.


---

# Continuation: exact interpolation, failed common-scale repairs, and the remaining energy target

Date: 2026-09-16.

**Status.** Sections 1–9 above are preserved as the handoff. This continuation supplies mathematical proofs, without Lean, of three further structural results and one exact reformulation of the remaining problem. It does not prove RH or the forward implication in (5.3), and does not claim novelty.

The new conclusions are:

1. The forced coefficients already interpolate the constant on every finite initial segment, using only the candidate minimal family \(S_*\).
2. A natural way to convert squarefree full-family approximants into legal packets fails: transporting all component charges by a common multiplier forces the correction energy to diverge. This conclusion retains all signed correlations between components.
3. The power damping \(\ell_m\mapsto\ell_m m^{-\varepsilon}\) also fails near \(\varepsilon=0\): its pointwise sum lies outside the actual Hilbert space because of a genuine Mellin pole.
4. Repairs at freely chosen larger indices remain open. For that problem, a uniform bound on the minimum norm of exact interpolants is enough; the bound need not tend to one. An exact finite Gram formula identifies the required cancellation.

## 10. The candidate minimal family already gives exact finite interpolation

Write \(t(m)=2m\) when the selected edge uses seed 2, and \(t(m)=3m\) otherwise. Define
\[
A_N:=\sum_{m\le N}\ell_mh_m,
\qquad
T_Nf:=\sum_{m\le N}L_m(f)h_m.
\tag{10.1}
\]
Since \(\ell_m=0\) off \(S_*\), the packet \(A_N\) belongs to the finite span of the candidate minimal family.

**Theorem 10.1 (exact interpolation).** For every \(N\ge1\),
\[
\boxed{A_N(n)=1\quad(1\le n\le N).}
\tag{10.2}
\]
More generally, \(T_Nf(n)=f(n)\) for \(1\le n\le N\).

**Proof.** We have
\[
h_m(n)=0\quad(n<m),\qquad h_m(m)=m.
\]
Consequently the restrictions of \(h_1,\ldots,h_N\) to the first \(N\) coordinates form an invertible lower triangular matrix. Every prescribed head has a unique interpolant in their span. The functional \(L_m\) depends only on coordinates at most \(m\). Applying it to the interpolant and using biorthogonality shows that its coefficient at \(h_m\) is \(L_m(f)\). Taking \(f=1\) proves (10.2). ∎

There is also an exact formula displaying the boundary charge. Put
\[
b_{N,d}:=\sum_{\substack{m\le N\\t(m)=d}}\ell_m
\qquad(N<d\le3N).
\]
The divergence of the tree flow gives
\[
\alpha_d(A_N)=
\begin{cases}
\mu(d),&d\le N,\\
-d\,b_{N,d},&N<d\le3N,\\
0,&d>3N.
\end{cases}
\tag{10.3}
\]
Indeed, the finite cut below a vertex is the disjoint union of that vertex and the cuts below its incoming neighbors; hence
\(\ell_d-\sum_{t(m)=d}\ell_m=\mu(d)/d\).
Using the floor expansion (4.2),
\[
\boxed{
A_N(n)=\sum_{d\le N}\mu(d)\lfloor n/d\rfloor
-\sum_{N<d\le3N}d\,b_{N,d}\lfloor n/d\rfloor.
}
\tag{10.4}
\]
The slopes cancel exactly:
\[
\sum_{d\le N}\frac{\mu(d)}d
=\sum_{N<d\le3N}b_{N,d}.
\tag{10.5}
\]
Thus (10.4) is a bounded periodic legal packet, despite its expression as a difference of growing floor sums.

**What this resolves.** Finite head interpolation is not the missing step, even after deleting every zero-target generator. All difficulty lies in the full norm outside the interpolated head.

**What it does not resolve.** The particular sequence \(A_N\) is unbounded in norm. For \(M=6^k\), \(k\ge1\),
\[
\|A_M-A_{M-1}\|=\frac{\sqrt{M\log2}}3,
\]
so
\[
\max(\|A_M\|,\|A_{M-1}\|)
\ge\frac{\sqrt{M\log2}}6.
\tag{10.6}
\]
This rules out a uniform bound for all these canonical truncations. It does not rule out useful subsequences, averages, or corrections beyond the interpolated head.

## 11. A common outward multiplier cannot repair the component charges

The following estimate applies to the full signed packet; it does not estimate separate arithmetic components and then add their norms.

**Lemma 11.1 (coercivity for a common dilation).** Let \(A\ge2\) be an integer, \(f\in\mathcal H_P\), and \(q\in\mathbb R\). Then
\[
C=D_Af+qR_A
\quad\Longrightarrow\quad
\boxed{
\|C\|^2\ge\frac{A}{(1+2\sqrt2)^2}\|f\|^2.
}
\tag{11.1}
\]

**Proof.** Telescoping the Pareto weights over each block gives
\[
\|D_Af\|^2=A\|f\|^2.
\tag{11.2}
\]
On \(1\le n<A\), we have \(C(n)=qn\). With \(H_A=\sum_{j=1}^A1/j\),
\[
\|C\|^2\ge q^2\sum_{n=1}^{A-1}\frac n{n+1}
=q^2(A-H_A)\ge\frac A4q^2.
\tag{11.3}
\]
Here \(H_A\le3A/4\) for \(A\ge2\), as follows from the case \(A=2\) and induction. Also, splitting at \(A\) and using \(R_A(n)\le A\) gives
\[
\|R_A\|^2\le(A-1)+A^2\sum_{n=A}^\infty\frac1{n(n+1)}<2A.
\tag{11.4}
\]
Therefore
\[
\sqrt A\|f\|=\|D_Af\|
\le\|C\|+|q|\|R_A\|
\le(1+2\sqrt2)\|C\|.
\]
Squaring proves the lemma. No restriction on the sign of \(q\), or on cancellations within \(f\), was used. ∎

Let \(\mathcal U=\{u\ge1:(u,6)=1,\ \mu(u)\ne0\}\). For any finitely supported real array \((q_u)_{u\in\mathcal U}\), define
\[
f=\sum_{u\in\mathcal U}q_uR_u,
\qquad
C_A=\sum_{u\in\mathcal U}q_uR_{Au}.
\]
The exact remainder identity is
\[
C_A=D_Af+\Big(\sum_uq_u\Big)R_A.
\tag{11.5}
\]
The term \(q_1R_1\) in \(f\) is zero; \(q_1\) may be chosen freely.

The functional
\[
\alpha_5(f)=f(5)-f(4)-f(1)=-5q_5
\]
has squared dual norm \(30+20+2=52\). Consequently Lemma 11.1 yields
\[
\boxed{
\|C_A\|^2\ge
\frac{25Aq_5^2}{52(1+2\sqrt2)^2}.
}
\tag{11.6}
\]
All other component coefficients can vary arbitrarily with \(A\); inequality (11.6) still holds. In particular, cross-component cancellation cannot evade this estimate.

### Application to squarefree full-family approximants

Suppose
\[
P_j=\sum_{d\text{ squarefree},\ d\ge2}r_{j,d}R_d
\longrightarrow1
\quad\text{in }\mathcal H_P,
\tag{11.7}
\]
with finite support at each stage. Such a sequence exists under RH by the squarefree refinement in [Bagchi, Remark 4](https://arxiv.org/pdf/math/0607733).

For a squarefree rough root \(u>1\), its component charge is
\[
q_{j,u}=r_{j,u}+r_{j,2u}+r_{j,3u}+r_{j,6u}.
\tag{11.8}
\]
Continuity of the physical remainder coordinates forces
\[
q_{j,u}\longrightarrow-\frac{\mu(u)}{3u}.
\tag{11.9}
\]
In particular \(q_{j,5}\to1/15\).

Consider repairing all these charges at the same outward multiplier:
\[
C_j=\sum_{u\in\mathcal U}q_{j,u}R_{A_ju},
\qquad F_j=P_j-C_j,
\qquad A_j\longrightarrow\infty.
\tag{11.10}
\]
Allow \(q_{j,1}\) to be arbitrary. When \(A_j=6^{K_j}\), \(K_j\ge1\), the terminal vertices lie on the retained paths, and the repaired packet is in the span of \(S_*\): every component with \(u>1\) has zero total coefficient, and the component \(u=1\) is rooted at \(R_1=0\).

Nevertheless, (11.6) proves
\[
\liminf_{j\to\infty}\frac{\|C_j\|^2}{A_j}
\ge\frac1{468(1+2\sqrt2)^2}>0.
\tag{11.11}
\]
Since \(P_j\) is bounded in norm,
\[
\boxed{\|P_j-C_j\|\longrightarrow\infty.}
\tag{11.12}
\]

**Consequence.** The squarefree full-family criterion cannot be transferred to \(S_*\) by this common-multiplier terminal repair. This is an obstruction to a specific construction, not a disproof of (5.3). Different components may still be repaired at different scales, or by several terminal vertices with jointly optimized coefficients.

## 12. Power damping the forced coefficients creates a genuine Mellin pole

A second tempting construction is
\[
F_\varepsilon(n)
:=\sum_{m\ge1}\ell_m m^{-\varepsilon}h_m(n),
\qquad \varepsilon>0.
\tag{12.1}
\]
For each fixed \(n\), this sum is finite because \(h_m(n)=0\) for \(m>n\). Theorem 10.1 implies
\[
F_\varepsilon(n)\longrightarrow1
\quad\text{as }\varepsilon\downarrow0.
\tag{12.2}
\]
The issue is whether these pointwise sums belong to \(\mathcal H_P\).

**Theorem 12.1 (power-damping obstruction).** There is an \(\varepsilon_0>0\), unconditionally, such that
\[
F_\varepsilon\notin\mathcal H_P
\qquad(0<\varepsilon<\varepsilon_0).
\tag{12.3}
\]
Under RH the same conclusion holds for every \(0<\varepsilon<1/2\). For \(\varepsilon>1/2\), by contrast, (12.1) converges absolutely in the Hilbert norm.

**Proof.** Write
\[
w=s+\varepsilon,\quad
x=2^{1-s},\quad y=3^{1-s},\quad
 a=2^{1-w},\quad b=3^{1-w},\quad r=ab=6^{1-w},
\]
and set
\[
E(w)=(1-2^{-w})(1-3^{-w}).
\]
The rough-root Möbius series is
\[
\sum_{(u,6)=1}\frac{\mu(u)}{u^w}
=\frac1{\zeta(w)E(w)}\qquad(\Re w>1).
\tag{12.4}
\]
Using the explicit coefficient table in Section 4, the first three edges in each component contribute
\[
(1-x)(1-b/3)+(a/2)(1-y),
\]
while the two edges in each subsequent level contribute a geometric series. Define
\[
\Psi_\varepsilon(s)
=(1-x)(1-b/3)+\frac a2(1-y)
+\frac{r}{3(1-r)}\big((1-x)+a(1-y)\big).
\tag{12.5}
\]
Termwise Mellin integration, initially on \(\Re s>1\), gives
\[
\boxed{
\mathcal MF_\varepsilon(s)
=\frac{\zeta(s)}s\,
\frac{\Psi_\varepsilon(s)}{\zeta(s+\varepsilon)E(s+\varepsilon)}.
}
\tag{12.6}
\]
For justification, on this half-plane the absolute Mellin integrals are bounded by convergent rough-root and geometric series: the relevant parameters are \(\sum_u u^{-\Re w}\) and \(\sum_k6^{k(1-\Re w)}\). Thus the displayed identity does not assume Hilbert-space membership.

Put
\[
T=\frac{2\pi}{\log6},\qquad s_\varepsilon=1-\varepsilon+iT.
\tag{12.7}
\]
At \(s=s_\varepsilon\), we have \(r=1\). If \(a_0=e^{-iT\log2}\), then the numerator of the singular term in (12.5) is
\[
(1-x)+a(1-y)
=1-3^\varepsilon+(1-2^\varepsilon)a_0.
\tag{12.8}
\]
This is nonzero: its two summands have unequal magnitudes, since
\(3^\varepsilon-1>2^\varepsilon-1\).
Thus \(\Psi_\varepsilon\) has a simple pole at \(s_\varepsilon\), with residue
\[
\frac{1-3^\varepsilon+(1-2^\varepsilon)a_0}{3\log6}.
\tag{12.9}
\]
The denominator \(\zeta(1+iT)E(1+iT)\) is finite and nonzero. Here we use the classical zero-free line \(\Re s=1\); see [NIST DLMF §25.10(i)](https://dlmf.nist.gov/25.10#i).

By continuity and \(\zeta(1+iT)\ne0\), there is \(0<\varepsilon_0<1/2\) such that \(\zeta(s_\varepsilon)\ne0\) for \(0<\varepsilon<\varepsilon_0\). Hence (12.6) has a genuine pole inside \(\Re s>1/2\). Under RH, the numerator is nonzero at this point for every \(0<\varepsilon<1/2\).

If \(F_\varepsilon\) belonged to \(\mathcal H_P\), its Mellin transform would be holomorphic on \(\Re s>1/2\), by Cauchy–Schwarz and local domination. Its equality with (12.6) on \(\Re s>1\), followed by uniqueness of meromorphic continuation, would make such a pole impossible. This proves the nonmembership assertions.

For the last assertion, \(\|h_m\|\le C\sqrt m\) for an absolute constant \(C\), by the exact dilation norm. The coefficient table bounds the sum of term norms by a constant times
\[
\sum_{u\ge1}u^{-1/2-\varepsilon}
\left(1+\sum_{k\ge1}6^{k(1/2-\varepsilon)}\right),
\]
which is finite when \(\varepsilon>1/2\). ∎

There is a revealing cancellation at the formal endpoint \(\varepsilon=0\). In that case
\[
(1-x)+x(1-y)=1-xy=1-r,
\]
and direct algebra gives
\[
\Psi_0(s)=(1-2^{-s})(1-3^{-s})=E(s).
\tag{12.10}
\]
The right side of (12.6) then reduces to \(1/s\) on its initial domain, consistently with the pointwise identity \(F_0=1\).

**Interpretation.** The exact undamped coefficients cancel a geometric resonance. Power damping breaks that cancellation and introduces poles approaching \(1+2\pi i/\log6\). The failure is stronger than the divergence of individual terms in the forced series: even the pointwise-defined damped sum is outside the Hilbert space for all sufficiently small positive damping parameters. This does not exclude every possible smoothing procedure or every finite array with varying coefficients.

## 13. A bounded-energy criterion that would suffice for the retained family

Let
\[
Y_*:=\overline{\operatorname{span}\{h_m:m\in S_*\}}.
\]
For \(B\ge N\), put
\[
\mathcal T_{N,B}:=\operatorname{span}\{h_m:m\in S_*,\ N<m\le B\},
\]
and define
\[
K_{N,B}:=\min_{v\in\mathcal T_{N,B}}\|A_N+v\|^2,
\qquad
K_N:=\inf_{B\ge N}K_{N,B}.
\tag{13.1}
\]
Every packet in the minimum is exactly one on the first \(N\) coordinates. Conversely, every finite packet from \(S_*\) with that head has this form for some \(B\): its first \(N\) coefficients must be \(\ell_m\), by the finite-coordinate functionals.

**Theorem 13.1 (bounded energy suffices; exact dichotomy).** The following are equivalent:
\[
\begin{aligned}
&1\in Y_*;\\
&\sup_NK_N<\infty;\\
&K_N\longrightarrow1.
\end{aligned}
\tag{13.2}
\]
In fact \(K_N\) is nondecreasing and
\[
\boxed{
\begin{cases}
N/(N+1)\le K_N\le1,\quad K_N\to1,&1\in Y_*,\\
K_N\to\infty,&1\notin Y_*.
\end{cases}
}
\tag{13.3}
\]

**Proof.** Exact head interpolation implies
\[
\|A_N+v\|^2\ge\sum_{n=1}^N\frac1{n(n+1)}=\frac N{N+1}.
\tag{13.4}
\]
The feasible sets shrink as \(N\) increases, so \(K_N\) is nondecreasing.

Suppose \(1\in Y_*\), and choose finite packets \(P_j\to1\) in this family. For fixed \(N\), define
\[
\widetilde P_j=P_j+T_N(1-P_j)=A_N+(I-T_N)P_j.
\tag{13.5}
\]
These are finite packets from \(S_*\), exactly equal to one on the first \(N\) coordinates. The use of \(S_*\) is valid because \(L_m(P_j)=L_m(1)=0\) for every deleted index. Since \(T_N\) is a bounded finite-rank operator, \(\widetilde P_j\to1\). Hence \(K_N\le1\), and (13.4) proves convergence to one.

Conversely, if \(K_N\) is uniformly bounded, choose exact interpolants \(G_N\) from the defining finite spans with \(\|G_N\|^2\le K_N+1/N\). A subsequence converges weakly in the Hilbert space. Every fixed coordinate of \(G_N\) is eventually one, and coordinate evaluations are continuous. Thus its weak limit is precisely the constant sequence \(1\). The closed linear subspace \(Y_*\) is weakly closed, so \(1\in Y_*\). This proves (13.2); monotonicity proves the remaining alternative in (13.3). ∎

This makes the role of weak compactness precise. It turns a proved uniform energy estimate into constant approximation. It supplies no such estimate by itself. Convex combinations of a weakly convergent subsequence can then give finite legal packets converging in norm.

### The exact finite signed Gram calculation

Enumerate \(I_{N,B}=\{m\in S_*:N<m\le B\}\). Define
\[
G=(\langle h_m,h_n\rangle)_{m,n\in I_{N,B}},
\qquad b=(\langle h_m,A_N\rangle)_{m\in I_{N,B}}.
\tag{13.6}
\]
Linear independence makes \(G\) positive definite when the index set is nonempty. Completing the square gives
\[
\boxed{K_{N,B}=\|A_N\|^2-b^TG^{-1}b.}
\tag{13.7}
\]
For an empty index set, the subtraction is zero. Every entry is calculated in the actual Pareto inner product:
\[
\langle h_m,h_n\rangle
=\sum_{r\ge1}\frac{h_m(r)h_n(r)}{r(r+1)}.
\]
Thus (13.7) retains every signed cross term induced by the coefficients, including correlations across rough roots and across scales.

A concrete sufficient target is therefore:
\[
\boxed{
\exists C<\infty\ \forall N\ \exists B\ge N:
\quad b_{N,B}^{T}G_{N,B}^{-1}b_{N,B}
\ge\|A_N\|^2-C.
}
\tag{13.8}
\]
Proving (13.8) would give \(1\in Y_*\), hence \(1\in\overline V\), hence RH by the established bridge in Section 1. No prescribed rate for \(B\) is required for this implication.

An upper bound \(K_N\le C\) with any fixed finite \(C\) suffices. Theorem 13.1 would then force the optimal energies to tend to one automatically. On the other hand, a subpolynomial bound that still diverges does not supply the weak compactness used here.

**Dependency warning.** We have proved equivalence with \(1\in Y_*\), not equivalence with RH alone. The implication RH \(\Rightarrow1\in Y_*\) remains exactly the unproved thinning conjecture (5.3). The new criterion does not silently assume or establish that implication.

## 14. Research decision after these calculations

| Construction or claim | Status after this continuation | Consequence |
|---|---|---|
| Exact interpolation from the nonzero-target generators | Proved for every finite head | No additional local interpolation lemma is needed. |
| Uniform norm bound for all canonical truncations \(A_N\) | Refuted by (10.6) | Coefficients beyond the head, or a different summation procedure, are necessary for a uniformly bounded family. |
| Common-multiplier terminal repair of squarefree approximants | Refuted by (11.11)–(11.12) | Moving every component outward by the same multiplier cannot control full energy. |
| Power damping \(\ell_m m^{-\varepsilon}\) as \(\varepsilon\downarrow0\) | Refuted by a genuine Mellin pole | Pointwise convergence here does not even give Hilbert-space membership near the endpoint. |
| Unrestricted corrections within \(S_*\) | Open | Their optimum has the exact dichotomy in (13.3). |
| RH implies approximation from \(S_*\) | Open | Neither obstruction disproves this conditional statement. |
| Uniform bound in (13.8) | Open; sufficient for RH | This is the remaining full signed-energy target for this continuation. |

**Recommended next calculation.** Work on (13.8) using corrections at different scales, allowing several terminal vertices in each component. The first estimate must concern their combined signed Gram form. A common outward multiplier has now been ruled out, and termwise power damping introduces a separate resonance obstruction. Neither should be reused as a presumed repair.

A meaningful negative result would have to prove \(K_N\to\infty\) for the unrestricted optimum, rather than for one ansatz. A meaningful positive result would prove one uniform constant in (13.8), rather than pointwise interpolation, individual coefficient convergence, or separate component estimates.

### Verification and source scope

The proofs in Sections 10–13 are given above and were checked algebraically. As a supplementary finite check, the exact interpolation identity was verified with rational arithmetic for all \(1\le n\le N\le100\); this is not used in place of the proof. No Lean verification was performed.

The externally cited inputs are the established full-family/squarefree approximation criterion in Bagchi and the classical zero-free line for zeta recorded by NIST. The common-dilation estimate, the damping calculation, and the bounded-energy dichotomy are derivations in this continuation. No claim that these results settle RH is made.

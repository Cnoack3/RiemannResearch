# Exact interpolation, Pythagoras, and a weighted CRT extension target

Source: user-provided research request, 9 September 2026. The Hilbert argument
uses standard projection theory. It is not claimed as a new theorem in the
literature. The arithmetic construction proposed below remains open.

## Status and scope

Lean checked the complete abstract implication in
[BoundedInterpolation.lean](../Analysis/BoundedInterpolation.lean):
existence of minimum-norm exact interpolants, their exact Pythagorean identity,
and strong convergence from a uniform norm bound. The actual weighted-space
specialization is in
[ThresholdBoundedInterpolation.lean](ThresholdBoundedInterpolation.lean).

The finite interpolation argument, capacity dichotomy, charge formulation, and
CRT matrix assembly below are written mathematical arguments. They have not
all been newly formalized in these modules. Existing checked weighted CRT
and finite Schur identities are cited where used.

**Open:** uniformly bounded finite legal exact interpolants. Neither that
arithmetic bound nor RH is proved here.

## 1. Preserve the actual span and the actual norm

Put
\[
 w_k=\frac1{k(k+1)},\quad
 H=\ell^2(\mathbb N_{>0},w),\quad
 \|F\|^2=\sum_{k\ge1}w_kF(k)^2,\quad \|\mathbf1\|^2=1.
\]
Coordinate zero is anchored separately and has no Hilbert mass.

For \(r_a(k)=k\bmod a\), the legal generators are
\[
 g_{a,m}(k)=m\bigl(\lfloor k/m\rfloor\bmod a\bigr)
          =r_{am}(k)-r_m(k).
\]
Let \(S=\operatorname{span}_{\mathbb R}\{g_{2,m},g_{3,m}:m\ge1\}\)
and \(V=\overline S^{\,H}\). Every positive integer dilation remains available.

These generators lie in the full residue span. Thus
\(\mathbf1\in V\) implies membership in the full residue closure, which implies
RH by the discrete Nyman-Beurling-Baez-Duarte criterion. Bagchi's
[Theorem 1](https://arxiv.org/pdf/math/0607733) states that criterion with
\(\gamma_a(k)=\{k/a\}=r_a(k)/a\) and exactly these weights.
No converse identifying the two-seed closure with the full residue closure is
assumed or newly verified here.

## 2. Exact finite interpolation is unconditional

The binary columns \(u_m=g_{2,m}\), \(1\le m\le N\), satisfy
\[
 u_m(k)=0\ (k<m),\qquad u_m(m)=m.
\]
Their first \(N\) rows form an invertible triangular matrix. In particular,
the finite legal interpolant
\[
 F_N=\sum_{m=1}^N\lambda_m u_m,\qquad
 \lambda_m=\frac{1-\sum_{j<m}\lambda_j u_j(m)}m
\]
equals one on \(1,\ldots,N\). This construction proves feasibility, but gives
no uniform full-norm estimate. The second seed supplies additional tail
corrections; it is unnecessary for finite-head feasibility.

For any exact-head interpolant there is the exact decomposition
\[
 \|F_N\|^2=\frac{N}{N+1}
       +\sum_{k>N}\frac{F_N(k)^2}{k(k+1)}.
\]
Bounded tail energy suffices; tail energy of the chosen witnesses need not
itself tend to zero.

## 3. Pythagoras supplies strong convergence after boundedness

Let
\[
 A_N=\{v\in V:v(k)=1,\ 1\le k\le N\},\qquad
 T_N=\{t\in V:t(k)=0,\ 1\le k\le N\}.
\]
Coordinates are continuous because \(|v(k)|\le\|v\|/\sqrt{w_k}\).
Thus \(A_N\) is a nonempty closed affine subspace. For any \(F_N\in A_N\),
\[
 v_N=F_N-P_{T_N}F_N
\]
is its unique minimum-norm element. Write \(c_N=\|v_N\|^2\).

Since \(v_N\perp T_N\) and \(v_M-v_N\in T_N\) for \(M\ge N\),
\[
 \boxed{c_M=c_N+\|v_M-v_N\|^2.}
\]
Hence \(c_N\) is increasing. If it is bounded, its scalar limit exists and
this exact identity makes \(v_N\) Cauchy in \(H\). Completeness and closedness
give a limit in \(V\). Every positive coordinate of that limit is one, so
the limit is \(\mathbf1\).

Only **after** this step may one put \(\mathbf1-v_N\in T_N\) and obtain
\[
 \boxed{\|\mathbf1-v_N\|^2=1-c_N,\qquad c_N\uparrow1.}
\]
This is the desired exact squared distance formula, with the limit proved
from boundedness rather than assumed.

For any closed space with these nonempty affine slices, the capacities have
the dichotomy
\[
 c_N\uparrow1\quad\hbox{or}\quad c_N\longrightarrow+\infty.
\]
Indeed bounded capacities force the first alternative; an increasing
unbounded real sequence has the second. A finite limiting capacity greater
than one is impossible.

Arbitrary bounded witnesses \(F_N\) need not themselves converge strongly.
The minimum-norm interpolants \(v_N\) are the strongly convergent sequence.

## 4. Finite witnesses and closed minima have the same infimum

Let \(E_N:H\to\mathbb R^N\) be the head map. Triangular interpolation supplies
a linear right inverse \(R_N:\mathbb R^N\to S\). This map is continuous since
its domain is finite dimensional. Its operator norm may depend on \(N\).

For \(v\in A_N\), choose \(s_j\in S\) tending to \(v\). Then
\[
 t_j=s_j+R_N(\mathbf1_N-E_Ns_j)
\]
lies in \(S\), matches the head exactly, and tends to \(v\). Consequently
\[
 c_N=\inf\{\|F\|^2:F\in S,\ E_NF=\mathbf1_N\}.
\]
The algebraic infimum need not be attained. Closed minimizers must not be
called finite legal combinations.

It follows that the following are equivalent:
\[
 \mathbf1\in V
 \quad\Longleftrightarrow\quad
 \exists C<\infty\ \forall N\ \exists F_N\in S:
 E_NF_N=\mathbf1_N,\quad\|F_N\|^2\le C.
\]
For the reverse construction, if \(\mathbf1\in V\), finite exact-head
approximations can be chosen with squared norm at most \(2\).
No uniform bound on the right inverses \(R_N\) is needed: choose the
approximation accuracy separately for each \(N\).

Thus the proposed arithmetic theorem is equivalent to this target closure
statement. It is not advertised as easier merely because it asks for a bound.

## 5. The remaining theorem as an exact CRT Schur complement

Fix \(N\). Select finitely many legal columns \(g_{a,m}\), and choose an
arbitrary common multiple \(Q>N\) of their periods \(am\). Use representatives
\(r=1,\ldots,Q\), including \(r=Q\), the class of positive multiples of \(Q\).

Define
\[
 W_Q(r)=\sum_{j\ge0}\frac1{(r+jQ)(r+jQ+1)},\qquad
 \tau_{Q,N}(r)=W_Q(r)-\mathbf1_{\{r\le N\}}w_r>0.
\]
Let \(A\) be the matrix of legal column values on these representatives and
\(A_H\) its first \(N\) rows. Put
\[
 K=A^\top\operatorname{diag}(\tau_{Q,N})A.
\]
For every feasible coefficient vector \(c\), \(A_Hc=\mathbf1_N\), periodic
regrouping gives the exact full norm
\[
 \boxed{\|Ac\|_H^2=\frac N{N+1}+c^\top Kc.}
\]
These are infinite progression masses, not uniform CRT counting weights or
truncated numerical tails. The positive-multiples row is retained even
though every legal column vanishes there.

Remove redundant columns of \(A\), take a feasible \(c_0\), and let the
independent columns of \(Z\) span \(\ker A_H\). All feasible coefficients
are \(c_0+Zb\). Set
\[
 H_0=Z^\top KZ,\qquad q=Z^\top Kc_0.
\]
If the kernel is nonzero, \(H_0\) is positive definite and exact completion
of the square gives
\[
 (c_0+Zb)^\top K(c_0+Zb)
 =c_0^\top Kc_0-q^\top H_0^{-1}q
 +(b+H_0^{-1}q)^\top H_0(b+H_0^{-1}q).
\]
For a zero-dimensional kernel, the correction is simply absent.

The concrete arithmetic target is:

> There is a constant \(B\), independent of \(N\), such that one can choose
> the finite legal columns and a common period \(Q_N\) with feasible head
> constraints and
> \[
> c_0^\top Kc_0-q^\top H_0^{-1}q\le B.
> \]

This requires only uniformly bounded optimized tail energy, not a prescribed
rate of vanishing squared error. Finite matrix invertibility by itself gives
no uniform bound. The full mixed Gram terms remain in \(K\) and \(H_0\).

Existing checked components:
[ThresholdWeightedCRT.lean](ThresholdWeightedCRT.lean),
[ParetoPeriodicRegrouping.lean](ParetoPeriodicRegrouping.lean), and
[ParetoFiniteSchur.lean](ParetoFiniteSchur.lean).
Their assembly into this particular family and the uniform arithmetic bound
are not discharged by those component theorems.

## 6. A more explicit two-seed charge extension problem

In the normalized Mobius-difference coordinates \(d_n\), the generator
\(g_{a,m}=r_{am}-r_m\) has charge \(\delta_m-\delta_{am}\).
The components for seeds 2 and 3 are
\(\{q2^i3^j:i,j\ge0\}\), where \((q,6)=1\).
A finite legal charge vector has total zero in each component; conversely
finite zero-sum charges can be realized by finite edge flows in that
connected component.

Exact head interpolation prescribes
\[
 d_n=\frac{\mu(n)}n\quad(1\le n\le N).
\]
The high charges must balance
\[
 \sum_{\substack{n>N\\\operatorname{core}_6(n)=q}}d_n=-S_{q,N},\qquad
 S_{q,N}=\frac{\mu(q)}q
 \left(\mathbf1_{q\le N}-\tfrac12\mathbf1_{2q\le N}
 -\tfrac13\mathbf1_{3q\le N}+\tfrac16\mathbf1_{6q\le N}\right).
\]
For \(q\le N/6\), this is \(S_{q,N}=\mu(q)/(3q)\).
Reconstruct
\[
 F(k)=-\sum_{n\ge2}d_n r_n(k).
\]
Sending each low component's imbalance to one sufficiently high vertex
\(q2^J\) proves feasibility. It supplies no uniform norm bound.
The remaining construction must distribute and cancel these charges while
bounding the complete Pareto quadratic form, including cross-component
terms. It must handle all rough cores, not only the \(2^i3^j\) component.

## 7. Two tempting shortcuts that do not prove the bound

The existing hilbertBlockProjection_pythagoras concerns the physical
dilation-range projection \(P_m=m^{-1}T_mT_m^*\), not projection onto the
legal span. Its coordinate formula gives
\[
 P_m\mathbf1=\mathbf1_{\{k\ge m\}},\quad
 \|P_m\mathbf1\|^2=1/m,\quad
 \|\mathbf1-P_m\mathbf1\|^2=1-1/m.
\]
That particular family therefore does not approach the target as \(m\to\infty\).

Likewise weighted conditional expectation onto a coarser CRT quotient is
not automatically a legal operation. Already the one-residue average sends
\(r_2\) to \((\log2)\mathbf1\). Assuming it preserves the legal closure
would already imply the target closure assertion.

For nested quotients and newly added legal columns \(B\), let \(J\) be the
isometric coarse embedding, \(E=J^*\), \(P\) the old legal projection,
\(r=\mathbf1-P\mathbf1\), \(C=EB\), and \(D=B-JC\). Residualization gives
\[
 B-JPC=J(I-P)C+D,\qquad
 K_{\rm new}=C^*(I-P)C+D^*D,\qquad u=C^*r.
\]
The exact gain is \(u^*K_{\rm new}^{\dagger}u\). The fine defect \(D\) has
zero direct target correlation but positive Gram cost. Any CRT construction
must control that cost rather than omit it. All adjoints here use the
actual Pareto weights.

## Verification

The coherent Lean candidate, including the actual weighted-space
specialization, passed with no diagnostics. The two main declarations
depend only on ordinary Lean/Mathlib foundational axioms:
propext, Classical.choice, and Quot.sound.
This dependency audit does not discharge the explicitly quantified
uniform interpolation hypothesis.

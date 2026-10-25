# Squarefree CRT indicators, topology, and canonical approximants

Date: 2026-10-25. Source: user-provided argument and questions.

## Scope and status

This development formalizes the CRT indicator discussion, weak compactness,
the norm boundary, and the canonical finite projections. It proves neither
\(1\in H_{\mathrm{sf}}\) nor its negation. The concrete counterexample below
concerns closure under products and unions, not convergence of the projection
residuals.

The ambient space is the repository's complete \(L^2(Q)\) model with
\(Q(k)=1/(\zeta(2)k^2)\), \(k\ge1\), and
\(g_d(k)=(k\bmod d)/d\). The closed subspace \(H_{\mathrm{sf}}\) is
`ZetaTwoOptimizerStage.closure`. The masked finite stages repeat at
nonsquarefree conductors; their nonzero stages give the usual squarefree
exhaustion.

## CRT and the obstruction to combining indicators

The general identity already exists as
`CRTCarryArithmetic.real_decomposition` and `QCRTCarry.qCarry_eq_linear`.
For positive \(p,q\) and integer \(a,b,t\) satisfying
\(aq+bp=1+tpq\),
\[
C_{p,q}(k)=\lfloor a g_p(k)+b g_q(k)\rfloor,\qquad
g_{pq}=a g_p+b g_q-C_{p,q}.
\]
The floor-defined carry is encoded independently; the identity is proved.

The new concrete legal vector is
\[
A=g_6-g_2+g_3=\mathbf1_{\{k\bmod6\in\{2,4,5\}\}}.
\]
It is the negative carry for \(p=2,q=3,a=1,b=-1\).
It belongs even to the finite squarefree span and differs from \(1\).

The odd indicator \(O=2g_2\) also belongs to the squarefree span. However,
\[
U=AO=\mathbf1_{\{k\bmod6=5\}}\notin H_{\mathrm{sf}}.
\]
The existing continuous omitted-coordinate functional certifies this:
\[
qCoefficientCLM(25)(f)=0\quad(f\in H_{\mathrm{sf}}),\qquad
qCoefficientCLM(25)(U)=1.
\]
Consequently the union indicator
\[
A+O-U=\mathbf1_{\{6\nmid k\}}
\]
also lies outside \(H_{\mathrm{sf}}\). Membership of the factors alone cannot
justify multiplication, intersection, or union of their supports.

For a binary physical vector \(f\), the complete normalized-Q identity is
\[
\|1-f\|_Q^2=1-\langle1,f\rangle_Q.
\]
Thus a sequence of legal binary vectors with Q mass tending to one would
prove target membership. This is a conditional research reduction:
**Open:** produce the legal binary sequence and prove its complete-Q mass
limit. Neither is supplied merely by the CRT identity.

## Norm boundary and dimension

The explicit continuous functional
\[
\Lambda(f)=f(4)-f(3)-f(2)+f(1)
\]
vanishes on \(H_{\mathrm{sf}}\) and on \(1\), while \(\Lambda(g_4)=-1\).
It proves that the squarefree closed span is proper. It does not separate
the target \(1\) from that span.

The ambient norm interior is empty and
\[
\partial H_{\mathrm{sf}}=H_{\mathrm{sf}}.
\]
The subspace is unbounded and hence its boundary is not norm compact.
The prime atoms form an infinite linearly independent subfamily. Therefore
\(H_{\mathrm{sf}}\) is infinite-dimensional and every intrinsic norm closed
ball of positive radius is noncompact.

## Actual weak compactness

For every real \(r\), the set
\[
B_r=\{f\in H_{\mathrm{sf}}:\|f\|_Q\le r\}
\]
is compact in the ambient weak topology. The formal statement uses
`WeakSpace ℝ QHilbert`; it does not accidentally use norm compactness.
The proof transports Mathlib's Banach--Alaoglu theorem through Riesz duality
and the continuous weak map induced by the subspace inclusion.

The subspace is separable because it is the closed span of a countable
dictionary. The same ball is weakly sequentially compact, with a
strictly increasing subsequence and a limit satisfying the same radius bound.
For \(r=0\) the ball is \(\{0\}\); for \(r<0\) it is empty.

## Canonical finite approximants

Here \(F_M\) is exactly the existing canonical optimizer,
\(F_M=P_{V_M}1\), and \(r_M=1-F_M\). The new exact identities are
\[
F_M\in H_{\mathrm{sf}},\qquad \|F_M\|_Q\le1,\qquad
\|F_M\|_Q^2+\|r_M\|_Q^2=1,
\]
and for every \(f\in V_M\),
\[
\|1-f\|_Q^2=\|r_M\|_Q^2+\|F_M-f\|_Q^2.
\]
The existing strong convergence theorem is
`ZetaTwoOptimizerStage.optimizer_tendsto`. The new actual weak convergence
theorem has the same full-sequence limit:
\[
F_M\longrightarrow P_{H_{\mathrm{sf}}}1
\quad\text{strongly and weakly}.
\]
In particular,
\[
F_M\rightharpoonup1\quad\Longleftrightarrow\quad1\in H_{\mathrm{sf}}.
\]
Weak compactness yields a legal bounded limit; it does not identify that
limit with the target. **Open:** prove \(P_{H_{\mathrm{sf}}}1=1\), equivalently
the original zero residual limit. No unconditional RH claim is made.

## Formalization and validation

The six new exported modules are:
- `Analysis/HilbertWeakCompactness.lean`
- `RH/QCRTIndicatorClosure.lean`
- `RH/QCRTIndicatorProduct.lean`
- `RH/QSquarefreeBoundary.lean`
- `RH/QSquarefreeDimension.lean`
- `RH/QSquarefreeWeakCompactness.lean`

The exact declaration types distinguish unconditional identities and
topological statements from the conditional indicator-exhaustion theorem.
The publication checkpoint is responsible for auditing and validating the
final source delta, including aggregate imports. No placeholders, project
axioms, or unsafe declarations are part of this development.

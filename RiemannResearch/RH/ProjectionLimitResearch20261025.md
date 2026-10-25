# Squarefree projection limits, moments, and the residual-tail dichotomy

Date: 2026-10-25.

Source: the user's CRT, exact-head, projection, and moment discussion.
The arguments use the actual inverse-square probability law and standard
Hilbert-space identities. No novelty claim is made.

## Verification status

The new declarations listed below are part of this change's server-verified
publication checkpoint. Previously published results and ordinary calculations
not newly formalized are distinguished explicitly. The checkpoint validates
the saved modules and their aggregate imports; an isolated snippet is not the
publication gate.

**Open:** prove that the constant target belongs to the closed squarefree span.
No unconditional RH conclusion is claimed, and no counterexample to that
membership statement has been constructed.

## 1. The two families must remain distinct

Work with
\[
Q(n)=\frac1{\zeta(2)n^2},\qquad g_d(n)=\frac{n\bmod d}{d},\qquad n\ge1,
\]
and let \(H_{\rm sf}\) be the norm closure of the span of the squarefree
atoms with conductors at least two. The canonical finite projections are
\[
F_M=P_{V_M}1,\qquad F_\infty=P_{H_{\rm sf}}1,\qquad r=1-F_\infty.
\]
The repository's masked stages exhaust squarefree conductors in \(2,\ldots,M+1\).
Reindexing immediately after each nonzero atom gives the first-M-atoms convention.

Previously published: \(F_M\to F_\infty\) strongly, \(\|F_M\|_Q\le1\),
and \(F_M\to1\) is equivalent to \(1\in H_{\rm sf}\). The exact equality is
\[
\|1-F_M\|_Q^2=\|r\|_Q^2+\|F_\infty-F_M\|_Q^2.
\]
Relevant modules: `ZetaTwoOptimizerStage`, `QSquarefreeWeakCompactness`,
`QSquarefreeResidualLimit`. The precise epsilon formulation and the bound
from one finite competitor to every later optimizer were published in
commit `e27aa636b5eaa287d5fb42c0d62ad3dd1b65b270`.

The auxiliary \(G_H\) instead matches \(1\) on \(1,\ldots,H\) exactly.
It is not the canonical projection. Ordinary Mobius inversion forces its
finite atomic coefficients to satisfy
\[
c_{H,d}=-\mu(d)\quad(2\le d\le H).
\]
This exact coefficient stabilization for \(G_H\) does not establish the
corresponding limiting coefficient statement for the optimizers \(F_M\).

## 2. Norm, coordinate, and moment convergence

**Formalized:** `QHilbertConvergence`, `QProjectionMoments`, and
`QSquarefreeProjectionLimits`.
Every physical coordinate evaluation is continuous, because \(Q(n)>0\):
\[
|f(n)-g(n)|\le \sqrt{\zeta(2)}\,n\,\|f-g\|_Q.
\]
Consequently the entire sequence \(F_M(n)\) tends to \(F_\infty(n)\) at
every positive integer; no subsequence is required. The ordinary finite-set
corollary is uniform convergence on each fixed finite head. It does not
identify the limit as one.

The new actual weighted-sum statements include summability and the bounds
\[
\mathbb E_Q|f|\le\|f\|_Q,\qquad
\mathbb E_Q|f^2-g^2|\le\|f-g\|_Q(\|f\|_Q+\|g\|_Q).
\]
They yield
\[
F_M\to F_\infty\text{ in }L^1(Q),\quad
F_M^2\to F_\infty^2\text{ in }L^1(Q),
\]
and convergence of both first and second moments. The second moments of
the nested projections increase to \(\mathbb E_Q[F_\infty^2]\le1\).

## 3. A strict projection gives no moment contradiction

Here **strict projection** means \(F_\infty\ne1\), not a pointwise inequality.
Put \(\delta=\|r\|_Q^2\). **Formalized** projection-moment identities give
\[
\mathbb E_Q[F_\infty]=\mathbb E_Q[F_\infty^2]=1-\delta,
\qquad
\mathbb E_Q[r]=\mathbb E_Q[r^2]=\delta,
\]
and retain the exact centered energy
\[
\operatorname{Var}_Q(F_\infty)=\delta(1-\delta).
\]
The previously established `QParityProjectionDefect.limiting_error_lt_quarter`
gives \(\delta<1/4\). In the strict case,
\[
0<\delta<\tfrac14,\qquad
\tfrac34<\mathbb E_Q[F_\infty]<1,
\qquad \operatorname{Var}_Q(F_\infty)>0.
\]
These statements are compatible; equality of first and second moments does
not by itself imply a constant or an indicator.

**Formalized countermodel:** projection onto the one-dimensional odd-indicator
space gives \(P1=\mathbf1_{\rm odd}\ne1\), with first and second moments both
\(3/4\) and variance \(3/16\). This only refutes the proposed general Hilbert
space inference. It is not a counterexample for the full squarefree space,
and it does not satisfy that space's additional orthogonality conditions.

## 4. Pointwise order and the first coordinate

**Formalized:** `QSquarefreeProjectionSigns` and the first-coordinate bound.
Orthogonal projection is not a coordinatewise truncation into \([0,1]\).
For the actual squarefree limit,
\[
F_\infty=1\quad\text{or}\quad
\exists m,n:\ F_\infty(m)>1,\quad F_\infty(n)<1.
\]
Indeed, if \(r\) had one sign, its orthogonality to every \(g_p\), together
with \(g_p(n)>0\) for \(p>n\), would force every coordinate of \(r\) to vanish.
Thus either global pointwise inequality \(F_\infty\le1\) or
\(F_\infty\ge1\) would already settle the target membership question.

`QSquarefreeFirstCoordinate.projection_first_sq_bound` gives
\[
|F_\infty(1)-1|^2\le\frac{\zeta(2)-4/3}{16},
\]
or approximately \(0.860447\le F_\infty(1)\le1.139553\).
It does not prove \(F_\infty(1)=1\). The calculation uses the legal odd
indicator and the evaluation-at-one Riesz vector.

Ordinary numerical calculation, not a new Lean result: the projection onto
\(\operatorname{span}\{g_2,g_3\}\) has value approximately \(1.028847\) at one.
This finite-stage overshoot does not prove that the limiting projection overshoots there.

## 5. The tail criterion applies to the actual squarefree residual

**Formalized:** `QSquarefreeResidualTail`, using the general estimates in `QPhysicalTailEnergy`.
Define the complete physical tail energy
\[
T_N(r)=\sum_{n>N}Q(n)|r(n)|^2.
\]
The proof derives the result using legal squarefree exact heads at
comparable prime cutoffs. It does not silently identify a full-conductor
residual with the squarefree residual. Its conclusion is
\[
\boxed{
r=0\quad\text{or}\quad N T_N(r)\longrightarrow+\infty.
}
\]
Always \(T_N(r)\to0\), since \(r\in L^2(Q)\). In the nonzero case it is the
**scaled tail**, not the ordinary norm or unscaled tail, that diverges.
There is no contradiction: decay such as \(T_N=N^{-1/2}\) has exactly these
two behaviors.

The module also proves the precise frequent-bound criterion
\[
r=0\iff\exists C<\infty:\ N T_N(r)\le C
\text{ for arbitrarily large }N.
\]
For any physically bounded vector \(|u(n)|\le C\), the companion establishes
\[
N T_N(u)\le\frac{2C^2}{\zeta(2)}.
\]
Consequently, for this actual residual and limiting projection,
\[
r=0\iff r\text{ is physically bounded},\qquad
F_\infty=1\iff F_\infty\text{ is physically bounded}.
\]
A strict limiting projection must therefore be unbounded as a function of n,
while retaining finite \(L^2(Q)\) norm. Finite \(F_M\) are individually bounded
periodic functions, but no common bound on their amplitudes has been proved.
Norm convergence, full pointwise convergence, and convergence of moments do
not provide such a uniform amplitude bound or the required scaled-tail rate.

The ordinary comparison with a finite residual r_M makes the missing rate
explicit:
\[
N T_N(r)\le2N\|r-r_M\|_Q^2+2N T_N(r_M).
\]
For fixed M the first error is multiplied by N. Letting M depend on N can
reduce it, but the physical amplitude bound for r_M then also depends on N.
Taking these two limits without simultaneous control would discard the
substantive arithmetic obligation.

**Open arithmetic provider:** bound \(N T_N(r)\) along arbitrarily large N,
or prove the physical boundedness of the actual \(F_\infty\). Either provider
would force \(r=0\); neither is assumed to follow from projection alone.

## 6. The explicit primorial interpolants fail boundedness

Let \(L_H=\prod_{p\le H}p\), \(S_H=\sum_{d\le H}\mu(d)/d\), and, for H >= 3,
\[
G_H=-\sum_{d=2}^H\mu(d)g_d+L_H S_H g_{L_H}.
\]
**Formalized:** `QPrimorialExactHeadObstruction` proves legality, exact heads,
and the prime-jump obstruction. For \(P=L_{p-1}\) and prime p,
\[
G_p(n)-G_{p-1}(n)=-\lfloor n/p\rfloor\quad(1\le n<P),
\]
so
\[
\|G_p-G_{p-1}\|_Q^2\ge\frac{(P-p)_+}{4\zeta(2)p^2}.
\]
The primorial growth provider makes these jump norms unbounded. Thus this
family has no eventual uniform norm bound and cannot converge in Q to any
vector. Every fixed G_H still belongs to the finite legal span and to L2(Q).
This failure does not transfer to the canonical projections, whose norms are at most one.

Ordinary calculations from the discussion, not newly formalized here:
S_H tends to zero by the prime number theorem, but the separate correction
has squared norm between
\((L_H-1)S_H^2/\zeta(2)\) and \((2L_H-1)S_H^2/\zeta(2)\).
Scalar convergence alone therefore cannot discard this growing-conductor term.
For the PNT equivalence, see Terence Tao, "A remark on partial sums involving
the Mobius function" (2009), equation (3):
https://terrytao.wordpress.com/2009/08/30/an-elementary-inequality-involving-the-mobius-function/

## 7. Carries and amplitude estimates

Previously published simultaneous CRT identifies the squarefree span with
the span of prime atoms and canonical carries; it does not make that space
an algebra or a lattice. The modules `QSimultaneousCRT`, `QCRTIndicatorClosure`,
and `QCRTIndicatorProduct` record the relevant facts.

**Formalized concrete carry check:**
\[
C_{15}=2g_3+2g_5-g_{15},\qquad
C_{15}(1)=1,\ C_{15}(2)=2,\ C_{15}(15)=0.
\]
This is a legal CRT carry but not an indicator. Splitting a nonnegative carry
into level-set indicators does not prove that the individual indicators are legal.

Ordinary estimate: if an exact-head G_H has amplitude B_H, then
\[
\|1-G_H\|_Q^2\le\frac{(1+B_H)^2}{\zeta(2)H}.
\]
The denominator cannot universally be replaced by H squared, even within
the finite squarefree legal class. The discussion gave a concrete counterexample
with H=10, G=G_0+200K, where
\[
G_0=\frac{209}{210}g_{11}+g_2+g_3+g_5-g_6+g_7-g_{10},
\qquad K=g_{11}-\frac{23}{11}g_{23}.
\]
It matches the head, has amplitude below 407, and its complete error exceeds
\(194^2/(22\zeta(2))\), whereas the proposed squared-denominator bound is
less than \(408^2/(100\zeta(2))\). This particular counterexample is ordinary
analysis here, not a newly checked declaration.

## 8. Compactness and simultaneous CRT do not supply the missing rate

Previously published: every radius-r closed ball in the closed Hilbert subspace
Hsf is weakly compact (also for radius zero; negative radii give the empty set).
The subspace is infinite dimensional and proper. Its ambient norm boundary is
Hsf itself and is not compact; positive-radius intrinsic norm balls are not
norm compact. See `QSquarefreeWeakCompactness`, `QSquarefreeBoundary`, and
`QSquarefreeDimension`.

The simultaneous CRT identity is an identity of linear spans, not closure
under multiplication or indicator level sets. The ambient cylinder
h_L = 1 minus the multiple-of-L indicator has exact error L^(-2), but its
projection into Hsf converges to F_infinity; its error retains the residual
floor delta. See `QSimultaneousCRT`, `QCRTCylinderProjection`, and
`QCRTIndicatorProduct`. No inference of h_L legality is made from its small
ambient error. These facts do not supply a bounded-amplitude approximating
family or the frequent scaled-tail upper bound.

## Remaining conclusion

The actual squarefree tail analysis strengthens what a nonzero residual would
have to look like. It does not rule that case out. The remaining assertion is
still \(r=0\), equivalently \(F_\infty=1\), equivalently constant membership
in the closed squarefree span. The numerical, algebraic, and convergence
facts above must not be reported as an unconditional proof of that assertion.

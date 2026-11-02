# Legal weighted projection, exact heads, and a delayed mean repair

Christian Noack research continuation, 2 November 2026.

This note investigates replacements for ambient weighted CRT averaging. It does
not reproduce the ten completed weighted-CRT publications. Its finite-dimensional
arguments use the repository's literal zero-mean legal primitive definition.
The asymptotic RH energy provider is still open.

## 1. Spaces and the actual arithmetic metric

Write

\[
 g_d(n)=\frac{n\bmod d}{d},\quad Sg(n)=\sum_{k=1}^n g(k),\quad
 \kappa(n)=\frac{2n+1}{\zeta(2)n^3(n+1)^2}\quad(n\ge1).
\]

For a positive period L, put

\[
 V_L=\operatorname{span}\{g_d:1<d\mid L\},\qquad
 \mathcal L_L=\{(Sg(r))_{0\le r<L}:g\in V_L,\ Sg(L)=0\}.
\]

When L is squarefree all its divisor conductors are squarefree. Define

\[
 \omega_L(r)=\sum_{n\ge1,\ n\equiv r\ (L)}\kappa(n)>0,
 \quad W_L=\operatorname{diag}(\omega_L(r)),\quad
 E_L(R)=R^TW_LR.
\]

These are primitive weights, not Q(n)=1/(zeta(2)n²) itself and not Haar
weights. For a zero-mean periodic g, the existing `legalPrimitive_energy`
identifies E_L(Sg) with the complete latent-Q Cesàro energy

\[
 \mathcal E(g)=\sum_{n\ge1}\kappa(n)Sg(n)^2
 =\sum_{n\ge1}\nu_Q(n)\left(\frac{Sg(n)}n\right)^2,
 \quad \nu_Q(n)=\frac{2n+1}{\zeta(2)n(n+1)^2}.
\]

Every infinite tail remains in these definitions.

## 2. Exact finite basis and feasibility

The g_d, for 1<d|L, are linearly independent. Indeed, taking the difference
at n of an identically zero combination gives
sum_{d|L,d>1} a_d(1/d-1_{d|n})=0. At n=1 its constant term vanishes.
Evaluating successively at the divisors of L then gives each a_d=0.
Their period means are m_d=(d-1)/(2d)>0. Thus, for L>1,

\[
 \dim\mathcal L_L=\tau(L)-2.
\]

The primitive map on the zero-mean space is injective: differences recover g
at 1,...,L-1, and every divisor generator vanishes at L. Choose one divisor
d0>1. An explicit basis is formed by the primitive vectors of

\[
 g_d-\frac{m_d}{m_{d_0}}g_{d_0},\qquad d\mid L,\quad d>1,\ d\ne d_0.
\]

Let B be the matrix with these primitive columns, G=B^TW_LB, and let E_H
evaluate at residues n mod L for 1<=n<=H. Put C=E_HB. Prescribed primitive
head t is feasible exactly when t is in range(C), equivalently
rank(C)=rank([C|t]). This check is rational and independent of the weights.
For a nonzero exact constant arithmetic head, t_n=c*n. Necessarily H<L,
because every legal primitive vanishes at residue zero.

## 3. The legal orthogonal projection

For nonzero dimension G is positive definite. The actual weighted projection is

\[
 P_L=B G^{-1}B^TW_L.
\]

It is independent of the chosen basis, fixes every legal primitive, and obeys

\[
 E_L(F)=E_L(P_LF)+E_L(F-P_LF).
\]

Zero-dimensional spaces are handled by P_L=0; no empty inverse is needed.
The existence here is unconditional finite-dimensional linear algebra.

Let M|L. Denote the existing weighted average by A_{M,L}, and isometric
pullback by J_{M,L}. A valid replacement is

\[
 T_{M,L}=P_M A_{M,L}.
\]

It always returns a legal primitive. On the legal spaces it is the adjoint
of the legal isometric inclusion J_{M,L}. Consequently J_{M,L}T_{M,L}
is the orthogonal projection onto \(J_{M,L}\mathcal L_M\) and

\[
 E_L(F)=E_M(T_{M,L}F)+E_L(F-J_{M,L}T_{M,L}F).
\]

It fixes pulled-back legal vectors and satisfies the tower law
T_{K,M}T_{M,L}=T_{K,L} when K|M|L. This follows from legal nesting and
the existing adjoint/isometry identities; no independence of CRT coordinates
is invoked. It does not, in general, fix head values.

## 4. Period 6 is completely explicit

The zero-mean relation on a2*g2+a3*g3+a6*g6 is
3*a2+4*a3+5*a6=0. Taking cumulative sums gives exactly

\[
 \mathcal L_6=\{(0,a,b,a,0,0):a,b\in\mathbb R\}.
\]

Writing w_r=omega_6(r),

\[
 P_6F=(0,a,F(2),a,0,0),\qquad
 a=\frac{w_1F(1)+w_3F(3)}{w_1+w_3}.
\]

The period-6 counterexample is (0,1,-1,1,0,0), so it is fixed by P_6.
At period 2, however, V_2=span(g2), and g2 has nonzero period mean.
Therefore \(\mathcal L_2=\{0\}\). The repaired coarse adjoint T_{2,6} sends the
counterexample to zero. A nonzero first head at period 2 is infeasible.

At period 6 with c=1:

* H=1: the minimum-energy primitive is (0,1,0,1,0,0), from
  3*g2-g3-g6, with energy w1+w3.
* H=2: the unique feasible primitive is (0,1,2,1,0,0), from
  g2+3*g3-3*g6, with energy w1+4*w2+w3.
* H=3: infeasible, since R(3)=R(1), while the target would require 3=1.

Even projecting an ambient vector that already has the correct head need
not contract its energy. F=(0,1,0,0,0,0) has H=1 head and energy w1, but
every legal vector with that head has energy at least w1+w3>w1.

## 5. Exact constrained projection and its entire cost

For a feasible t, put K=C G^{-1}C^T. It is positive semidefinite and
range(K)=range(C). Write K^+ for its Moore-Penrose inverse, allowing redundant
head rows. For arbitrary F set p=P_LF, t0=E_Hp and delta=t-t0. Then

\[
 Z(\delta)=B G^{-1}C^T K^+\delta,\qquad
 R_*(F,t)=p+Z(\delta).
\]

This is the unique closest legal primitive with head t. For every feasible R,

\[
 \boxed{E_L(F-R)=E_L(F-p)+\delta^TK^+\delta+
 E_L(R-R_*(F,t)).}
\]

The correction cost is exactly delta^TK^+delta, not an omitted error term.
The output energy retains its signed cross term:

\[
 E_L(R_*)=E_L(p)+2t_0^TK^+\delta+\delta^TK^+\delta
 =E_L(p)-t_0^TK^+t_0+t^TK^+t.
\]

In particular the unique minimum-energy exact-head legal primitive is

\[
 R_{\min}(t)=B G^{-1}C^TK^+t,\qquad E_{\min}(t)=t^TK^+t,
\]

and every feasible R satisfies E_L(R)=E_min(t)+E_L(R-R_min(t)).
After retaining independent observation rows, K is positive definite and
the correction is at most ||delta||²/lambda_min(K). Uniform control of this
inverse observation Gram is an additional arithmetic estimate, not a
consequence of positivity or projection contraction.

The general exact-observation and inverse-Gram statements are already supported
by `Analysis/FiniteConstrainedProjection.lean` and
`Analysis/MultipleAffineObservationProjection.lean`; the arithmetic work here
is choosing the literal legal subspace and evaluating its actual metric.

## 6. Two useful exact comparison identities

For M|L, keep the same feasible physical head and pull back the coarse
minimizer. Legal nesting and isometry give

\[
 E_M(R_{\min,M})=E_L(R_{\min,L})+
 E_L(J_{M,L}R_{\min,M}-R_{\min,L}).
\]

Thus increasing the period along divisibility cannot increase the optimum.
Increasing the head at a fixed period has the reverse effect. If U is the
legal zero-head displacement space, u is the Riesz representative in U of
the next observation, and delta is its mismatch, the added minimum energy
is delta²/||u||². If u=0 the new observation is feasible exactly when
delta=0. These identities identify where quantitative growth enters.

## 7. A constructive mean repair with vanishing cost

For q>1 define

\[
 h_q(n)=4g_{2q}(n)-2g_q(n)
 =2\,\mathbf 1_{q\le n\bmod(2q)<2q}.
\]

Then h_q(n)=0 for n<q, 0<=h_q<=2, and its period mean is exactly 1.
For any common multiple L of 2q, Sh_q(L)=L. If q is odd and squarefree,
both conductors q and 2q are squarefree. Odd primes q may be taken arbitrarily
large and away from a fixed finite conductor set.

Let g be any finite squarefree residue combination with period N, mean m,
and prescribed arithmetic head g(n)=c for 1<=n<=H. Choose an odd prime q>H
and use a squarefree common period L=lcm(N,2q). Then

\[
 \widetilde g=g-mh_q
\]

lies in V_L, has zero period mean and exactly the same head. Hence its
primitive is legal in the precise weighted-CRT sense.

The existing Q Cesàro contraction gives the quantitative bound

\[
 \mathcal E(h_q)\le \sum_{n\ge1}Q(n)h_q(n)^2
 \le4\sum_{n\ge q}Q(n)\le\frac4{\zeta(2)(q-1)}.
\]

The last inequality is the integral comparison for the decreasing function
x^{-2}. Thus

\[
 \boxed{\sqrt{\mathcal E(\widetilde g)}\le
 \sqrt{\mathcal E(g)}+\frac{2|m|}{\sqrt{\zeta(2)(q-1)}}.}
\]

The full signed identity precedes this estimate:
\(\mathcal E(g-mh_q)=\mathcal E(g)-2m\sum_n\kappa(n)Sg(n)Sh_q(n)+m^2\mathcal E(h_q)\). All these series converge since the residue combinations
are bounded. The inequality is weighted Cauchy-Schwarz/Minkowski applied
to this identity.

For every fixed head, the infimum of complete primitive energy over finite
squarefree combinations is therefore unchanged by requiring zero period
mean. One inequality is inclusion; the reverse follows from this explicit
repair and q tending to infinity. This is an equality of infima over all
allowed periods, not an attained minimum at a fixed period. It also proves
that the period-mean functional is not continuous in the complete primitive
energy norm on the algebraic union: its value on h_q is always 1 while
the norm tends to zero.

For a varying family with means m_j, choose q_j so large that
2|m_j|/sqrt(zeta(2)(q_j-1)) <= |c_j|*epsilon_j. Then the normalized repaired
energy is at most \((\sqrt{\mathcal E(g_j)/|c_j|^2}+\epsilon_j)^2\). Consequently a
subpolynomial energy provider for unrestricted-mean exact-head squarefree
combinations transfers to legal zero-mean primitives with no new rate
assumption on m_j. The periods may grow arbitrarily; a prescribed period
schedule would require additional work. No such subpolynomial provider is
constructed in this note.

## 8. Small-period tests using actual weights

The feasibility/rank calculations use exact rational arithmetic. The listed
minima are floating-point diagnostics of the arithmetic weighted problem,
with the omitted positive residue weight bounded by 2/(3*zeta(2)*N³).
That bound controls truncation; floating-point rounding is separate.

| Period | Head | Legal dimension | Head rank | Feasible | Numerical minimum |
|---:|---:|---:|---:|:---:|---:|
| 2 | 1 | 0 | 0 | No | — |
| 6 | 1 | 2 | 1 | Yes | 0.4664546094 |
| 6 | 2 | 2 | 2 | Yes | 0.6364830303 |
| 6 | 3 | 2 | 2 | No | — |
| 10 | 2 | 2 | 2 | Yes | 0.9354507520 |
| 15 | 2 | 2 | 1 | No | — |
| 30 | 2 | 6 | 2 | Yes | 0.6311721922 |
| 30 | 4 | 6 | 3 | Yes | 0.7704340063 |
| 30 | 6 | 6 | 5 | Yes | 0.9183104368 |
| 210 | 6 | 14 | 5 | Yes | 0.8385227825 |
| 210 | 10 | 14 | 7 | Yes | 0.9268330553 |

Checks of idempotency, weighted symmetry, affine head preservation and exact
completion were also performed. The largest head residual was 1.51e-14;
projection idempotency at period 210 had residual 2.39e-10, consistent with
the greater conditioning difficulty. These diagnostics are not exact proofs.

Rank deficiency need not mean infeasibility. For example the fourth primitive
observation at period 30 is redundant for this target. Unrelated periods
need not have monotone minima; only divisibility refinements have that property.

## 9. An exact rational strict-improvement certificate

At period 30 use the explicitly feasible arithmetic combination

\[
 g=g_2+\frac{273}{80}g_3-\frac{21}{16}g_5-\frac{43}{20}g_6
 -\frac7{20}g_{10}+\frac3{20}g_{15}+\frac14g_{30}.
\]

Its mean is zero and g(1)=g(2)=1, all checked with exact rational operations.
Its complete energy obeys the rigorous enclosure

\[
 0.6311726046 < \mathcal E(g) < 0.6311726122.
\]

The unique period-6 H=2 feasible vector has

\[
 0.6364830283 < E_{\min,6}(2) < 0.6364830360.
\]

Thus the period-30 feasible trial rigorously improves the period-6 optimum,
without claiming to certify the exact period-30 minimum.

The independent Python certificate sums the exact rational unnormalized
kernel through N=600 and bounds the omitted energy by
2*max_r|R(r)|²/(3N³). It encloses zeta(2) by the positive accelerated series
sum_{k>=0} H_{k+1}/((k+1)2^k), with remainder at most 2^(1-K) after K terms.
This follows by expanding 1/(1+x)=sum_{k>=0}(1-x)^k/2^(k+1) in the
integral 2*integral_0^1(-log x)/(1+x) dx; the beta integral is
integral_0^1(1-x)^k(-log x)dx=H_{k+1}/(k+1)<=1.
`certificates.py` uses K=80 and retains exact rational endpoints.
These external computations are not Lean certificates.

## 10. Verification status

The general finite weighted projection construction passed a coherent Lean
check with exit code 0 (job `job_IOFZ-Yh647L_Mq4CJMAVP4ZbMLYTUr7A`, server
reported check duration 21.501 seconds). Its exact weighted and constrained
completion theorems were inspected with `#print axioms`, reporting only
`propext`, `Classical.choice`, and `Quot.sound`. This is an isolated
check, followed by a successful saved-module build (22 seconds). Publication
validation is recorded in the focused theorem catalog and checkpoint receipt.

The arithmetic specialization to the actual legal primitive submodule is
retained as a source candidate requiring final saved-source validation. Its
saved-module import check reached a 300-second wall timeout after the generic
module had built successfully (22 seconds). A further import request timed
out after 180.022 seconds. The final checkpoint, if successful, validates
the arithmetic module; the failed import requests supply no axiom audit. A bounded full-file check
also reached its 180.152-second wall timeout without proof diagnostics. The matrix formulas, dimension calculation,
compressed-adjoint tower, delayed mean-repair energy bound and equality of
energy infima are paper arguments unless separately identified as checked
declarations in that catalog. Arithmetic repair candidates reached wall
timeouts of 240, 600 and 180 seconds without proof diagnostics. A timeout is
not a refutation, and those candidates are not claimed as verified.

The conditional RH consumer already exists. Neither the finite numerical
tables nor the vanishing-cost mean repair supplies its missing cofinal
subpolynomial complete-energy hypothesis. RH remains unproved here.

## 11. Next research obligations

1. Use exact rational feasibility to select independent head rows and reject
   impossible period/head pairs before any optimization.
2. Track the actual inverse observation Gram in the target direction, retaining
   its signed entries and exact correction cost. Avoid a smallest-eigenvalue
   bound when the target direction admits a sharper estimate.
3. Generate legal head-null innovations from new squarefree conductors, and
   use the exact refinement gain to produce certified decreasing upper bounds
   at each fixed head.
4. Apply the delayed mean repair after constructing a low-energy raw exact-head
   family. This removes mean zero as a separate obstruction while permitting
   arbitrarily large periods.
5. Prove a quantitative cofinal energy bound for the resulting actual family.
   This remains the RH-strength arithmetic step; finite projections alone
   provide no asymptotic rate.

## Source modules reused

* `RH/QWeightedResidues.lean`: positive arithmetic weights and exact energy.
* `RH/QWeightedResidueMaps.lean`: isometry, adjoint, Pythagoras and tower.
* `RH/SquarefreeWeightedPrimitives.lean`: literal legality and legal nesting.
* `Analysis/FiniteConstrainedProjection.lean`: exact constrained Gram repair.
* `Analysis/MultipleAffineObservationProjection.lean`: affine minimization.
* `RH/QCesaroEnergy.lean`: complete Q Cesàro contraction.
* `RH/CesaroResidueMean.lean`: exact complete-period residue sums.

Source of the new application and repair construction: the user's directed
weighted-CRT continuation, 2 November 2026, and the calculations in this note.

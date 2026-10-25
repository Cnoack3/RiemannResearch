# Change of measure and the two squarefree projections

Date: 2026-10-25.

Source: the user's proposal to compare the Q and Pareto projections of one
in search of a contradiction. The generic identities are Hilbert projection
geometry. The actual squarefree rigidity result additionally uses the checked
squarefree annihilator tail theorem, including its sublinear exact-head input.

## Keep the physical dictionary fixed

For positive integers n, use

```
P(n) = 1/(n(n+1)),       Q(n) = 1/(zeta(2)n^2).
```

The physical change of realization T preserves functions, constants and atoms.
Its bounded inverse gives the same closed physical span in both measures.
Here V is the FULL squarefree closed span. The Pareto space is defined as
the closure of T(V), with an explicit equivalence of membership. It is not
silently replaced with the existing all-conductor Pareto closedSpace.

Write f_Q=P_V^Q(1), f_P=P_V^P(1), r_Q=1-f_Q, r_P=1-f_P, and d=f_Q-f_P.
Pareto functions may be represented back in Q coordinates using toQ.

## Exact comparison, with all remainders

Let kappa(f)=E_P[f(n)^2/n]. Then

```
zeta(2) ||f||_Q^2 = ||f||_P^2 + kappa(f),
||r_Q||_P^2 = ||r_P||_P^2 + ||d||_P^2,
||r_P||_Q^2 = ||r_Q||_Q^2 + ||d||_Q^2,
zeta(2) ||r_Q||_Q^2 = ||r_P||_P^2 + ||d||_P^2 + kappa(r_Q),
kappa(r_P)-kappa(r_Q) = ||d||_P^2 + zeta(2)||d||_Q^2.
```

Zero residual transfers between the two projections. A nonzero Q residual
gives the strict inequality ||r_P||_P^2 < zeta(2)||r_Q||_Q^2; the positive
remainder accounts for this difference and is not a contradiction.

With Df(n)=f(n)/n, the displacement satisfies the Pareto normal equation

```
d + P_V^P(Dd) = P_V^P(Dr_P).
```

These statements are recorded for arbitrary closed subspaces with an explicit
same-function membership equivalence in QParetoClosedProjectionComparison.

## A new rigidity criterion for the actual squarefree span

The inverse density is P/Q=zeta(2)*(1-1/(n+1)). Define Bf(n)=f(n)/(n+1).
QShiftedReciprocal proves the exact formula

```
<Tf,Tg>_P = zeta(2) * (<f,g>_Q - <f,Bg>_Q).
```

B is symmetric, positive and faithful: <u,Bu>_Q=0 implies u=0. Every Bu
is physically bounded, with |Bu(n)| <= sqrt(zeta(2))*||u||_Q.

The arithmetic tail input gives a general lemma: every physically bounded
u in V's Q orthogonal complement has <1,u>_Q=0. This does not assert u=0.

If f_Q=f_P, the common residual is orthogonal to V in both measures.
The inverse density formula then gives Br_Q in V's Q orthogonal complement.
Its physical boundedness and the tail lemma give <1,Br_Q>_Q=0. Since f_Q
is in V,

```
<r_Q,Br_Q>_Q = <1,Br_Q>_Q - <f_Q,Br_Q>_Q = 0.
```

Faithfulness forces r_Q=0. Conversely r_Q=0 puts one in V, so both projections
are one. QSquarefreeMeasureRigidity therefore proves

```
f_Q=f_P  iff  r_Q=0  iff  1 belongs to V.
Br_Q is Q-orthogonal to V  iff  r_Q=0.
```

In particular, a strict squarefree projection necessarily changes when the
measure changes. This criterion depends on the full squarefree dictionary;
it is not a general theorem about projections onto arbitrary smaller spaces.

## What convergence does and does not transfer

The existing Q finite-stage optimizers converge to f_Q in Q norm. Bounded
change of measure makes the SAME sequence converge to T f_Q in Pareto norm.
It does not make this sequence the Pareto finite-stage optimizer sequence.

QSquarefreeMeasureRigidity also records that this transferred sequence
converges to the Pareto squarefree projection if and only if r_Q=0. This uses
uniqueness of limits and the rigidity criterion, with no extra arithmetic
assumption.

## Status

Established: exact projection comparisons and normal equation, faithful
shifted correction, bounded-annihilator mean-zero consequence, and the actual
squarefree projection-agreement criterion.

Open: prove agreement of the projections, or equivalently establish the extra
Pareto orthogonality of the Q residual. Neither equivalent norms, convergence
transfer, nor the separate first/second-moment projection identities supplies
this step. No contradiction from a nonzero residual, proof of target membership,
or counterexample to target membership is claimed.

## Continuation: bounded displacement is enough

The original agreement premise can be replaced by physical boundedness.
All quantities below use the full squarefree space V, with Pareto functions
represented in Q coordinates. Let

```
r = r_Q,   d = f_Q - f_P,   r_P = r + d,
u = B r_P - d.
```

The Pareto normal equations and inverse-density identity give u in V-perp.
Since d belongs to V and r is Q-orthogonal to V, exact expansion gives

```
zeta(2) <1,u>_Q
  = zeta(2) <r,B r>_Q + ||T d||_P^2.
```

This retains both nonnegative terms. If d is physically bounded, then u is
bounded because B r_P is always bounded. The checked squarefree
bounded-annihilator theorem gives <1,u>_Q=0, forcing <r,B r>_Q=0. Faithfulness
of B then gives r=0. Conversely r=0 makes both projections equal to 1.

Thus the following statements are equivalent, without an RH assumption:

```
d is physically bounded
  iff d = 0
  iff r_Q = 0
  iff 1 belongs to the squarefree closed span.
```

The boundedness implication to Mathlib's RiemannHypothesis is assembled
through the existing checked squarefree-capacity bridge. It is a
**conditional research reduction**: no provider of boundedness is proved.

Lean module: QSquarefreeDisplacementRigidity.lean.
Key declarations: witness_mean_energy,
residual_eq_zero_iff_displacement_physically_bounded,
riemannHypothesis_of_displacement_bounded.

## Continuation: divergent tails in the displacement

The arithmetic tail theorem applies to every squarefree Q-annihilator with
nonzero mean. If r is nonzero, the exact identity above makes the mean of u
nonzero, so

```
N ||tail_N u||_Q^2 -> infinity.
```

A bounded physical function has bounded scaled Q tails, and B r_P is
physically bounded. Therefore

```
r != 0  ==>  N ||tail_N d||_Q^2 -> infinity.
```

The general perturbation module first preserves the signed equality

```
||tail_N(f-g)||^2 =
  ||tail_N f||^2 + ||tail_N g||^2 - 2 <tail_N f,tail_N g>,
```

then uses the triangle bound only to transfer divergence. Consequently,

```
r = 0  iff  there exist C and arbitrarily large N with
              N ||tail_N d||_Q^2 <= C.
```

Here tail_N contains every physical site n>N; its energy is the complete
weighted infinite sum. Ordinary unscaled tail decay does not give this bound.

Lean modules: QScaledTailPerturbation.lean and
QSquarefreeDisplacementRigidity.lean.
Key declarations: tail_sub_energy_exact, scaled_tail_transfer_sub,
displacement_scaled_tail_tendsto,
residual_zero_iff_frequently_bounded_displacement_tail,
riemannHypothesis_of_frequently_bounded_displacement_tail.

## Continuation: a single projected smooth test

There is a second regularity criterion using only Q projections. Define

```
b = P_V^Q(B r),    w = B r - b.
```

Then w belongs to V-perp and

```
<1,w>_Q = <r,B r>_Q.
```

The same bounded-annihilator argument proves

```
b is physically bounded  iff  r=0.
r != 0  ==>  N ||tail_N b||_Q^2 -> infinity.
```

In particular, it is not necessary to assume b=0 in advance.
A bounded scaled tail along an unbounded subsequence also suffices.

Lean module: QSquarefreeSmoothedProjection.lean.
Key declarations: screened_mean_eq_energy,
correction_bounded_iff_residual_zero, correction_scaled_tail_tendsto,
residual_zero_iff_correction_frequently_bounded_scaled_tail.

## A finite, explicit sufficient estimate

Let V_N be the repository's masked squarefree stage, F_N=P_{V_N}^Q 1,
and define the finite moving correction

```
b_N = P_{V_N}^Q B(1-F_N).
```

It is computable from two finite normal-equation systems, using the complete
Q inner product throughout. The new module proves b_N -> b in Q norm, hence
at every fixed physical site. More precisely, with
c_N=P_{V_N}^Q B r,

```
||b_N-b||_Q <= ||(1-F_N)-r||_Q + ||c_N-b||_Q.
```

It is enough to establish one constant C>=0 such that

```
for every N and every 1 <= n <= N,  |b_N(n)| <= C.
```

This is a bound on an expanding finite head, not on an entire CRT period.
For each fixed n the hypothesis holds eventually, so passage to the
pointwise limit gives |b(n)|<=C. The bounded-correction criterion then gives
r=0 and Mathlib's RH.

The checked declaration is
QSquarefreeSmoothedProjection.riemannHypothesis_of_moving_head_bound.
Its displayed head-bound hypothesis remains **Open**.

For concrete arithmetic work, choose the stage atoms a_i, and write
F_N=sum_i c_i a_i and b_N=sum_i alpha_i a_i. Set

```
G_ji = <a_j,a_i>_Q,         m_j = <a_j,1>_Q,
H_ji = <a_j,B a_i>_Q,       h_j = <a_j,B 1>_Q.
```

The exact systems are

```
G c = m,     G alpha = h - H c.
```

Use solvable normal equations for the masked dictionary, which includes
zero/redundant coordinates. Do not silently use a totalized matrix inverse
as if the masked Gram matrix were invertible. The signed difference
h-Hc is the quantity whose arithmetic cancellation must be estimated.
These matrix displays are explanatory derivations; the new Lean
finite-stage theorem is stated directly using orthogonal projections.

## A checked obstruction to multiplier invariance

Every member of V satisfies

```
F(1)-F(2)-F(3)+F(4)=0.
```

But the same functional applied to B g_2 is exactly 1/8. Hence

```
B g_2 is not in V, and B(V) is not contained in V.
```

This is compatible with 1 belonging to V. It rules out a general
multiplier-invariance shortcut; it does not refute squarefree target closure.
Wolfram independently returned 1/8 for this elementary diagnostic, and the
exact statement is also checked in Lean.

Lean module: QSquarefreeReciprocalObstruction.lean.
Key declarations: fourSiteFunctional_B_qResidue_two,
B_qResidue_two_not_mem, B_not_preserves_closure.

## Why compactness alone still leaves an arithmetic obligation

As an informal comparison model, in the same L2(Q) space take
v(n)=log(n+1) and U=v-perp. Its annihilator is the line spanned by the
unbounded v, so every bounded annihilator has mean zero. The same B is
positive, faithful, compact, and physically smoothing. Nevertheless the
projection residual of 1 onto U is nonzero.

There are exact-head elements in U: with
a=<1,v>_Q and v_H=1_{n>H}v, set
F_H=1-a v_H/||v_H||_Q^2. Then F_H belongs to U and equals 1 on n<=H,
while its error is a^2/||v_H||_Q^2, of order H/(log H)^2.
Thus even sublinear exact-head energy and the bounded-annihilator
consequence do not, as abstract hypotheses, force zero residual.
This model is not a claim about the actual squarefree span, and this
illustrative comparison has not been formalized in this continuation.

## Focused next work and status

1. **Open:** prove the expanding-head bound for b_N, retaining h-Hc.
   This is the most concrete new finite sufficient condition.
2. **Open:** prove physical boundedness of the actual displacement d, or the
   weaker cofinal bound on N||tail_N d||^2.
3. **Open:** derive estimates for projected reciprocal kernels. Hilbert
   contraction and compactness supply Q-norm estimates, not uniform physical
   coordinate estimates.
4. **Ruled out:** invariance of the whole squarefree span under B.
5. **Established implications:** each of the regularity premises above forces
   zero residual; the explicit RH corollaries use the repository's existing
   squarefree closure-to-RH bridge.

No boundedness provider, unconditional zero-residual theorem, or proof of RH
has been obtained. No all-conductor density or invariance theorem has been
silently transferred to the squarefree space.

External context checked: B. Bagchi, *On Nyman, Beurling and Baez-Duarte's
Hilbert space reformulation of the Riemann hypothesis*, Remarks 4 and 8,
https://arxiv.org/abs/math/0607733 . These identify the squarefree closure
criterion and the equivalence of comparable inverse-square weights; they
do not supply the new regularity bounds. See also Alouges, Darses and Hillion,
*Polynomial approximations in a generalized Nyman-Beurling criterion*,
https://arxiv.org/abs/2006.02953 , for the distinction between constructing
approximants and controlling their coefficients/Gram systems.

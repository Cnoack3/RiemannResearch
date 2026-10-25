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

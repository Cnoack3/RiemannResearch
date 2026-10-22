# Independent squarefree heads and the complete-Q reduced Gram

22 October 2026. Continuation of commit
`ee5413b8f7bcc200a6af27d5746c1f84f7af75f6`; development workspace started at
`7e35bec12ee8814963f1f4543c2f56840dc03ee5`.

## Verification evidence

The final saved modules and seven central axiom audits passed server job
`job_EPVfXQaAuE2MuDqWx6kNbNclb7UJ5TA1`: exit code 0, verified=true.
The job built the three new modules, the extended finite repair module, and
the affected head-repair import. All audited declarations used only
`propext`, `Classical.choice`, and `Quot.sound`. The RH consumer still has
the explicitly stated uniform-cost hypothesis.

The server reported 264.880 seconds for this module-validation job, including
its import builds; this is not a kernel-only timing. Queue start followed
submission by less than 0.001 seconds. Workspace-opening wall time and
polling latency were not measured separately. The final publication is gated
by the separate checkpoint validation of the complete unpublished delta.

## Result and scope

For M >= 1 let S_M be the squarefree integers in [1,M]. In any squarefree
residue dictionary containing all squarefree d in [2,M] and one conductor
r > M, the physical head map has rank exactly |S_M|. The independent
observations are F(1) and F(s)-F(1) for s in S_M other than 1. They encode
exactly the same feasible heads as all M physical observations. The complete
projected Gram of these compressed rows is invertible.

The original memorandum wrote **discrete jumps** Delta F(s)-F(1), whereas
the follow-up request wrote **value differences** F(s)-F(1). This development
formalizes the requested value differences. It reuses the already verified
radical-jump identities to prove reconstruction, rather than treating the
two formulas as identical.

Compression changes coordinates, not the exact constrained minimum. It
removes singular normal equations and exposes the correct weighted head
metric. It does not supply a uniform arithmetic bound or prove RH.

## Formalization map

- `RH/QSquarefreeHeadCompression.lean`: `head_eq_of_squarefree_eq`,
  `observations_iff_head`, `interpolate_squarefree`, `interpolate_observations`,
  `projected_observations_independent`, `observation_kernels`, `physical_rank`,
  and `exists_physical_reconstruction`.
- `RH/QSquarefreeReducedGram.lean`: reduced complete-Gram entries, literal
  exact physical heads, exact constrained completion, signed correction
  identity, infinite-tail identity, transported physical head energy, and
  a conditional RH consumer reusing the existing bounded-exact-head theorem.
- `RH/QSquarefreeHeadCompressionExamples.lean`: the rational 3-by-3
  determinant, exact four- and six-site heads, and actual four-site rank.
- `Analysis/FiniteFeasibleGramRepair.lean`: the normal-solution probe bound
  and its target-direction Rayleigh-quotient specialization.

The exact declaration hypotheses matter: no uniform arithmetic estimate is
hidden in a rank or independence premise. The concrete dictionary theorem
supplies the independence premise used by the reduced Gram assembly.

## Arithmetic reconstruction and rank

Write g_d(n)=(n mod d)/d, F=sum_d a_d g_d, and c=F(1). Then

    F(n) = n c - sum_{2 <= d <= n, d squarefree} a_d floor(n/d).

On squarefree sites the floor-incidence block is lower triangular with
unit diagonal. In the Lean proof the same triangular elimination is realized
by existing compensated directions

    v_{d,r} = g_d - (r/d) g_r.

For n < d < r, v_{d,r}(n)=0, while v_{d,r}(d)=-1. Site one is handled by
g_1=0, so v_{1,r}=-r g_r. Successively adjusting only squarefree sites
interpolates arbitrary squarefree values in the specified dictionary.

The existing exact identity Delta F(n)=Delta F(rad(n)) supplies the other
half. If n is nonsquarefree, rad(n)<n. Strong induction therefore recovers
F(n) from earlier values. This applies to every radical-compatible Hilbert
vector, including legal vectors and the constant target. The formalization
proves equality of observation kernels and uses finite-dimensional
rank-nullity to obtain the exact rank; it does not assume that rank.

The constant head becomes t=(1,0,...,0). As in the existing exact-head modules,
it forces a_d=-mu(d) for every low squarefree conductor 2 <= d <= M; the
remaining high conductors supply the reciprocal normalization. These prior
coefficient results are reused conceptually, not re-proved as new results.

## Reduced complete-Q system

Fix a legal dictionary v_d=g_d. All matrices below use the complete law
Q(n)=1/(zeta(2)n^2), n>=1. Let o_i be the Riesz vectors of the compressed
observations, and put

    G_de = <v_d,v_e>_Q,
    A_id = <o_i,v_d>_Q,
    b_d  = <v_d,1>_Q,
    W    = A G^{-1} A^T,
    c0   = G^{-1} b,
    r    = t - A c0,
    delta = 1 - b^T G^{-1} b.

The independence theorem proves G and W invertible for the specified
squarefree dictionaries. The matrices A are rational; G and b generally
are not rational. In particular, replacing G by a finite head sum is not
an exact arithmetic computation of the complete problem.

The optimizer and its cost are

    c* = c0 + G^{-1} A^T W^{-1} r,
    C  = r^T W^{-1} r,
    ||1-F*||_Q^2 = delta + C.

For every feasible coefficient vector c,

    ||1-F_c||_Q^2 = delta + C + ||F_c-F*||_Q^2.

The formal `reduced_complete_tail_identity` identifies this same value with

    delta + C = sum_{n>M} (1-F*(n))^2 / (zeta(2)n^2).

No infinite-tail contribution has been omitted. For an arbitrary correction
U to a baseline P, before invoking any normal equations, the exact identity
is

    ||1-(P+U)||_Q^2
      = ||1-P||_Q^2 - 2<1-P,U>_Q + ||U||_Q^2.

The signed cross term is retained in `signed_correction_tail`. It vanishes
for the actual complete-Q projection baseline and a legal correction by
orthogonality, not by an independence assumption or an absolute-value bound.
For a split source r=r1+r2 the inverse quadratic similarly retains
r1^T W^{-1} r1 + 2 r1^T W^{-1} r2 + r2^T W^{-1} r2.

## The physical weights survive compression

The reconstruction theorem supplies a matrix R with physical head Rz for
compressed coordinates z. Thus the correct compressed head metric is

    J = R^T diag(Q(1),...,Q(M)) R,
    sum_{n<=M} Q(n) F(n)^2 = z^T J z.

`headEnergy_reconstructed` formalizes this equality in finite-sum form.
Using only weights at squarefree sites would discard positive terms.

For M=4, z=(F(1), F(2)-F(1), F(3)-F(1)), and

    Rz = (z1, z1+z2, z1+z3, z1+z2+z3),
    J = (1/(144*zeta(2))) * [[205,45,25],[45,45,9],[25,9,25]].

Ordinary finite-dimensional spectral translation: the nonzero eigenvalues
of the weighted physical projected Gram are the eigenvalues of
W^(1/2) J W^(1/2). Consequently a correct compression preserves the weighted
frame constant. This spectral matrix identification is explanatory ordinary
linear algebra, not a separately checked eigenvalue declaration here.
The Lean statement keeps the equivalent exact physical quadratic form.

The proved identity

    headEnergy(M+1,F) = headEnergy(M,F) + Q(M+1) F(M+1)^2

shows that a redundant nonsquarefree row can improve a frame estimate without
adding any feasible constraint. For a fixed dictionary and unchanged row
span, the smallest positive weighted eigenvalue cannot decrease when that
positive term is added. The displayed eigenvalue consequence is an ordinary
finite-dimensional inference from the exact form identity.

## A target-direction estimate

Let d solve the actual observation normal equations, U=sum_i d_i P_V o_i,
Vprobe=sum_i d_i o_i, E=||U||^2, and delta=||1-P_V1||^2. The existing
complementary covariance inequality gives the unconditional scalar inequality

    E^2 <= delta * (||Vprobe||^2-E).

The added theorem proves: if K>=1 and ||Vprobe||^2<=K E, then

    E <= delta (K-1).

When E>0 it also proves the actual-direction Rayleigh bound

    E <= delta * (||Vprobe||^2/E - 1).

This tests only the actual repair direction. A uniform smallest-eigenvalue
bound would control all directions and can be substantially stronger than
what is needed. The estimate does not assert that this Rayleigh quotient,
or its product with delta, is uniformly bounded. Choosing a different
representative of dependent physical observation multipliers can change the
unprojected probe norm; that choice must be retained in any comparison.

## Small exact and numerical examples

For the dictionary {2,3,5}, the compressed observation matrix is

    A = [[1/2,1/3,1/5],[-1/2,1/3,1/5],[0,-1/3,2/5]],  det(A)=1/5.

Lean verifies this determinant, actual physical rank 3 at M=4, and the exact
head of F=g2+g3+(5/6)g5 through site 4. It also verifies
F=g2+g3+g5-g6+(14/15)g7 through site 6. These coefficients are unique in
these minimal dictionaries, so the displayed feasible vectors are the
constrained optimizers there.

For a common period L, the complete residue-class weight is exactly

    w_k = (1/zeta(2)) sum_{j>=0} 1/(k+jL)^2
        = trigamma(k/L)/(zeta(2)L^2),  1<=k<=L.

The positive representative k=L is retained. The reproducible Python
experiment uses exact Fraction arithmetic and the elementary integral bounds
for a decreasing tail:

    S_K + 1/(L(k+KL)) <= sum_{j>=0} 1/(k+jL)^2
      <= S_K + 1/(L(k+KL)) + 1/(k+KL)^2.

It bounds zeta(2) by the same construction and divides positive intervals.
These are exact-rational computations with an explicit infinite-tail bound;
the decimal endpoints below are not newly asserted Lean theorems.

| Head | Dictionary | Complete squared error interval |
|---|---|---|
| 2 | 2,3 | [0.0706635, 0.0706654] |
| 4 | 2,3,5 | [0.0277012, 0.0277016] |
| 6 | 2,3,5,6,7 | [0.0230894, 0.0230895] |

The separate floating-point experiment evaluates the complete periodic
trigamma formula. Values below are exploratory, not certified eigenvalue
bounds or Lean assertions.

| M | Dictionary | delta | Repair C | Complete error | Weighted lambda+ |
|---|---|---:|---:|---:|---:|
| 3 | 2,3,5 | .02723690 | .00046452 | .02770142 | .37272604 |
| 4 | 2,3,5 | .02723690 | .00046452 | .02770142 | .65936261 |
| 4 | 2,3,5,6,7 | .01725797 | .00037691 | .01763488 | .78655573 |
| 6 | 2,3,5,6,7 | .01725797 | .00583150 | .02308947 | .47478351 |
| 6 | 2,3,5,6,7,10,11,13 | .01401690 | .00408156 | .01809846 | .49880815 |

For the fixed {2,3,5} dictionary the fourth site leaves the optimum unchanged
and strengthens the weighted frame. Enlarging the dictionary lowers the
complete constrained minimum in these examples, as the existing general
monotonicity theorem predicts. These few small examples establish no
asymptotic trend or uniform bound.

## Precise remaining RH estimate

Choose finite legal dictionaries satisfying the concrete inclusion conditions
at each M, and form their complete matrices G_M,A_M,W_M. The sufficient
remaining arithmetic estimate is

    sup_M r_M^T W_M^{-1} r_M < infinity.

Equivalently, for some B>=0 independent of M,

    (y^T r_M)^2 <= B y^T W_M y     for all M and all reduced y.

Since 0<=delta_M<=1, this yields uniformly bounded complete-error exact-head
vectors. The existing bounded-exact-head closure theorem then gives
squarefree closure, capacity divergence, and RH. The new consumer is
`closure_capacity_rh_of_uniform_reduced_cost`. It is explicitly a conditional
research reduction; the uniform provider remains Open.

A sufficient alternative is a uniform bound on
`delta_M*(K_M-1)` for actual normal-solution probe comparisons. A uniform
positive weighted frame constant also suffices, but controls more than the
target direction. Compression itself proves none of these estimates.

Next research tasks: preserve the full transported metric J_M; exploit the
forced low Mobius coefficients while optimizing all high conductor directions;
seek a signed estimate in the actual inverse-normal direction; and certify
larger periodic examples before inferring any conditioning law. Keep the
complete Gram and all signed cross terms throughout.

## Reproducible experiment

The following script runs the exact rational enclosures with the Python standard
library. Pass `--spectra` with NumPy and SciPy installed for the separately labeled
floating-point experiment. Both modes were run during this continuation.

```python
#!/usr/bin/env python3
"""Reproduce the 2026-10-22 squarefree-head examples.

Default: exact Fraction enclosures including infinite tails (stdlib only).
--spectra: additionally evaluate complete periodic Grams with NumPy/SciPy;
these floating-point outputs are exploratory, not certified eigenvalues.
"""
from fractions import Fraction as F
from math import lcm

# Pure rational bounds. For f decreasing, integral(K,infinity) <=
# sum_{j=K}^infinity f(j) <= f(K)+integral(K,infinity).
def progression(k,L,K):
    p=sum((F(1,(k+j*L)**2) for j in range(K)),F(0))
    x=k+K*L
    return p+F(1,L*x),p+F(1,L*x)+F(1,x*x)
def bound(D,c,K=128):
    L=lcm(*D);lo=hi=F(0)
    for k in range(1,L+1):
        residual=1-sum((a*F(k%d,d) for d,a in zip(D,c)),F(0))
        a,b=progression(k,L,K)
        lo+=residual**2*a;hi+=residual**2*b
    zl,zu=progression(1,1,1024)
    lower,upper=lo/zu,hi/zl
    scale=10**7
    lb=(lower.numerator*scale)//lower.denominator
    ub=-((-upper.numerator*scale)//upper.denominator)
    assert F(lb,scale)<=lower<=upper<=F(ub,scale)
    print(D,list(map(str,c)),f'{lb}/{scale} <= error <= {ub}/{scale}')

def sf(n):return all(n%(p*p) for p in range(2,isqrt(n)+1))
def rank(A):
    A=[r[:] for r in A]; i=0
    for j in range(len(A[0])):
        k=next((k for k in range(i,len(A)) if A[k][j]),None)
        if k is None:continue
        A[i],A[k]=A[k],A[i]; v=A[i][j]; A[i]=[x/v for x in A[i]]
        for k in range(len(A)):
            if k!=i:
                v=A[k][j]; A[k]=[x-v*y for x,y in zip(A[k],A[i])]
        i+=1
        if i==len(A):break
    return i

def calc(M,D):
    sites=[n for n in range(1,M+1) if sf(n)]
    C=[[F(n%d,d) for d in D] for n in range(1,M+1)]
    A=[[F(1,d) if n==1 else F(n%d,d)-F(1,d) for d in D] for n in sites]
    L=lcm(*D); k=np.arange(1,L+1,dtype=float); z=np.pi**2/6
    w=polygamma(1,k/L)/(L*L*z)
    atoms=np.array([[(int(n)%d)/d for d in D] for n in k])
    G=atoms.T@(w[:,None]*atoms); b=atoms.T@w
    a=np.array(A,dtype=float); c=np.array(C,dtype=float)
    W=a@np.linalg.solve(G,a.T); t=np.zeros(len(sites));t[0]=1
    c0=np.linalg.solve(G,b); r=t-a@c0
    coeff=c0+np.linalg.solve(G,a.T)@np.linalg.solve(W,r)
    delta=1-b@c0; cost=r@np.linalg.solve(W,r)
    q=1/(np.sqrt(z)*np.arange(1,M+1))
    ev=np.linalg.eigvalsh(q[:,None]*(c@np.linalg.solve(G,c.T))*q[None,:])
    lam=min(ev[ev>1e-9])
    print({'M':M,'D':D,'sites':sites,'rank':rank(C),'A':[[str(v) for v in row] for row in A],
       'delta':float(delta),'repair':float(cost),'error':float(delta+cost),
       'lambda_plus':float(lam),'spectral_bound':float(delta*(1/lam-1)),
       'coeff':coeff.tolist()})

if __name__ == '__main__':
    import sys
    bound([2,3],[F(1),F(3,2)])
    bound([2,3,5],[F(1),F(1),F(5,6)])
    bound([2,3,5,6,7],[F(1),F(1),F(1),F(-1),F(14,15)])
    if '--spectra' in sys.argv:
        from math import isqrt
        import numpy as np
        from scipy.special import polygamma
        for M,D in [(1,[2]),(2,[2,3]),(3,[2,3,5]),(4,[2,3,5]),
                    (4,[2,3,5,6,7]),(5,[2,3,5,7]),(6,[2,3,5,6,7]),
                    (6,[2,3,5,6,7,10,11,13])]:
            calc(M,D)
```

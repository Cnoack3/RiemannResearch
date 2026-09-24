# Trigamma mean points, stable midpoint inverses, and signed arithmetic

Date: 2026-09-21. Task: add the trigamma/DPP discussion to RiemannResearch
and investigate saturation. Verification status is recorded in the theorem
catalog and final checkpoint; the mathematical research below does not claim RH.

## Exact normalization

Let g_d(n)=(n mod d)/d, w_n=1/[n(n+1)], S_N=span(g_2,...,g_{N+1}),
and choose one common conductor L divisible by every generator conductor.
The exact class weight is

W_L(r)=sum_{k>=0} 1/[(r+kL)(r+kL+1)]
      =[psi((r+1)/L)-psi(r/L)]/L.

For the actual digamma derivative f=psi_1, there is one and only one
alpha_{r,L} in (r/L,(r+1)/L) with W_L(r)=f(alpha_{r,L})/L^2.
The reciprocal-product series for the secant slope proves alpha increases
strictly with r and decreases strictly with L. It also proves

sqrt(r(r+1))/L < alpha_{r,L} < (r+1/2)/L.

The quantitative bound proved by `progressionAlpha_scaled_sq_error` is

0 <= (L alpha_{r,L})^2-r(r+1)
  <= psi_1(1) r(r+1)^3/L^2.

Thus L alpha_{r,L}->sqrt(r(r+1)) for fixed r. Residues varying with L do
not satisfy the fixed-r limit: if r/L->x>0 then alpha_{r,L}->x.

## Stronger scaled monotonicity: mathematical proof, formalization pending

The claim L alpha_{r,L} strictly decreases in L uses more than the sign
of the first derivative. Put h_L(x)=L^-2 psi_1(x/L). Its Laplace formula is

h_L(x)=integral_0^infinity t exp(-xt)/(1-exp(-Lt)) dt.

The curvature h_L''/(-h_L') is the mean of t under density proportional to
t^2 exp(-xt)/(1-exp(-Lt)). For L2>L1 the likelihood ratio
(1-exp(-L1 t))/(1-exp(-L2 t)) increases strictly with t. Hence that
curvature increases with L. The composition h_L2 o h_L1^{-1} is strictly
convex. Jensen, followed by the decreasing inverse, shows that its
quasi-arithmetic mean of Uniform[r,r+1] strictly decreases in L.
The limits at infinity and zero are respectively sqrt(r(r+1)) and
1/log(1+1/r). This proof is recorded for continuation, not disguised as a
checked provider or used as a hypothesis in the new verified reductions.

## What survives growing matrices

The pole-removed midpoint weight is

M_L(r)=w_r+L^-2 psi_1(1+(r+1/2)/L).

The project already proves its exact positive error, bounded above by
pi^4/(360 L^4). Its existing relative bound is stronger for our use:

(1-delta_L) W_L(r) <= M_L(r) <= W_L(r),
delta_L=1/(2L+3)^2, r>=1.

For a finite feature matrix A, the weighted Grams therefore satisfy
(1-delta_L) G <= M <= G as quadratic forms. Positive definiteness of G
implies that of M. Actual inverse forms satisfy

(1-delta_L) b^T M^-1 b <= b^T G^-1 b <= b^T M^-1 b.

For a retained row a_r, both w_r a_r^T G^-1 a_r and its midpoint analogue
are in [0,1]. Combining the row-weight and inverse comparisons gives an
absolute occupation error <=delta_L, uniformly in coefficient growth,
dimension, and condition number. The checked theorem
`progressionMidpoint_occupation_tendsto_iff` transfers every real limit
when L tends to infinity; limit one gives the saturation equivalence.

This is a finite weighted-Gram theorem, with ordinary positive definiteness
explicit. Arithmetic residue-Gram positivity and the exact CRT regrouping
are existing project results. No saturation or capacity divergence is a
consequence of these comparison bounds alone.

## Research attempt: target the monotone physical-site energy

For normalized F in S_N, define U_N=minimum sum_{n>=2} w_n F(n)^2.
The actual integer-site probability is p_N=(1/2)/(1/2+U_N), whereas the
class probability q_N=2W_L(1)p_N need not be monotone. Nested S_N make U_N
decrease. The capacity 1/(2U_N) is the divergent quantity, not q_N.
The midpoint probabilities lie in [0,1] as well.

The new three-site obstruction proves signed coefficients are essential.
Every d>=2 satisfies g_d(2)+2g_d(3)>=2g_d(1). Thus c_d>=0 and F(1)=1 imply

F(2)+2F(3)>=2,
F(2)^2/6+F(3)^2/12 >= (F(2)+2F(3))^2/54 >=2/27.

Every such trial has U>=2/27, occupation surrogate <=27/31, and
normalized capacity <=27/4. This does not restrict unrestricted signed
inverse-Gram coefficients; it excludes a positive-mixture shortcut.

An additional informal example: the dyadic generator family g_{2^j}
has a nonzero orthogonal vector supported on {1,2,3}, with values 2,6,-12.
Its squared weighted norm is 20 and its inner product with the point
indicator at 1 is 1. Thus even this increasing infinite-rank family has
normalized first-site vacancy at least 1/10. Increasing rank/conductor
and completely monotone weights cannot alone prove saturation.

## A concrete signed candidate and its unresolved first block

Write b_d=mu(d)-1_{2 divides d} mu(d/2), A_M=sum_{d<=M} b_d/d,
and B(x)=sum_{d<=x} b_d=Mertens(x)-Mertens(floor(x/2)). The unique trial
from g_2,...,g_{M+1} with F_M(n)=1_{n=1} for 1<=n<=M is

F_M=-sum_{d=2}^M b_d g_d + (M+1)A_M g_{M+1}.

Möbius inversion and the reciprocal normalization prove the exact identity

F_M(n)=sum_{d<=M} b_d floor(n/d)
       -(M+1)A_M floor(n/(M+1)).

For M+1<=n<=2M+1 this becomes

F_M(n)=B(M)-B(n)-(M+1)A_M.

A sufficient route is sum_{n>M} w_n F_M(n)^2->0. Its first necessary test
is mean-square vanishing of the displayed expression on the block
[M+1,2M+1]. Neither test is proved here. The identities in this section
are mathematical research notes, not new Lean declarations.

Sources: user-provided discussion; NIST DLMF 5.15.1 and 5.15.5 for the
special-function series/recurrence, https://dlmf.nist.gov/5.15. The project
provides the actual derivative and arithmetic progression identifications.

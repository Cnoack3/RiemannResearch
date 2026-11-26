# Signed character cross certificate (2026-11-26)

## Exact target

Put
[
T_{23}=log 2+rac{log 3}{2}-rac{pi}{3sqrt3}-(log2)(log3).
]
The existing theorem `riemannHypothesis_of_two_three_projected_covariance`
proves the standard `RiemannHypothesis` predicate from
[
T_{23}le langle P_MJ_2,P_MJ_3angle_P.
]

## New unconditional reduction

For a finite set (s) of mixed conductors, define
[
X_a(s)=sum_{qin s}c_q(a)e_q,qquad
C_s(2,3)=sum_{qin s}c_q(2)c_q(3),
]
where (e_q) is the orthonormal mixed-conductor basis and the coefficients
(c_q(a)) are computed from the character Gram recurrence
(`characterRow`). The following identities are now Lean-checked:

[
langle P_MJ_2,P_MJ_3angle_P
 = C_s(2,3)+
 langle P_MJ_2-X_2(s),P_MJ_3-X_3(s)angle_P,
]
[
|P_MJ_a-X_a(s)|_P^2
 =|P_MJ_a|_P^2-sum_{qin s}c_q(a)^2.
]

Consequently, the new theorem
`riemannHypothesis_of_character_cross_certificate` proves RH from the
single finite inequality
[
T_{23}
+|P_MJ_2-X_2(s)|_P,|P_MJ_3-X_3(s)|_P
le C_s(2,3).
]
This is Cauchy--Schwarz applied only to the exact residual, so no signed
character mode is discarded.

## Numerical diagnostic, not a proof

A high-precision external calculation of the same Cholesky recurrence over all
mixed conductors through 180 (124 modes) gave
[
C_s(2,3)approx-0.12392098427701582,qquad
T_{23}approx-0.12364647360288139.
]
After subtracting the rigorous-form Cauchy tail allowance, the resulting lower
envelope was approximately
[
-0.16809415697404553,
]
which misses (T_{23}) by approximately (0.04444768337116414).

Thus the finite cross sum itself is already very close to the target, but that
observation cannot prove RH: the unresolved signed residual is still too large
for the unconditional norm-only estimate. The first character mode is also not
decisive. It contributes positively to the cross pairing, whereas the complete
target is negative.

## Exact remaining hypotheses

Either of the following would close this route:

1. Exhibit one finite (s) satisfying the Lean theorem's displayed Cauchy
   certificate.
2. Prove a sharper lower bound on the residual cross term than the product of
   the two residual norms.
3. Prove directly that the full signed series
   (sum_q c_q(2)c_q(3)) is at least (T_{23}).

The original mean-ladder alternative remains valid: one uniform constant (C)
such that for every (K) some (Nge K) obeys (U_N(k)ge C) for every
(1le kle K). The known negative value at (N=11,k=9856) rules out replacing
this cofinal statement by naive global positivity.

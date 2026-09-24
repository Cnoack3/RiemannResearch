# Second-moment RH attempt: quantitative first window and exact primitive energy

Date: 2026-09-24. Starting commit: 8112aaa91e270b71c5a290cc7eb388188a805ca9.
No unconditional proof of RH was obtained.

## Stronger unconditional arithmetic estimate

Write
m_N=sum_{d<=N}mu(d)/d,
M(k)=sum_{d<=k}mu(d),
U_N(k)=1+sum_{d<=N}mu(d)*(k mod d)/d.

Define actual first-window increment energy and budget by

    I_N = sum_{N<k<=2N} (M(k)-M(N))^2/[k(k+1)],
    W_N = N*m_N^2 + sum_{N<k<=2N} U_N(k)^2/[k(k+1)].

The new finite provider proves I_N <= 4*A^2*N from
|M(t)|<=A*t on the finite interval N<=t<=2N.
The existing quantitative PNT supplies an absolute finite C>=0 such that

    I_N <= 4*C^2*N/(log N)^2

for every sufficiently large N. No unproved arithmetic premise remains.

The exact first-window identity from the preceding commit gives

    W_N <= 3*N*m_N^2 + 2*I_N.

Combining this with the existing unconditional limit m_N^2*log N -> 0 proves

    (W_N/N)*log N -> 0.

This improves the actual first-window control, including its reciprocal head.
It is still weaker than W_N being bounded by every positive power of N.
It also does not cover the whole N<k<=N^2 window.

Module: RH/RawMobiusFirstWindowQuantitative.lean.
Principal declarations:
- mobiusFirstWindowIncrementEnergy_eventual_log_square_bound
- rawMobiusFirstWindowBudget_le_increment_energy
- rawMobiusFirstWindowBudget_div_mul_log_tendsto_zero

## Exact energy identity with every signed term retained

Let G_d(k)=r(r-d)/(2d), r=k mod d, and
P_N(k)=sum_{d<=N}mu(d)G_d(k).
Let c_N=1+sum_{d<=N}mu(d)(d-1)/(2d), and
D_N(k)=sum_{d<=N,d|k}mu(d).

Lean proves P_N(k+1)-P_N(k)=U_N(k)-c_N and the exact point identity

    U_N(k)^2
      = c_N*U_N(k)
        + P_N(k+1)*U_N(k+1)-P_N(k)*U_N(k)
        - m_N*P_N(k+1)
        + H_N(k+1),

where

    H_N(n)=sum_{d,e<=N, d!=e} mu(d)mu(e)G_d(n) 1_{e|n}
          =P_N(n)*D_N(n).

The d=e terms vanish in this product because G_d(n)=0 when d|n.
The separate -m_N*P_N(n) term remains; no cancellation of the entire energy
diagonal is claimed.

The interval theorem gives exact weighted summation by parts for arbitrary
weights, positive starting index, and finite length. Both endpoints, the
weight-difference sum, the mean term, and the signed cross sum are retained.

Module: RH/RawMobiusPrimitiveEnergy.lean.
Principal declarations: rawMobiusPrimitiveJumpCross_eq_product,
rawMobius_energy_primitive_point, rawMobius_energy_primitive_interval.

## A rigorous limitation on uniform-variance shortcuts

The exact upper-half coordinates from the preceding commit imply the
finite lower bound

    V_N >= #{p prime : N/2<p<=N}/16,   N>=2.

Each such prime contributes (1-p^(-2))/12, at least 1/16, to uniform variance.
The prime-count lower bound is kernel-verified. Combining it with classical
prime-count growth shows that the uniform variance itself cannot have
subpower growth. That asymptotic combination was not separately formalized
in this task. Uniform variance is not the actual Pareto middle-window energy.

Extended module: RH/ParetoUniformJordanIdentification.lean.
Declaration: centeredMobius_factorial_variance_ge_top_half_prime_count.

## Literature checked and limits of the attempted argument

Primary source: R. de la Breteche, F. Dress, G. Tenenbaum,
Remarques sur une somme liee a la fonction de Mobius,
Mathematika 66 (2020), 416--421, equation (1.5):
https://tenenb.perso.math.cnrs.fr/PPP/Sxz.pdf

It supplies a uniform bound sum_{n<=x}D_N(n)^2 <= A*x.
This statement was checked in the paper, not formalized or imported as an
axiom. It is a credible future provider for quantitative residual-jump energy.

At paper level, Abel transfer yields a weighted jump-square bound at cutoff a
proportional to (m_N^2+A)/a. Cauchy--Schwarz together with
|P_N|<=N(N+1)/16 still gives a bound proportional to N at a=N for the signed
primitive-jump correlation. Thus this additional established estimate does
not close the current energy argument. No independence of the jumps is assumed.

The explicit-double-sum literature was also checked:
O. Ramare and S. Zuniga Alterman, On a Mobius double sum,
arXiv:2603.25961v3, https://arxiv.org/html/2603.25961v3.
Its uniform-period double sum is relevant to D_N, but no theorem from that
paper was imported as an axiom or formalized in this task.

## The still-open RH obligation

The already verified theorem
riemannHypothesis_of_frequently_subpower_raw_square_budget
proves Mathlib RiemannHypothesis from the actual finite budget

    B_N=N*m_N^2+sum_{N<k<=N^2}U_N(k)^2/[k(k+1)]

and the single substantive premise

    for every epsilon>0, some C_epsilon bounds
    B_N/(N+1)^epsilon at arbitrarily large N.

This attempt does not establish that premise. The new first-window rate
does not establish it even for W_N. The exact primitive formula exposes a
signed correlation whose sufficient cancellation remains unproved.

## Verification status

All coherent candidate checks completed with exit code 0.
The principal declarations' axiom outputs contained only
[propext, Classical.choice, Quot.sound].
No admitted proof or project-local axiom was introduced.
The final checkpoint validates persisted changed modules and affected
dependents before commit and publication.

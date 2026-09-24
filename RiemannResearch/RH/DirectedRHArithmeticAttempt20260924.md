# What remains for RH: directed arithmetic attempt

Date: 2026-09-24. Starting commit: b9bb3309a094e8d31e8c7a29492af95007273b0c.
No unconditional proof of RH was obtained.

## Exact remaining sufficient obligation in the current Lean route

Let m_N=sum_{d<=N}mu(d)/d,
U_N(k)=1+sum_{d<=N}mu(d)*(k mod d)/d, and

    B_N = N*m_N^2 + sum_{N<k<=N^2} U_N(k)^2/[k(k+1)].

The existing theorem
riemannHypothesis_of_frequently_subpower_raw_square_budget
concludes Mathlib's RiemannHypothesis from exactly the substantive premise

    forall epsilon : Real, 0<epsilon ->
      exists C : Real, frequently N atTop,
        rawMobiusSquareBudget N <= C*((N:Real)+1)^epsilon.

Each epsilon may have its own constant and cofinal set. No claim is made
that the theorem proves this premise. The already established unconditional
B_N/N limit and its logarithmic-saving ceiling do not yield this rate.

## New verified arithmetic work

### Discrete primitive and signed tail

For r=k mod d, define G_d(k)=r*(r-d)/(2d). For positive d,

    G_d(k+1)-G_d(k)=((k mod d)-(d-1)/2)/d,
    -d/8 <= G_d(k) <= 0.

Finite telescoping gives the exact endpoint formula and the uniform bound

    abs(sum_{i<L} h_d(K+i)) <= d/8.

For F_N(k)=sum_{d<=N}mu(d)*h_d(k), the actual arithmetic provider is

    abs(sum_{i<L} F_N(K+i))
      <= (1/8)*sum_{d<=N}abs(mu(d))*d
      <= N*(N+1)/16.

Summability is proved by a summable Pareto majorant, and signed Abel transfer
then gives

    abs(sum_{k>K} F_N(k)/[k(k+1)])
      <= N*(N+1)/[16*(K+1)*(K+2)].

All statements are unconditional, uniform in shift and interval length, and
do not use the least-common-multiple period. This controls a signed first
moment, not the square-energy sum in B_N.

Module: RH/CenteredResiduePrefixes.lean.
Main declarations: centeredResiduePrimitive_step,
centeredResidue_prefix_eq, centeredMobius_prefix_abs_le_quadratic,
centeredMobius_pareto_tail_abs_le.

### First-window Mertens identity

For N<k<=2N+1, the exact omitted floor sum has one term:

    U_N(k) = k*m_N + M(k)-M(N).

For N>=2 this yields

    sum_{N<k<=2N} (M(k)-M(N))^2/[k(k+1)] <= 2*B_N.

Module: RH/RawMobiusFirstWindow.lean.
Main declarations: rawMobiusResidual_first_window,
mobiusFirstWindowIncrementEnergy_le_square_budget.
These are actual arithmetic identities and bounds, with only finite index
conditions. They expose a necessary component of the missing rate, but do
not bound it from above independently of B_N.

### Exact moving Jordan coordinates

For 0<q<=N<2q,

    sum_{q|d<=N}mu(d)/d = mu(q)/q.

Combined with the existing uniform variance identity this proves

    V_N >= (1/12)*sum_{N/2<q<=N} J_2(q)*(mu(q)/q)^2.

Module: RH/ParetoUniformJordanIdentification.lean.
Main declarations: centeredMobius_divisorCoordinate_eq_top_half,
centeredMobius_factorial_variance_ge_top_half.
The coefficient statement is exact and retains the Mobius sign. Fixed-q
limit arguments do not supply estimates for this moving top-half range.
This uniform-variance lower bound is not a Pareto middle-window estimate.

## Verification and publication

All coherent proof candidates passed Lean with exit code 0.
The principal new declarations' axiom output contained only
[propext, Classical.choice, Quot.sound].
No admitted goal or domain-specific axiom is introduced.
The final checkpoint validates persisted modules and affected dependents,
then commits and pushes through the configured research workflow.

## Literature audit and next arithmetic target

Maier--Rassias, Explicit estimates of sums related to the Nyman-Beurling
criterion for the Riemann Hypothesis, arXiv:1806.05070v1, Theorem 2.1:
https://arxiv.org/html/1806.05070v1

The checked theorem gives a fixed power saving for a related Mobius sum
on k^D<=n<2k^D with D>=2. It was not imported as a Lean axiom or formalized.
Its range does not directly cover the balanced first-middle-window problem.

The Fourier coordinates at reduced a/q involve the signed divisor sums
above. Conductors q of order N yield rational frequency separations of order
1/N^2, whereas the earliest observation window has length N. Generic
large-sieve control consequently does not supply the needed middle-window
saving. This is a mathematical diagnosis, not a kernel-verified Fourier
formalization in this task.

The next substantive target remains a quantitative bound for the actual
weighted second moments over the entire N<k<=N^2 window, on a common cofinal
set with the reciprocal-head control. Signed first-moment cancellation,
uniform-period variance, and adding more RH equivalences do not establish it.

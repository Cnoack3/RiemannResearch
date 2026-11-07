# Compact square-root corrections and explicit full-Gram approximants

Date: November 6, 2026 (user-local date).
Source: CrossedDistanceLeanHandoff20261106.md, priorities 1, 2, 3, and 5.

## Status

The compactness, exact distance identities, finite correction constructions,
and weakened convergence reductions below are proved in Lean.
**RH and the actual full-conductor displacement equality d=0 remain unproved.**
The complete-error decay and signed nonpositive-limit providers remain Open.
Priority 4's second-inverse membership provider is also still Open.

The starting workspace was clean at
3b0eff7557b9e37381b7707efa93285bfcc32907, following the mathematical
baseline 3473ba7c75c1306acb013d07ae4fad2257499b02.

## Operators and exact distance identities

Use all conductors m>=2. Let Q(n)=1/(Z n^2), P(n)=1/(n(n+1)),
Z=zeta(2), V_Q and V_P their closed legal spans, and
d=Pi_Q 1-Pi_P 1 in the common physical-sequence interpretation.
I is the same-sequence map, A the isometry, T=A^{-1}I on Q,
and J=Id-T/sqrt(Z). Put W=A(V_Q).

For legal g in V_Q, Lean now proves the exact identities

    a(g) = dist_P(A g,V_P) = dist_P(A Jg,V_P),
    b(g) = dist_P(I g,W) = sqrt(Z) dist_Q(Jg,V_Q).

Declarations in QFullCrossedDistances:
forwardDistance_eq_rootDefect and inverseDistance_eq_rootDefect.
They use translation by legal vectors, not an identification of W with V_P.

The reusable Submodule API in Analysis/OrthogonalDistanceBound now includes
the exact distance-to-projection-residual formula and translation/scaling
identities used here.

## Complete tail improvement and compactness

At encoded coordinate k>=0 (physical site k+1), the exact coefficient is

    j_k = 1-sqrt((k+1)/(k+2))
        = 1/((k+2)(1+sqrt((k+1)/(k+2)))).

Its rational upper bound is 1/(2k+3). Thus, if f has zero encoded
coordinates k<N,

    ||Jf||_Q <= ||f||_Q/(2N+3).

The existing rootDefect_norm_le_of_head_zero,
rootDefect_head_trial_bound, and two_distance_head_certificate statements
are strengthened from denominator N+2 to 2N+3.
The exact rationalized coefficient precedes the estimate.
This rational bound is an improvement, not a claim of optimality.

Let H_N be coordinate restriction to k<N and J_N=J H_N.
The new QParetoSquareRootCompactness module proves

    ||J-J_N|| <= 1/(2N+3),    J_N -> J in operator norm,
    IsCompactOperator J.

Every J_N is a finite sum of coordinate rank-one maps followed by J.
The full infinite remainder, rather than a sampled tail, is bounded.

It also proves: if sup_M ||G_M||_Q <= C and each encoded coordinate
G_M(k) tends to f(k), then JG_M -> Jf strongly in Q.
A bounded weak-pairing version follows by testing coordinate unit vectors.

Principal declarations:
rootDefectHead_opNorm_error, rootDefectHead_tendsto, rootDefect_compact,
rootDefect_tendsto_of_bounded_coordinates,
rootDefect_tendsto_of_bounded_weak.

The limit is Jf. Compactness alone gives neither Jf=0 nor legal membership.

## Explicit finite approximants and both complete Gram problems

In QFullCorrectionCertificates, at stage N the dictionary is
phi_i=g_{i+2}, i in Fin N. All Hilbert products below are complete.

For a Q target x, define

    C_Q(N)_{ij} = <phi_i,phi_j>_Q,
    c_Q(N,x)_i = <phi_i,x>_Q,
    k_N(x) = sum_i (C_Q(N)^{-1} c_Q(N,x))_i phi_i.

For the second correction define

    C_T(N)_{ij} = <T phi_i,T phi_j>_Q,
    c_T(N,x)_i = <T phi_i,x>_Q,
    h_N(x) = sum_i (C_T(N)^{-1} c_T(N,x))_i phi_i.

The T Gram matrix is the complete Pareto Gram matrix under the encoded
isometry. Both k_N and h_N are finite legal vectors.
The code's correction and inverseCorrection are these two constructions;
their coefficients have explicit inverse-matrix declarations.

Lean proves k_N(x)=Pi_{V_N} x and T h_N(x)=Pi_{T V_N} x.
It retains the exact Schur objectives and completion remainders, for example

    ||x-sum_i c_i phi_i||_Q^2
      = ||x-k_N(x)||_Q^2
        + ||sum_i (c_i-c_Q^*_i) phi_i||_Q^2,

with the analogous full equality for T phi_i.
These are global norm minimizers, not just finite-head interpolants.

The concrete sequence

    G_N = k_N(1) - h_N(T1)

uses two finite Gram solves with the constant target and converges strongly
to the actual full-conductor displacement d.
It does not require knowing d in order to define its coefficients.
The definitions use noncomputable exact real inverses in Lean; no numerical
zero certificate or certified numerical solver was added.

Principal declarations:
correctionCoefficients_eq_inv_mulVec,
inverseCorrectionCoefficients_eq_inv_mulVec,
correction_completion, inverseCorrection_completion,
matchedApprox_mem_legalSpan, matchedApprox_tendsto.

## Applying the complete certificate to those approximants

Set x=J H_N G_M, h=h_H(x), k=k_K(x), and

    E = ||G_M-H_N G_M||_Q/(2N+3).

The theorem matched_head_certificate instantiates the improved certificate:

    sqrt(Z/2)||d||_Q^2 + <G_M,TG_M>_Q
      <= 2 { ||r_P||_P (||x-T h||_Q+E)
             + ||r_Q||_Q sqrt(Z) (||x-k||_Q+E) }
         + sqrt(Z)||d-G_M||_Q^2.

Every correction norm, the whole tail E, and the approximation remainder
remain present. Pairings against x are finite coordinate sums
(inner_rootDefect_finiteHead), while both Gram matrices remain complete.

For fixed legal g, optimized complete correction errors have exact limits:

    ||Jg-T h_N(Jg)||_Q -> a(g),
    sqrt(Z)||Jg-k_N(Jg)||_Q -> b(g).

Consequently their weighted sum tends to the actual crossedBudget g.
This is optimized_correction_budget_tendsto. It does not assert zero.

## Weaker convergence and signed cancellation

QFullCompactCrossedDistances combines compact smoothing with the exact
distance identities. For legal norm-bounded G_M converging coordinatewise
to legal f, a(G_M), b(G_M), and the weighted budget converge to their
values at f. In particular, for coordinate limit d,

    d=0 iff crossedBudget(G_M) -> 0.

riemannHypothesis_of_bounded_coordinate_budget exposes the remaining
zero-budget assumption explicitly. Strong convergence is no longer needed
for that conditional implication.

Independently, weak-pairing convergence G_M -> d already implies

    F(G_M) -> <d,Td>_Q,

without a legality hypothesis or a separately supplied norm bound.
The signed functional is tested against the fixed vector Td.

riemannHypothesis_of_weak_signed_limit_nonpos proves RH if an independently
justified limit F(G_M)->L with L<=0 is supplied.
No nonpositive limit is proved here.

## Verification and publication

Assembled new modules and nine principal axiom audits passed:
job_M5yiY2OyEf3aD5ELvT--00J40dERKUWb,
verified=true, exit code 0, server-reported elapsed 24.999 seconds.
The reports contain only propext, Classical.choice, and Quot.sound.
These audits do not discharge hypotheses in theorem types.

The strengthened earlier modules also passed
job_cFExCk8Agk2SmB_F7AgVlwLzqT0Kliha (21.186 seconds).
The compact and weak-limit assembly passed
job_Ps1byxbHWyAktFYyp0jDmqOb3PJFJoaQ (17.110 seconds).

Publication uses the final source-audited checkpoint and its aggregate
project validation. A checkpoint result, rather than the isolated runs
above, records final publication acceptance and any integration with main.
Workspace-opening latency was not separately measured; it is not included
in these server-reported verification durations. Status polls obeyed the
server's 30-second retry guidance.

## Remaining research obligations

1. Open: choose cofinal M,N,H,K and prove vanishing of the full correction
   terms in matched_head_certificate, with E and ||d-G_M|| controlled.
   The explicit approximants and optimal finite corrections now exist.
2. Open: prove actual crossed-budget decay for matchedApprox, or for a
   bounded legal family with coordinate limit d.
3. Open: independently control the signed tests to a nonpositive limit.
   Substituting the identity F(G_M)-><d,Td> and declaring this zero is circular.
4. Open: prove T(Td) belongs to V_Q, or an equivalent complete approximation.
   No invariance of T on V_Q, and no first-to-second inverse shortcut, is used.
5. A single diagonal convergence theorem for the optimized corrections
   with a moving target would make the explicit scalar sequence more convenient;
   the current fixed-target optimal-error limits and four-index certificates
   already retain the complete obstruction.

Retained workspace token: ws_Zc2GDeYR_6AQeljCtBv0mJCOjS-pFNK_.
Root:
/home/cri_2025/lean-agent-workspaces/ws_Zc2GDeYR_6AQeljCtBv0mJCOjS-pFNK_/RiemannResearch.
Follow any publication continuation workspace returned by the final checkpoint.

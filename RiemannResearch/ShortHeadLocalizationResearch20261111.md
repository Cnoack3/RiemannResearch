# Short-head localization and high-conductor slope
Prepared 11 November 2026. The localization modules are published; the arithmetic
Schur bound remains Open.

12 November continuation: [exact fixed-pair Schur limits and a weaker common-bound
criterion](ShortHeadSchurLimitResearch20261112.md). The new limit theorem does not
supply the common bound. This document's original verification discussion is historical.

Base: `6c4fe3312e24b00813bcc5c329cf28ba0fe14333`.
Requested starting argument:
[commit 29fa2567](https://github.com/Cnoack3/RiemannResearch/commit/29fa256722998cc6fa8b9b0f6682fd7788ffae85).

## Result

The localization argument is formalized for the actual matched full-conductor
divisor projections. The residualized short-head Schur estimate remains Open.
No RH assumption, zero residual assumption, prescribed residual decay rate, or
discarded cross term is used in the localization.

The proof reuses `QFullDivisorProjection.pOptimizer_tendsto`,
`QUniformTail.uniform_tail_tightness_of_tendsto`,
`QMatchedOscillationKernel.matched_pair_identity`, and the nested-projection
identities in `Analysis/NestedOrthogonalDecomposition.lean`.

## Definitions and endpoint conventions

Physical sites are positive integers. Coordinate i of the raw l2 carrier represents
site s=i+1. Physical value at zero is anchored to zero.

P(s)=1/[s(s+1)], Q(s)=1/[zeta(2)s^2]. For nested positive periods R_j exhausting
every conductor, S_j is the full Q span of g_q(s)=(s mod q)/q for q dividing R_j.
T_j is the identical physical span encoded with P weights. Both norms include
the entire infinite tail.

Let f_Q,j and f_P,j be the actual projections of 1, d_j=f_Q,j-f_P,j,
r_j=1-f_P,j in P coordinates, and K_j;n,m=Pi^Q_Sj(e_n-e_m).
The operator D divides physical coordinate s by s.

`tail A` removes raw coordinates 0,...,A-1, so it is exactly the physical
restriction to s>A. Although the existing truncation was originally defined
in a Q module, it is applied here to the **Pareto encoding**, and its norm is P.

Define
```text
rho(A) = sup_j ||tail A r_j||_P,
b(H)   = floor(sqrt(H)),
A(H)   = ceil(max(sqrt(H), H sqrt(rho(b(H))))).
```

Proved:
- 0 <= rho(A) <= 1; rho is decreasing; rho(A) tends to zero.
- A(0)=0 by definition; H>0 implies A(H)>0.
- floor(sqrt(H)) <= A(H), sqrt(H) <= A(H), and H sqrt(rho(b(H))) <= A(H).
- A(H) tends to infinity, A(H)/H tends to zero, and eventually A(H)<=H.
- The H=0 quotient uses Lean's usual total real division. All estimates remain valid.
- The high-conductor energy bound requires H>0, and its physical head formula
  requires A<=H. The chosen A(H) meets this condition eventually.

The supremum tail convergence follows from strong convergence of the residuals
to their actual limiting residual. That limiting residual need not be zero.

## Complete signed localization

Set
```text
Head_A(r,K) = <r, 1_{s<=A} D K>_P,
Tail_A(r,K) = <1_{s>A} r, 1_{s>A} D K>_P.
```

The exact matched identity is
```text
zeta(2) [d_j(n)-d_j(m)] = Head_A(r_j,K_j;n,m) + Tail_A(r_j,K_j;n,m).
```

The complete reciprocal tail satisfies
```text
||1_{s>A} D K||_P^2 <= zeta(2)/[(A+1)(A+2)] ||K||_Q^2,
||K_j;n,m||_Q^2 <= 2 zeta(2) H^2       (0<=n,m<=H).
```

Consequently,
```text
|Tail_A(r_j,K_j;n,m)|
 <= zeta(2) sqrt(2) H rho(A)/sqrt((A+1)(A+2)).
```

For the precise integer cutoff,
```text
H rho(A(H))/sqrt((A(H)+1)(A(H)+2)) <= sqrt(rho(floor(sqrt(H)))) -> 0.
```

The tail tends to zero uniformly in j and in every pair n,m<=H.
`signed_remainder_tendsto` permits an arbitrary moving stage selector j(H);
it need not be monotone or tend to infinity.

## High-conductor slope and Schur remainder

Let U_j,H be the span of those q dividing R_j with q>H.
Every f in U_j,H satisfies f(s)=s f(1) for 0<=s<=H.
Define u=Pi_U^Q e_1 and alpha=||u||_Q^2. Then
```text
Pi_U^Q(e_n-e_m) = (n-m)u,
u(s) = s alpha                           (0<=s<=H),
alpha <= zeta(2)/H                       (H>0).
```

The last estimate uses H physical coordinates in the complete Q norm:
H alpha^2/zeta(2) <= alpha. The alpha=0 case is included.

For A<=H, the exact high-head term is
```text
(n-m) alpha sum_{1<=s<=A} P(s) r_j(s).
```
Its absolute value is at most zeta(2)||r_j||_P <= zeta(2).
Thus the normalized high contribution to displacement is at most 1.

Define K_low=K_j;n,m-Pi_U^Q(e_n-e_m). It is the projection of e_n-e_m onto
S_j intersect U_j,H^perp. The three-term identity is
```text
zeta(2) [d_j(n)-d_j(m)]
 = (n-m) alpha <r_j,1_{s<=A}>_P
   + Head_A(r_j,K_low)
   + Tail_A(r_j,K_j;n,m).
```
This is an equality, including all signs.

For residualized atoms u_a=g_a-Pi_U g_a, every Gram entry is retained:
```text
<u_a,u_b>_Q = <g_a,g_b>_Q - <Pi_U g_a,Pi_U g_b>_Q.
```
The numerical script evaluates the full Schur matrix
G_low,low-G_low,high G_high,high^{-1} G_high,low,
the residualized evaluation difference, and the signed source together.

## The remaining condition

The conditional theorem
`QFullShortHeadLocalization.riemannHypothesis_of_short_schur_bound`
requires a single positive modulus L, a finite C, and physical heads H_j
tending to infinity, such that eventually for every positive n,m<=H_j with
n mod L = m mod L,
```text
|Head_{A(H_j)}(r_j,K_low;j,H_j;n,m)| <= C.
```

It then proves Mathlib's RiemannHypothesis using the existing full-displacement
oscillation theorem. The arithmetic Schur bound is an explicit hypothesis and
remains Open. It is not supplied by tail tightness, finite-stage periodicity,
or finite numerical evidence.

## Finite Gram investigation

The accompanying `short_head_gram.py` folds the complete infinite P and Q weights by each
period using digamma and trigamma formulas. It keeps all divisor conductors,
including prime powers and the period itself. No physical tail is truncated
when constructing the Gram matrices or the actual residuals.

Runs use fixed modulus 2 and both A=floor(sqrt(H)) and A=H.

| R | H | alpha H/zeta(2) | max signed Schur magnitude at A=floor(sqrt(H)) | Schur condition number |
|---:|---:|---:|---:|---:|
| 6 | 3 | 0.479715 | 0.027888 | 2.526 |
| 12 | 4 | 0.692509 | 0.073044 | 4.802 |
| 60 | 5 | 0.930186 | 0.070278 | 8.407 |
| 420 | 7 | 0.755819 | 0.051525 | 28.316 |
| 840 | 8 | 0.864794 | 0.051150 | 31.920 |
| 2520 | 9 | 0.976161 | 0.055111 | 47.787 |
| 27720 | 11 | 0.985210 | 0.045263 | 97.104 |

The slope bound is nearly sharp in the largest sample. The signed Schur
values remain small in these samples, while the conditioning worsens.
The maximum normal-equation defect is below 1.7e-16; the maximum three-term
head-split defect is below 2.0e-15. These are floating-point diagnostics,
not interval certificates or Lean proofs.

A proposed diagonal-only inverse bound fails for general coefficient
directions on the tested Schur matrices. The worst inverse/diagonal ratio
rises from about 2.30 at (R,H)=(60,5) to 6.39 at (27720,11).
The canonical residual source itself did not violate that candidate
inequality in these samples; its largest observed ratio is about 0.805.
The arbitrary-vector failure therefore must not be presented as a
counterexample to the actual residual estimate.

An independent exact rational check is
```text
S = [[1,3/4],[3/4,1]], beta=(1,-1).
det(S)=7/16>0.
beta^T S^{-1} beta = 8, but sum beta_i^2/S_ii = 2.
```
This disproves the universal replacement of the inverse Gram pairing by
its diagonal entries. It is exact rational Python arithmetic; no new Lean
verification is claimed for this counterexample.

These finite A choices are diagnostic choices. They are not claimed to
evaluate the infinite-family supremum rho or the canonical A(H).

## Proposed files

| File | Responsibility |
|---|---|
| Analysis/SublinearTailCutoff.lean | Explicit ceiling/floor cutoff and normalized-tail limit |
| RH/QMatchedResidualTails.lean | Actual Pareto residuals, uniform supremum tails, endpoint interpretation |
| RH/QHighConductorSlope.lean | Linear high head, slope representation, energy bound, physical signed formula |
| RH/QMatchedShortHead.lean | Sharp reciprocal tail estimate and exact signed localization |
| RH/QFullShortHeadLocalization.lean | Actual divisor stages, three-term split, moving-tail limit, conditional RH criterion |
| RiemannResearch.lean | Export the five modules |
| THEOREM_CATALOG_FULL_OSCILLATION_DUAL_20261109.md | Update localization status and retain the open Schur obligation |

The review package also contains the standalone experiment script and its JSON
results. These Python artifacts are not part of the server source patch.

## Verification and publication

Verification details, exact job IDs, and source hashes accompany the review package.
The final project check is recorded separately from focused file checks.
There are no proof placeholders or new project-local axioms in these modules.
Publication is intentionally withheld pending review of the proposed changes.

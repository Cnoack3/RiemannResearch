# Finite density providers: proofs from elementary structure to optimal limits

Date: 2026-11-14 (user-facing date).
Base revision: 8d46119bc3623a72c4abb5834a18c44e05f69f3d.
Source: independently developed continuation of the repository's Priority 1
finite-approximation provider, at Christian Noack's request to prove
declarations from easiest to hardest.

This batch proves 16 declarations. It closes finite-support and explicit
witness-selection gaps. The arithmetic small-o estimate remains Open.
It does not assert an unconditional proof of RH or a proof of the
Baez-Duarte analytic converse provider.

## Notation and exact identities

Use the actual complete Q Hilbert norm, with
Z = zeta(2), g_k(n) = (n mod k)/k, Df(n) = f(n)/n, and B=(I+D)/Z.
Let S be the finite legal span, V its closure, and
r = 1 - Pi_V 1.
The existing inverse-Gram candidate u_N is the actual complete-Q
projection of 1 onto span(g_2,...,g_(N+1)).

The new explicit finite trial is

    a_(k,N) = g_k/Z + u_N/(Z k).

For every k>0 and N>=0 the checked signed identity is

    Z k (B g_k - a_(k,N)) = k D g_k - u_N.

For k>=2 this trial is in S. Its complete error satisfies

    ||B g_k - a_(k,N)|| <= 2/(Z k).

For any a in V, the full error identity is

    ||B g_k-a||^2
      = ||Pi_(V-perp) B g_k||^2
        + ||Pi_V B g_k-a||^2.

The second square is retained throughout; no finite physical tail is discarded.

## Completed declarations, ordered by proof difficulty

Namespace A = RiemannResearch.RH.QDensityLeakageArithmetic.
Namespace F = RiemannResearch.RH.QDensityFiniteProvider.

| Order | Declarations | Proven conclusion |
| --- | --- | --- |
| 1. Finite support | A.exists_trialSpace_of_mem_legalSpan | Every finite legal vector lies in one positive finite divisor dictionary. |
| 2. Exact obstruction | A.density_atom_not_mem_legalSpan; A.density_atom_error_pos | For k>=2, B g_k is not a finite legal synthesis and every finite legal error is strictly positive. |
| 3. Explicit construction | F.trial_mem_legalSpan; F.trial_error_identity; F.trial_error_norm_le | Legal membership, the exact signed identity, and the unconditional O(1/k) bound. |
| 4. Universal comparison | F.leakage_le_legal_error; F.legal_error_pythagoras; F.legal_error_lower_certificate | Complete orthogonal decomposition and a finite lower certificate against every competitor in V. |
| 5. Two moving parameters | F.trial_scaled_error_tendsto; F.trial_scaled_norm_tendsto | The scaled error converges to r, and its norm to ||r||, for independently cofinal k_j and N_j. |
| 6. Optimality | F.trial_optimality_gap_tendsto; F.trial_projection_gap_tendsto; F.residual_norm_le_error_limit | The scaled gap to the infinite best approximation tends to zero; any convergent normalized legal error has limit at least ||r||. |
| 7. Uniform obstruction | F.eventually_all_legal_error_lower | If r is nonzero, Z k ||B g_k-a|| >= ||r||/2 simultaneously for every a in V at every sufficiently large k. |
| 8. Provider equivalence | F.one_mem_iff_finite_provider | For every prescribed cofinal k_j>=2, a finite legal small-o(1/k_j) provider exists iff 1 is in V. The witness in the forward direction is a_(k_j,j). |

The order is local to this finite-approximation branch; this is not an
exhaustive ranking of all research hypotheses in the repository.

## Sharp asymptotic statement

For any independently cofinal sequences k_j and N_j,

    Z k_j (B g_(k_j) - a_(k_j,N_j)) -> r,
    Z k_j ||B g_(k_j) - a_(k_j,N_j)|| -> ||r||.

No relation between the growth rates of the two sequences is required.
The trials are asymptotically optimal in the stronger vector sense:

    Z k_j (Pi_V B g_(k_j) - a_(k_j,N_j)) -> 0.

Moreover, if a_j belongs to V and its normalized error converges to L,
then ||r|| <= L. This does not assume that an arbitrary competitor has
a convergent error.

The finite lower certificate, valid for every k>=2 and every a in V, is

    ||r|| - sqrt(1/[Z(k-1)]) <= Z k ||B g_k-a||.

Thus the same optimality obstruction applies to arbitrary finite coefficient
choices, not only the explicit inverse-Gram family.

## Exact remaining RH obligation

For every prescribed cofinal k_j>=2, the new equivalence is

    1 in V
      iff exists a_j in S with k_j ||B g_(k_j)-a_j|| -> 0.

Existential witness selection is settled: when this condition holds, the
explicit a_(k_j,j) works. What remains Open is proving the small-o limit,
or equivalently r=0, for the actual arithmetic family.

The existing checked implication

    QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure

then gives Mathlib's RiemannHypothesis. No RH-to-density converse is used.
The unconditional O(1/k) bound has a potentially nonzero leading constant
||r||/Z and therefore does not supply the needed small-o bound.

The exact finite-span obstruction is compatible with closure membership:
strictly positive errors at every finite stage may still tend to zero.

## Files and verification

- Extended RH/QDensityLeakageArithmetic.lean with the three finite-span results.
- Added RH/QDensityFiniteProvider.lean with thirteen theorems and the trial definition.
- Exported the new module from RiemannResearch.lean.
- Thirteen guarded axiom reports require exactly propext, Classical.choice,
  and Quot.sound for the central results, including the finite-span obstruction.
- No new axioms, unsafe declarations, or proof placeholders are introduced.

The coherent 16-theorem candidate passed Bazel/BuildBuddy snippet acceptance
in job job_gKrajt1AgQEbTqvmVXPhiQ7KfIFDiVDD, exit code 0, verified=true.
Server verification duration: 54.910 seconds.
Receipt: https://app.buildbuddy.io/invocation/3af066b3-e699-4508-be32-ce5dcd2d2bda

The saved modules, including all thirteen guarded axiom reports, passed
focused acceptance in job job_9z97H7GzI7dHsKgXEZqcdny6ctgcgYzE,
backend=bazel, exit code 0, verified=true.
Server verification duration: 73.061 seconds.
Receipt: https://app.buildbuddy.io/invocation/90a95f77-c0f8-40f4-af05-e4595cfb1bab

The complete-project publication checkpoint is a separate acceptance stage.
Its terminal record and exact published commit are reported with the delivery.
Focused acceptance alone is not whole-project acceptance.

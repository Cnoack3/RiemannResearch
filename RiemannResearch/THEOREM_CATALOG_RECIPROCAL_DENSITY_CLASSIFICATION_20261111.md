# Reciprocal residue density and the Nyman–Beurling boundary — 2026-11-11

## Scope and notation

Physical positive coordinates: P(n)=1/(n(n+1)), Q(n)=1/(zeta(2)n^2),
g_k(n)=(n mod k)/k. QReciprocalMetric.D divides by n.
QDensityMetric.B is dQ/dP=(I+D)/zeta(2).
QShiftedReciprocal.B, when mentioned elsewhere, divides by n+1 and is a different operator.

The two physical L² norms are equivalent. Closure, convergence and boundedness
transfer; orthogonality transfers through the density multiplier rather than
by exchanging P/Q labels. No unconditional RH claim is made.

## Unconditional formal results

* QReciprocalFullDensity.fullReciprocalClosure_eq_top and
  pareto_fullReciprocalClosure_eq_top: the Dg_k family for all k>=2 is total.
  Proof: exact finite factorial Möbius sieve, coordinate eventual equality,
  dominated complete-norm convergence, and density of finite-support vectors.
* QReciprocalSieveNorm.floorAtom_pareto_norm_le_rpow:
  F_m(n)=floor(n/m)/n has complete Pareto norm at most m^(-3/2), for m>0.
* QReciprocalSpanObstruction.one_mem_reciprocalClosure_of_unbounded:
  every unbounded conductor set has 1 in its smoothed closure.
* QReciprocalDensityClassification.D_one_mem_squarefree_reciprocalClosure
  and pareto_D_one_mem_squarefree_reciprocalClosure:
  squarefree k>=2 also approximate the correct smoothed target D1.
* QReciprocalSpanObstruction.squarefree_reciprocalClosure_ne_top:
  squarefree Dg_k are not total; Dg_4 is excluded by
  f(1)-2f(2)-3f(3)+4f(4).
* QReciprocalSpanObstruction.squarefree_reciprocal_D_D_one_not_mem
  and D_not_preserves_squarefree_reciprocalClosure:
  D²1 is excluded (functional value 5/12); D²g_2 is excluded (value 1/3).
  The squarefree smoothed closure is therefore not D-invariant.
* QReciprocalDensityClassification.strict_reciprocalClosure_eq_ker,
  strict_reciprocalClosure_mem_iff and pareto_strict_reciprocalClosure_mem_iff:
  the strict k>2 D-family has exactly the closed hyperplane f(1)=f(2).
  It contains 1 but excludes D1 and Dg_2.
* QReciprocalSpanObstruction.strict_density_one_not_mem:
  the strict k>2 B-family excludes 1, detected by 3f(1)-2f(2).
* Existing QDensitySquarefreeObstruction at base f3fb0b2:
  squarefree B-family excludes 1, detected by
  f(1)/2-2f(2)/3-3f(3)/4+4f(4)/5.

## Explicitly conditional lifting results

QReciprocalTargetLift specializes the existing bounded injective lift and
divergence theorems to D:
* bounded_D_lift_iff_mem: for a complete separable submodule S, existence
  of bounded F_j in S with D F_j -> D x is equivalent to x in S.
* mem_of_bounded_subsequence_D_tendsto: a bound along one cofinal subsequence suffices.
* norm_tendsto_atTop_of_not_mem_D_tendsto: if x is outside S, source norms tend to infinity.
* riemannHypothesis_of_bounded_subsequence_D_target: legal full-conductor
  vectors approaching D1 after D imply Mathlib RH when one cofinal
  subsequence has uniformly bounded source norms.
* riemannHypothesis_of_regularized_D_cost: reg_j>0 tends to 0, F_j belongs
  to the finite legalSpan, and
  ||D(F_j-1)||² + reg_j ||F_j||² <= C reg_j
  for a fixed nonnegative C imply Mathlib RH.
* bounded_D_target_pareto_iff and pareto_inner_density_eq_q_inner
  give the precise physical P/Q transfer.

The uniform source-norm / O(reg) cost estimate is OPEN. Sieve bounds concern
smoothed vectors only. The reverse analytic RH equivalences in the accompanying
paper are sourced to Bagchi and Báez-Duarte, not asserted as new Lean theorems.

## K cancellation boundary

Existing QParetoJointAnnihilator and QParetoJointBlock retain their hypotheses.
For K=V_sf intersect W^(perp P) intersect W^(perp Q), prime testing gives P-mean zero.
Q-mean zero additionally requires the D1 pairing. The K-block forcing and its
coupling term must be retained. Squarefree D1 membership does not automatically
extend prime-only orthogonality to squarefree conductors.

## Verification provenance

Base main: f3fb0b2fff1ab7c443d2710ccbb1294cfdd34857.

Independent scoped Bazel checks (integration is separately validated by checkpoint):
* full density: job_m93ugN0XrrDE3eFfTqo3_sz8nFX13UNe, verified, 33.151s;
  https://app.buildbuddy.io/invocation/6bd4b089-cc51-43c5-9530-a1f099eb3079
* norm estimate: job_xKafPhjRgQi7ykwfORWLWQkUJgzt4JKF, verified, 60.735s;
  https://app.buildbuddy.io/invocation/ee234070-395b-4b67-8ce9-bd74e91ee986
* restricted spans: job_wBkKqA6QMJczuYEBi78P9lmRrZ7mYh8G, verified, 54.001s;
  https://app.buildbuddy.io/invocation/f1881e96-bde7-4eb7-b208-511df6f9b521

Combined root import and twelve guarded axiom checks:
job_3fTbF24FWMFRsKlJtT0qeF0_PRa48TKL, verified=true, exit 0, 71.146s;
https://app.buildbuddy.io/invocation/673ef448-705a-423d-abda-3b9b292689d7
The five new modules contain 83 theorems and 9 definitions.

Guarded axiom audits permit only propext, Classical.choice, Quot.sound.
No new axioms, sorry/admit placeholders, or unsafe proof steps.
The publication checkpoint verifies the full root import before commit/push.

## Research agenda

1. Preserve the exact legal conductor family, target D1, and full P/Q energy.
2. Turn the explicit sieve into finite legal preimages; expose all source-energy growth.
3. Supply a cofinal O(reg) regularized-cost certificate using complete Gram matrices.
4. Retain signed Möbius and CRT cross terms; do not substitute absolute-value bounds silently.
5. Prove the prime-to-squarefree pairing bridge and the actual K-block cancellation.
6. Derive a uniform source bound or compatible head-tail estimate; use published damped
   Möbius constructions as coefficient candidates without importing their RH assumptions.
7. Close only with the checked bounded-lift consumer and actual unconditional provider.

Published references: Bagchi (2006), doi:10.1007/BF02829783;
Báez-Duarte (2003), arXiv:math/0202141; Burnol (2002), arXiv:math/0103058;
Bettin–Conrey–Farmer (2013), arXiv:1211.5191 (conditional on RH and a derivative-moment bound).

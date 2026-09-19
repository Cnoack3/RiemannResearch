# Contradiction search under not RH — 2026-09-19

## Outcome and scope

No genuine contradiction has been established, and RH has not been proved.
Two new Lean modules contain 41 verified theorem declarations:
20 in ExactHeadResidualTail and 21 in RHCriterionFailures.
They formalize necessary failures, the actual residual-tail obstruction,
and conditional sufficient bounds. They do not assert the missing bounds.

This was a targeted dependency-and-hypothesis audit of the strongest candidate
clashes, not a claim that every possible consequence of the entire project
has been exhausted. A theorem P -> RH gives not P under not RH; it supplies
a contradiction only when P is also proved with all its hypotheses met.

Sources motivating the formalization:

- RH_Equivalent_Formulations_Lean_Audit_2026-09-19(1)(1).md
- RH_Weighted_Telescoping_Construction_and_Tail_Repair_2026-09-19.md

The explicit arithmetic telescope formulas and every matrix entry from the
written notes are not all newly formalized here. The new tail obstruction
applies to any exact-head vector in the actual closed residue span, including
a telescope once its legality and head identities are supplied. Existing
finite signed quadratic and Schur modules retain the full signed cross terms.

## The sharp obstruction now proved

Let V be the closed residue span, r = 1 - P_V 1, E = norm(r)^2, and
t_N = sum_{n>N} r(n)^2/[n(n+1)]. Under the explicit hypothesis not RH,
E > 0. Independently, t_N tends to zero.

For every F in V with F(k)=1 for 1 <= k <= N:

    inner(r, 1-F) = E
    E^2 <= t_N * norm(1-F)^2.

The factor t_N is the complete physical weighted tail, not a finite
truncation. Therefore every family of such exact-head vectors has
norm(1-F_N)^2 tending to infinity under not RH.

For a complete correction subspace K <= V whose vectors vanish on the head,
write e = 1-F and F* = F + P_K e. Then:

    norm(1-F*)^2 = norm(e)^2 - norm(P_K e)^2
    E^2 <= t_N * (norm(e)^2 - norm(P_K e)^2).

For a finite independent correction basis this is precisely the signed
Schur remainder rawError - b^T G^{-1} b. The projection formulation also
handles a dependent basis without assuming an inverse exists.

A contradiction would follow from ONE actual admissible witness, under
not RH, satisfying the strict opposite inequality:

    t_N * (rawError - correctionGain) < E^2.

No such witness or general upper bound has been established. A useful
E-independent sufficient construction is: for every epsilon>0, provide an
admissible witness whose product is <epsilon. Lean now proves that this
construction implies the actual Mathlib RiemannHypothesis. Uniformly bounded
exact-head errors are a stronger sufficient input, not a proved fact.

## Candidate clashes checked

| Apparent clash | What is actually proved | Missing condition or distinction |
| --- | --- | --- |
| Vanishing residual tails versus positive residual energy | t_N -> 0 and E^2 <= t_N D_N | D_N diverges under not RH. No upper bound gives t_N D_N -> 0. |
| Exact finite tail improvement versus divergent exact-head minima | Every finite projection gives an exact error decrement | Finite decrements do not bound the remaining error uniformly as the head grows. |
| Actual Gibbs pi/4 contraction versus failure of approximation | The actual mean-zero operator contracts unconditionally | Arithmetic legal invariance or a legal vanishing-repair orbit is not supplied. |
| Strong convergence versus escaping Mobius reconstruction norms | Dual Riesz projections converge; residue-coordinate reconstructions escape under not RH | These are different sequences in different finite spans. Density of the dual dictionary is not density of the residue dictionary. |
| Cauchy closed head minimizers versus divergent optimal energy | Cauchy convergence is proved assuming bounded energy | The boundedness hypothesis is exactly what not RH excludes. |
| Positive or exact telescoping gains versus an RH-producing divergent sum | Finite gain identities and conditional nonsummable-gain criteria | Nonnegative, even strictly positive, gains can have finite total sum. No divergent lower schedule is supplied. |
| Conditional-iid averaging versus a positive approximation floor | The within-sample term decays, leaving conditionalMeanError | The remaining conditional-mean term has a uniform positive floor under not RH. |
| Actual linear conditional-head upper bound versus the off-line-zero lower bound | For large Y, c_rho Y^(2 Re(rho)-1) <= conditionalHeadMinimum(Y) < 2Y | The exponent lies strictly between zero and one. These bounds are compatible. |
| Primitive square summability versus certificate primitive nonsummability | The primitive is in l2, not necessarily l1 | ParetoOscillatoryRegularityGap gives the explicit non-certificate example A_n=1/n. |
| Damped prime-power bounds versus the arithmetic RH target | The proved damped bounds hold for s>2 | The target asks for every s>1; the critical bound is only linear, and the cell energy is not the legal head infimum. |

Concrete declarations inspected include:

- ParetoGibbsSpectralGap.hilbertGibbs_meanZero_norm_le and
  hilbertGibbs_legal_repair_iff_closure_unconditional.
- GibbsArithmeticResearchTargets.GibbsLegalInvarianceTarget,
  GibbsArithmeticRepairTarget, and their conditional RH consumers.
- MobiusResidualEscape.dualCoordinateProjection_tendsto,
  defect_reconstruction_dual_bound_sq, and not_RH_defect_norms_tendsto_atTop.
- TwoSeedHeadEnergyGeometry.closedMinimizer_tendsto_one_of_bddAbove,
  energy_bddAbove_iff_closure, and energy_limit_dichotomy.
- TailCapacityJointCorrections.jointCapacityGain_partial_sum_le and
  riemannHypothesis_of_jointScreenedGainDivergence.
- DyadicGainEndpoint.dyadic_distance_product,
  dyadic_distance_tendsto_zero_iff, and the gain/cost schedule consumers.

Additional arithmetic checks: CanonicalMobiusConditionalHead.conditionalHeadMinimum_lt_two_mul,
ConditionalMeanSubpolynomial.exact_head_polynomial_obstruction_eventually,
PrimePowerEnergyBounds.enumerated_critical_energy_le_linear and enumerated_damped_energy_le,
and ParetoOscillatoryRegularityGap.constantOne_not_summable_signedTail.
The cubic-gap remainder bound in PrimePowerCriticalEnergy has an explicit
summability hypothesis and bounds a geometric remainder, not the full signed
arithmetic discrepancy. No provider for CanonicalTailSummability or the
canonical additive-cancellation hypothesis was found in the inspected sources.

These are file-and-short-declaration references, not fully qualified Lean names.

## Why the Hilbert identities alone cannot yield a contradiction

There is an explicit abstract example with the SAME weights, but a different
legal space. This is not a model of the arithmetic residue dictionary and
does not establish consistency of the entire project with not RH.

Take H = l2(n>=1, 1/[n(n+1)]) and V = {f : inner(f,1)=0}.
Then r=1 and E=1. Put:

    F_N(n) = 1   for n <= N
             -N  for n > N.

Since the head mass is N/(N+1) and tail mass is 1/(N+1), F_N lies in V,
is exact on the head, and has:

    t_N = 1/(N+1)
    norm(F_N)^2 = N
    norm(1-F_N)^2 = N+1
    t_N * norm(1-F_N)^2 = 1 = E^2.

Moreover F_N is already the least-error exact-head vector in this V:
the general Cauchy-Schwarz bound is attained. Head-preserving orthogonal
tail corrections cannot lower its error.

Thus exact heads, vanishing residual tails, projections, finite optimization,
and the full energy identities do not by themselves contradict a nonzero
residual. A new fact specific to the arithmetic legal space is required.

## Verification record

The final sources were jointly checked by the Lean service:

- job_a3Idj37JzTIct9KGK-Rl0RffGvD9wiEj: succeeded, exit_code=0,
  verified=true; 41 declarations and axiom-print commands.
- job_aCayak5MqZGCErPbdY-sATjiE1MeTuqV: succeeded, exit_code=0,
  verified=true; untruncated repeat of the first 16 axiom reports.

Together the displayed reports cover every new theorem. Their only reported
axioms are propext, Classical.choice, and Quot.sound. There is no sorryAx
or new mathematical axiom. This checks proof dependencies, not the truth
of a theorem's explicitly stated hypotheses.

The exported modules and theorem catalog have been updated.
The final repository checkpoint performs its own affected-module validation
and publication; its result is reported separately by the workflow.

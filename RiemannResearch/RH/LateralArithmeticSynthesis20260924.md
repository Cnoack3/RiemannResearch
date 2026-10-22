# Lateral arithmetic synthesis: RH attempt
Date: 2026-09-24
Starting commit: a29555248e4a76e01dffac51056bcb45fa1a5543

## Outcome

Unconditional RH was not proved. This continuation combines actual reciprocal
charges, exact signed dilation correlations, canonical capacities, finite
orthogonal projections, and the repository's proved PNT pairing mechanism.

The successful results below have no unproved arithmetic hypotheses beyond
the explicit domains or test-class assumptions in their statements.
The final RH implication still has an explicit physical-primitive bound.
Neither that bound nor capacity divergence is asserted.

## 1. Actual geometric cancellation

Write R_N = reciprocalChargeRiesz N. Existing modules prove

    ||R_N||^2 -> 15/pi^2,
    <R_N,R_(2N)> -> -6/pi^2.

The new square-divisibility argument proves

    4 | h, h > 0  ==>  <R_N,R_(hN)> -> 0,

because mu(hd)=0 for every d. Consequently the limiting Gram matrix for
R_N,R_(2N),...,R_(2^L N) is tridiagonal: 15/pi^2 on the diagonal,
-6/pi^2 immediately off it, and zero further away.

Retaining both signed off-diagonal terms gives the exact limit

    ||sum_(j=0)^L R_(2^j N)||^2 -> (3L+15)/pi^2.

Thus, for A_(L,N)=(L+1)^(-1) sum_(j=0)^L R_(2^j N),

    ||A_(L,N)||^2 -> (3L+15)/(pi^2 (L+1)^2).

The latter scalar tends to zero as L tends to infinity. Lean also proves
that for every epsilon>0 there is a fixed L with eventual squared norm
less than epsilon. The order is first N, then L. No uniform cutoff rate
or interchange of these limits is assumed.

Module: RH/ReciprocalChargeDyadicAverages.lean.
Principal declarations:
- reciprocalChargeRiesz_four_dvd_dilation_inner_tendsto
- reciprocalChargeRiesz_dyadic_far_inner_tendsto
- dyadicReciprocalChargeAverage_norm_sq_tendsto
- dyadicReciprocalChargeAverage_eventually_small

These are dual charge vectors. Their norm cancellation is not convergence
of legal approximants to the RH target.

## 2. Direct charge/innovation connection

Let rho_d denote normalizedResidueHilbert d and define the actual step

    v_M = (M+2)rho_(M+2) - (M+1)rho_(M+1).

The new exact pairing formulas are

    <R_K,rho_d> = 0 if d<=K, and 1/d otherwise;
    <R_K,v_M> = 1 if K=M+1, and 0 otherwise,

for positive K, d>=2, M>=1. If P_M projects onto finiteSpace M,
then R_K is orthogonal to that entire space when K>=M+1. In particular,

    <R_(M+1),(I-P_M)v_M> = 1.

Combining Cauchy--Schwarz with the established uniform bound ||R_K||^2<=42
yields an unconditional full-space innovation lower bound

    ||(I-P_M)v_M||^2 >= 1/42.

This is the full-space projection innovation. It is not the distinct
tail-screened denominator in the capacity gain.

Module: RH/ReciprocalChargeInnovations.lean.
Principal declarations:
- reciprocalChargeRiesz_consecutive_biorthogonal
- reciprocalChargeRiesz_mem_finiteSpace_orthogonal
- consecutiveResidue_full_innovation_energy_lower

## 3. The capacity source is an actual residual pairing

Let e_1=finiteHeadIndicator 1, E_M=||e_1-P_M e_1||^2,
K_M=windowCapacity 1 M, and Q_M=windowNormal 1 M.
The earlier exact formula is E_M=(K_M+2)^(-1).

The new vector identification of the arithmetic optimizer with the
one-observation normalized projection gives

    E_M Q_M = tail_1(P_M e_1) = -tail_1(e_1-P_M e_1).

Consequently the signed source from the previous gain calculation satisfies

    E_M <tail_1(v_M),Q_M>
      = -<tail_1(v_M),tail_1(e_1-P_M e_1)>.

No independent-variable model, diagonal covariance replacement, or deletion
of a mixed term is used. This identifies exactly what the arithmetic source
measures. It supplies no positive lower bound on accumulated source energy.

Module: RH/CanonicalMobiusSourceProjection.lean.
Principal declarations:
- singleHead_optimizer_eq_projection
- singleHeadError_smul_windowNormal_eq_neg_residual_tail
- singleHead_normalized_source_eq_residual_pairing

The direction of the dual bound explains why geometric averaging does not
close RH. For any charge combination A whose cutoffs are all >=M+1,

    <A,e_1-P_M e_1> = <A,e_1>,
    (K_M+2)|<A,e_1>|^2 <= ||A||^2.

This last displayed inequality is an ordinary consequence of the proved
orthogonality, Cauchy--Schwarz, and the existing capacity/error identity;
it is not a separately named new Lean declaration. It bounds capacity from
above after normalizing a nonzero signal. As A tends to zero, its first-head
signal also tends to zero. Hence no divergent capacity lower bound follows.

## 4. A logarithmic extension of the PNT test class

An elementary Dirichlet-convolution comparison proves

    sum g(n)/n < infinity
      ==> sum tau(n) g(n)^2/n < infinity

for nonnegative g decreasing on positive integers. For d|n,
g(d)g(n/d)>=g(n)^2. Absolute convergence of the convolution therefore
provides the majorant. Taking g(n)=1/log(2n)^(p/2) proves

    sum tau(n)/(n log(2n)^p) < infinity,  p>2.

The convention at n=0 is Lean's totalized division; this term is zero.
The analytic inputs are already proved local logarithmic p-series and
Mathlib's LSeriesSummable.convolution.

Module: NumberTheory/DivisorCountLogSummability.lean.

For H_f(K)=sum_(k=1)^K hilbertSequence f k, the new arithmetic consumer gives

    |H_f(K)| <= C (K+1)/log(2(K+1))^p for every K, p>2
      ==> <hilbertOne-rawMobiusHilbert N,f> -> 0.

This extends the earlier fixed-power primitive tests. For the actual
limiting orthogonal residual r, the left pairing is exactly limitEnergy,
so the same estimate for H_r would force r=0 and Mathlib RiemannHypothesis.

Module: RH/NaturalMobiusLogarithmicTests.lean.
Principal declarations:
- rawMobiusResidual_inner_tendsto_of_primitive_log_bound
- riemannHypothesis_of_residual_primitive_log_bound

The latter declaration is explicitly CONDITIONAL. Its hH argument is the
unproved bound on H_r. Axiom cleanliness does not discharge that argument.

## 5. What still prevents the unconditional conclusion

The project already proves E_M=(K_M+2)^(-1), convergence of E_M to the
limiting first-head defect, and the equivalence of a zero first-head defect
with legal density. One exact remaining route is

    K_M -> infinity, equivalently E_M -> 0.

The signed source formula and the denominator estimates do not establish
this divergence. PNT does not furnish a lower bound on the required moving
projection-source accumulation.

The new logarithmic route instead requires an actual arithmetic provider

    exists C,p>2, for every K,
      |H_r(K)| <= C (K+1)/log(2(K+1))^p.

The repository's unconditional weighted-tail/primitive regularity is about
different quantities and cannot be substituted for these physical partial
sums. No such provider was found in this attempt.

The earlier PNT/dichotomy remains compatible: nonzero residual energy forces
N*T_N -> infinity while T_N -> 0 and canonical approximation energy is o(N).
Those assertions are not contradictory.

## Verification

The coherent candidate, including all the displayed principal declarations
and the conditional RH implication, completed with exit code 0 and
verified=true in job_SYfKXQ2NWTX0_AXOmtz29lMBaIdcfndh.

The inspected axiom outputs contain only propext, Classical.choice, and
Quot.sound. The full printed RH theorem retains its physical-primitive hH
argument. No sorry, local axioms, or assumed RH were introduced.

The five subject modules are exported and cataloged. The final checkpoint
runs focused affected-module validation before committing and publishing.

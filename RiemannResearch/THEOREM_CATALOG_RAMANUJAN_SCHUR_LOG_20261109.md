# Ramanujan Schur limits, global logarithms, and zero certificates

Research continuation: 2026-11-09. These are additions to the existing
full-conductor program, not a proof of RH. The four modules are exported
by RiemannResearch.lean and use the complete Pareto Hilbert norm.

## Files and scope

| Module | Result |
| --- | --- |
| RH/PrimePowerRamanujanLimits.lean | Convergence of mixed-corrected packets and their Gram entries; exact mean/covariance error; explicit covariance-decay implication to Mathlib RH. |
| RH/PrimePowerRamanujanClosure.lean | Complete mixed-conductor elimination preserves the target-membership condition. |
| RH/GlobalLogDilation.lean | Absolutely convergent global logarithmic dilation; explicit contractive damping; legal Neumann inverse. |
| RH/RamanujanSchurLogZero.lean | Exact zero-test remainder for screened covariance; filtered source, convergence, legality, and quantitative error comparison. |

All declarations below have ordinary Lean proofs. No sorry, admit, custom
axiom, unproved analytic provider, or numerical approximation is introduced.
The final publication checkpoint performs the full Bazel/BuildBuddy acceptance
check; the commit and invocation are reported by that checkpoint.

## 1. Full Schur correction and convergent families

Write V for CoefficientStabilization.closedSpace, R_q for
ramanujanPacketHilbert q, and C_N for mixedSpace (Icc 2 N).
The mixed conductors are precisely the non-prime-powers in that window.
Let C be the closure of the increasing union C_N.

In namespace RiemannResearch.RH.Pareto.PrimePowerSchur:

- screenedPacket_tendsto:
  R_q - P_{C_N} R_q tends to R_q - P_C R_q in the complete norm.
- screenedPacket_norm_sq_decomposition:
  ||R_q - P_{C_N} R_q||^2 =
  ||R_q - P_C R_q||^2 + ||P_C R_q - P_{C_N} R_q||^2.
- screenedPacket_gram_tendsto: every fixed corrected Gram entry converges.
- limitScreenedPacket_inner_one: the limiting source is still Lambda(q).
- screenedPacket_mem_closedSpace and limitScreenedPacket_mem_closedSpace:
  every finite correction and its limit are legal for q >= 2.

These convergence statements are unconditional. They do not assert that
the target residual vanishes.

## 2. Prime-power reduction without losing the target

Let W be screenedPrimeClosure, the closed span of R_q - P_C R_q over
prime powers q >= 2. Full screening S = I - P_C satisfies:

- fullScreening_closedSpace_mem: S(V) is contained in W.
- screenedPrimeClosure_le_closedSpace: W is contained in V.
- fullScreening_one: S(1) = 1.
- one_mem_screenedPrimeClosure_iff: 1 belongs to W iff 1 belongs to V.
- riemannHypothesis_of_one_mem_screenedPrimeClosure: membership in W implies RH.

This justifies removing mixed conductors AFTER their full projection correction.
It does not justify deleting uncorrected mixed columns. The full correction
need not be computable from any fixed finite matrix; its exact finite-stage
projection remainder is retained above.

No reverse implication from RH is added. Existing reverse criteria that
require a NaturalApproximation provider keep that boundary.

## 3. The complete covariance is the remaining arithmetic quantity

For a finite window s and coefficients a on its prime powers, put

  v = sum_q a_q (R_q - P_{C_s} R_q),
  b = sum_q a_q Lambda(q),
  C(a) = sum_{q,r} a_q a_r
    ( <R_q-P_{C_s}R_q, R_r-P_{C_s}R_r> - Lambda(q)Lambda(r) ).

The theorems screenedCovariance_eq, screenedCovariance_nonneg, and
screened_error_mean_covariance prove

  C(a) = ||v||^2 - b^2 >= 0,
  ||1-v||^2 = (1-b)^2 + C(a).

riemannHypothesis_of_screened_covariance proves RH from b_N -> 1 and
C(a_N) -> 0 for legal finite windows. Neither convergence hypothesis is
silently supplied. In particular, pointwise Gram-entry convergence does not
give convergence of growing quadratic forms with varying coefficients.

## 4. A global legal (I - log_*) filter

For unscaled floor dilation T_m f(n) = f(floor(n/m)), define mathematically

  L_sigma = sum_{m>=2} [Lambda(m)/log(m)] m^(-sigma) T_m.

The formal definition uses the isometry U_m = D_m/sqrt(m), where D_m=m T_m:

  globalLog s = sum_{m>=2} [Lambda(m)/log(m)] m^(-s) U_m,
  floorLog sigma = globalLog (sigma + 1/2).

summable_logTerm_norm and floorLog_partial_tendsto prove absolute
operator-norm convergence for sigma > 1/2. The proof uses
0 <= Lambda(m)/log(m) <= 1 and the ordinary p-series, with no RH input.

At sigma=3/2, the finite inequality

  sum_{m=2}^{N+1} 1/m^2 <= 3/4 - 3/(2(N+2))

gives globalLog_two_norm_le: ||L_{3/2}|| <= 3/4.
Set F = I-L_{3/2}. The Neumann inverse converges, and

- logFilter_mul_inverse and logFilter_inverse_mul give both inverse identities.
- logFilter_mem_iff gives F(f) in V iff f in V.
- logFilter_norm_lower and logFilter_norm_upper give
  (1/4)||f|| <= ||F(f)|| <= (7/4)||f||.
- globalLog_inner_one and logFilter_inner_one give exact source scaling.
  The multiplier 1-meanFactor(2) is strictly positive.

Here meanFactor(s) is the convergent arithmetic sum
sum_{m>=2} [Lambda(m)/log(m)] m^(-s)/sqrt(m), proved by meanTerm_hasSum.
Identification with log zeta(s+1/2) is not needed or formalized here.
This Dirichlet-convolution logarithm is not the Banach logarithm of one
floor-dilation operator.

The sharper sigma=1 contraction estimate from log zeta(3/2), the critical
sigma=1/2 domain analysis, and the undamped obstruction remain outside this
formalized package.

## 5. Joining the filter to the Schur and zero phases

In namespace RiemannResearch.RH.Pareto.RamanujanSchurLogZero:

- logFilter_screenedPacket_tendsto transports the convergent corrected family.
- logFilter_screenedPacket_inner_one and
  logFilter_limitScreenedPacket_inner_one retain the source
  (1-meanFactor(2))*Lambda(q).
- logFilter_screenedCombination_mem proves legality.
- logFilter_screened_error_bounds proves

  (1/16) [(1-b)^2+C(a)] <= ||F(1)-F(v)||^2
    <= (49/16) [(1-b)^2+C(a)].

- logFilter_tendsto_iff proves F(v_N)->F(1) iff v_N->1.

The target is F(1). The theorem does not replace it by 1. The bounded
invertible filter preserves the unresolved density problem.

For a finite family of actual zeta zeros with Re(z)>1/2,
screened_zeroTest_energy_exact identifies (1-b)^2+C(a) with the existing
signed zeroTestCharge plus the COMPLETE nonnegative Mellin integral remainder.
At b=1, screened_covariance_zeroTest_floor bounds C(a) below by that charge.

These are actual-zero certificates in the bounded Mellin half-plane.
Critical-line ordinates alone do not meet Re(z)>1/2. The separate
RamanujanZeroSignal ordinate asymptotics still retain their explicit
horizontal-energy/count-provider hypotheses. No spectral diagonalization
or growing-dimension uniform estimate is inferred from fixed-conductor
ordinate limits.

## Next mathematical obligation

Construct normalized prime-power coefficient families with b_N=1 (or b_N->1)
and prove decay of their complete screened covariance. Retain all signed
cross terms and the correction tail. A useful intermediate objective is a
uniform quadratic-form bound in the coefficient metric, not just entrywise
convergence or finite-head interpolation.

The checked filter allows equivalent transformed equations with an explicit
factor-16 bound on recovering squared error. It supplies a controlled change
of equations, not the missing covariance decay.

Provenance: the user's Full_Conductor_RH_Projection_Machinery research agenda;
existing finite Schur, Ramanujan/residue, increasing-projection, and legal
dilation modules; Mathlib Hilbert projection and p-series results.
The zero-certificate source attribution remains in RamanujanZeroCertificates.
No novelty claim is made.

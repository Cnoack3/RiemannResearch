# Uniform dual bound: proved restrictions and the remaining signed problem

Research continuation for Christian Noack, 22 October 2026.

## Status

The requested support-independent dual bound for all signed tests remains
**Open**. It has not been replaced by an assumption or by a nonnegative-test
claim. The following two unconditional results have been proved in Lean:

1. All signed finite-support tests satisfy a support-dependent bound whose
   squared constants are sublinear.
2. All nonnegative Q tests satisfy a uniform bound, including tests with
   infinite support.

Neither result supplies the full signed bound required by
QFiniteSupportDualCriterion.riemannHypothesis_of_finite_test_bound.
RH remains unproved in this continuation.

## Exact signed identity and support-dependent estimate

Write V for the actual closed full legal Q residue span and P_V for its
orthogonal projection. Let a_M = finiteHead M a. If E_M is the existing
Möbius exact-head vector, its legality and exact physical coordinates give

    <1,a_M>_Q = <E_M,a_M>_Q = <E_M,P_V a_M>_Q.

No signed term is removed in this equality. Cauchy--Schwarz gives

    |<1,a_M>_Q| <= C_M ||P_V a_M||_Q,
    C_M = ||E_M||_Q.

The norm is the complete Q norm, including all tails. The existing Möbius
energy results imply

    C_M^2 / M -> 0,
    C_M^2 < 8 M / zeta(2)  for M>0.

These are QFiniteSupportDualEstimates.exactHead_finite_test_pairing,
finiteHead_dual_bound, dualHeadConstant_sq_sublinear, and
dualHeadConstant_sq_lt. The sublinear result reuses the existing unconditional
Möbius asymptotic; it is not a new proof of that asymptotic.

The quantifier order matters: these estimates give a bound for each M.
They do not establish one finite bound for every M. Sublinear squared growth
alone does not imply boundedness.

## A genuine uniform bound for nonnegative tests

For K>=0 define the finite legal vector

    B_K = 4 sum_{k<K} g_{4^(k+1)}.

QNonnegativeDualBound.fourMajorant_sequence proves this exact physical
sequence formula; fourMajorant_mem_legalSpan proves actual legality.
The existing complete atom estimate

    ||g_d||_Q^2 <= 2 / (zeta(2) d),  d>=2,

gives

    ||g_{4^(k+1)}||_Q <= sqrt(2/zeta(2)) 2^(-(k+1)),
    ||B_K||_Q <= 4 sqrt(2/zeta(2)).

If 0<n<4^K, some k<K satisfies 4^k<=n<4^(k+1). At that conductor,
g_{4^(k+1)}(n)=n/4^(k+1)>=1/4; every other summand is nonnegative.
Hence B_K(n)>=1.

Take K=M+1, which covers the physical coordinates 1 through M. For a_M>=0,

    0 <= <1,a_M>_Q
      <= <B_K,a_M>_Q
       = <B_K,P_V a_M>_Q
      <= ||B_K||_Q ||P_V a_M||_Q.

The resulting theorem is

    QNonnegativeDualBound.nonnegative_finite_test_uniform_dual_bound.

Its constant 4 sqrt(2/zeta(2)) is independent of both M and a.
Finite-head convergence and continuity of the full projection give

    |<1,a>_Q| <= 4 sqrt(2/zeta(2)) ||P_V a||_Q

for every nonnegative a in QHilbert, without finite support. This is

    QNonnegativeDualBound.nonnegative_uniform_dual_bound.

In the Lean realization, a n is the normalized lp coordinate corresponding
to physical n+1. The normalization multiplies physical values by a strictly
positive square root, so the sign condition has the same physical meaning.

## Why this does not prove the signed estimate

The comparison <1,a_M><=<B_K,a_M> requires a_M>=0. For signed tests,
the summands can cancel. Replacing a by its absolute value changes the
denominator to ||P_V |a|||, for which no suitable upper bound by ||P_V a||
has been established.

Bounded majorants also do not give bounded exact-head interpolants.
A limiting majorant B in V may satisfy B>=1 without B=1. Subtracting the
excess B-1 would require proving that excess belongs to V; with B in V,
that is equivalent to the missing target membership.

An elementary example illustrates this distinction (explanatory, not a new
Lean declaration). In R^2 take target t=(1,1), V=span(1,2), and b=(1,2).
Then b>=t and the orthogonal projector onto V is positive. Nevertheless
a=(2,-1) has P_V a=0 and <t,a>=1. Thus even a positive projector and a legal
majorant do not imply a signed dual bound.

The outstanding arithmetic obligation remains

    exists C, forall M a,
      |<1,finiteHead M a>_Q|
        <= C ||P_V(finiteHead M a)||_Q,

with no sign restriction and one constant independent of M. The existing
closure/RH consumers remain conditional research reductions.

## Verification and provenance

Source: the user's uniform-dual-bound request and the prior
UnitSignalFiniteTestResearch20261022.md reduction. The geometric majorant
argument is an elementary construction developed in this continuation;
no claim of mathematical novelty is made. Existing arithmetic providers
are cited by their owning Lean imports.

The combined candidate passed in job_EBU77w9LrkbKruhd-pJ4_vJFynthC18o:
exit code 0, server-reported checking duration 7.252 seconds.

After saving the separate source modules and shared finite-head lemmas,
the import and axiom audit passed in job_lcka8m2T4Zf526dmj0iDIVHRMpeV6j_I:
exit code 0, server-reported verification duration 18.865 seconds and queue
delay below 0.01 seconds. Eleven key declarations, including the two
uniform nonnegative bounds and the signed estimate, reported only propext,
Classical.choice, and Quot.sound. Their substantive hypotheses were also
reviewed directly; no target-closure hypothesis is hidden in these estimates.

The active workspace was reused without an opening request in this task.
Queue times and server durations above exclude deliberate polling delays.
Final aggregate/affected-source validation and publication are governed
by the checkpoint receipt, not by the successful candidate alone.

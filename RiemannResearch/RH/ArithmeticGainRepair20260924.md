# Directed arithmetic repair after the PNT/dichotomy audit
Date: 2026-09-24
Starting commit: 789bf521d697499fbab10e2ca6b3c79c1d8deb68

## Outcome

The previous module compiled successfully. Its obstruction was mathematical:
sublinear energy does not exclude divergence. This continuation attacks the
actual arithmetic vectors rather than changing or bypassing that obstruction.

New Lean results give an exact cancellation in the canonical capacity gain,
a harmonic upper bound for its normalized denominator, and a finite lower
bound for the actual accumulated capacity. A second exact result identifies
the full-period mean of the surviving primitive remainder.

Unconditional RH was not obtained. No new RH-strength hypothesis was assumed
in the established identities and inequalities below.

## The actual capacity gain

Fix integers 1 <= N <= M. Let u_M be canonicalMobiusHilbert M, let
m_M be mobiusReciprocalSum M, and write

    v_(N,M) = tail_N((M+2)*rho_(M+2) - (M+1)*rho_(M+1)),

where rho_d is the actual normalized residue vector. Let Q_(N,M) be the
existing window capacity normal and let P_(N,M) denote orthogonal screening
onto the old complete-tail family u_N,...,u_M. Define

    a_(N,M) = inner(v_(N,M), Q_(N,M)),
    s_(N,M) = ||(I-P_(N,M)) v_(N,M)||^2.

The existing exact step is u_(M+1)-u_M = m_(M+1)*v_M before tail restriction.
The new identities prove

    oneStepDefect = -m_(M+1) * a_(N,M),
    oneStepSchur  = m_(M+1)^2 * s_(N,M),
    windowGain   = a_(N,M)^2 / s_(N,M).

The last equality uses the established finite theorem m_(M+1) != 0.
There is no division by an unproved nonzero quantity. The new proof also
establishes s_(N,M)>0.

This shows why reciprocal Mobius decay by itself does not estimate the
normalized gain: its explicit scalar factor cancels exactly. The vectors
and normal still contain the full residue/Gram structure; this is not a
replacement by independent variables or a diagonal-only covariance.

Principal declaration:
CoefficientStabilization.SignedCovariance.windowGain_eq_step_pairing_quotient
in RH/CanonicalMobiusWindowGainBounds.lean.

## The harmonic bound and accumulation target

The adjacent step is the negative raw consecutive-residue difference.
Transferring the established exact adjacent-residue energy formula gives

    ||v_M||^2 =
      H_(M+1) - (M+1)/(M+2) + adjacentResidueRemainder(M+1),

with 0 <= remainder <= (M+1)/(M+2). Tail restriction and screening do not
increase squared norm. Consequently the new theorems give

    0 < s_(N,M) <= H_(M+1),
    a_(N,M)^2/H_(M+1) <= windowGain(N,M).

All infinite physical tail contributions are retained.

The finite accumulated result is

    baseCapacity(N) + sum_{j<L} a_(N,N+j)^2/H_(N+j+1)
      <= windowCapacity(N,N+L).

Declarations:
- consecutiveResidueHilbert_energy_exact;
- windowStepScreened_energy_pos;
- windowStepScreened_energy_le_harmonic;
- windowGain_harmonic_source_lower;
- windowCapacity_harmonic_source_lower.

Existing fixed-head capacity divergence implies Mathlib RiemannHypothesis.
Thus divergence of the displayed source sum, for one fixed positive N,
would suffice. This is a sufficient lower-bound strategy, not a claimed
equivalence with RH. No unconditional divergence provider was obtained.

The signed source involves the actual growing optimizer Q_(N,M); it is not
an ordinary partial sum of mu. A quantitative lower bound on accumulation
of these sources is the unresolved step in this attempt.

## Exact primitive-remainder mean

Let P_N(k) be rawMobiusCenteredPrimitive N k and let H_N(k) be
rawMobiusPrimitiveJumpCross N k. Define C_N(k) to be the centered raw
residue combination, including coordinate zero.

The new calculation keeps both signed terms:

    H_N(k+1) - m_N*P_N(k+1)
      = C_N(k)^2 - [P_N(k+1)C_N(k+1) - P_N(k)C_N(k)].

For every common period Q of 1,...,N, both boundary primitives vanish.
Therefore, exactly,

    sum_{k<Q} [H_N(k+1)-m_N*P_N(k+1)] = sum_{k<Q} C_N(k)^2.

At Q=N!, the existing variance identification yields

    mean[H_N(k+1)-m_N*P_N(k+1)]
      = (1/12) sum_{q=2}^N J_2(q)
          (sum_{d<=N, q|d} mu(d)/d)^2
      >= #{p prime: N/2 < p <= N}/16.

Principal declarations in RH/RawMobiusPrimitivePeriodMean.lean:
- rawMobiusPrimitiveRemainder_period_sum;
- rawMobiusPrimitiveRemainder_factorial_mean_eq_jordan;
- rawMobiusPrimitiveRemainder_factorial_mean_ge_prime_count.

This rules out simply discarding the combined remainder as uniformly
nonpositive. It does not rule out a subpower Pareto bound: a uniform
period mean and the weighted growing middle window are different quantities.

## Verification and persistence

The coherent candidate completed with exit code 0, verified=true
(job_i8i-CKovNg-wkjUUW97HYSbKTPlgtAyQ).
All six principal axiom audits returned only propext, Classical.choice,
and Quot.sound. There are no placeholders, project-local axioms, or assumed RH.

General screening calculus is saved in
Analysis/FiniteGramScreeningCalculus.lean. The arithmetic results occupy the
two subject modules named above. The final checkpoint validates their focused
imports and exports before publishing.

The cofinal bounded actual-residual-tail estimate and the full raw subpower
budget from previous turns remain open. The new finite lower bound does not
supply either estimate.

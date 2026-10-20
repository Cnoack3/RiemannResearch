# Actual floor CRT carries and orthogonal screening

Source: Christian Noack's *CRT Carries and Squarefree Residual Exhaustion*,
19 October 2026, sections 2, 3, and 5, and the subsequent request to connect
the previously checked linear-map lemmas to the actual arithmetic functions
and the actual Q-Hilbert orthogonal projection.

## Exact arithmetic and the actual Hilbert encoding

Write g_d(n)=(n mod d)/d. The carry is defined by the integer floor

    κ_{p,q}^{a,b}(n) = floor(a g_p(n)+b g_q(n)).

For positive natural p,q and integer a,b,t satisfying aq+bp=1+tpq,

    κ = tn-a floor(n/p)-b floor(n/q)+floor(n/(pq)),
    g_{pq}=a g_p+b g_q-κ.

The integer coefficients are essential. Positivity and the displayed
coefficient equation suffice; primality is unnecessary. Coprime conductors
have such coefficients by the ordinary Bezout identity, also formalized.
Thus the same results apply when an old conductor is composite.

The floor carry is uniformly bounded, including without a CRT hypothesis.
`QCRTCarry.qCarry` uses `encodeQ` on that floor-defined sequence directly.
Its evaluation theorem and its equality with

    a • qResidue p + b • qResidue q - qResidue (p*q)

are proved, rather than assumed. Every norm and pairing is the existing
complete inverse-square Q-Hilbert norm, including the infinite tail.

## What orthogonal screening proves

For an actual submodule V with orthogonal projection and qResidue p,
qResidue q in V, the operator is literally

    R_V = ContinuousLinearMap.id - V.starProjection.

The main identity is

    R_V(qCarry p q a b) = -R_V(qResidue (p*q)).

Consequently all valid representatives, including arbitrary two solutions
of the CRT coefficient equation, give the same screened vector. Parameterizing
their difference as a shift is not needed for this conclusion.

The finite algebra also gives:

- Exact projection of the raw carry onto the old space and membership
  equivalence: the carry belongs to V exactly when the composite atom does.
- Equal screened norms, a contraction bound by the composite norm, and the
  complete conductor bound inherited from `qResidue_norm_sq_le_two_div`.
- The full six-term signed raw Gram identity and the exact Pythagorean
  decomposition into old-space energy and screened energy.
- Screened cross-Gram entries equal those of the corresponding composite
  columns; residual target correlations have the opposite sign.
- Adjoining a carry or its composite atom gives exactly the same subspace.
  Thus all target projections and approximation errors agree.
- The optimally refitted vector and its exact Rayleigh gain agree. Changing
  CRT representatives changes neither of these quantities.
- Finite screened block synthesis retains its complete signed cancellations;
  the results include every indexed old conductor, including composite ones.

The primorial consumer uses the repository's existing `primorialStage`,
whose generators are all divisors greater than one of `primorialPeriod`.
It does not replace that dictionary by prime atoms alone.

## Integration with the newer carry-block results

`QCRTCarryBlockBridge` proves agreement with the existing
`QCarryScreenedBlock.pairVector`, screening operator and fullBlock.
The complete divisor-stage equality and complete trace bound therefore
apply to the directly encoded floor vectors. This connects the new
projection results to the independently developed block theory on main.

## Verification and mathematical boundary

The modules are checked as project sources on the user's Lean server, then
published only through the checkpoint gate, which also validates integration
with newer main changes. The primary arithmetic and projection statements
are unconditional finite results with their ordinary explicit hypotheses.
They contain no residual-exhaustion assumption and imply no new asymptotic
lower bound by themselves.

The open research obligation is still quantitative cumulative gain or an
equivalent signed absorption estimate. Representative invariance identifies
the finite object that such an estimate must control; it does not prove that
the limiting legal residual vanishes.

# CRT–Pareto coordinates: verified finite reduction and remaining obligation

Date: 2026-09-18.

## Result status

The missing RH-strength subpolynomial bound is **Open**. This continuation
does not prove RH. It proves a uniform comparison that eliminates the
infinite progression tails, a complete coefficient-level description of
exact-head and zero-mean feasibility, and a formal obstruction to an
unconstrained coordinate shortcut.

All substantive results are proved from existing project/Mathlib
declarations. The RH endpoints are explicitly conditional research
reductions; their cost hypothesis has no proved provider.

## Exact energy and the first-period theorem

For a real sequence F of positive integral period Q, write

- S(r) = sum of F(n) over 1 <= n <= r;
- m = S(Q)/Q;
- B(r) = S(r) - r*m;
- E(F) = sum over r >= 1 of 2/(r*(r+1)*(r+2)) * (S(r)^2/r).

Thus E is exactly the project's conditionalMeanSquare, with the original
Cesaro means and probability weights. Assume m=0. Define the finite form

  A_Q(F) = sum over 1 <= r <= Q of
             2*B(r)^2 / (r^2*(r+1)*(r+2)).

The new theorem zeroMean_firstPeriod_enclosure proves

  A_Q(F) <= E(F) <= (9/8)*A_Q(F).

firstPeriodEnergy_eq_prefix proves that A_Q is exactly the first Q terms
of E. The constant is uniform in Q and F; no coefficientwise absolute
values or replacement by a uniform residue average occurs. In particular,
squaring the actual signed cumulative synthesis retains all mixed terms.

Proof: put a(r)=2/(r^2*(r+1)*(r+2)). For 1 <= r < Q, the progression
coefficient M_Q(r)=sum_{k>=0} a(Q*k+r) satisfies

  a(r) <= M_Q(r) <= (9/8)*a(r).

Indeed a(Q*k+r) <= a(r)/(k+1)^4, and for n>=2,

  1/n^4 <= (1/8)*(1/(n-1)-1/n).

The tail telescopes to at most 1/8. The terminal residue r=Q has B(Q)=0,
so it contributes zero without requiring this progression estimate.
Summing the nonnegative diagonal contributions proves the theorem.

The firstPeriod_subpolynomial_iff theorem transfers subpolynomial growth
in either direction for the same mean-zero periodic family. It does not
supply that family's growth bound.

## Complete normalized coefficient constraints

Let S be a finite set of integers d>=2, every d dividing Q>0, and put

  F(n) = sum_{d in S} c_d * ((n mod d)/d).

This is an actual legal Pareto witness and is Q-periodic. Missing
coefficients are interpreted as zero. For Y>0,

  [F(n)=1 for 1<=n<=Y, and periodMean(F,Q)=0]

is equivalent to all three algebraic constraints

  sum_{d in S} c_d/d = 1,
  sum_{d in S} c_d = 1,
  c_d = -mu(d) for 2<=d<=Y, interpreting c_d=0 when d is absent.

This is normalizedResidueSynthesis_zeroMean_exact_head_iff.
The converse is proved using finite Mobius inversion, not assumed.
The modulus-one coefficient is excluded because its residue function
vanishes identically.

For S={2,...,D} and Y<=D, exact_zeroMean_head_high_moments further proves

  sum_{Y<d<=D} c_d/d = sum_{1<=d<=Y} mu(d)/d,
  sum_{Y<d<=D} c_d   = sum_{1<=d<=Y} mu(d).

These signed obligations expose the arithmetic cancellation required from
the adjustable high coefficients. Every prime p<=Y divides the common
support conductor Q.

The exact increment formula is also proved:

  F(n)-F(n-1) = sum c_d/d - sum_{d|n} c_d,       n>0.

Consequently increments are constant on each gcd(n,Q) class.
The defect's second differences inherit this exact compatibility.
Thus CRT defect coordinates cannot be chosen independently.

## A verified obstruction to the free-coordinate shortcut

Ignore coefficient feasibility and set B(r)=r for r<=Y and B(r)=0 later,
with Q>Y. Then the finite diagonal objective is exactly

  A_Q(B) = Y/(Y+2),

and its complete progression objective is at most (9/8)*Y/(Y+2).
This looks strong enough if one mistakes arbitrary defect vectors for
legal witnesses.

cutoffDefect_not_realizable proves that, for Y>0 and Q>=Y+4,
this vector cannot arise from a legal, mean-zero, Q-periodic witness.
The proof uses the exact legal reflection

  F(n)+F(Q-1-n)=F(Q-1).

The cutoff forces F(1)=1 and F(Q-2)=F(Q-1)=0, contradicting this identity
at n=1. legal_reflection_at_period establishes the identity for any
actual positive period of the legal witness.

This refutes that specific shortcut. It neither refutes RH nor rules out
other constrained CRT constructions.

## The remaining explicit finite problem

For arbitrarily large Y, construct a finite coefficient set S, coefficients
c, and a common conductor Q satisfying the three algebraic constraints
above and, for every epsilon>0,

  A_Q(F) <= C_epsilon * Y^epsilon

eventually along one cofinal family. Here A_Q is an entirely finite
rational-weighted quadratic expression in the signed coefficients.
A continuous quadratic minimization without the legal constraints does
not discharge this obligation. Computing finitely many examples also
would not give the required uniform asymptotic theorem.

riemannHypothesis_of_subpolynomial_residue_coordinates connects exactly
these explicit coefficient conditions and the remaining cost bound to
Mathlib's RiemannHypothesis. The only new RH-strength input is hcost; it
is a hypothesis, not a proved theorem. Ordinary foundational axiom audits
do not discharge hypotheses appearing in a theorem's type.

## Files and verification

- RH/CRTFirstPeriodEnergy.lean: kernel bound, 9/8 enclosure,
  first-period identity, comparison and conditional RH consumer.
- RH/CRTLegalCoordinates.lean: complete finite feasibility equivalence,
  high moments, prime conductor necessity, gcd compatibility.
- RH/CRTCoordinateLegality.lean: legal reflection, inexpensive forbidden
  coordinate vector, and explicit coefficient-level conditional endpoint.

The combined proof candidate compiled with no warnings. Axiom checks of
the energy enclosure, feasibility equivalence, high moments, gcd
compatibility, cutoff results, and RH consumer reported only propext,
Classical.choice, and Quot.sound. Publication additionally validates the
separate modules and affected project imports.

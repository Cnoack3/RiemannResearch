# Exhaustive squarefree exact-head geometry and the remaining RH estimate

Research continuation for Christian Noack. October 17, 2026.
Source: the supplied Squarefree_Lattice_Log_Exp_Theory_2026-10-16(1).md,
especially Sections 8, 9, and research targets 1, 3, and 5.
Base commit: de3660c827e46ba5a145f2acd93e8ba9e2134123.

## Result and scope

The exhaustive affine characterization in the supplied paper is now formalized.
The complete-Q optimizer is built from the actual Gram inverse of every
available compensated direction, including composite conductors formed from
old primes. The minimum and optimizer are independent of the chosen anchor.
Nested periods have an exact squared-displacement gain identity.

There are 27 new theorem declarations: one in
NormalizedResidueExactHeadCharges.lean, twelve in QResidueHeadSpace.lean,
and fourteen in QSquarefreeAffineHead.lean. No RH assumption is used for
the finite geometry. The final RH implication retains a uniform bound
on the actual optimized errors as an explicit Open hypothesis.

## Physical setting and support assumptions

Put
    Z = zeta(2), Q(n) = 1/(Z*n^2), g_d(n) = (n mod d)/d.
The actual QHilbert realization gives the complete positive-coordinate
Q norm. All physical sequences have auxiliary value zero at n=0.

Let V_L be the real span of g_d for 1<d dividing L. For the squarefree
application assume L>0 is squarefree, H>=1, an anchor r divides L with
H<r, and every squarefree d with 1<d<=H divides L. A primorial
containing all primes at most H satisfies the last support condition;
this elementary primorial specialization is not a new theorem here.

The geometric statements are slightly more general: they work for any
positive L satisfying the same low-conductor support assumption.
Squarefreeness of L is needed for membership in the squarefree legal span.

## The complete feasible space

Write
    S_H = sum_(1<=d<=H) mu(d)/d,
    B_(H,r) = -sum_(1<=d<=H) mu(d)*g_d + r*S_H*g_r,
    v_(d,r) = g_d - (r/d)*g_r.
The divisor-one atom is zero. The checked baseline equals one on 1,...,H.

Let I_(H,L,r) consist of every divisor d of L with d>H, d>1, and d!=r.
The checked equality is
    {F in V_L : F(n)=1 for 1<=n<=H}
      = B_(H,r) + span {v_(d,r) : d in I_(H,L,r)}.

Declaration: QSquarefreeAffineHead.exact_head_iff, expressed as membership
of F-B in the zero-head direction span. The span and all its directions
are actual QHilbert vectors.

The argument first proves a general finite-dictionary assertion.
For distinct conductors in a finite set s, all greater than one,
    sum_(d in s) c_d*g_d = 0 on 1,...,H
iff
    sum_(d in s) c_d/d = 0
and
    c_d=0 for each d in s with d<=H.
Möbius extraction supplies the low coefficients; evaluation at one gives
the reciprocal slope. Conversely, after the low coefficients vanish,
every remaining atom has its linear unwrapped head, so the zero slope
cancels the entire head.

Compensation then expresses every such combination in all the high
directions, with the anchor direction removed. This is exhaustive,
rather than a restriction to fresh-prime dilations of a fixed seed.

The compensated directions are linearly independent. Their independence
is proved using independence of the enlarged family consisting of the
anchor and all free residue atoms; it is not assumed as a Gram hypothesis.
The construction also handles an empty free-direction set.

Declaration QSquarefreeAffineHead.exact_head_forces_conductor proves
that any d<=H with d>1 and mu(d)!=0 must divide the actual period of an
exact-head vector. Thus missing low support cannot be repaired by
arbitrarily many large conductors.

## Complete-Q minimization and exact remainders

Set
    K_de = <v_(d,r),v_(e,r)>_Q,
    h_d = <v_(d,r),1-B_(H,r)>_Q.
Independence supplies the actual finite Gram inverse. If z*=K^(-1)h,
    F* = B_(H,r) + sum_d z*_d*v_(d,r),
    E(H,L) = ||1-B_(H,r)||_Q^2 - h^T*K^(-1)*h.

The Lean inverse uses the equivalent finite-dimensional linear
endomorphism rather than assuming that a supplied matrix is invertible.
QResidueHeadSpace.affineOptimizer_error_formula gives this exact value.
For every feasible F, the checked complete error identity is
    ||1-F||_Q^2 = E(H,L) + ||F-F*||_Q^2.
In particular F* is the unique global minimizer in the complete finite
feasible space. No physical periods, signs, correlations, or remainder
terms are dropped.

For L dividing K, with the same H and available anchor, the exact gain is
    E(H,L) = E(H,K) + ||F*_(H,L)-F*_(H,K)||_Q^2.
Declaration: QSquarefreeAffineHead.minimumError_period_gain.
Monotonicity follows from the nonnegative last term.

Changing an admissible anchor changes the coordinates but preserves both
the actual optimum error and the actual optimizer. Declarations:
minimumError_anchor_independent and optimizer_anchor_independent.

These are finite Hilbert-space identities. The gain identity alone
does not show that a limiting minimum is zero, or that the minima stay
uniformly bounded when H grows.

## The checked conditional RH consumer

QSquarefreeAffineHead.riemannHypothesis_of_bounded_affine_minima
takes squarefree periods L_N and anchors r_N with
    H_N=N+1, H_N<r_N dividing L_N,
    all squarefree conductors <=H_N available,
    E(H_N,L_N)<=B for one real B and every N.
It proves Mathlib's RiemannHypothesis by applying the existing checked
squarefree bounded-exact-head averaging theorem to these actual optimizers.

Classification: conditional research reduction.
Open provider: the displayed uniform complete-Q minimum bound.

The support, head-size, positivity, and squarefreeness assumptions are
explicit in the theorem type. The inverse-Gram solvability and the full
affine minimization are proved, not extra provider assumptions.
Axiom inspection does not discharge the local uniform-bound hypothesis.

This continuation does not formalize the supplied all-order nilpotent
convolution algebra, the triangular cumulant formulas, the full
RH-to-density direction, or the analytic subpolynomial zero-witness
criterion. The earlier two-prime log/exp development remains available.

## Verification evidence and publication gate

Server job job_wRrhOcFOyQcOmFp9pn6-eQZRPXHNccv0 succeeded with exit code 0.
It built the final new squarefree module and checked imports of the
general head-space module and amended coefficient module.

The seven selected axiom inspections, including the conditional RH
consumer, returned only propext, Classical.choice, and Quot.sound.
No sorry, admit, project-local axiom, or unsafe declaration was added.

Publication is through the mandatory server checkpoint, which validates
the aggregate project and changed modules before pushing the exact source.
The final checkpoint job and published commit are reported in the
accompanying response. The snippet check is not described as a full
project validation.

## Next research obligations

1. Establish a cofinal bound on E(H,L), allowing period growth independently
   of H and all high composite conductors. The uniform bound above has a
   checked RH consumer. The weaker all-positive-exponent subpolynomial
   condition in the supplied paper still needs its analytic consumer formalized.
2. Sum the exact period gains for a fixed head, then compare those gains
   across increasing heads. A positive gain at every finite step is
   insufficient: the remaining baseline energy must be controlled.
3. Formalize the fixed-head infinite affine projection and approximation
   by finite exact-head vectors. Use the complete Q norm and continuous
   physical evaluations; coefficientwise or Haar limits do not supply it.
4. Develop the general squarefree convolution log/exp algebra and its
   triangular cumulant coordinates. Its physical application can now
   target the already verified exhaustive affine minimum, rather than a
   restricted fresh-prime packet space.

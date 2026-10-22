# Sharp Q comparison and squarefree exact-head converse

Source: user-provided CRT squarefree-span request, 13 October 2026.

Let r_d(n)=(n mod d)/d, P(n)=1/(n(n+1)), and
Q(n)=1/(zeta(2)n^2), for n>=1. These modules use the actual weighted
Hilbert realizations, with coordinate zero anchored and carrying no mass.

For an L-periodic residual R, define B_L(R)=sum_{a=1}^L R(a)^2/a^2.
The complete Q progression weights satisfy
1/(zeta(2)a^2) <= W_L(a) <= 1/a^2 for 1<=a<=L.
Consequently B_L(R)/zeta(2) <= ||R||_Q^2 <= B_L(R).
Uniform boundedness and convergence to zero are equivalent for the two
energies, even for changing periods. The zero residue is represented by L.

## Exact-head criterion

The formal sufficient theorem is
`Pareto.riemannHypothesis_of_squarefree_span_bounded_tail`
in `CRTSquarefreeBoundedTail.lean`. Its assumptions are exactly:
- M_j tends to infinity;
- every L_j is squarefree;
- F_j belongs to the algebraic span of r_d with d|L_j and d>=2;
- F_j(n)=1 for 1<=n<=M_j;
- the finite sums from M_j+1 through L_j of |1-F_j(a)|^2/a^2
  have a common real upper bound.

The conclusion is Mathlib's actual RiemannHypothesis proposition.
Periodicity, individual boundedness, the Hilbert encoding, and the
closure-to-RH Mellin implication are proved, not extra assumptions.

Boundedness of the displayed tail is sufficient. The proof passes through
bounded Hilbert vectors and increasingly exact coordinates to closed-span
membership. It does not claim that this same family converges strongly,
or that its own tail energies tend to zero.

## Geometric converse

`Analysis.exists_near_with_same_finite_observations` proves that a vector
in a subspace closure admits arbitrarily close subspace approximants with
any finite list of continuous linear observations exactly preserved.
Its proof constructs a continuous right inverse on the finite-dimensional
observation image. There is no uniform-in-head-length correction estimate.

`Pareto.squarefree_exact_head_small_tail_of_closure` specializes this:
for every head length M and every epsilon>0, squarefree closure membership
gives a finite squarefree-period F exact through M and with reciprocal
tail energy <epsilon.

`Pareto.squarefreeClosure_iff_exact_head_tail_bound` identifies squarefree
closure membership with one uniformly bounded family of exact-head tails.
The algebraic common-period space is proved equal to the literal span of
all normalized residues indexed by squarefree d>=2.

`ZetaTwoProbability.qSquarefreeClosure_iff_exact_head_tail_bound`
proves the same characterization in Q, using both directions of the
complete P/Q norm comparison.

## Remaining arithmetic and analytic obligations

These are verified reductions and geometric equivalences, not a proof of RH.
Constructing a family satisfying the uniform arithmetic tail bound is Open.
The analytic implication RH -> squarefree residue density is not proved by
these modules. Repository results currently keep that implication as a
separate provider; no such provider is assumed in the sufficient theorem
or the geometric converse above. No full equivalence with RH is claimed.

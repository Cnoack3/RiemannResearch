# Universal Pareto/Q and dual Ramanujan transfer — 23 October 2026

Source: the user's request to transfer the original Pareto/Q results into dual
Ramanujan coordinates and strengthen the original statements. The algebraic
packet identities and the sequence-preserving change of law are existing
repository constructions. The Hilbert-space projection identities use standard
Mathlib orthogonal projection theory. No novelty claim is made.

## Master statement

Let P(n)=1/[n(n+1)] and Q(n)=1/[zeta(2)n^2], n>=1. Write

    g_d(n) = (n mod d)/d,
    R_q(n) = sum_{d|q} mu(q/d) d g_d(n).

The packet R_q is the integrated Ramanujan packet, not the ordinary unintegrated
Ramanujan sum. Its exact inverse is

    g_d = (1/d) sum_{q|d} R_q,  d>0.

Let S be ANY set of positive conductors such that, whenever d belongs to S,
q divides d and q>1, q belongs to S. Conductor one can be omitted, since both
g_1 and R_1 vanish. There is no finiteness, independence, or exhaustion hypothesis.

In EACH of the actual complete Hilbert spaces H=L2(P) and H=L2(Q),

    span{g_d : d in S} = span{R_q : q in S}.

Consequently their norm closures, orthogonal complements, and orthogonal
projections are exactly equal in the SAME metric. Every theorem about one of
these subspaces can be transported by rewriting this equality. This is stronger
than a finite-prefix or constant-target transfer.

The declaration names in RH/RamanujanHilbertTransfer.lean are:
- RamanujanTransfer.q_span_eq and p_span_eq;
- q_closure_eq and p_closure_eq;
- q_orthogonal_eq;
- q_projection_eq and p_projection_eq.

All-positive conductors, all squarefree conductors above one, and arbitrary
divisor ideals satisfy the structural condition. A family consisting only of
selected composite conductors need not satisfy it; its divisor closure supplies
the matching full packet dictionary.

## Change of probability law

The existing bounded invertible map toPareto preserves the entire physical
sequence. For EVERY Q vector f and EVERY packet family S, without divisor
closure,

    f in closure_Q span{R_q:q in S}
      iff toPareto(f) in closure_P span{R_q:q in S}.

This is packet_closure_transfer. For a divisor-closed S,
legal_closure_iff_ramanujan combines this equivalence with the exact basis
change. It applies to every target f, including the constant target.

The four closure questions (P/residue, P/packet, Q/residue, Q/packet) are thus
equivalent with the same physical target. Numerical inner products, Gram
matrices and orthogonal projections across the two DIFFERENT metrics are not
identified.

## Strong dual observation formulation

For ANY linear functional ell:H->R, ANY z in H, and any two indexed families
v,w spanning the same algebraic subspace,

    [forall i, <v_i,z> = ell(v_i)]
      iff [forall j, <w_j,z> = ell(w_j)].

There is no finiteness, linear independence, completeness, or continuity
hypothesis. This is the strengthened original observation theorem
FiniteGramCapacity.observations_iff_of_span_eq in
Analysis/FiniteGramBasisInvariance.lean. The existing finite inverse-Gram
capacity invariance now reuses this general theorem.

The concrete Pareto and Q versions are p_dual_observations_iff and
q_dual_observations_iff. Taking ell=0 gives annihilator equivalence; taking
ell(x)=<x,target> gives all moment matching constraints for an arbitrary target.

For Q, packet_moment and residue_moment prove the exact arithmetic conversions

    <f,R_q>_Q = sum_{d|q} mu(q/d)d <f,g_d>_Q,
    <f,g_d>_Q = (1/d) sum_{q|d} <f,R_q>_Q.

The finite inverse-Gram quadratic forms transfer when the observation data
transform with the dictionary. The existing
capacity_evaluation_eq_of_span_eq covers every linear observation functional,
not just the reciprocal or constant source. A finite basis used with an inverse
Gram matrix must still be linearly independent; adding the zero conductor-one
vector does not create an invertible Gram matrix.

## The residual is retained exactly

For ANY packet family S, let V be its closed Q span. The new declarations
q_moments_eq_projection and q_dual_error_exact prove

    <R_q,f>_Q = <R_q,P_V f>_Q  for q in S,

and, for EVERY v in V,

    ||f-v||_Q^2 = ||P_V f-v||_Q^2 + ||f-P_V f||_Q^2.

Thus the moment coordinates identify the projected vector. They cannot discard
the orthogonal remainder. The full triangular/Mobius coefficient probes that
separate the ambient Hilbert space are a different coordinate family.

In particular this transfer does not establish 1 in V, a uniform complete
approximation-energy bound, pointwise projection positivity, or RH. Those
arithmetic questions retain their exact original content after the basis change.

## Stronger original Pareto/Q comparison

The existing exact identity is

    ||toPareto(f)||_P^2
      = zeta(2)||f||_Q^2 - zeta(2) C(f),

where the entire infinite correction is

    C(f) = sum_{n>=1} Q(n)|f(n)|^2/(n+1).

Suppose the physical sequence vanishes for n<M. The new theorem
normCorrection_le_of_head_zero proves

    C(f) <= ||f||_Q^2/(M+1).

Hence toPareto_norm_sq_lower_of_head_zero proves

    zeta(2) M/(M+1) ||f||_Q^2
      <= ||toPareto(f)||_P^2
      <= zeta(2)||f||_Q^2.

For M>=1, zetaTwo_mul_norm_sq_le_head_toPareto_norm_sq gives the useful form

    ||toPareto(f)||_P^2
      <= zeta(2)||f||_Q^2
      <= (1+1/M)||toPareto(f)||_P^2.

The earlier global reverse factor was two. The improved factor tends to one
as the first possibly nonzero coordinate escapes to infinity. If an approximant
equals its target through H, apply this with M=H+1 to its error: the reverse
factor is 1+1/(H+1). No bound on the infinite tail is assumed in obtaining the
comparison.

norm_gap_bounds_of_head_zero retains both signs and the exact correction:

    0 <= zeta(2)||f||_Q^2 - ||toPareto(f)||_P^2
      <= zeta(2)||f||_Q^2/(M+1).

These results are in RH/ZetaTwoParetoTransfer.lean. Their hypotheses concern
only vanishing finite coordinates; they do not assume RH or any unproved
analytic provider.

## Verification interpretation

The declarations are ordinary Lean proofs with no sorry, admit, unsafe
declaration, or project-local axiom. Their structural hypotheses remain visible
in their exact types. The final server checkpoint certifies the published
project delta and its required validation scope; isolated proof checks alone
are not a claim of project publication.

Mathlib reference supporting the standard projection machinery:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Projection/Submodule.html

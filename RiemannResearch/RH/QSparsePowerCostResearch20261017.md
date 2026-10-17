# Sparse squarefree power costs: iteration 1 of 5

Research for Christian Noack. 17 October 2026.
Program identifier: sparse-power-cost-20261017.
Base revision: 8b382951737e8d935d0adb652942a35c581451c7.

## Outcome and precise gap

The full sparse power-cost assertion has not been proved. The infinite
annihilator mean-zero implication also remains open.

This pass chooses sparse power costs because the actual complete Q energy
gives a numerical quantity and an exact affine optimization problem to attack.
It establishes the exponent-one case unconditionally and identifies precisely
what any smaller exponent would buy. This is a mathematical baseline, not
a proof of RH or a power saving below exponent one.

Let Q(n)=1/(zeta(2)n^2) on positive integers, let g_d(n)=(n mod d)/d,
and let S be the real algebraic span of squarefree g_d with d>=2.
For real a, write SPC(a) for:

    for every c>0 and every cutoff N, there exist n>=max(1,N)
    and F in S, with F(k)=1 for 1<=k<n, such that
        ||1-F||_Q^2 < c*n^a.

There is no assumed uniform norm bound, prescribed family, or positive-density
condition on the chosen heads.

## The explicit prime-anchor construction

For an integer H>=0, set
    s_H = sum_(1<=d<=H) mu(d)/d,
    B_H = -sum_(1<=d<=H) mu(d) g_d + (H+1)*s_H*g_(H+1).

The existing canonical Mobius identity gives B_H(k)=1 for 1<=k<=H.
Every nonzero low-conductor term has squarefree d. Therefore B_H belongs
to S whenever H+1 is squarefree; in particular it does when H+1 is prime.
The d=1 atom is zero. No nonsquarefree anchor is silently admitted.

The complete physical error is exactly
    ||1-B_H||_Q^2
      = sum_(k>=1) |1-B_H(k)|^2/(zeta(2)*k^2).
The head summands vanish. All other physical sites and signed cross terms
remain in this equality.

Under the exact identification of physical sequences, write C_H for the
existing canonical Pareto vector. Its established unconditional PNT theorem
gives
    ||C_H||_P^2/H -> 0,
    ||1-C_H||_P^2/H -> 0.
The complete comparison gives
    zeta(2)*||B_H||_Q^2 <= 2*||C_H||_P^2,
    zeta(2)*||1-B_H||_Q^2 <= 2*||1-C_H||_P^2.
Consequently both complete Q energies divided by H tend to zero.

Given c>0 and cutoff N, choose a prime p sufficiently large, put H=p-1,
and use F=B_H. Then F is squarefree legal, its exact head is k<p, and
    ||1-F||_Q^2 < c*p.

This proves SPC(1). Since n>=1, n<=n^a for a>=1, hence SPC(a) holds
unconditionally for every a>=1.

## What a fixed exponent actually implies

For a hypothetical zero s with beta=Re(s)>1/2, s!=1, the existing
localized Mellin theorem gives, for every squarefree legal exact head,
    C_s*n^(2*beta-1) <= ||1-F||_Q^2,
    C_s=(2*beta-1)/(zeta(2)*||s||^2)>0.

If SPC(a) holds and a<=2*beta-1, choose c=C_s.
Since n>=1,
    C_s*n^(2*beta-1)
       <= ||1-F||_Q^2
       < C_s*n^a
       <= C_s*n^(2*beta-1),
a contradiction.

Thus a positive fixed exponent a rules out zeros with
    beta >= (1+a)/2.
The unconditional a=1 result reaches beta>=1, consistent with the PNT
input. It does not establish a new zero-free vertical strip inside (1/2,1).

If a_j -> 0 and SPC(a_j) is available for every j, then every hypothetical
beta>1/2 is excluded by some a_j<2*beta-1. The checked consumer concludes
actual Mathlib RiemannHypothesis.

Open: an arithmetic provider for the exponents tending to zero.
Even proving SPC(a) for one fixed a in (0,1) would require a substantive
new arithmetic estimate; it does not follow from the sublinear baseline.

## Why the attempted shortcut stops

An o(n) estimate allows errors such as sqrt(n), which are much larger than
n^(1/4). It cannot be promoted to all positive exponents by selecting a
sparse subsequence. Similarly, inverse-logarithmic improvements for each
fixed logarithmic power do not justify choosing that power as a function
of n without quantitative threshold control.

Pointwise convergence on growing exact heads also supplies no Q-norm
bound. Neither argument closes the sparse-cost assertion.

This pass did not prove that signed prime-head averages have small cost;
their full correlations must still be controlled. It did not assume a
dimension-free inverse-Gram bound.

## Lean declarations and verification evidence

RH/QSquarefreeSublinearHeads.lean:
- exactHead_mem_squarefreeSpan
- toPareto_exactHead
- exactHead_sublinear
- exactHead_error_sublinear
- arbitrarily_small_linear_cost

RH/QSquarefreeSparsePowerCost.lean:
- SparsePowerCost
- sparsePowerCost_one
- sparsePowerCost_of_one_le
- zero_free_of_sparsePowerCost
- riemannHypothesis_of_sparsePowerCost_tendsto_zero

Established: squarefree legality for squarefree anchors, the two complete
Q sublinear limits, and SPC(a) for a>=1.
Conditional research reductions: the fixed-exponent zero-free consumer
and the exponent-sequence RH consumer, with SPC hypotheses explicit.

Server snippet job job_-kVpIudQXb1nXXGlvmXy2dWeIHvukHkw succeeded:
classification success, verified true, exit code 0.
Selected axiom reports for the unconditional power-cost range and both
consumers list only propext, Classical.choice, and Quot.sound.
The final project modules and integrated source must still pass the
publication checkpoint; the snippet alone is not project publication evidence.
The checkpoint terminal job and exact published commit accompany delivery.

## Best next attempt

Attack the complete signed Gram matrix of several prime-anchor canonical
heads sharing one fixed head, and compare this restricted family with the
exhaustive high-conductor affine space. For candidates F_i exact on the
same head and real coefficients b_i with sum b_i=1, the identity to retain is
    ||1-sum_i b_i F_i||_Q^2
       = sum_(i,j) b_i*b_j*<1-F_i,1-F_j>_Q.

Seek an actual upper bound below c*n^a for a<1, or an exact obstruction
showing why that restricted family cannot provide one. Positivity of a
Gram matrix or a formal inverse does not supply the needed quantitative
bound. Keep high composite squarefree conductors available when the
prime-only family is too restrictive. Do not repeat the already checked
implications as if they discharged the arithmetic provider.

If that attack fails, use the precise failure to choose the next idea:
exhaustive affine Schur gains, then the infinite annihilator tail constraints
if they offer a stronger arithmetic handle. Preserve complete signed terms,
normalization, support restrictions, and all boundary contributions.
Exclude the trigamma convergence route.

## Bounded autonomous continuation

The user authorized publication followed by the best next idea and a halt
after five total iterations. This published pass is iteration 1; four further
automatic passes are requested. Use QSparsePowerCostIterationState.json as
the durable count on published main. Each subsequent pass must attempt
mathematics, verify useful Lean additions on the server, publish through
agent_workspace_checkpoint only, append its outcome here, and update the
count. A failed provider remains Open; do not force a proof or dilute its
hypotheses to claim success. A failed verification blocks publication.

Stop once the published count is five. Do not create a second continuation,
extend its recurrence, reset the count, or modify unrelated scheduled tasks.

# Sparse squarefree power costs: iterations 1–2 of 5

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

## Original bounded continuation authorization (after iteration 1)

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

## Iteration 2 of 5: exact correlations and the sparse-averaging obstruction

Date: 17 October 2026.
Starting published commit: e1e77d99da036cfa01b3e8bbe2fa4712c51796f8.
The preceding pass's full project checkpoint
job_8n30Xd35RsquYRQUqZPDlPlQy8YGG6a1 succeeded and pushed that exact revision.

### What was attempted

Try to select increasingly distant prime-anchor canonical heads with very
small cross correlations, then average their residuals to improve SPC(1).
This pass proves the available correlation decay and identifies why that
selection-and-averaging deduction stops. No SPC(a) for 0<a<1 is proved.
The infinite annihilator mean-zero provider remains Open.

Write r_N=1-B_N and K(M,N)=<r_M,r_N>_Q. Before estimating, the complete
arithmetic entry is
    K(M,N)=sum_(k>=1) Q(k)
       (1-B_M(k))(1-B_N(k)).
The auxiliary zero coordinate contributes zero, as in the actual Lean model.

For any physically bounded Q vector f with |f(k)|<=C, and a Q vector u
vanishing on 1,...,N, N>=1, the newly checked bound is
    |<f,u>_Q|^2 <= [2*C^2/zeta(2)] * ||u||_Q^2/N.
It follows from the exact physical tail representation and
    zeta(2)*||tail_(>N) f||_Q^2 <= 2*C^2/(N+1),
followed by complete-tail Cauchy--Schwarz. No finite physical tail is discarded.

Since |r_M(k)|<=1+2M for M>=1, this gives the actual mixed-entry estimate
    |K(M,N)|^2 <= [2*(1+2M)^2/zeta(2)] * ||r_N||_Q^2/N.
Iteration 1 supplied ||r_N||_Q^2/N -> 0. Therefore, for every fixed M>=1,
    K(M,N) -> 0 as N -> infinity.
In particular it holds along every sequence of prime anchors escaping to
infinity. It is not a uniform bound in M.

For finite signed weights b_i with sum b_i=1, put F=sum_i b_i B_i.
The checked complete identity is
    ||1-F||_Q^2 = sum_(i,j) b_i*b_j*K(i,j).
If all i+1 are squarefree, F is squarefree legal. If every i>=H, then
F(k)=1 for 1<=k<=H. The sign of b_i is unrestricted.

### A precise obstruction to the proposed deduction

Vanishing fixed rows do not control the growing diagonal energies of
a recursively selected sparse family. Even perfect orthogonality does not
make arbitrary signed affine averages cheap.

Consider the explicit positive diagonal Gram model
    G_ij = 0 for i!=j,    G_ii=4^(i+1).
Its exact energy is
    E_m(b)=sum_(0<=i<m) (2^(i+1)*b_i)^2.
The assigned heads H_i=16^(i+1) have
    G_ii/H_i=(1/4)^(i+1) -> 0.
Every cross term is identically zero. Nevertheless, the exact reciprocal sum is
    S_m=sum_(0<=i<m) 4^(-(i+1))=(1-4^(-m))/3 <= 1/3.
For sum b_i=1, finite Cauchy--Schwarz gives
    1 <= E_m(b)*S_m,
and hence the checked conclusion
    E_m(b)>=3
for every finite signed affine choice. The result also covers negative weights.

The diagonal Gram matrix can be realized by orthogonal coordinate vectors
of norms 2^(i+1), placed at physical site H_i+1. This
realization is an explanatory paper construction; the module verifies
the scalar Gram energy, reciprocal sum, affine lower bound, and sublinear
diagonal/head limit. These vectors are not asserted to be legal residue
errors. Thus this is not a counterexample to SPC(a) or to RH.

It is a counterexample to deducing vanishing affine cost merely from
sublinear individual energy and small/zero pairwise cross entries.
The issue is finite total reciprocal energy after sparse selection.
The selection threshold can depend on every earlier head and force diagonal
costs to grow too quickly. Sublinear energy along all primes does not
preserve a divergent reciprocal-energy sum on an adaptively sparse selection.

### Exact formal declarations and scope

RH/QExactHeadCorrelations.lean:
- tail_norm_sq_bounded;
- inner_sq_le_sublinear_energy;
- inner_tendsto_zero_of_sublinear_head_zero;
- residual, residual_sequence, residual_head_zero, residual_bounded;
- residual_pairing_weighted, residual_mixed_sq_le;
- residual_fixed_row_tendsto_zero;
- signedHeadAverage, signedHeadAverage_mem, signedHeadAverage_head;
- signedHeadAverage_error_exact.

Analysis/OrthogonalAffineCostObstruction.lean:
- modelEnergy;
- reciprocal_square_sum;
- affine_cost_lower;
- model_diagonal_sublinear.

All these results are unconditional in their displayed types. The generic
correlation theorem has explicit bounded-test, zero-head, and sublinear
hypotheses; its canonical specialization supplies those inputs internally.
There is no new RH consumer and no asserted provider below exponent one.

Server snippet job job_hBp7zpkSuoYzUu8X_s0QPlNdqkV6XVqE succeeded with
verified=true and exit code 0. Axiom inspection of fixed-row decay, the
full signed energy identity, the model floor, and the model sublinear limit
lists only propext, Classical.choice, and Quot.sound.
Final module publication is subject to the current checkpoint; its terminal
result and exact commit accompany delivery.

### Best next idea after this obstruction

Obtain quantitative arithmetic control of a growing block of the actual
signed Gram entries, or of the actual screened capacity gains. Fixed-row
limits alone are no longer an adequate target.

Use the canonical floor expansion to express r_(p-1)(n), for a prime p and positive n,
as exact Mobius tail sums and reciprocal charges:
    r_(p-1)(n)
      = sum_(p<=d<=n) mu(d)*floor(n/d)
          + p*s_(p-1)*floor(n/p).
For p<=n<2p this becomes
    r_(p-1)(n)=M(n)-M(p-1)+p*s_(p-1).
These are proposed paper arithmetic interfaces for the next pass, not
additional newly checked declarations in this module.

Investigate signed weights that cancel the reciprocal-charge contribution
on specified quotient blocks, while retaining the complete remaining
Mobius correlations and all other physical blocks. Seek an actual bound
at exponent a<1. An identity, positivity of the Gram matrix, or a formal
inverse is not such a bound. If prime-only canonical mixtures are too
restrictive, compare against exhaustive high-composite squarefree affine
directions and their exact Schur gains.

Do not replace growing-block control by an unjustified uniform Bessel bound.
The countermodel and the quadratic fixed-row constant must remain visible
in future attempts.

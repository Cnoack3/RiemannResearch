# Sparse squarefree power costs: iterations 1–4 of 5

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

## Iteration 3 of 5: screened variance and the finite common-quotient region

17 October 2026. Base published revision:
8ad676eb44d25858f77b394f54522af96426d260. This is exactly the third pass;
the finite program still stops after five published iterations.

### Discovery and arithmetic attempt

The proposed Mobius tail interface was already available, with all boundary
terms, in CanonicalMobiusQuotientCells.canonicalMobiusResidual_quotient_identity.
CanonicalMobiusPrimeCells already supplies the common-cell variance and
two-cell offset incompatibility for Pareto weights. These identities were
not reproved or counted as this iteration's result.

Write A_Y=(Y+1)S(Y)-M(Y), H(q,n)=sum_(k<=q) M(floor(n/k)).
The exact physical residual is r_Y(n)=H(q,n)+q*A_Y with
q=floor(n/(Y+1)). In particular r_(p-1)(n)=M(n)-M(p-1)+p*S(p-1)
on p<=n<2p, as requested. This is the existing checked interface.

The attempted arithmetic improvement was to cancel reciprocal charge after
screening against an old window. Its common profile has coefficient
delta=1-sum(screening coefficients), precisely the signed Schur source
defect, rather than coefficient one. Canceling the constant alone therefore
does not remove the nonconstant profile. Canceling delta makes the numerator
of the capacity gain zero as well.

### Newly proved complete Q identity and gain obstruction

In RH/QCanonicalSchurVariance.lean, let s be any finite physical cell of
positive integers on which the new anchor T+1 and every old window anchor
N+i+1 share quotient q. Let W, m, V be respectively the mass, weighted mean
and unnormalized variance of H(q,n) on s for the actual Q weights
1/(zeta(2)*n^2). Let Bscr=A_T-sum_i screening_i*A_(N+i).
The new exact identity is

    schur = delta^2*V + W*(delta*m+q*Bscr)^2
              + sum_(n outside s) Q(n)*screenedResidual(n)^2.

Every screening coefficient is signed. The complementary series is the
entire infinite Q complement, not a finite period or an omitted error term.
No limit is interchanged. In particular, when V>0,

    delta^2*V <= schur,
    delta^2/schur <= 1/V.

The zero-Schur case is included using Lean's total division. For a genuinely
new independent anchor the existing positive-Schur theorem gives the usual
positive denominator. These are upper caps on a gain, not lower gain
certificates or upper error estimates. The identity by itself does not
exclude successful canonical mixtures; it identifies exactly what local
charge cancellation leaves behind.

Exact declarations in namespace RH.QCanonicalWindowCapacity:
- schur_quotient_variance_full_energy
- schur_quotient_variance_le
- schur_gain_le_inverse_quotient_variance

The generic scalar-affine completion, including zero slope, is now
Analysis.FiniteWeightedVariance.affine_energy in the owning variance module.
No new RH consumer or assumed arithmetic provider was added.

The Q application concerns actual contiguous canonical windows. Such a
window is not asserted to be squarefree legal. It includes the legal
two-anchor screening case N=M, with N+1 and T+1 squarefree; arbitrary
contiguous-window gains must not be inserted into the squarefree consumer
without a legality proof.

### Why the common-profile simplification cannot cover the tail

NumberTheory/CommonFloorQuotient.lean proves
NumberTheory.common_floor_quotient_bound:

    0<a<b and floor(n/a)=floor(n/b) imply n*(b-a)<a*b.

Thus all common quotient cells for two distinct anchors lie below a finite
explicit cutoff. Even taking their union leaves every sufficiently large
physical coordinate in the complement. Reciprocal-charge cancellation on
common cells supplies no bound at all on that infinite mixed-quotient tail.
This is a concrete limitation of the attempted simplification, not a
refutation of SPC or a contradiction in the actual Q space.

### Verification and publication scope

The coherent candidate passed server snippet job
job_PAU-maMn3xwGUFCqRDomiUPzEQOAGg4R. The printed axiom reports for the
gain cap and the common-quotient bound contain only propext,
Classical.choice and Quot.sound. Two earlier candidate checks failed on
elementary Nat rewriting, were repaired, and supplied no mathematical
counterexample. No admitted proof was persisted.

The final checkpoint must audit and compile the actual aggregate project
and all changed child modules before publishing this iteration. Snippet
success alone is not that gate. The terminal checkpoint job and published
commit are reported in the run report; the state records this workspace and
successful snippet for recovery. The state count becomes durable only with
a successful checkpoint publication.

### Remaining gap and concrete next idea

No exponent in (0,1) is provided. SPC(a) remains proved here only for a>=1.
The full infinite squarefree annihilator mean-zero implication remains open.
The variance lower bound and reciprocal gain upper cap cannot substitute
for the missing upper cost estimate.

The next attempt should use differing quotient profiles rather than assume
that a common cell controls the tail. A precise paper interface to investigate
is the cumulative anchor transform. For finite signed weights b_Y of sum one,
define

    C(t)=sum_(Y in support, Y+1<=t) b_Y,
    D(t)=sum_(Y in support, Y+1<=t) b_Y*A_Y.

Finite reordering of the checked quotient identity proposes, for n>0,

    sum_Y b_Y*r_Y(n)
      = sum_(k=1..n) [C(floor(n/k))*M(floor(n/k))+D(floor(n/k))].

This displayed transform is a paper argument, not a new checked declaration.
Both cumulative charges vanish below the smallest anchor; above the largest,
C=1 and D is the total offset. Investigate the first mixed q=1/2 strip
between two nearby legal anchors: it exposes signed M(n)M(floor(n/2))
correlations absent from a constant-offset calculation. The target is an
actual complete-Q screened-gain or cost bound, retaining all other quotient
blocks, then comparison with high-composite squarefree affine directions.
Do not claim that a finite rearrangement, local cancellation, fixed-row
decay, or o(n) alone gives a power saving.

## Iteration 4 of 5: exhaustive legal canonical coordinates and prime-only incompleteness

17 October 2026. Base published revision:
855d4ce719b07c988e9072f22009463a3b4cb751. The preceding terminal checkpoint
job_OW1P7OC4wbAGCbosys3YG8NoacGCsA9B succeeded and pushed; no prior
verification or publication was left pending. This is exactly pass four.

### Arithmetic attempt and change of direction

The cumulative C,D transform from iteration 3 remains a valid proposed finite
reordering, not a new power-cost provider. On the first mixed strip for
anchors a<b<2a, where floor(n/a)=2 and floor(n/b)=1, the two profiles differ
by M(floor(n/2)). For signed weights t and 1-t the residual is exactly

    M(n)+t*M(floor(n/2))+2*t*A_(a-1)+(1-t)*A_(b-1).

Squaring retains a signed M(n)M(floor(n/2)) cross term. No useful uniform
bound for this cross term together with every other quotient block was
obtained. Cauchy--Schwarz and the existing PNT sublinear estimates alone did
not produce an exponent below one. This failed estimate is not a refutation
of the mixed-quotient method.

Before committing further to prime anchors, this pass checked whether that
family loses legal candidates. The existing CanonicalMobiusTriangular
exhaustion uses all conductors, so its canonical windows cannot simply be
declared squarefree legal. The new results supply the exact missing support
elimination and identify the difference between prime-only and exhaustive
squarefree canonical families.

### Proved support elimination

Let B_Y be the canonical head and c_m the continuous coefficient functional
that extracts the coefficient of g_m. For m>=2 nonsquarefree, every low
Mobius term at g_m vanishes. Therefore the new exact identity is

    c_m(B_Y) = if m=Y+1 then (Y+1)*S(Y) else 0.

Every c_m vanishes on the algebraic squarefree residue span. Apply it to a
finite canonical expansion indexed by Y=H,...,M, H>=1. At a nonsquarefree
anchor m=Y+1, the entire sum reduces to the one term

    b_Y * (Y+1)*S(Y) = 0.

The already proved unconditional finite reciprocal-sum nonvanishing,
S(Y)!=0 for Y>=1, forces b_Y=0. This uses integer denominator clearing and
Bertrand's postulate through the existing provider, not RH or a uniform
asymptotic estimate.

RH/SquarefreeCanonicalCoordinates.lean proves, in
Pareto.CoefficientStabilization:
- coefficient_canonical_nonsquarefree;
- coefficient_squarefree_zero;
- canonical_expansion_squarefree_mask;
- exists_finiteSpace_of_squarefree;
- exists_squarefree_canonical_affine_expansion.

The final theorem keeps the original fixed conductor budget M+1 from the
full triangular expansion and forces every illegal anchor coefficient to
zero. Its positive-head assumption H>=1 is explicit.

The generic coefficient_normalizedResidue helper is placed in its owning
RH/MobiusCoefficientStabilization.lean module. It also covers the harmless
conductor-one atom.

### Exhaustion in the actual Q space

RH/QSquarefreeCanonicalExhaustion.lean proves exists_affine_expansion:
for every f in the algebraic squarefree Q span, if f(n)=1 for 1<=n<=H,
H>=1, there are M>=H and finite signed coefficients b_i with

    sum_i b_i = 1,
    b_i = 0 whenever H+i+1 is not squarefree,
    f = sum_i b_i * exactHead(H+i).

Thus allowing every legal squarefree canonical anchor beyond the head
loses no finite exact-head candidate, including those constructed from high
composite conductors. This is a vector identity in the full Q Hilbert space:
the physical sequence and complete norm are unchanged. No physical tail,
signed term, boundary contribution, or support restriction is discarded.

This is an unconditional algebraic exhaustion theorem, not an RH consumer
with a renamed missing estimate. It gives no quantitative bound on the
coefficients, Gram inverse, minimum energy, or asymptotic power cost.

### A concrete obstruction to prime-only exhaustion

The same Q module proves six_not_prime_expansion. For every M>=5 and every
coefficient vector on B_1,...,B_M that vanishes at all nonprime anchors,

    exactHead(5) != sum_i b_i * exactHead(i+1).

The target has anchor 6, which is squarefree and composite, and it is exact
on 1,...,5. The existing finite full canonical linear independence makes its
unique coefficient at B_5 equal one. Prime-only support forces that same
coefficient to zero, a contradiction. Every finite prime-anchor expansion
fits some such budget, so prime-only canonical heads omit a real legal
candidate even when signed coefficients are allowed.

This does not prove a cost lower bound for prime-only mixtures, nor that
any composite direction gives a nonzero or quantitatively useful source
gain. Independence and a positive Schur denominator alone cannot establish
such a gain.

### Verification and remaining gap

Coherent snippet job job__eDhUGZZIDqPULK5LMf0N3SbKyg8FqdM succeeded,
verified=true, exit code zero. Axiom reports for the Q exhaustion and the
anchor-6 obstruction contain only propext, Classical.choice, and Quot.sound.
An earlier candidate failed only on rewriting between toPareto and its
linear-map encoding; the repaired candidate passed. No admitted proof or
project-local axiom was saved.

Final publication is gated by source audit and the actual aggregate project
plus changed-module checkpoint validation. The terminal checkpoint and
published commit accompany the run report. The count advances only when
the checkpoint has actually pushed.

SPC(a) remains proved here only for a>=1. Neither an exponent in (0,1) nor
the full infinite squarefree annihilator mean-zero implication was proved.

### Best next idea: fifth and final pass

Use the now exhaustive legal canonical coordinates to compare a prime
trial family with the full block of squarefree anchors H<d<=2H, including
composites. Inspect the actual signed source defects and complete Q Schur
denominators of those additions. Seek a block estimate giving a genuine
power saving; do not infer a gain from the incompleteness theorem itself.
Cumulative C,D may organize differing quotient profiles, but every other
physical block and the infinite complement must remain.

If no such arithmetic estimate emerges, record its precise failure and the
strongest verified partial result. The next pass is iteration five and must
halt the program after publication, even if both full targets remain open.
Do not extend the recurrence or restart the count.

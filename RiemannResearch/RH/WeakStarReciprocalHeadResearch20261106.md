# Weak-star compactness, reciprocal heads, and the residual-tail cost

Date: November 6, 2026 (user-local date; verification continued November 7 UTC).
Source: the user's request to attempt weak-star compactness toward RH, continuing
CrossedDistanceLeanHandoff20261106.md and the compact crossed-correction work.

## Status

The new Lean results prove compactness implications, an exact-head membership
criterion, divergence obstructions, and a weaker residual-tail product criterion.
**They do not prove RH or that the actual displacement is zero.**
The missing bound on legal interpolation remains explicitly Open.
No mathematical priority claim is made for the Hilbert-space arguments.

The development starts from published commit
fe0d257152ef23b9edc07b966f7e2b4f6758315b.

## The actual spaces and operators

All conductors m >= 2 are used. Put Q(n)=1/(Z n^2),
P(n)=1/(n(n+1)), and Z=zeta(2), for physical n >= 1.
V is the closed Q-legal span and legalSpan its algebraic finite span.
Let d=f_Q-f_P be the actual matched-projection displacement, and
r_Q=1-f_Q the actual Q residual. Thus d belongs to V and r_Q is orthogonal to V.
I is the sequence-preserving map from Q to P.

R is physical multiplication by 1/(n+1). Its Lean name is
QShiftedReciprocal.B. The metric operator is I* I=Z(Id-R).
Lean's encoded coordinate k represents physical site k+1, so R's encoded
multiplier is 1/(k+2). H_N keeps encoded coordinates k < N.
Matching these encoded heads is equivalent to matching the corresponding
physical values, because the encoding weights are nonzero.

The established energy and membership implications used here are

    ||I d||_P^2 = Z <R d,r_Q>_Q,
    d=0 iff R d belongs to V,
    d=0 implies Mathlib's RiemannHypothesis.

The last implication is inherited from QFullDisplacement and
QFullCofinalHarmonic; no additional RH-to-displacement converse is asserted.

## What weak-star compactness now supplies

Analysis/BoundedWeakInterpolation.lean uses the existing Riesz transport of
Banach--Alaoglu in Analysis/HilbertWeakCompactness. Closed norm balls in the
weak-star dual become weakly compact Hilbert balls. Separability supplies a
subsequence; completeness and separability of the full legal closure are
now explicit instances in QFullResidueProjection.

For a complete separable real Hilbert subspace S, continuous linear tests
L_n, target values b_n, and one fixed C, Lean proves

    [for every N, some f_N in S has ||f_N|| <= C
       and L_n(f_N)=b_n for every n<N]
      iff
    [some f in S has ||f|| <= C and L_n(f)=b_n for every n].

There is also a version for convergent, rather than eventually exact,
test values. For a continuous linear map L into real l2, equality of all
coordinate tests identifies Lf with the target vector.
No strong convergence of f_N and no separate closed-image assumption are needed.

Principal declarations:

- Submodule.exists_ambient_weak_subsequence_of_norm_le
- Submodule.exists_mem_of_bounded_test_limits
- Submodule.bounded_finite_test_feasibility_iff
- Submodule.bounded_lp_head_image_feasibility_iff

## One reciprocal target suffices

QFullHeadObstruction.mem_closure_iff_bounded_exact_heads proves, for every x,

    x belongs to V
      iff
    there is C such that every finite head of x has an exact
    finite legal interpolant F with complete Q norm at most C.

The reverse direction uses the new Banach--Alaoglu argument. In the forward
direction the existing exact-head repair theorem gives a finite legal F
with ||F|| <= ||x||+1, uniformly in the head length.

Consequently displacement_eq_zero_iff_bounded_reciprocal_heads proves

    d=0 iff every finite head of R d admits such a uniformly bounded repair.

riemannHypothesis_of_bounded_reciprocal_heads exposes the uniform bound as
its hypothesis. Exact solvability at each fixed head is insufficient.

There is an explicit obstruction. If x is outside V, then for every C a
finite test H_M a satisfies

    C ||Pi_V H_M a|| < |<x,H_M a>|.

Every legal vector matching that head must therefore have norm greater
than C. The theorem exact_head_norm_tendsto_atTop proves divergence to
infinity for every family matching successively longer heads. In particular,
reciprocal_head_norm_tendsto_atTop proves this for x=R d if d is nonzero.
The conclusion concerns the whole family, not merely an unbounded subsequence.

## A weaker condition allowing growing correction norms

QFullReciprocalHeadTail proves the exact identity, for F in V matching the
first N coordinates of R d,

    ||I d||_P^2 = Z <R d-F, r_Q-H_N r_Q>_Q.

Legality gives <F,r_Q>=0. Head matching gives
<R d-F,H_N r_Q>=0. These are the only terms removed.
Writing tau_N=||r_Q-H_N r_Q||_Q, Cauchy--Schwarz yields

    ||I d||_P^2 <= Z ||R d-F||_Q tau_N
                <= Z (||R d||_Q+||F||_Q) tau_N.

Lean proves tau_N -> 0 unconditionally. Thus either of the following
additional providers forces d=0 and RH:

    ||R d-F_N||_Q tau_N -> 0,
    ||F_N||_Q tau_N -> 0,

where F_N is legal and exactly matches the first N coordinates of R d.
The second condition follows from a uniform norm bound, but permits
unbounded norms growing sufficiently slowly relative to the residual tail.
Neither product-decay condition is proved for the actual repairs.

Principal declarations:

- reciprocal_head_energy_identity
- reciprocal_head_energy_le_error_tail
- residual_tail_norm_tendsto_zero
- displacement_eq_zero_of_error_tail_product
- displacement_eq_zero_of_repair_norm_tail_product
- riemannHypothesis_of_repair_norm_tail_product

For d nonzero, the same identity proves tau_N>0 whenever a legal head
repair exists, and gives the explicit cost

    ||F_N||_Q >= ||I d||_P^2/(Z tau_N) - ||R d||_Q.

This is reciprocal_head_norm_lower. The corresponding complete-error
lower bound is reciprocal_head_error_lower.
The related constant-target strategy already exists in
QSquarefreeExactHeadResidualBarrier; the current statements use the
different full-conductor target R d and its actual Pareto energy.

## Both crossed corrections

QFullWeakHeadCorrections also applies the bounded finite-test theorem to
T=A^{-1}I and J=Id-T/sqrt(Z). If every finite head of Jd admits h_N,k_N in V
with uniformly bounded respective norms and

    H_N T h_N = H_N Jd,    H_N k_N = H_N Jd,

then weak limits give exact corrections Th=Jd=k. The existing crossed-distance
bounds then force both distances to zero, hence d=0 and RH.
displacement_eq_zero_iff_bounded_head_corrections states the precise equivalence.
Both uniform correction bounds remain Open.

## Why the obvious bounded sequence does not finish the proof

The earlier matchedApprox sequence G_M is legal, bounded, and converges to d.
Therefore RG_M is bounded and converges to Rd, but membership of RG_M in V
has not been established. Projecting gives bounded legal Pi_V RG_M, whose
limit is Pi_V Rd. Identifying that limit with Rd is precisely the remaining
membership condition. Weak-star compactness does not remove this defect.

The next arithmetic task is to construct or estimate exact reciprocal-head
repairs, using the existing full-head repair or constrained Gram machinery,
and control their complete Q norms relative to 1/tau_N. A finite head fit
or a truncated energy computation does not estimate either complete factor.

## Verification

The combined source candidate passed job_G9PUjB9eFP-jR0EXaLsITvbe2D9crKOJ:
verified=true, exit code 0, server-reported 9.201 seconds.
This includes all 28 new theorem declarations and the two closure instances.
The persisted four-module import and nine principal axiom reports passed
job_CN-XP_8VlGeCnueN-51fITbhAeY-q23n: verified=true, exit code 0,
server-reported 154.211 seconds including affected dependency rebuilds.
All nine reports contain only propext, Classical.choice, and Quot.sound.
No sorry, admit, project axiom, or unsafe declaration was introduced.
Publication additionally requires the source-audited aggregate and
changed-module checkpoint; its terminal result is the publication evidence.

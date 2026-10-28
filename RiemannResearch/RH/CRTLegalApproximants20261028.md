# Explicit legal CRT approximants: verified scope and remaining goal

28 October 2026. Source: the user's request to construct bounded squarefree
legal approximants in Lean using infinite CRT, with Pareto space allowed.

## Outcome

The new module `QCRTCoprimeApproximation.lean` constructs actual legal
squarefree approximants with pointwise limit 1. It also proves that the
uncorrected Mobius construction has divergent complete Q norm.
It does not prove a bounded family, constant closure, or RH.

Notation: Q(n)=1/(Z n^2), Z=zeta(2), P(n)=1/[n(n+1)],
g_d(n)=(n mod d)/d, and L_H=product of primes at most H.

## Checked construction

Let C_L(n) count positive integers at most n coprime to L. Define

    F_L = sieveVector L 1 + totient(L) * g_L
        = -sum_{d|L} mu(d) g_d + totient(L) g_L.

For positive squarefree L this is a finite squarefree legal sum.
The coefficient at d=1 causes no issue because g_1=0.

The exact sequence identities are

    F_L(n) = C_L(n) - totient(L) floor(n/L)
           = C_L(n mod L).

The declarations `coprimeApprox_sequence`, `coprimeApprox_mod`, and
`coprimeApprox_count_mod` prove these identities. They concern the actual
Q Hilbert vectors and their physical coordinates.

With F_j=F_{primorial(j+2)}, Lean proves:

- `approximant_legal`: F_j belongs to the algebraic squarefree legal span.
- `approximant_exact_head`: F_j(n)=1 for 1<=n<=j+1.
- `approximant_pointwise`: F_j(n) tends to 1 for every n>0.

The arithmetic input is the explicit prime cover: every prime at most
j+1 divides primorial(j+2). If k<=j+1 is coprime to that period, its least
prime factor forces k=1.

## Checked complete-energy obstruction for the raw family

Define G_H=-sum_{d|L_H} mu(d) g_d and a_H=product_{p<=H}(1-1/p).
The declarations `rawApproximant_eq_moebius`, `rawApproximant_head`,
and `rawApproximant_pointwise` prove

    G_H(n)=1-a_H*n   (1<=n<=H, H>=2),
    G_H(n) -> 1      (fixed n>0).

The theorem `rawApproximant_norm_lower` gives

    ||G_H||_Q^2 >= H*a_H^2/(2Z)-1.

Existing unconditional finite prime-product estimates then yield
`rawApproximant_norm_sq_tendsto_atTop` and
`rawApproximant_norm_tendsto_atTop`: the complete norm diverges at
every sufficiently large cutoff, not merely along a subsequence.

This is a counterexample to inferring bounded complete energy from
pointwise convergence of actual legal sums. It does not rule out different
signed legal sums.

## Exact correction energy, checked

The module retains the entire identity

    ||F_L||_Q^2 = ||G_L||_Q^2
      + 2*totient(L)*<G_L,g_L>_Q
      + totient(L)^2*||g_L||_Q^2,

where G_L here means sieveVector L 1, with modulus L rather than cutoff L.
This is `coprimeApprox_norm_sq`. Raw-family divergence alone does not
prove corrected-family divergence: the mixed term cannot be discarded.

## Corrected-family obstruction: mathematical proof, not Lean-verified here

For even L>2, reflection a -> L-a pairs the reduced residues, with no
fixed reduced residue at L/2. Hence C_L(L/2)=totient(L)/2.
Since C_L is nondecreasing, F_L(n)>=totient(L)/2 for L/2<=n<L.
The exact Pareto mass of that interval is

    sum_{n=L/2}^{L-1} 1/[n(n+1)] = 1/L.

It follows that

    ||F_L||_P^2 >= totient(L)^2/(4L),
    ||F_L||_Q^2 >= totient(L)^2/(4ZL).

The second inequality uses P(n)<=Z*Q(n).
For L equal to the product of the first M primes,

    totient(L)^2/L
      = product_{p|L} (p-1)^2/p
      >= (1/2)*(4/3)^(M-1).

Thus the corrected family also has divergent energy. This specific family
is not a candidate for the missing uniform bound. The reflection, plateau,
and product argument in this section has not been submitted as a Lean proof
in this change; the formal divergence theorem concerns G_H.

## Research agenda and exact open obligation

1. Preserve the explicit exact-head construction as an interpolation base.
   Seek additional signed legal corrections that vanish on the existing head.
2. Analyze the complete Gram/Schur form, retaining all mixed inner products.
   Neither conditional energy nor Haar energy controls the needed full norm.
3. The unresolved existence target is a different family A_N in the
   squarefree legal span with exact heads (or pointwise convergence) and
   uniformly bounded complete Q energy.
4. The repository already has
   `QSquarefreeExactHeadAverages.squarefree_closure_capacity_and_rh_of_bounded_exact_heads`.
   Its actual full-error bound is an explicit hypothesis. Once supplied by
   a valid family, it concludes constant closure and Mathlib's RH.
5. Optional formalization: certify the corrected-family plateau obstruction
   above. This would certify another failed construction, not settle RH.

Infinite CRT supplies the compatible finite residue descriptions. It supplies
no analytic bound on the real linear combinations in the Q/Pareto norm.

Reference for the squarefree RH interpretation:
Bagchi, https://arxiv.org/abs/math/0607733, Theorem 1, the comparable-weight
discussion, and Remark 4. No novelty claim is made.

## Verification record

The final isolated candidate passed server job
`job_4CTfvvsLcEE2QzkqFNIZWN2VP8fykEkx` with exit code 0.
Reported verification duration: 6.871 seconds, separate from request and
queue/polling time. The principal checked declarations report only
`propext`, `Classical.choice`, and `Quot.sound`.
There are no added axioms, unfinished proofs, or RH assumptions.
The following publication checkpoint validates the persisted module and
its required project consumers; its terminal result is reported in the chat.

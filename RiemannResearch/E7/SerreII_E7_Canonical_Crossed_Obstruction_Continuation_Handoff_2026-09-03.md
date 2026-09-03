# Full Serre II / E7 canonical crossed obstruction continuation handoff

Date: 2026-09-03

## New exact reduction

The crossed-kernel rectangle introduced in the preceding checkpoint has now
been reduced from a two-preimage choice problem to a canonical one-witness
obstruction.

Let M/F split q₁, let U/M be quadratic, and put

    alpha = q₂ + q₃,
    beta  = q₁ + q₂.

For s,t in Br₂(M), the crossed class is

    cross(s,t) = t + conjugate(s).

Lean proves three invariance statements.

First, if cor(u)=0, diagonal gauge translation does nothing:

    cross(s+u,t+u) = cross(s,t).

Second, if

    s+t = s'+t',
    cor(s) = cor(s') = q₂,

then

    cross(s,t) = cross(s',t').

Thus, for a fixed total witness r=s+t and prescribed q₂-corestriction, neither
the crossed Brauer class nor its quaternionity depends on the decomposition
of r. Changing the q₂-preimage cannot repair a failed common-slot condition.

Third, Lean proves the equivalence

    HasCrossedQuaternionKernelRectangle(q₂,q₃)

if and only if

    q₂ lies in cor(ker(Br₂(M) -> Br₂(U)))

and there exists one r such that

    r|_U = 0,
    cor(r) = q₂+q₃,
    r + res(q₁+q₂) is quaternion.

The q₃-preimage is then forced as t=r+s. It is not an independent
synchronization obligation.

Under Tignol dual-quartic detection, the first condition becomes simply

    (q₂)|_(check U) = 0.

The full crossed-rectangle criterion is therefore exactly

    (q₂)|_(check U) = 0

plus one quaternion point in the affine kernel fibre

    { r in ker(Br₂(M)->Br₂(U)) : cor(r)=q₂+q₃ }

after translation by res(q₁+q₂).

## Lean declarations

All declarations are in
RiemannResearch/E7/E7IndexEightDualQuarticIncidence.lean:

- crossedConjugate_add_diagonal_of_corestriction_zero;
- kernelRectangle_crossedConjugate_eq_of_same_total;
- kernelRectangle_crossedQuaternion_iff_of_same_total;
- hasCrossedQuaternionKernelRectangle_iff_constituentImage_and_kernelComplement;
- hasCrossedQuaternionKernelRectangle_iff_dualConstituentSplitting_and_kernelComplement.

The existing linked-lift and packet-effectivity theorems then turn this
criterion into the E7 endpoint.

## Mathematical interpretation

Lam--Leep--Tignol Theorem 5.12 supplies a quaternion corestriction
presentation of a biquaternion class under the prescribed-discriminant cup
condition:

<https://www.numdam.org/item/PMIHES_1993__77__63_0.pdf>

Tignol Corollary 3.5 and Example 5.3 identify the image of the fixed
upper-layer relative Brauer kernel with classes split by the dual quartic:

<https://arxiv.org/html/1704.04072v1#S3.SS3>

<https://arxiv.org/html/1704.04072v1#S5.SS3>

These results justify the field interpretation of the two image conditions.
They do not prove that the prescribed constituent q₂ is split by the chosen
dual member, nor that the canonical translated fibre contains a quaternion
point.

Barry Theorem 3.3 and Proposition 3.4 provide decompositions adapted to
quadratic and biquadratic subfields over cd₂ at most two:

<https://arxiv.org/pdf/1304.2620>

The remaining issue is still label alignment: an adapted decomposition must
control the prescribed q₂ label or the affine total witness r, rather than
merely produce some tensor decomposition.

## Exact next target

Fix the surviving nonnormal LLT dual pair (U, check U).

1. Prove that check U splits q₂ (equivalently q₃, since it already splits
   q₂+q₃), or find a construction in which this is built into the LLT norm
   coordinates.

2. In the affine fibre

       F_alpha(U) =
       { r : r|_U=0 and cor(r)=q₂+q₃ },

   prove that at least one translated class

       r + res(q₁+q₂)

   is quaternion.

Only the choice of r in this affine fibre remains adjustable. For fixed r,
diagonal changes of the constituent preimages have been proved irrelevant.

A promising next route is to identify Barry's adapted quaternion factor with
the prescribed q₂ class, then write the remaining r-fibre translation in
LLT's explicit norm-polynomial coordinates. A merely unlabeled common-slot
decomposition does not suffice.

## Verification and publication

The four algebraic statements and the dual-quartic rewrite were checked with
Lean. The source module, theorem catalog, and this handoff are validated and
published by the checkpoint accompanying this file.

Base commit before this checkpoint:
6964f61c12a4088cd1c1b8b0c7a485fb6fd2d401.

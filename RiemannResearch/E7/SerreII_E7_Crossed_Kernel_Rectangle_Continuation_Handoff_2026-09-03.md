# Full Serre II / E7 crossed-kernel-rectangle continuation handoff

Date: 2026-09-03

## Result added in this checkpoint

The hard E7 packet now has a second, transfer-theoretic sufficient condition
which does not require a constituent quaternion to split on the same quartic
member as q₁.

Let M/F be quadratic and split q₁. Let U/M be quadratic, and suppose there are
classes s,t in Br₂(M) satisfying

    s|_U = 0,        cor_M/F(s) = q₂,
    t|_U = 0,        cor_M/F(t) = q₃.

Because a class split by a quadratic extension has index at most two, s, t,
and s+t are quaternion classes. The restriction--corestriction identity gives

    res_M/F(q₂) = s + conjugate(s).

Consequently Lean proves the exact identity

    (s+t) + res_M/F(q₁+q₂) = t + conjugate(s).

Therefore, if the single crossed class t+conjugate(s) is quaternion, then s+t
is a linked quaternion lift with corestriction q₂+q₃, and the existing
common-discriminant constructor makes the original labelled E7 packet
effective.

The declarations are:

- HasCrossedQuaternionKernelRectangle;
- kernelRectangle_linkedComplement_eq_crossedConjugate;
- hasCorestrictionLinkedLiftForTriple_of_crossedQuaternionKernelRectangle;
- BoundaryRealization.isEffective_of_crossedQuaternionKernelRectangle.

They are in
RiemannResearch/E7/E7IndexEightDualQuarticIncidence.lean.

## Why this is a genuine reduction

The previous endpoint asked for opposite packet-label splitting, or more
concretely for q₂ or q₃ to split over the quartic U containing a quadratic
subfield of q₁. The new endpoint separates the problem into:

1. simultaneous relative corestriction presentations of q₂ and q₃ in one
   fixed upper-layer kernel;
2. quaternionity of one crossed conjugate sum.

The first four rectangle equations force all uncrossed sums to be quaternion
by the quadratic splitting-field index bound. No further norm or common-slot
condition is needed except on t+conjugate(s).

This does not yet prove that the rectangle exists. It is a strictly
conditional reduction and should not be read as a consequence of the cited
papers without an additional synchronization argument.

## Source audit

Lam--Leep--Tignol, *Biquaternion algebras and quartic extensions*, Theorem
5.12, proves for a non-split biquaternion class A and a quadratic M/F that
splitting by some quartic 2-extension of the prescribed discriminant,
membership in the image of corestriction from Br₂(M), and vanishing of the
corresponding degree-three cup product are equivalent:

<https://www.numdam.org/item/PMIHES_1993__77__63_0.pdf>

This supplies individual corestriction presentations, but its proof chooses a
quartic splitter from an adapted decomposition. It does not state that
presentations of two prescribed quaternion labels can be placed in the same
fixed relative Brauer kernel.

Tignol, *Tores associés à une algèbre étale quartique*, Corollary 3.5 and
Example 5.3, identifies the two-torsion relative Brauer group of a quartic
2-extension using its dual quartic:

<https://arxiv.org/html/1704.04072v1#S3.SS3>

<https://arxiv.org/html/1704.04072v1#S5.SS3>

In the project this is isolated by
DualQuarticRestrictionDetectsLayerCorestrictions. It identifies when one
ground-field class has a corestriction preimage in the fixed layer kernel; it
does not force the crossed sum to be quaternion.

Barry, *Decomposable and indecomposable algebras of degree 8 and exponent 2*,
Theorem 3.3 and Proposition 3.4, gives decompositions adapted to quadratic or
biquadratic subfields when cd₂(F) ≤ 2:

<https://arxiv.org/pdf/1304.2620>

This is the most promising next source for synchronizing the two kernel
preimages, but the published statement does not identify its quaternion
factors with the prescribed E7 labels. That label-alignment step remains open.

## Exact remaining field-theoretic target

Work in the surviving nonnormal conjugacy orbit of LLT quartic layers. Prove
one of the following:

1. the earlier direct incidence

       (q₂)|_U = 0 or (q₃)|_U = 0;

2. a crossed kernel rectangle: choose s,t in Br₂(U/M) with respective
   corestrictions q₂,q₃ and prove

       t + conjugate(s)

   is quaternion.

A productive next calculation is to express s and t using LLT's explicit norm
coordinates and test whether Barry's adapted decomposition forces a common
slot for t and conjugate(s). Any argument must preserve the prescribed E7
labels; an unlabeled tensor decomposition is insufficient.

## Verification and publication

The algebraic reduction was first checked as one coherent ephemeral Lean
snippet. The final source declarations, theorem catalog, and this handoff are
validated and published by the checkpoint accompanying this document.

Base commit before this checkpoint:
4eec599e5491dc278485e18cd1098d2cba497e39.

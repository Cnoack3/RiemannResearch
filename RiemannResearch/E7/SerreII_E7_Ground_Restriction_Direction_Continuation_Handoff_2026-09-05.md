# Serre II E7 ground-restriction direction continuation handoff

Date: 2026-09-05

## Scope and status

This continuation sharpens the hard index-eight E7 affine obstruction.  It
does not prove E7 Serre II and does not provide a field-theoretic
counterexample.

The previous reduction fixed a nonnormal quadratic layer (U/M), defined the
canonical corestriction fibre, and proved that any repair of a bad basepoint
must use a nonzero element of

[
D_U=ker(operatorname{res}_{U/M})
       capker(operatorname{cor}_{M/F})
       subseteq operatorname{Br}_2(M).
]

## New exact identification

Assume exponent two on the base Brauer group and exactness at the quadratic
transfer:

[
ker(operatorname{cor}_{M/F})
  =operatorname{im}(operatorname{res}_{M/F}).
]

Lean now proves

[
oxed{
D_U=
operatorname{res}_{M/F}
 left(
   ker!left(
     operatorname{Br}_2(F)longrightarrowoperatorname{Br}_2(U)
   
ight)
 
ight).
}
]

The right-hand kernel is represented in the abstract model by
(ker(mathrm{down}circmathrm{res})).

The declarations are:

- `UpperLayerAddsNoNewGroundRestrictionKernel`;
- `mem_canonicalCrossedDirection_iff_exists_restricted_layerSplitter`;
- `canonicalCrossedDirection_eq_restriction_map_layerKernel`;
- `canonicalCrossedDirection_trivial_iff_upperLayerAddsNoNew`;
- `exists_nonzero_restrictedGroundCorrection_of_bad_basepoint`.

They live in
`RiemannResearch/E7/E7IndexEightPrescribedDualCommonSplitter.lean`.

## Consequence for the hard E7 search

Let (r_0) be the explicit canonical-fibre witness and suppose

[
r_0+operatorname{res}(q_1+q_2)
]

has index four.  If the same quartic layer nevertheless yields the required
crossed quaternion rectangle, Lean proves that there is a ground-field class
(gammainoperatorname{Br}_2(F)) such that

[
operatorname{res}_{M/F}(gamma)
e0,qquad
operatorname{res}_{U/F}(gamma)=0,
]

and

[
r_0+operatorname{res}_{M/F}(gamma)
   +operatorname{res}_{M/F}(q_1+q_2)
]

is quaternion.

Thus the remaining correction is not an arbitrary relative Brauer class.
It must be a genuinely new ground-field class killed by the nonnormal quartic
extension but not by its quadratic discriminant field.

Equivalently, the direction group is trivial precisely when every
ground-field class split by (U) was already split after restriction to
(M).  In that case the bad explicit witness excludes the entire chosen
quartic layer.

## Verification

Direct Lean diagnostics accepted the modified common-splitter module with no
messages.  No `sorry`, `admit`, project-local axiom, or unsafe declaration
was introduced.  The theorem catalog records the new exact reduction.

## Highest-leverage next target

Compute the relative restriction-kernel quotient

[
kerigl(operatorname{Br}_2(F)	ooperatorname{Br}_2(U)igr)
Big/
kerigl(operatorname{Br}_2(F)	ooperatorname{Br}_2(M)igr)
]

for an LLT nonnormal quartic splitter.

A useful next theorem would either:

1. prove this quotient is zero for the explicit bad layer, excluding it;
2. classify its nonzero elements by the quadratic resolvent/norm data and
   test which one lowers the translated index to two; or
3. prove the conjugate nonnormal layer has the required quaternion point.

This is now a base-field restriction-kernel/norm problem rather than an
unstructured search through (operatorname{Br}_2(M)).

## References

- Lam--Leep--Tignol, *Biquaternion algebras and quartic extensions*,
  Theorem 4.2 and Proposition 3.3:
  <https://www.numdam.org/item/PMIHES_1993__77__63_0.pdf>
- Tignol, *Tores associés à une algèbre étale quartique*, Corollary 3.5 and
  Example 5.3: <https://arxiv.org/abs/1704.04072>
- Barry, adapted decompositions of biquaternion algebras:
  <https://arxiv.org/abs/1304.2620>

## Publication note

Continue only on branch `serre-ii-archive-20260904`.  The default branch is
reserved for the RH development.

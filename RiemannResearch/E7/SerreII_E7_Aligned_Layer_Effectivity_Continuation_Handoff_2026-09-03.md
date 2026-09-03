# Full Serre II / E7 continuation handoff — aligned layer implies effectivity

Date: 2026-09-03

## Published starting point

This continuation began from commit
`16344f15691766120453e4fcedcfafef7b506ab5`, which identifies the two
surviving nonnormal quartic layers in the dihedral hull as a single orbit
under quadratic conjugation. The preceding stable-layer theorem excludes
the conjugation-stable/Galois quartic layer in the total-index-eight case.

## New exact reduction

The module
`RiemannResearch/E7/E7IndexEightCorestrictionAlignedLayerBridge.lean`
closes the previously implicit logical gap between an aligned upper
quadratic layer and the original E7 linked-quaternion target.

Let `T : QuadraticBrauerTransferModel A B` model restriction and
corestriction for `M/F`, and let `down : B →+ C` model restriction for
`U/M`. Assume:

- `T.res q₂ = 0`;
- there is `r : B` with
  `down (T.res q₁) = 0`, `down r = 0`, and
  `T.cor r = q₂ + q₃`;
- every class in `ker down` is a quaternion class.

Then Lean proves

```text
HasCorestrictionLinkedLiftForTriple T IsQuaternionClassB q₁ q₂ q₃.
```

Indeed, `r` lies in the restriction kernel, so it is quaternion. Also

```text
down (r + T.res (q₁ + q₂)) = 0
```

because the layer splits `r` and `res_M(q₁)`, while `M` already splits
`q₂`. Hence the translated endpoint is quaternion as well. This is exactly
the required linked edge with prescribed corestriction `q₂ + q₃`.

For an actual quadratic extension `U/M`, the kernel hypothesis follows
from the standard index divisibility theorem: a class split by a degree-two
extension has index dividing two, hence is split or quaternion in the
intended exponent-two Brauer setting. See Stacks Project, Lemma 11.8.4,
tag 074X: <https://stacks.math.columbia.edu/tag/074X>.

The theorem
`BoundaryRealization.isEffective_of_alignedLayerForTriple` then composes
this edge with a supplied `CommonDiscriminantSumConstructor` and proves
effectivity of the original packet `BrauerPacket.ofTriple q₁ q₂ q₃`.

## Verification

Both principal declarations were checked by Lean Verifier with source
scanning enabled. They report no warnings and depend only on the standard
`propext` axiom. The new module has no diagnostic messages.

## Correct remaining mathematical target

The hard field-theoretic problem is now sharply localized:

> Given the hard total-index-eight triple and a quadratic `M/F` splitting
> `q₂`, construct one nonnormal quadratic `U/M` in the single surviving
> conjugacy orbit and one relative class `r` such that
> `q₁,U = 0`, `r_U = 0`, and
> `cor_M/F(r) = q₂ + q₃`.

The stable quartic layer cannot work, and the two nonnormal layers are
conjugate, so they are not separate cases. Once one such aligned layer is
constructed, the present module supplies the quaternion edge and reduces
packet realization to the already explicit common-discriminant constructor.

## Highest-leverage next step

Analyze the norm/coset incidence on either representative nonnormal
quadratic layer of the LLT dihedral hull. The desired result should either:

1. produce a relative Brauer class in
   `ker(Br₂(M) → Br₂(U))` with corestriction `q₂ + q₃` while
   `q₁` also restricts to zero on `U`; or
2. give a genuine field-theoretic obstruction/counterexample to that
   simultaneous alignment.

Do not spend effort on the conjugate layer separately: the published
conjugation transport theorem makes the two incidences equivalent.

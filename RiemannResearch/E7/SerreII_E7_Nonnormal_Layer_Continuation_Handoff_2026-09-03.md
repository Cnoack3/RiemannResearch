# Serre II — E7 nonnormal-layer continuation handoff

Date: 2026-09-03

Starting checkpoint: `af433bce605a41e5e173ca3f35da9871043116e9`

## Status

Full Serre II and the hard inner E7 case remain open. The preceding checkpoint
proved that, after choosing a quadratic `M/F` splitting `q₂`, the hard
index-eight packet automatically makes the gauge translation fixed-point-free.
The linked-lift problem is exactly the existence of a genuine two-element orbit
in the quotient quaternion locus.

This continuation eliminates an entire class of candidate quadratic layers:
an aligned layer `U/M` cannot be stable under the nontrivial conjugation of
`M/F`. In the intended field model, it follows in particular that `U/F`
cannot be Galois.

## Correct aligned-layer predicate

Let `T` model restriction and corestriction between the two-primary Brauer
groups of `F` and `M`, and let

```text
down : Br₂(M) -> Br₂(U)
```

model restriction to a further quadratic layer `U/M`.

The corrected labelled target is represented by

```text
HasAlignedRelativeCorestrictionLayer T down q₁ q₂ q₃
```

meaning that there is `r ∈ Br₂(M)` such that

```text
down(res_M(q₁)) = 0,
down(r) = 0,
cor_M/F(r) = q₂+q₃.
```

Thus `U` splits `q₁_M` while `r` lies in the relative Brauer group
`Br(U/M)` and has the prescribed corestriction.

## New exact transfer obstruction

Assume the restriction kernel of `down` is preserved by conjugation:

```text
down(r)=0  =>  down(conjugate(r))=0.
```

The quadratic transfer identity gives

```text
res_M(cor_M/F(r)) = r + conjugate(r).
```

Therefore Lean proves

```text
down(res_M(cor_M/F(r))) = 0.
```

For an aligned witness, this says that `U` splits `q₂+q₃`. Because
`q₂_M=0`, it also splits `q₂`, hence `q₃). Alignment already says that
it splits `q₁`. Consequently Lean proves

```text
down(res_M(q₁+q₂+q₃)) = 0.
```

If `[U:F]=4`, the standard splitting-field theorem gives

```text
ind(q₁+q₂+q₃) <= 4,
```

contradicting the hard value eight. The source for index divisibility is the
Stacks Project, Lemma 11.8.4 (tag 074X):
<https://stacks.math.columbia.edu/tag/074X>.

## Field and D8 consequence

If the nontrivial automorphism of `M/F` extends to `U`, restriction-kernel
stability follows. In particular it holds when the quartic extension `U/F`
is Galois. Hence:

```text
Every successful aligned U/M in the hard row is nonnormal over F.
```

For `D₈=<r,s | r⁴=s²=1, srs=r⁻¹>`, the discriminant-field subgroup is
the Klein four group

```text
H=<r²,s>.
```

Its three order-two subgroups are

```text
<r²>, <s>, <r²s>.
```

Conjugation by `r` fixes `<r²>` and exchanges `<s>` with `<r²s>`.
Wolfram independently checked this permutation calculation. Therefore the
three quadratic layers over the discriminant field consist of one stable
quartic layer and one conjugate pair of nonnormal quartic layers. The new
Lean theorem excludes the stable layer.

Only the two nonnormal conjugate layers remain candidates for the simultaneous
conditions

```text
q₁_U=0,
q₂+q₃ ∈ cor_M/F(Br(U/M)).
```

Lam--Leep--Tignol supplies the dihedral/corestriction setting:
*Biquaternion algebras and quartic extensions*, Publ. Math. IHÉS 77 (1993),
Proposition 3.3 and Theorems 5.10 and 5.12:
<https://www.numdam.org/articles/10.1007/BF02699188/>.

## Lean declarations

Added in
`RiemannResearch/E7/E7IndexEightCorestrictionStableLayerExclusion.lean`:

```text
ConjugationPreservesLayerRestrictionKernel
DegreeFourTowerRestrictionKernelHasIndexAtMostFour
HasAlignedRelativeCorestrictionLayer
layerRestriction_res_corestriction_eq_zero
alignedLayer_splits_total_of_conjugationStable
totalIndexEight_excludes_conjugationStable_alignedLayer
totalIndexEight_alignedLayer_not_conjugationStable
```

The result is a conditional research reduction. The field interpretation still
requires providers for the tower restriction, the degree-four index bound, and
the link between a Galois quartic layer and conjugation-stability. These are
standard field facts but are not internalized in the abstract Brauer model.

## Highest-leverage continuation

1. Work only with one of the two nonnormal conjugate quartic layers in the
   `D₈` hull; the other is its conjugate and should carry equivalent data.
2. Compute how a relative-corestriction witness transforms between this
   conjugate pair and whether splitting `q₁_M` on one member forces or
   obstructs the prescribed corestriction label.
3. Recast the remaining choice as a single-orbit incidence problem rather than
   a three-layer search.
4. Compare the two nonnormal layers with Barry's biquadratic-adapted
   decomposition, keeping the labels `q₁` and `q₂+q₃` fixed.
5. On the staged-slot route, impose nonnormality on the quartic field generated
   by the quadratic norm-coset solution; use `I³(F)=0` only at that final
   incidence.
6. Treat characteristic two separately after the characteristic-not-two
   labelled-layer problem is settled.

No field-theoretic existence theorem or counterexample has yet been obtained.

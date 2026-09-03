# Serre II — E7 gauge two-cycle continuation handoff

Date: 2026-09-03

Base checkpoint: `e16ecbbaafe5bda5515958cf8cd9c11f97aac83d`

## Status

Full Serre II, and the hard inner E7 case, remain open in this project. The
characteristic-not-two, `cd₂(F) ≤ 2` index-eight boundary is now reduced to a
genuine two-cycle in a quaternion locus on a gauge quotient.

The quotient is

```text
TwistGaugeQuotient = Br₂(F) / (ker(res) + ⟨α⟩),
```

and the prescribed-corestriction linked lift is exactly a `[β]`-edge in its
quaternion locus. The base checkpoint proved that `[β]` has a fixed point
exactly when `res(β)=0` or `res(β)=res(α)`.

## New packet-label specialization

For a triple `(q₁,q₂,q₃)`, put

```text
α = q₂+q₃,
β = q₁+q₂.
```

If the chosen quadratic field `M/F` splits `q₂`, Lean now proves, for every
gauge class `q`,

```text
translate_[q₁+q₂](q) = q
  ↔ res_M(q₁)=0 or res_M(q₁+q₃)=0.
```

In the hard `(4,4,4)`, total-index-eight branch both alternatives are
excluded by standard field index facts:

1. If `q₁_M=0`, then `q₁` and `q₂` share the quadratic splitting field
   `M`, contradicting `ind(q₁+q₂)=4`.
2. If `(q₁+q₃)_M=0`, then the degree-two extension `M/F` splits
   `q₁+q₂+q₃`, impossible for an index-eight division class.

Thus the quotient translation is fixed-point-free in the intended hard field
case. A successful lift must be a genuine two-element orbit wholly contained
in the quaternion quotient locus; a degenerate fixed point cannot solve it.

## Corrected nested-quadratic target

The preceding dihedral handoff had the wrong label. For a quadratic `U/M`,
the Albert–Draxl/common-slot criterion requires

```text
β_U=0
and
α ∈ cor_{M/F}(Br(U/M)).
```

Since `q₂_M=0`, one has `β_M=(q₁)_M`. Therefore the first condition is

```text
q₁_U=0,
```

not `q₂_U=0`. The latter is already automatic. The exact dihedral alignment
problem is now:

```text
Find U/M inside the relevant dihedral hull such that
q₁_U=0
and
q₂+q₃ ∈ cor_{M/F}(Br(U/M)).
```

The automatic dihedral maximal splitting field does not finish E7 unless one
quadratic layer splits this opposite packet label while supporting the required
relative corestriction class.

## One-parameter staged slot

The independent staged-slot route remains

```text
(q₃)_M = (a t, c_t)_M
for some t∈F×,
c_t = N_{K/F}(t-w)=t²-t Tr(w)+p,
M=F(√p).
```

For fixed `t` and a presentation `(q₃)_M=(at,c)_M`, equality is equivalent
to

```text
c_t/c ∈ N_{M(√(at))/M}(M(√(at))×).
```

This separates the incidence into a descended first-slot condition and a
quadratic norm-coset condition. Ordinary corestriction surjectivity does not
select either.

## Lean declarations

Added to
`RiemannResearch/E7/E7IndexEightCorestrictionAffineReduction.lean`:

```text
middleSplitting_twistGaugeQuotientTranslate_eq_self_iff
middleSplitting_twistGaugeQuotientTranslate_fixedPointFree
```

The first is the exact packet-label specialization. The second records the
fixed-point-free middle-splitting branch under the two non-splitting
hypotheses.

## Authoritative inputs

- Lam–Leep–Tignol, *Biquaternion algebras and quartic extensions*,
  Publ. Math. IHÉS 77 (1993), Theorems 4.7, 5.10, and 5.12 and
  Proposition 3.3:
  <https://www.numdam.org/item/PMIHES_1993__77__63_0.pdf>
- D. Barry, *Decomposable and indecomposable algebras of degree 8 and
  exponent 2*, Theorem 3.3:
  <https://arxiv.org/pdf/1304.2620>
- Albert–Draxl common-slot theorem and the cyclic description of a quadratic
  relative Brauer group; see Gille–Szamuely, Corollaries 4.4.6 and 4.7.4.

LLT supplies quaternion corestriction preimages and the relevant
quartic-2-extension/dihedral structures when the `H³` obstruction vanishes.
It does not force the corrected labelled condition `q₁_U=0`.

## Highest-leverage continuation

1. Analyze the quadratic layers over the discriminant field and determine
   whether one can split `q₁_M` while preserving the relative corestriction
   condition.
2. Express the one-parameter equation as an intersection between the first-slot
   conic of `q₃_M` and `t ↦ N(t-w)`; use `I³(F)=0` only at this
   intersection.
3. Compare Barry's decomposition adapted to a biquadratic subfield with the
   three labelled packet classes, not merely their total.
4. Formalize the field-index lemmas that derive the two non-splitting
   hypotheses from the hard index data.
5. Treat characteristic two separately after the characteristic-not-two edge
   is solved.

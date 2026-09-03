# Full Serre II / E7 continuation handoff — dual-quartic incidence

Date: 3 September 2026

## Outcome

The hard affine quaternion witness has been eliminated from the remaining E7
field problem.

Put α = q₂ + q₃. Let M/F be the quadratic extension chosen to split q₂, let
U/M be a surviving nonnormal quadratic layer, and let check U/F be the
canonical quartic 2-extension dual to U/F. The new exact target is

> An aligned layer over U exists if and only if q₁ becomes split over U and α
> becomes split over check U.

In formulas:

    HasAligned(U)  ↔  q₁|U = 0  and  α|checkU = 0.

Thus the residual variable r in Br₂(M), with r|U = 0 and cor_M/F(r) = α, is no
longer part of the search. For a fixed dual pair, Tignol's relative-Brauer
calculation solves that fibre completely.

## New Lean module

RiemannResearch/E7/E7IndexEightDualQuarticIncidence.lean

The umbrella import RiemannResearch.lean and the theorem catalog are updated.

Principal declarations:

- hasAlignedRelativeCorestrictionLayer_iff_kernel_and_corestrictionImage
- hasAlignedRelativeCorestrictionLayer_iff_affineKernelIncidence
- LayerIncidenceCokernel
- alignedLayerIncidenceObstruction
- alignedLayerIncidenceObstruction_eq_of_same_corestriction
- hasAlignedRelativeCorestrictionLayer_iff_obstruction_eq_zero
- DualQuarticRestrictionDetectsLayerCorestrictions
- hasAlignedRelativeCorestrictionLayer_iff_dualQuarticSplitting
- exists_alignedRelativeCorestrictionLayer_iff_exists_dualQuarticSplitting
- alignedLayerIncidenceObstruction_eq_zero_iff_dualQuarticSplitting
- conjugateLayer_corestrictionImage_eq
- conjugateLayer_baseRestrictionKernel_eq
- dualQuarticRestrictionDetectsLayerCorestrictions_conjugate_iff
- oppositePairIndex_eq_four_of_totalIndexEight
- totalIndexEight_quaternionPreimageLayer_not_conjugationStable
- dualQuartic_normPolynomial_identity
- BoundaryRealization.isEffective_of_dualQuarticSplitting

## Canonical obstruction

For any basepoint r₀ with cor_M/F(r₀) = α, Lean defines

    ω_U(α) = [r₀|U] in Br₂(U) / res_U/F Br₂(F).

Arason middle exactness proves that this class is independent of r₀. Lean then
proves

    HasAligned(U) ↔ q₁|U = 0 and ω_U(α) = 0.

Under the Tignol dual-quartic kernel equality it further proves

    ω_U(α) = 0 ↔ α|checkU = 0.

This converts a choice-dependent affine problem into a canonical vanishing
class, and then identifies its vanishing with an ordinary splitting condition
over the opposite quartic.

## Published mathematical input

For a nonbiquadratic quartic 2-extension U/F with unique quadratic subfield
M, let Δ/F be its discriminant quadratic extension and let L = check U be the
dual quartic. Tignol's Corollary 3.5 and Example 5.3, together with the
quaternion projection formula, yield the derived exact sequence

    0 →
    N_Δ/F(Δ×) / (F×² N_L/F(L×)) →
    Br(U/M) →
    Br₂(L/F) →
    0,

where the middle-to-right arrow is cor_M/F and a norm class λ maps on the left
to the relative quaternion symbol (U/M, λ).

In particular,

    α|L = 0
    ↔ there exists r with r|U = 0 and cor_M/F(r) = α.

This consequence is not quoted as a separate theorem in Tignol; it is the
direct specialization of Corollary 3.5 and Example 5.3 to the dual quartic,
using the projection formula to absorb the discriminant quaternion summand.

Primary source:

- Jean-Pierre Tignol, Tores associés à une algèbre étale quartique,
  Corollary 3.5 and Example 5.3:
  https://arxiv.org/html/1704.04072v1

## Embedded-slot and norm form

Write

    M = F(√a),
    U = M(√z),
    z = b + 2c√a,
    n = N_M/F(z) = b² - 4ac²,
    Δ = F(√n).

Up to F-isomorphism the dual quartic is

    check U = Δ(√(2(b + √n))).

For f(T) = aT² + bT + c², Lam--Leep--Tignol Theorem 3.9 gives the explicit
first-label condition

    q₁|U = 0 ↔ q₁ = (-e, f(e))_F

for a suitable e. Over M this has the embedded-slot form

    q₁|M = (z, f(e))_M.

The second slot f(e) is a Δ/F norm. The polynomial calculation supporting that
claim is now separately kernel checked:

    (2ae+b)² - (b²-4ac²) = 4a(ae²+be+c²).

Tignol's norm calculation also gives, inside M×,

    N_Δ/F(Δ×) ∩ N_U/M(U×) = F×² N_checkU/F(checkU×).

Therefore the prescribed-corestriction witness fibre, when nonempty, is a
torsor under

    N_Δ/F(Δ×) / (F×² N_checkU/F(checkU×)).

The hard condition q₁|M ≠ 0 says that the gauge multiplier f(e) is nontrivial
in exactly this norm quotient. This is the concrete norm-coset version of the
previous fixed-point-free two-cycle.

Primary source for the embedded-slot parametrization:

- Lam, Leep, and Tignol, Biquaternion algebras and quartic extensions,
  Theorem 3.9:
  https://www.numdam.org/item/PMIHES_1993__77__63_0.pdf

## Stronger automatic nonnormality

Lean now first derives that α has index exactly four. Indeed q₁ has index at
most two, α has index at most four, and index(q₁ + α) = 8; index
submultiplicativity forces index(α) = 4.

Becher--Grenier-Boley--Tignol Theorem 0.1 then gives a stronger exclusion than
the previous aligned-layer theorem: every quadratic splitting layer of every
quaternion preimage r with cor_M/F(r) = α is already nonnormal over F. No
assumption that the layer also splits q₁ is needed.

The exact BGT consequence is isolated in Lean as
StableLayerQuaternionCorestrictionHasIndexAtMostTwo, and the resulting theorem
is totalIndexEight_quaternionPreimageLayer_not_conjugationStable.

Primary source:

- Becher, Grenier-Boley, and Tignol, Transfer of quadratic forms and quaternion
  algebras over quadratic field extensions, Theorem 0.1:
  https://arxiv.org/pdf/1610.06096

## Conjugation orbit

Lean proves that both relevant subgroups are unchanged when U is replaced by
its M/F-conjugate:

    cor_M/F(Br(U/M)) = cor_M/F(Br(conj U/M)),

and the base classes split by U are exactly those split by conj U. Thus the two
nonnormal quartics remain one search orbit. This agrees with the D₈ subgroup
calculation independently checked in Wolfram.

Wolfram also exhaustively checked the existing finite additive countermodel:
among all 2,825 subspaces, no non-conjugation-stable quaternion kernel
containing the required first restriction exists. This explains why that
countermodel cannot be upgraded to a field-shaped aligned-layer
counterexample; it is not itself a field-theoretic proof.

## Verification

The new module has no Lean diagnostic errors or warnings.

Targeted verification of the dual-incidence theorem and its direct E7
effectivity endpoint reports only propext. The quotient-obstruction and
automatic-nonnormality proofs add only standard quotient/choice foundations.
No sorry, admit, axiom, unsafe declaration, or source-scan warning is present.

## Exact remaining theorem

The unresolved field statement is now:

> Given the hard E7 data, find a nonbiquadratic quartic 2-extension L/F of
> discriminant M that splits α = q₂ + q₃ and whose dual quartic check L splits
> q₁.

Equivalently, find one labelled D₈ hull whose two dual quartic subfields split
q₁ and α on opposite sides.

Lam--Leep--Tignol Theorem 5.12 guarantees quartic α-splitting fields of the
prescribed discriminant, but it does not force the dual member to split q₁.
It is invalid to combine two independent existential splitting theorems and
assume their chosen quartics are dual.

No authoritative theorem located in this search forces the synchronization,
and no field-theoretic counterexample was found.

## Highest-leverage next steps

1. Study the moduli of LLT Theorem 5.12 quartic α-splitters and evaluate the
   dual q₁-splitting condition on that family, using the explicit resolvent
   polynomial from Tignol Corollary 4.4.
2. Express the simultaneous conditions as symbol/norm equations in e and the
   LLT corestriction parameter; use cd₂(F) ≤ 2 to test whether their final
   obstruction lies in H³(F, μ₂) and therefore vanishes.
3. Obtain and inspect the full text of Sivatski's 2026 filtration paper for the
   nonbiquadratic tower factor containing the norm quotient above. The abstract
   is directly relevant, but the full theorem text was not accessible in this
   run.
4. If universal vanishing fails, search for an actual cd₂ ≤ 2 field example,
   not an additive surrogate, where every α-splitting quartic of discriminant
   M has a dual that fails to split q₁.

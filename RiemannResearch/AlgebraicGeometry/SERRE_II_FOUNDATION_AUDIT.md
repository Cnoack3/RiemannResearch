# Serre II formalization gap audit

This document tracks the structures needed to replace the project's conditional
Serre-II assembly interfaces by the intrinsic theorem. “Available” means a
usable Lean definition exists; it does not mean the mathematical theorem has
been proved. “Open mathematics” marks a genuine unresolved branch rather than
an engineering task.

## Available foundations

- Mathlib supplies commutative rings and fields, finite-dimensional extensions,
  schemes, tensor products, Hopf algebras, central simple algebra carriers, and
  a quotient carrier named `BrauerGroup`.
- This project supplies fpqc covers, fixed-cover nonabelian Cech H¹, a global
  common-refinement quotient `FpqcH1`, affine group objects from Hopf algebras,
  tensor-product base change of affine group coordinates, fpqc torsors,
  point-field indices, degree-one splitting cycles, gcd-one descent lemmas, and
  conditional Dynkin-family assembly.
- The E8 directory contains substantial finite-group and Weyl-group
  certificates. These are not yet attached to an intrinsic E8 group scheme and
  its torsors.

## Added concrete interface

`FpqcH1ScalarExtension.lean` supplies `FiniteFieldExtension`, the actual
tensor-product target `baseChangedFpqcH1`, and typed scalar-extension and
restriction-system interfaces. `FpqcH1CanonicalScalarExtension.lean` now
constructs their canonical fixed-cover and global maps, proves refinement and
common-refinement quotient descent, and proves preservation of the neutral
class.

`FpqcH1ChangeOfBase.lean` and `FpqcH1ScalarExtensionCoherence.lean` prove
generic identity, composition, and associativity laws for change of base,
coefficient functoriality, and the tensor/cover comparison isomorphisms for
identity and iterated scalar extension. The normalized scalar identity and
composition laws are reduced to two explicit fixed-cover coherence squares
for `pullbackSpecIso'` versus `Over.pullbackId` and `Over.pullbackComp`.

`SerreIITypeDScalarExtension.lean` can consume the resulting canonical
`FpqcH1RestrictionSystem`; scalar-extension maps are no longer an open input.

## Missing field and cohomology foundations

1. An intrinsic predicate on `CommRingCat` for fields, perfect fields, and
   perfect fields of cohomological dimension at most two.
2. Separable and algebraic closures usable functorially in the project.
3. Absolute Galois groups as profinite groups and continuous discrete modules.
4. Continuous Galois cohomology, including p-cohomological dimension and the
   characteristic-p/Kato variants required by the full conjecture.
5. Étale/fppf H² and H³, Tate twists, cup products, and comparison with Galois
   cohomology over fields.
6. Restriction and corestriction on those groups, transitivity, Mackey laws,
   and `cor (res x) = [L:K] • x`.

## Missing fpqc H¹ and torsor functoriality

The canonical finite-Galois fixed-cover comparison is complete:
`finiteGaloisFpqcGaloisCechComparison` packages the cocycle and gauge
relations, and `finiteGaloisCanonicalH1EquivNonabelian` gives the resulting
fixed-cover H¹ equivalence.

1. Discharge the two fixed-cover scalar-coherence squares comparing the
   explicit `pullbackSpecIso'` coefficient maps with `Over.pullbackId` and
   `Over.pullbackComp`; the global normalized laws then follow.
2. Construct `FpqcH1TorsorClassifier` by effective fpqc object descent. The
   current interface correctly assumes `Module.Flat R A`, supplies a canonical
   torsor self-cover, and proves consequences of a classifier, but Mathlib does
   not yet supply the needed scheme-valued effective descent equivalence.
3. Pass from finite quotients and fixed covers to continuous absolute-Galois
   H¹ and prove compatibility with pullback of torsors.
4. Add functoriality under homomorphisms of group schemes, twisting
   equivalences, and exact sequences of pointed sets.

## Missing algebraic-group structures

1. Finite type/presentation, smoothness, connectedness, reductivity, and
   semisimplicity for affine group schemes in the representation used here.
2. Centers, adjoint quotients, derived groups, central isogenies, and simply
   connected semisimple covers.
3. Tori, maximal tori, Borels, parabolics, unipotent radicals, and their
   behavior under scalar extension and twisting.
4. Inner and outer forms, automorphism group schemes, and nonabelian twisting.
5. Almost-simple decomposition and reduction of H¹ for semisimple products.

## Missing root data and classification

1. Root data attached to reductive groups, based root data, Dynkin diagrams,
   and the Galois star action.
2. A proved classification into A, B, C, D, E6, E7, E8, F4, and G2.
3. Intrinsic rank/form classifiers for inner and outer A, every B and C rank,
   nontrialitarian D, and the trialitarian ³D4 and ⁶D4 forms.
4. Proof that the classifiers are invariant under isomorphism and exhaustive.

Until these exist, `BaseCondition`, `GroupCondition`, and the family/form
classifiers in the Serre-II modules must remain explicit interfaces.

## Missing Brauer, Tits, and trialitarian structures

1. Abelian-group operations on the Brauer group. Current Mathlib exposes the
   quotient carrier but not an `AddCommGroup` instance.
2. Scalar extension and corestriction of Brauer classes.
3. CSA degree, index, exponent/period, division representatives, and splitting
   fields, with the usual divisibility and restriction/corestriction theorems.
4. Involutions, quadratic pairs, Clifford algebras, discriminants, orientations,
   Tits classes/algebras, and their twisting laws.
5. Trialitarian algebras, the Allen algebra, its triality compatibility datum,
   and proof that its index lies in {1, 2, 4, 8}.
6. Formalization of the known quasi-split and Allen-index-one/two theorems.
7. **Open mathematics:** neutrality/coprime descent for arbitrary trialitarian
   forms of Allen index four or eight. A degree-one zero-cycle alone does not
   prove this.

## Missing cohomological invariants

1. Construction of the Rost invariant with its exact coefficient and
   characteristic conventions.
2. Naturality under scalar extension and compatibility with corestriction.
3. Trivial-kernel theorems in their published scopes.
4. Connections among Rost, Tits/Allen, Arason, Clifford, and boundary
   invariants.

The generic pointed-invariant res-cor theorem already in the project is only
an assembly lemma. Instantiating its trivial-kernel premise for arbitrary
high-index trialitarian forms is equivalent to the unresolved branch on the
bare cd-at-most-two scope.

## Missing family providers

- A: inner and outer forms at all admissible ranks.
- B: every positive rank, retaining B1 as its own classified obligation.
- C: every rank.
- D: nontrialitarian forms; known low-Allen-index trialitarian branches; open
  Allen-index-four/eight branches.
- E6 and E7: arbitrary-form providers in the exact desired scope.
- F4 and G2: translate published proofs to the intrinsic fpqc-H¹ model.
- E8: the full E8 provider.

## Missing E8 bridge

1. Construct/classify the intrinsic simply connected E8 group scheme.
2. Define its Borel and parabolic varieties and prove their point/neutrality
   equivalences.
3. Attach the project's Weyl and finite-subgroup calculations to actions on
   those varieties.
4. Formalize the fixed-locus, compactification, motivic, common-gauge, and
   descent inputs currently represented by conditional interfaces.
5. Produce the E8 neutrality provider and combine it with the non-E8 provider.

## External dependency assessment

The Google DeepMind Formal Conjectures repository is a benchmark collection of
formalized statements. Its Mathlib-facing aggregate imports only projective
space and vector bundles from algebraic geometry, and repository searches show
no Serre II, fpqc H¹, reductive-group, root-datum, or cohomological-dimension
infrastructure. It also pins an older Mathlib release than this project.
Consequently it is not added as a dependency.

No maintained Lean package with the missing reductive-group classification,
continuous nonabelian Galois cohomology, and Rost/trialitarian stack was found.
A dependency should be added only when it provides concrete reusable
declarations; otherwise the components above should be developed as focused
modules here rather than vendoring an unrelated conjecture catalogue.

## Recommended implementation order

1. Prove the two explicit fixed-cover scalar-coherence squares.
2. Build the scheme-valued effective fpqc descent needed to construct the
   flat-coefficient `FpqcH1TorsorClassifier`.
3. Pass the completed finite-Galois fixed-cover comparison to continuous
   absolute-Galois H¹ with torsor-pullback compatibility.
4. Build intrinsic field/cohomological-dimension and semisimple simply
   connected predicates.
5. Build root data and classifiers, then discharge the classical and F4/G2
   providers from published mathematics.
6. Build Brauer/CSA/involution/trialitarian infrastructure and isolate the
   high-Allen-index open leaf.
7. Build H³ and Rost naturality/kernel results.
8. Attach the E8 finite computations to intrinsic E8 geometry and finish the
   single full-strength `SerreII.Conjecture`.

## Scalar-extension and comparison milestone (2026-08-15)

Scalar transport is constructed on fixed covers and on the global
common-refinement quotient, and it preserves the neutral class. Generic
identity, composition, associativity, and coefficient-map laws are proved.

The normalized scalar identity and composition statements are conditional
only on the two displayed fixed-cover coherence squares relating the explicit
affine base-change comparison to `Over.pullbackId` and `Over.pullbackComp`.

`FpqcH1TorsorClassification` specifies a flat-coefficient classifier
interface, constructs the canonical torsor self-cover, and proves the
neutral-class/global-section criterion from supplied classifier data.
Effective fpqc object descent, full faithfulness, and essential surjectivity
are still open.

`FiniteGaloisCechComparison` now constructs the cocycle equivalence, proves
preservation and reflection of the gauge relation, packages the canonical
`FpqcGaloisCechComparison`, and supplies the resulting fixed-cover fpqc
Čech-H¹/discrete-nonabelian-H¹ equivalence. Passage to continuous
absolute-Galois H¹ and compatibility with torsor pullback remain open.

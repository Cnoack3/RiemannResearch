# Chow motives and Rost nilpotence: formalization audit

Date: 7 August 2026

## Scope

The Lean module `RiemannResearch.Motives.RostNilpotence` is an abstract,
motive-ready foundation. It is not a construction of Chow motives and it is
not a formal proof of the geometric Rost nilpotence theorem.

It formalizes the exact algebraic interface used after a correspondence
category and base-change functor have been constructed:

```
End(M) -> End(M_L)
```

Rost nilpotence is represented by the statement that every element of the
kernel is nilpotent. A stronger predicate records one uniform exponent.

## Existing Lean code audited

The project uses Mathlib revision
`51e6992efd06126df61a496bebf8f49482a4e129`
(input revision `v4.33.0-rc2`).

Mathlib currently has one algebraic-cycle source file,
`Mathlib/AlgebraicGeometry/AlgebraicCycle/Basic.lean`. It defines an
algebraic cycle as a locally finitely supported function on scheme points and
defines weighted pushforward for quasicompact morphisms, with an identity law.
The public Mathlib directory contains no further algebraic-cycle files.

Mathlib also already supplies the reusable infrastructure closest to Chow
motives:

- preadditive categories and endomorphism rings;
- finite biproduct machinery;
- the Karoubi envelope and its idempotent completeness;
- noncommutative ring-theoretic lifting of single, orthogonal, and complete
  orthogonal idempotent families through a ring map whose kernel elements are
  nilpotent.

Public GitHub searches for Lean declarations named Chow motive, Chow group,
Rost nilpotence, and algebraic correspondence found no external project with a
more developed compatible implementation. A direct project fork therefore
would not currently bypass the missing geometry; Mathlib is the useful base.

## Primary mathematical sources audited

- V. Chernousov, S. Gille, A. Merkurjev, *Motivic decomposition of isotropic
  projective homogeneous varieties*, Duke Math. J. 126 (2005), Theorem 8.2 and
  Corollary 8.3. Theorem 8.2 states that for a projective homogeneous variety
  and every field extension, the kernel on motive endomorphism rings consists
  of nilpotent correspondences; its proof gives a uniform exponent.
  Corollary 8.3 lifts a projector lying in the image.
- P. Brosnan, *A short proof of Rost nilpotence via refined correspondences*,
  Documenta Math. 8 (2003), 69--78. Its proof depends on composition of refined
  correspondences via refined Gysin maps.
- The attached E8 manuscript cites the same Chernousov--Gille--Merkurjev
  theorem for integral Rost nilpotence. This audit does not promote that
  citation to a Lean theorem about E8 varieties.

## Kernel-checked layer

The new module proves:

- composition and descent laws for elementwise Rost-nilpotent kernels;
- multiplication of explicit kernel exponents through towers;
- construction of the endomorphism-ring homomorphism induced by an additive
  functor;
- objectwise and global Rost-nilpotence predicates for additive functors;
- lifting of a single projector and finite orthogonal or complete orthogonal
  projector families;
- packaging of a lifted projector as an object of the Karoubi envelope.

These are general algebra/category theorems. Their hypotheses are the ordinary
data appropriate to the exact statements, not hidden geometric assumptions.

## Missing geometry

An actual Chow-motive and E8 application still requires all of the following.

1. Graded cycle groups by dimension or codimension.
2. Rational equivalence and the resulting Chow groups.
3. Flat/lci pullback, exterior products, refined Gysin maps, and the
   intersection product.
4. Proofs of projection, base-change, and excess-intersection formulas.
5. Composition of correspondences and its associativity and identity cycles.
6. The preadditive correspondence category for smooth projective schemes.
7. Tate twists, finite sums, and its Karoubi envelope as the category of Chow
   motives.
8. Field-extension base change as an additive functor, including compatibility
   with correspondence composition.
9. Identification of the functor's endomorphism-ring map with extension of
   algebraic correspondences.
10. A geometric proof of Rost nilpotence for projective homogeneous varieties,
    including the motivic decomposition and the refined-correspondence
    nilpotence argument.
11. Construction of the relevant twisted E8 flag varieties and proof that the
    cited projective-homogeneous theorem applies.
12. Rationality/image proofs for every split projector to which the lifting
    theorem is to be applied.

Until these are supplied, the new declarations verify the projector-lifting
logic conditional on the precisely stated kernel property; they do not verify
a Chow-motive decomposition of an E8 variety.

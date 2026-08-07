# Lean dependency compatibility survey

Target environment: Lean 4 / Mathlib `v4.33.0-rc2`.

This survey records why the E8 Serre II formalization currently builds its
missing foundations locally instead of adding an external dependency. A
dependency is acceptable only if it is version-compatible, removes a real
proof obligation, and does not replace the cited theorem by an assumption.

## Reusable installed foundations

Current Mathlib already supplies:

- [fpqc and fppf sites](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/Sites/Fpqc.html),
  including precoverages, stability, and fpqc subcanonicality;
- [root-system definitions](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/RootSystem/Defs.html)
  and semisimple Lie-algebra construction;
- [basic algebraic cycles](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/AlgebraicCycle/Basic.html);
- fixed-cover nonabelian Čech H¹, affine group schemes, and additive group
  cohomology.

These are imported directly where needed.

## External projects checked

### Chevalley and reductive groups

The closest public Lean project found was
[singerng/steinberg-formalization](https://github.com/singerng/steinberg-formalization).
It formalizes presentations of a graded, unipotent, B3-large
Chevalley-like abstract group. It does not construct reductive group schemes,
E8, or algebraic-group torsors. Its
[toolchain](https://github.com/singerng/steinberg-formalization/blob/main/lean-toolchain)
pins Lean `v4.15.0-rc1`, far behind this project's toolchain.

Verdict: do not import.

### Group-cohomology corestriction

[kbuzzard/ClassFieldTheory](https://github.com/kbuzzard/ClassFieldTheory)
contains restriction, corestriction, inflation, Tate cohomology, and related
class-field-theory infrastructure. Its
[toolchain](https://github.com/kbuzzard/ClassFieldTheory/blob/main/lean-toolchain)
pins Lean `v4.31.0-rc2` and a different Mathlib commit. More importantly, its
[Corestriction module](https://github.com/kbuzzard/ClassFieldTheory/blob/main/ClassFieldTheory/Cohomology/Functors/Corestriction.lean)
still lists `cores ∘ res = multiplication by the index` as a TODO, and no
Mackey double-coset theorem was found.

Verdict: do not add it as a common dependency. A small audited port may be used
as a reference, but the required identity still has to be proved locally.

## No compatible implementation found

No current public Lean 4 package was found that supplies any of the following:

- reductive or Chevalley group schemes of type E8 and their torsors;
- classification of fpqc H¹ by group-scheme torsors;
- Chow groups, correspondences, Chow motives, or Rost nilpotence;
- algebraic cobordism or algebraic Morava K-theory;
- the Burnside ring as the Grothendieck ring of finite G-sets;
- the H¹ transfer/Mackey identities required for Brown stable elements.

## Decision

No external dependency is added. The project keeps its current Mathlib pin,
uses the installed lower-level foundations, and formalizes each missing bridge
locally with kernel checks. This avoids an incompatible downgrade and avoids
moving an unresolved theorem into an unaudited dependency.

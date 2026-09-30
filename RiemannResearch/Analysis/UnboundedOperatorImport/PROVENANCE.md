# Spectra unbounded operator core provenance

Imported from [adambornemann-glitch/Spectra](https://github.com/adambornemann-glitch/Spectra) at commit [8dbaaf6728d1342ae16acf79fd7eef7c59b37e63](https://github.com/adambornemann-glitch/Spectra/commit/8dbaaf6728d1342ae16acf79fd7eef7c59b37e63).

Copyright (c) 2026 Spectra Formalization Project. Authors: Adam Bornemann.
Licensed under Apache 2.0; the complete upstream license is preserved in LICENSE.md.

## Scope and preservation

- Prepared from pinned GitHub connector source reads. Target verification is performed by the coordinating agent.
- Upstream Lean: v4.31.0-rc1; upstream mathlib: 40f05009d036d2e4b488e8a01f559a6036ec2484. Target Lean/mathlib: v4.33.0-rc2 / 51e6992efd06126df61a496bebf8f49482a4e129. No upstream package/toolchain configuration is imported.
- Five full core files retain every original declaration statement and original proof argument, with imports rewritten/pruned. Helpers and DeficiencySubspace additionally close eight explicit subtype-coercion equality goals with Subtype.ext rfl for the target compiler. Two modules contain exact complete declaration extractions. No aliases are introduced and all original namespaces are preserved.
- Closable's unused Spectra.Operator.SelfAdjoint import is replaced by the exact Mathlib LinearPMap core. All partial operator domains, adjoints, and star-based IsSelfAdjoint definitions used by the proofs are canonical Mathlib definitions. This removes unrelated bundled observables, commutators, and variances.
- Helpers' unused Spectra.OneParameterUnitaryGroup.Basic import is replaced by the exact Mathlib LinearPMap core and named tactic modules. Helpers uses no unitary generator definition or theorem. This removes unrelated group construction while retaining every operator estimate and self-adjoint range theorem.
- EssentialSelfAdjointness's broad KatoRellich import is replaced by Operator.SurjectivityCriterion containing the exact isSelfAdjoint_of_surjective_addSub_smul declaration and complete proof. Full KatoRellich imports StoneFormula.Identities, which imports QuantumMechanics.DiracEquation.Operators; these physics/full spectral modules are deliberately not imported.
- DeficiencySubspace's broad Resolvent.Range.Surjectivity import is replaced by Resolvent.RangeSubmodule containing the exact rangeSubmodule definition with its complete submodule proofs. None of the other imported surjectivity theorems is used by DeficiencySubspace.
- Core imports are 7 Lean modules; explicit Mathlib subject/tactic imports only, no exact import Mathlib.
- Preliminary comment-stripped token scan found no sorry, admit, axiom, unsafe, native_decide, implemented_by, extern, or sorryAx in the selected source.
- Target Mathlib source inspection confirms the required LinearPMap adjoint, formal adjoint, domain, graph, closure, star-based self-adjointness, and Submodule.adjoint definitions remain present; all seven imported modules and the combined project now compile. The twelve listed principal endpoints pass #check and #print axioms, with only propext, Classical.choice, and Quot.sound in their dependencies.
- No claim is made here that the arithmetic Mellin/Jacobi operator satisfies the dense domain, symmetry, or dense shifted range hypotheses. The import is unconditional abstract operator theory; application to the actual RH operator remains a separate proof obligation.

## Compiler compatibility repairs

Target compatibility changes: two subtype subtraction equalities in YosidaHille.Helpers and six subtype zero/addition/scalar equalities in Operator.DeficiencySubspace are discharged by explicit Subtype.ext rfl immediately after the original convert steps. These eight definitional-equality closures add no hypotheses and change no theorem statements, signed terms, domains, or original proof arguments.

## Source manifest

| Local module/file | Upstream file | Upstream blob |
| --- | --- | --- |
| Operator/Closable.lean | Spectra/Operator/Closable.lean | 1da16740e569c536e82f74fa0539f5c23c8a374e |
| Operator/AdjointClosure.lean | Spectra/Operator/AdjointClosure.lean | 25375c0eaa5d025ebf6a7731920213a4c0fa87a9 |
| YosidaHille/Helpers.lean | Spectra/YosidaHille/Helpers.lean | 5c29b5fe96a0d5b846d0f381dd34b3212c681c0b |
| Operator/EssentialSelfAdjointness.lean | Spectra/Operator/EssentialSelfAdjointness.lean | f0ecb35a74bb688b246af6b0628cd9498ae20d22 |
| Operator/DeficiencySubspace.lean | Spectra/Operator/DeficiencySubspace.lean | 04ae0ae0c2948fc839928c28502b162d797120ad |
| Operator/SurjectivityCriterion.lean | Spectra/Operator/KatoRellich.lean | 111f48c792c370e5c184b982bc02f0e41f034c2d |
| Resolvent/RangeSubmodule.lean | Spectra/Resolvent/Range/Surjectivity.lean | 3da1ea36750b6070d03be7f8f389a2e371173174 |
| LICENSE.md | LICENSE | 921408b0f39987d9704f25c53aead7eba96c1d33 |

## Principal endpoints

- `Spectra.Operator.isClosable_iff_dense_adjoint_domain`
- `Spectra.Operator.closure_adjoint_eq_adjoint`
- `Spectra.Operator.adjoint_adjoint_eq_closure_of_isClosable`
- `Spectra.Operator.hasCore_iff_topologicalClosure_graph`
- `Spectra.YosidaHille.op_lower_bound`
- `Spectra.YosidaHille.op_range_isClosed`
- `Spectra.YosidaHille.selfAdjoint_surjective_sub_smul`
- `Spectra.Operator.isSelfAdjoint_of_surjective_addSub_smul`
- `Spectra.Operator.IsEssentiallySelfAdjoint`
- `Spectra.Operator.isEssentiallySelfAdjoint_of_denseRange_addSub`
- `Spectra.Operator.deficiencySubspacePlus_eq_orthogonal`
- `Spectra.Operator.deficiencySubspaceMinus_eq_orthogonal`

# Li criterion and Hadamard dependency import

Imported from [nicholasbulka/li-criterion-rh-equivalence-lean](https://github.com/nicholasbulka/li-criterion-rh-equivalence-lean) at commit `35df682f3b709ffe5fbcfdd452dfa964bd622b87` (2026-09-05).

Original authorship and Apache 2.0 licensing notices are retained. The adjacent LICENSE.md is the upstream license. No upstream NOTICE file exists at the pinned commit.

## Scope and faithful adaptations

This package contains exactly the 33-file project-local transitive dependency closure of `Lc/LiCriterion/XiOrderBridge.lean` and `Lc/LiCriterion/Fidelity.lean`. It includes the required Hadamard and FunctionsOfOneComplexVariable modules, rather than their full repositories or unused aggregate roots.

Original namespaces, declarations, theorem hypotheses, expressions, summability conditions, paired terms, multiplicities, and proofs are preserved except three core conditional lemma name substitutions needed for Lean v4.33 (see below). Project-local import names are prefixed with `RiemannResearch.Analysis.LiCriterionImport.`; Mathlib import names are unchanged. Every modified Lean file carries a port notice. Port notices point to LICENSE.md. Original copyright headers retain the canonical LICENSE wording required by the Mathlib linter; the bundled Apache license text is LICENSE.md. There are no new aliases or wrappers.

No exact `import Mathlib` occurs upstream. Every existing Mathlib import is focused, so none was replaced by a guessed narrower set.

## Source audit and verification status

A nested-comment/string-aware lexical scan of the copied closure found no `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `run_meta`, `implemented_by`, or `extern` in executable source. This is a preliminary source scan, not kernel verification or an axiom audit.

The upstream toolchain is `leanprover/lean4:v4.34.0-rc1`; upstream mathlib is `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`. The target is Lean v4.33.0-rc2 and mathlib `51e6992efd06126df61a496bebf8f49482a4e129`. No target toolchain or dependency configuration is changed. All 84 directly imported Mathlib module paths exist at the target commit. Target Init/PropLemmas uses the older conditional API; in Hadamard/General/Factorization.lean three uses of v4.34 ite_eq_right/ite_eq_left are faithfully replaced with if_neg/if_pos. All 33 modules and the combined project now compile in the target environment. The six principal Li endpoints and the general Hadamard factorization endpoint pass #check and #print axioms, with only propext, Classical.choice, and Quot.sound in their dependencies. The RH application obligations below remain open.

## Endpoints and normalization

- `LiCriterion.li_criterion_rh_iff`: Mathlib's `RiemannHypothesis` iff every `(LiCriterion.taylorCoeff riemannXi n).re` is nonnegative.
- `LiCriterion.taylorCoeff_eq_li_symmetrized`: exact half-sum over `LiCriterion.NontrivialZero`, with multiplicity `analyticOrderNatAt riemannXi ρ.val` and both signed exponents `-((n : ℤ)+1)` and `((n : ℤ)+1)`.
- `LiCriterion.summable_li_symmetrized`: genuine summability of that multiplicity-weighted paired family, so its `tsum` is not a nonsummable default.
- `LiCriterion.taylorCoeff_eq_weighted_tsum`: the identical normalization through `liPairedSummand`.
- `LiCriterion.xi_hasFiniteOrder` and `LiCriterion.xi_order_le_one`: unconditional order inputs from the Mellin/theta-kernel proof in `XiGrowth`.

Importing this criterion does not prove Li coefficient positivity and does not prove RH. Connecting these coefficients to the project's signed CRT/Weil forms is a separate mathematical obligation.

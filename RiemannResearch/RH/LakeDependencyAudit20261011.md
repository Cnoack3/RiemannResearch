# Lake dependency audit and structural refactor — 2026-10-11

Scope: Lake and the existing native GCS remote cache. The source baseline is
`785e2a8273ccd2c403d3f4f1c54950faa3d7d43c`. No Bazel, Lake configuration,
toolchain, package revision, cache policy, or compiler option is changed.

## Findings

The baseline has 2,500 Lean modules, 6,945 direct project import edges, and
203,150 ordered transitive project dependency relationships. The longest
project chain contains 51 modules. There are no import cycles, missing project
imports, child imports of the aggregate `RiemannResearch` module, or exact
`import Mathlib` statements. The aggregate exports all 2,499 child modules.
The substantial problem found is unnecessary coupling inside this acyclic graph.

1. `Analysis/MellinNormalizedResidue` imported `RH/ConditionalMeanHeadObstruction`
   solely for its last dual-square lower-bound lemma. That imported branch
   contributes 139 project modules beyond its other imports.
2. Four arithmetic/Hilbert modules imported the whole normalized Mellin
   development merely to use the normalized residue Hilbert vector and its
   sequence identity. Consequently, edits to that analytic development could
   reach arithmetic modules that do not use its Mellin theorems.

These are source-graph findings, not measured cache-hit or elapsed-time statistics.

A bounded history sample of 11 Lean-changing commits on 2026-10-11 added
105 child modules and modified seven existing child modules (plus ten aggregate
export updates). Six of those seven changed modules have at most 11 transitive
importers in the baseline; `ActualZeroOrdinate` has 81. Thus the sampled recent
history does not establish that very broad dependency invalidation is the main
cause of the observed cache performance. New modules need their first build,
and aggregate export changes do not create a reverse dependency from every
child module to the aggregate. The import refactor addresses a confirmed
structural problem; diagnosing the dominant runtime cost still requires cache
and build telemetry.

## Changes and preservation

The following declaration text is moved verbatim, including its statement and
proof or definition body. Fully qualified names are retained.

| Declaration in `RiemannResearch.RH.Pareto` | New owning module |
| --- | --- |
| `normalizedResidueHilbert` | `RH/ParetoNormalizedResidueHilbert` |
| `normalizedResidueHilbert_sequence` | `RH/ParetoNormalizedResidueHilbert` |
| `one_le_conditionalMellinDualSquare` | `RH/ConditionalMeanHeadObstruction` |

The new Hilbert module imports the existing digit-vector construction and
arithmetic residue definitions. `Analysis/MellinNormalizedResidue` retains
all its analytic identities and imports the Hilbert module. The lower-bound
lemma is placed alongside the total-mass theorem it actually needs.

`ParetoFullTailCRT`, `MobiusHilbertCoordinates`,
`ThresholdProjectedDilationHierarchy`, and `EndpointResidueCorrection` import
the Hilbert module directly. `ParetoFullTailCRT` explicitly imports the weighted
Hilbert inner-product module. Three genuine analytic consumers receive direct
Mellin imports: `ParetoOddMomentDyadicObstruction`, `HardyMobiusFamily`, and
`ProjectedDualMellinWitness`. No proof is rewritten to accommodate the imports.
The aggregate export and the theorem catalog's location information are updated.

A source-preservation check compares the three moved declaration blocks
byte-for-byte and checks that the bodies of every other modified Lean module
are identical after removing import lines. The machine-readable audit records
the block hashes. No declaration, hypothesis, attribute, theorem name, or
mathematical result is added or removed.

## Dependency measurements

Counts exclude the module itself and external Mathlib/package modules.
Reverse counts include the aggregate project importer. They describe the
potential scope of invalidation, not a prediction that every dependent will
necessarily recompile after every source edit.

| Module | Project dependencies before | After |
| --- | ---: | ---: |
| `Analysis/MellinNormalizedResidue` | 178 | 40 |
| `RH/MobiusHilbertCoordinates` | 198 | 38 |
| `RH/ParetoFullTailCRT` | 184 | 29 |
| `RH/ThresholdProjectedDilationHierarchy` | 185 | 26 |
| `RH/EndpointResidueCorrection` | 222 | 221 |

| Module changed in a later edit | Transitive importers before | After |
| --- | ---: | ---: |
| `Analysis/MellinNormalizedResidue` | 522 | 114 |
| `RH/ConditionalMeanHeadObstruction` | 591 | 295 |
| `Analysis/MellinCesaroSummability` | 597 | 355 |

Across the project, 462 existing modules have smaller dependency closures.
Total transitive relationships drop from 203,150 to 195,008, a reduction of
8,142 (approximately 4.0%), including the new module's dependencies.
Direct edges rise from 6,945 to 6,952 because explicit imports replace
accidental transitive availability; simply counting direct import lines would
miss the improvement. All 2,500 child modules remain exported after the split.

## How this affects Lake's cache

The pinned Lean/Lake version is `v4.33.0-rc2`. In its
[`Lake/Build/Module.lean`](https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/lake/Lake/Build/Module.lean),
`recFetchInput` hashes source text, `ModuleImportInfo.addImport` mixes import traces
and artifact traces, and `recFetchPreSetup` combines these with the compiler,
options, module name, package identity, and arguments. Narrowing actual import
closures therefore removes real dependencies from Lake's build traces.
It does not require disabling checks or weakening trace correctness.

The repository's `tools/agent_workspaces.py` selects shared dependency
environments by `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.
Those three files are unchanged here. When `LEAN_REMOTE_CACHE_SERVICE` is
enabled, the code explicitly bypasses legacy commit-keyed build snapshots and
uses native Lake mappings and artifacts. The opened server workspace confirmed
that native mode is active. A new Git commit alone is therefore not evidence
that all native artifact content keys have become invalid.

Lake searches recent ancestor revisions for published mappings, rather than
requiring an exact-HEAD mapping. `Package.id?` is the package name, not the Git
commit. These details were checked in the pinned upstream `Lake/CLI/Main.lean`
and `Lake/Config/Package.lean`.

The current wrapper attempts a no-build restoration, retrieves remote mappings
on the designated cache-miss exit code, then builds and uploads mappings. It
also removes the workspace's project build directory after successful work
when no editor is using it, while retaining the shared native cache. That can
make later runs spend time restoring files and checking traces even without
re-elaboration. The shared cache has a 100 GiB pruning budget. These policies
were inspected, not changed or benchmarked. No cache defect or measured cache-hit
rate is asserted by this audit.

This refactor necessarily changes some build traces once. The expected benefit
is a smaller dependency scope for subsequent edits, especially to the Mellin
and conditional-obstruction modules. A warm-cache before/after workload is
needed to quantify elapsed-time and transfer savings.

## Remaining candidates

These candidates are examined in the [follow-up audit](LakeDependencyAuditFollowup20261011.md).
The measurements above describe this first refactor only.

The graph still has broad foundations: `WeilExplicitFormula.Defs` reaches
1,145 importers after this refactor. Large reverse closures are not inherently
mistakes; many express actual mathematical use.

Further source review should examine the general smooth-decay definitions
inside `RH/NymanCompletionAdmissibility`, which are imported by
`Analysis/SmoothCompactCutoff` and `Analysis/SmoothCorrelationClosure`;
the general dual-square constant inside `RH/ConditionalMeanRHBridge`, used
by `Analysis/ConditionalMellinFunctional`; and the arithmetic import of
`Analysis/WeightedComplexPairing`. These are candidates requiring separate
proof-preserving splits and verification, not claims that every import is unused.

## Verification

Static checks: complete current Lean source set matched against GitHub blob
hashes; moved declaration blocks identical; unchanged remaining module bodies;
acyclic complete project import graph; all child modules exported; clean patch
whitespace. These checks do not substitute for Lean compilation.

Focused server verification succeeded in job
`job_zQxb9TGfC3meyh685kZJr6-2BslD6bqp` (exit code 0, verified).
Its snippet imports all ten changed or new child modules, checks
`normalizedResidueHilbert`, and prints the axioms of
`normalizedResidueHilbert_sequence` and `one_le_conditionalMellinDualSquare`.
Both theorem checks report only `propext`, `Classical.choice`, and `Quot.sound`.
Existing style warnings remain unchanged. This focused check does not certify
the full project.

Publication is gated by the server checkpoint's source audit and incremental
Lean build of the aggregate project plus the changed child modules, including
any integration with newer upstream changes. The final checkpoint job and
published commit are reported with delivery; this report makes no advance
claim that a pending full-project check has succeeded.

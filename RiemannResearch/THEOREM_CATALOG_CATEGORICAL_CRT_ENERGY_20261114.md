# Categorical CRT, compact gluing, and residual correction energy

Source: user-provided `Categorical_CRT_Exact_Gluing_and_Energy_2026-11-14.md`
(14 November 2026). This continuation formalizes the set-based finite
gluing criterion, compact fixed-budget extension, and the exact residual
correction cost, with an application to the actual full-conductor Q
projection sequence. It does not claim a proof of RH.

## Established declarations

| Module | Declaration | Exact scope |
| --- | --- | --- |
| `Logic/EquivalenceRelationCRT.lean` | `FamilyCRT.hereditaryCRT_iff_meetComposition` | Finite CRT for every nonempty subfamily is equivalent to the specified meet/composition inclusion for equivalence relations on a type. No ambient distributive or permutable congruence lattice is assumed. |
| same | `FamilyCRT.meet_composition_iff` | Both inclusions, expressed as the exact witness equivalence. |
| same | `FamilyCRT.solution_iff_intersection` | Given one solution, all solutions form exactly its intersection-relation class. |
| same | `FamilyCRT.exists_joint_of_pairwise` | Surjective observation maps and the family criterion give a common preimage of actual binary-image-compatible data. |
| `Topology/CompactConstraintGluing.lean` | `exists_of_finite_constraints` | Arbitrarily many closed constraints glue inside one specified compact set. |
| same | `exists_energy_le_iff` | Global feasibility with energy at most B is equivalent to finite feasibility with the same bound B, provided that sublevel is compact. |
| same | `exists_joint_of_finite`, `exists_joint_of_pairwise` | Compact arbitrary-family reconstruction, including the relation-criterion specialization; no countability or separability assumption. |
| `Analysis/ResidualCorrectionCost.lean` | `cost_completion` | Complete equality: correction cost = inverse projected-residual energy + a squared normalization error. |
| same | `cost_isLeast`, `no_correction_iff` | The optimum is attained when the residual projection is nonzero; zero projection means no nonzero-correlation correction exists. |
| same | `normalized_budget_iff`, `logarithmic_budget_iff` | Exact equivalence between a normalized cost budget and a lower bound on the actual projected-residual energy. |
| same | `mem_of_eventual_uniform_budget` | For a net in W converging to the orthogonal projection of x, one eventual stage-independent correction budget forces x to belong to W. The budget is a hypothesis. |
| `RH/QFullResidualCorrectionCost.lean` | `projected_residual` | For N <= M, projection of qOne - candidate N onto stage M is candidate M - candidate N. |
| same | `residual_energy_completion` | Exact Pythagorean residual-energy decrease. |
| same | `correction_cost_isLeast` | The minimum cost equals the reciprocal of the actual residual-energy decrease. |
| same | `correction_budget_iff_gain`, `logarithmic_correction_budget_iff_gain` | The actual inverse-Gram residuals satisfy the exact cost/gain equivalence. |

Namespaces follow the module names, except the relation module uses
`RiemannResearch.Logic.FamilyCRT`.

## The exact Q identity

Write r_N = qOne - candidate N, where candidate N is the already-established
actual Q-orthogonal projection onto the span of conductors 2 through N+1.
For N <= M,

```math
||r_N||^2 = ||r_M||^2 + ||candidate M - candidate N||^2.
```

If the increment is nonzero, then

```math
min_{w in stage M, <r_N,w> != 0} ||w||^2 / <r_N,w>^2
  = 1 / (||r_N||^2 - ||r_M||^2).
```

For r_N nonzero and K > 0, existence of a correction with normalized cost
at most K is equivalent to

```math
||r_N||^2 / K <= ||r_N||^2 - ||r_M||^2.
```

The equality `cost_completion` retains the full nonnegative error term;
the inequality above is derived from that exact identity.

## Conditional research reduction and open provider

`QFullResidualCorrectionCost.riemannHypothesis_of_uniform_legal_correction_budget`
proves RH under this explicit premise:

There is one K > 0 such that, at every sufficiently late stage N whose
actual residual r_N is nonzero, there is a finite legal correction w with
nonzero actual correlation and

```math
||r_N||^2 * ||w||^2 / <r_N,w>^2 <= K.
```

The proof first forces qOne into the full legal closure and then invokes
the existing, unconditional sufficient implication
`QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure`.
It uses no converse Baez-Duarte approximation provider.

**Open:** construct these corrections and prove the uniform budget.
**Open:** establish the note's arithmetic lower bound
`||P_W r_L||^2 >= ||r_L||^2 / (C log L)` for the intended correction spaces.
A logarithmic stage-dependent bound is not the stage-independent premise
above; a descent application also needs an appropriate growth/divergence
argument. Finite CRT and compactness do not establish either bound.

## Coverage boundary for the source note

| Source item | Coverage in this continuation |
| --- | --- |
| A | Exact equivalence for setoids on a type. General regular-category internal relations and regular-epimorphic covers remain to be formalized. |
| B | Set-based matching-map surjectivity and uniqueness modulo the intersection. A bundled categorical quotient/matching-object isomorphism and its functor/slice preservation remain. |
| C | Arbitrary-family existence on a compact domain. The quotient homeomorphism and general inverse-limit completion construction remain. Existing integer profinite modules are unchanged. |
| D | Exact extension at one prescribed compact energy sublevel. The full extended-real infimum/supremum equality and attainment at the optimal level remain. |
| E | Existing `Analysis/FiniteHilbertConstraints.lean` already supplies independent finite-row inverse-Gram minima and exact completion. The full singular-Gram Moore-Penrose and arbitrary-family optimal-energy package is not claimed here. |
| F | Attained optimum, zero-projection obstruction, full error identity, budget equivalence, and actual-Q residual specialization formalized. |

## Verification

Acceptance uses the Lean server with Bazel and BuildBuddy. The final
publication checkpoint validates the complete project, including all new
modules and their consumers. Eight named theorem axiom inspections are
included in the retained verification run; its terminal receipt and the
published commit are reported with the continuation. No unresolved
mathematical provider is promoted to an unconditional result.

Verified development receipts:

- All four modules imported together: `job_JR0aWd4nVjKniXiU0R2YotSk5hUaY5KK`, Bazel success.
- Eight guarded axiom checks: `job_NHg4VUpc80uyuI8v-1kdpqNnbTWOqyB2`, Bazel success.
- The guarded outputs are exactly `propext`, `Classical.choice`, and `Quot.sound`.
- [Axiom-check build receipt](https://app.buildbuddy.io/invocation/f83aa679-713c-4a30-bcfd-96580ea8c714).
- The publication checkpoint covers `//:RiemannResearch`; these focused receipts alone do not certify the full project.

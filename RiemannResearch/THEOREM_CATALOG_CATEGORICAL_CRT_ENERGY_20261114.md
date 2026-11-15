# Categorical CRT, compact reconstruction, and exact energy

Source: *Categorical Chinese remainder theorems: exact gluing, compact completion,
and energy*, research note for Christian Noack, 14 November 2026.

This development adds 17 Lean modules with 154 theorem declarations, formalizing
the reconstruction results developed in that note.
The literature survey is provenance, not a claim that the cited papers have been
formalized in their entirety. In particular, no Verdier-quotient or majority-category
classification theorem is asserted here.

## Finite categorical reconstruction

| Result | Lean source and main declaration |
| --- | --- |
| Hereditary finite CRT is equivalent to the family-local composition/intersection law | `CategoryTheory/FiniteFamilyCRT.lean` and `CategoryTheory/LocalFamilyCRT.lean`; `CategoryTheory.GeneralizedEquivalence.hasLocalFiniteCRT_iff_localGluing` |
| The local theorem applies to genuine internal equivalence-relation diagrams | `CategoryTheory.InternalEquivalencePresentation.finite_crt_iff_gluing` |
| Quotient matching tuples lift locally along a regular epimorphism | `CategoryTheory/QuotientMatchingCRT.lean`; `quotient_crt_local_lift`, `quotient_matching_isRegularEpi` |
| Exact common kernel, uniqueness in the separated case, image universal property, and stability under pullback | `quotient_matching_kernel`, `quotient_matching_isIso`, `quotient_image_matching_universal`, `quotient_matching_pullback` |

`RegularCoverCalculus` exposes the structural hypotheses actually used:
pullbacks exist, and regular epimorphisms are stable under composition and
pullback. Internal relations are presented by jointly monic projection pairs,
with reflexivity, symmetry, and transitivity diagrams. Local witnesses are
regular-epimorphic covers; no global section is assumed. This formulation applies
in a regular category without assuming effectiveness of all equivalence relations.

The Setoid development also supplies quotient/matching equivalence, uniqueness,
composition equals join for permuting congruences, and the family distributivity
sufficient condition. Agreement modulo a join is used only under the required
permutability condition.

`CategoryTheory/RegularCategoryCRT.lean` supplies standard regular-category
structure and constructs the matching quotient by factoring the joint product
map. The cover-composition property is derived from regular image factorization.
`FunctorCRT.lean` maps internal equivalence diagrams through pullback-preserving
functors and transports local witnesses when regular epimorphisms are preserved.

`OverlapEqualizerCRT.lean` constructs the literal equalizer of the two product
overlap arrows and proves `exists_overlap_equalizer_quotient`. Its explicit
overlap criterion states that agreement in each chosen common quotient is
exactly local binary realizability. This prevents an unjustified replacement
of actual compatibility by arbitrary common-quotient equality. The Setoid
version additionally derives the overlap criterion for permuting joins.

The transport API proves explicit internal-diagram/functor witness transport
and arbitrary parameter pullback stability. It does not introduce an automatic
instance for every slice category or a general-purpose regular-functor API for
all constructed limits and relation lattices.

## Infinite reconstruction and compact energy

| Result | Lean source and main declaration |
| --- | --- |
| Closed-constraint finite intersection criterion in a compact set | `Analysis/CompactConstraintEnergy.lean`; `CompactConstraintEnergy.exists_mem_all_iff_finite` |
| Exact extended-real identity: global infimum equals supremum of finite infima | `CompactConstraintEnergy.optimum_iInter_eq_iSup_finite` |
| A finite supremum is attained by a global minimizer | `CompactConstraintEnergy.exists_global_minimizer` |
| Continuous coordinate lifting and pairwise CRT under compactness | `CompactConstraintEnergy.exists_lift_iff_finite`, `exists_lift_iff_pairwise` |
| Compact quotient by common kernel is homeomorphic to matching tuples | `Analysis/CompactMatchingQuotient.lean`; `CompactConstraintEnergy.matchingQuotientHomeomorph` |
| Weak, weak-star, and general reflexive uniform-ball versions | `Analysis/WeakCompactConstraints.lean` |
| Completion as the inverse limit of actual finite coordinate images | `Analysis/FiniteCoordinateCompletion.lean`; `FiniteCoordinate.completionEquivImageLimit`, `completionHomeomorphImageLimit` |
| For discrete coordinates, completion is the image closure; the original image is dense | `FiniteCoordinate.compatible_iff_mem_closure`, `toCompletion_denseRange` |
| Compact coordinate spaces give compact completion; finite CRT identifies it with pairwise matching tuples | `FiniteCoordinate.completionCompactSpace`, `completionHomeomorphMatching` |

The energy theorem strengthens the note: Hausdorffness is unnecessary, and only
finite energy sublevels need be compact. Lower semicontinuity supplies closed
sublevels. Arbitrary index types are allowed, and the empty finite subsystem is
included. Infeasible systems retain energy infinity. Weak and weak-star closure
are explicit requirements for the corresponding applications. General reflexivity
is represented by surjectivity of the canonical map into the bidual; compactness
of weak balls is proved from this condition.

`FiniteCoordinate.compatible_operation`, `completionOperation`,
`toCompletion_operation`, and `continuous_completionOperation` construct the
induced compatible algebraic operations and prove preservation by the canonical
map, with continuity whenever the coordinate operations are continuous.

## Hilbert reconstruction and exact costs

| Result | Lean source and main declaration |
| --- | --- |
| Finite-dimensional Moore–Penrose operator and all four Penrose identities | `Analysis/FiniteMoorePenrose.lean`; `LinearMap.moorePenrose`, `map_moorePenrose_map`, `moorePenrose_map_moorePenrose`, `map_moorePenrose_symmetric`, `moorePenrose_map_symmetric` |
| Singular Gram feasibility is precisely the Gram range condition | `Analysis/FiniteSingularGramReconstruction.lean`; `finite_feasible_iff_gram_range` |
| Canonical least-norm vector, exact quadratic cost, and complete square remainder | `gramMinimumVector_energy`, `gramMinimumVector_completion`, `gramMinimumVector_unique`, `finiteConstraintEnergy_eq` |
| Arbitrary-family global bounded interpolation iff uniformly bounded finite interpolation | `Analysis/HilbertConstraintReconstruction.lean`; `Submodule.bounded_finset_test_feasibility_iff` |
| All solutions form an affine orthogonal complement; unique minimum in the closed constraint span | `isSolution_iff_sub_mem_orthogonal`, `canonical_unique_minimizer`, `existsUnique_solution_in_closedSpan` |
| Actual finite-optimum supremum is finite iff a global solution exists | `Analysis/HilbertConstraintEnergy.lean`; `exists_solution_iff_iSup_finiteOptimum_lt_top` |
| Global existence iff a uniform finite-coefficient dual inequality | `exists_solution_iff_dualBound` |
| Global optimum and canonical energy equal the supremum of finite optima | `globalOptimum_eq_iSup_finiteOptimum`, `canonical_energy_eq_iSup` |
| Canonical finite reconstructions converge strongly as a net; cofinal specializations | `finiteMinimum_tendsto`, `finiteMinimum_tendsto_of_cofinal` |
| Exact energy increments and approximation error | `finiteMinimum_energy_increment`, `finiteMinimum_exact_error` |
| The squared norm of the canonical solution is the optimal dual constant | `canonical_energy_isLeast_dualBound` |
| Exact residual-correlation cost, including the zero-projection/infinite-cost case | `Analysis/ResidualCorrelationCost.lean`; `residualCorrelationCost_inverse` |
| Normalized logarithmic cost bound iff the residual-projection lower bound | `logarithmic_cost_bound_iff` |

The Hilbert reconstruction statements use real Hilbert spaces, fixed targets,
and all finite subsets of an arbitrary index type. The finite coefficient
definition permits dependencies among constraint vectors. Inconsistent finite
data have infinite optimum. The net convergence theorem does not apply without
additional work to targets which change with the stage.

## Checked obstructions

`LinearAlgebra/CRTReconstructionObstructions.lean` contains:

- Join-compatible classes of two equivalence relations on three points with no
  common representative.
- Three linear observations of the plane whose binary maps are all surjective
  but whose prescribed triple has no solution.
- The exact kernel-lattice distributivity failure for those observations.
- A family of linear isomorphisms with unbounded reconstruction energy for one
  fixed target, including its exact inverse and energy.
- Unit coordinate data with finite square-summable realizations of optimal
  energy equal to the finite cardinality, but no global square-summable solution.

`NumberTheory/InfiniteCRTObstruction.lean` proves every finite system of
power-of-two zero congruences together with the residue one modulo three has
an integer solution, while the full infinite system has none.

## Existing arithmetic coverage reused

- `NumberTheory/FiniteGeneralizedCRT.lean`: arbitrary noncoprime integer CRT,
  pairwise gcd compatibility, lcm solution class, and standard representatives.
- `NumberTheory/ProfiniteGeneralizedCRT.lean`: arbitrary compatible residue
  families, cofinal uniqueness, and finite-coordinate convergence.
- `NumberTheory/ProfiniteCRT.lean`: the profinite integer ring is topologically
  isomorphic to the product of its p-adic integer factors.
- `NumberTheory/ProfiniteCRTUniversal.lean`: continuous ring-homomorphism
  universal properties and precomposition naturality.

## RH boundary

**Conditional research reduction.** Applying these abstract results to the
Pareto/RH reconstruction problem still requires checked providers for the actual
admissible space, bounded observation functionals, and the correct fixed target.
The target-specific uniform Gram cost (equivalently the finite-coefficient dual
bound) remains an arithmetic/analytic obligation. For residual-normalized
corrections, the remaining estimate is a lower bound on the actual residual's
projection onto the admissible correction space. The logarithmic equivalence
formalizes that obligation; it does not discharge it or prove RH.

## Actual-Q specialization retained from main

The earlier continuation in commit [ab7f34d](https://github.com/Cnoack3/RiemannResearch/commit/ab7f34dc8f5b6164804844f46c1792f95155e009) is retained. Its actual-residual application complements the abstract reconstruction package above.

### Established declarations

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

### The exact Q identity

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

### Conditional research reduction and open provider

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


### Earlier focused verification receipts

Verified development receipts:

- All four modules imported together: `job_JR0aWd4nVjKniXiU0R2YotSk5hUaY5KK`, Bazel success.
- Eight guarded axiom checks: `job_NHg4VUpc80uyuI8v-1kdpqNnbTWOqyB2`, Bazel success.
- The guarded outputs are exactly `propext`, `Classical.choice`, and `Quot.sound`.
- [Axiom-check build receipt](https://app.buildbuddy.io/invocation/f83aa679-713c-4a30-bcfd-96580ea8c714).
- The publication checkpoint covers `//:RiemannResearch`; these focused receipts alone do not certify the full project.


## Verification policy

The source is published only after the Lean server checkpoint audits the entire
unpublished change and successfully builds `//:RiemannResearch` with Bazel and
BuildBuddy, including integration with newer main-branch work. The handoff records
the terminal checkpoint receipt and exact published commit. Focused acceptance
and axiom receipts are recorded with the development handoff; they do not replace
the full-project gate. Explicit hypotheses in theorem types remain part of their
mathematical meaning even when their axiom inventories contain only standard
Lean foundations.

## Focused acceptance receipts

| Scope | Successful Bazel job | Server verification time |
| --- | --- | ---: |
| Fifteen integrated modules, thirteen principal guarded axiom lists | `job_r6TC2-WkiJ0zaz9h2pl0afaBXw6HnOg7` | 38.272 s |
| Standard regular-category provider and constructed matching quotient | `job_BefcC3LqwQG2uyOMon-C8mM-B1Erv476` | 14.584 s |
| Explicit overlap equalizer | `job_8Dyu-b7M6DIvvroKeayXJaY8QvC04D6N` | 28.704 s |
| Integrated structural category/equalizer modules, three further guarded axiom lists | `job_VBW49kT7grfqpwqobvdrowPHwEKnjm5S` | 50.182 s |

The sixteen integrated principal axiom guards require exactly `propext`,
`Classical.choice`, and `Quot.sound`. The subsequent full-project publication
checkpoint is the acceptance gate for the complete integrated change.

## Growing actual-Q correction budgets (15 November 2026)

Continuation module: `RH/QFullCorrectionBudgetDescent.lean`, namespace
`RiemannResearch.RH.QFullCorrectionBudgetDescent`. It adds two definitions
and fifteen theorems to the earlier reconstruction package.

### Exact finite statements

For a nondecreasing stage schedule σ, put
E_k = ||qOne - candidate (σ k)||² and let K_k > 0.
`CorrectionBudget (σ k) (σ (k+1)) (K k)` means that, unless the old
residual is zero, there is w in the specified next stage with nonzero
actual Q correlation and

```math
E_k ||w||² / <r_(σ k),w>² <= K_k.
```

The zero-residual case requires no correction. The exact cost conversion is

```math
CorrectionBudget (σ k) (σ (k+1)) K_k
  iff E_k / K_k <= E_k - E_(k+1).
```

`correction_budget_accounting` keeps both complete remainder sums:

```math
E_0 = E_n (1 + sum_(k<n) 1/K_k)
    + sum_(k<n) (E_k - E_n)/K_k
    + sum_(k<n) (||candidate(σ(k+1))-candidate(σ(k))||² - E_k/K_k).
```

No positivity or budget assumption is needed for this equality. Under valid
positive budgets, the remainders are nonnegative. The resulting finite bound is

```math
E_n <= E_0 exp(-sum_(k<n) 1/K_k).
```

For K_k = C(k+1), C > 0,
`energy_le_exp_neg_harmonic_of_linear_budgets` gives

```math
E_n <= E_0 exp(-H_n/C).
```

If δ = ||qOne - closure.starProjection qOne||² > 0, the complementary
`reciprocal_sum_le_of_positive_limiting_energy` proves, for every n,

```math
sum_(k<n) 1/K_k <= E_0/δ - 1.
```

### Conditional research reductions

| Declaration | Explicit sufficient input |
| --- | --- |
| `riemannHypothesis_of_reciprocal_budgets` | A nondecreasing stage schedule, positive budgets, eventual corrections in the specified next stage, and nonsummability of 1/K_k. |
| `riemannHypothesis_of_linear_budgets` | Eventual next-stage corrections with normalized cost at most C(k+1), for one C > 0. |
| `riemannHypothesis_of_logarithmic_budgets` | Eventual cost at most C log L_k and eventual log L_k <= A(k+1), for positive C and A. |
| `riemannHypothesis_of_geometric_scale_logarithmic_budgets` | Eventual cost at most C log(L^(k+1)), with C > 0 and L > 1. |

The proof first obtains vanishing actual-Q residual energy along the schedule,
then qOne membership in the full legal closure, and finally the existing
unconditional sufficient implication to RH. Cofinality is unnecessary for this
implication; the global limiting residual energy is a lower bound at every
stage. No converse from RH to full-Q density is used.

`summable_reciprocal_budgets_of_not_riemannHypothesis` records the contrapositive:
if RH fails, the reciprocals of every valid eventual positive budget schedule
are summable.

**Open arithmetic provider:** construct the corrections inside the specified
next stage and prove their normalized actual-Q costs obey one of these bounds.
An arbitrary correction lying somewhere in the full finite legal span gives
no prescribed bound on the next-stage conductor. If L_k is an LCM modulus,
the growth hypothesis must be proved for that actual modulus. Geometric
growth of the conductor cutoff does not itself give log L_k = O(k).

Finite CRT and the abstract duality theorems supply none of these arithmetic
cost or scale-growth estimates. RH remains open in this continuation.

### Focused acceptance for this continuation

- Final module and principal declaration checks: Bazel job
  `job_Uaks8JtHOGI-HWX2XWSwAxHTR6gZr0u3`, successful; server verification
  54.611 seconds. [Build receipt](https://app.buildbuddy.io/invocation/b9ea1637-b6ce-4373-81a2-092d25686063).
- Four exact axiom-output guards: Bazel job
  `job_yNb9bSuamgS9b-6stxt5jTBcJURSUoMw`, successful; server verification
  45.111 seconds. [Build receipt](https://app.buildbuddy.io/invocation/684b9ea8-84d0-4c04-bf31-b35696bdd5ae).
  The accounting identity, harmonic finite bound, reciprocal-budget RH
  implication, and geometric-scale logarithmic implication depend exactly on
  `propext`, `Classical.choice`, and `Quot.sound`.

These are focused receipts. Publication remains gated by the subsequent
full-project Bazel checkpoint, including integration of newer main changes.

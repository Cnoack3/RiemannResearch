# RH part 2 theorem catalog — 16 November 2026

This catalog covers selected formalizations from the Drive RH review. It does not certify entire papers. See [research report](RH_PART2_REVIEW_20261116.md) and [paper ledger](RH_PART2_PAPER_LEDGER_20261116.md).

## Established finite and Hilbert-space identities

### HeadTailDriftObstruction

File: `RiemannResearch/LinearAlgebra/HeadTailDriftObstruction.lean`.
Namespace: `RiemannResearch.LinearAlgebra.HeadTailDrift`.
Source: audited Nyman–Beurling paper, sections 21 and 23.9.

| Declaration | Exact content and assumptions |
|---|---|
| `normal_completion` | Under full column normal equations, the two-block least-squares loss equals target energy plus both column energies. |
| `normal_minimizes` | Coefficient zero minimizes the full loss under those normal equations. |
| `accessible_pairing` | Inverse of the complete tail Gram maps the head correlations to a tail vector with exactly those correlations. |
| `graph_normal` | The target `(h,-accessible h)` satisfies all full normal equations. |
| `drift_eq_accessible` | Every normal target has drift equal to its accessible head response. |
| `attainable_iff` | Exact attainable drift range, assuming the supplied linear equivalence is the full tail Gram. |
| `no_uniform_strict_angle` | Every nonzero accessible direction defeats any proposed target-independent angle constant κ<1. |
| `tail_completion` | Exact least-squares completion at the inverse-full-tail-Gram optimizer. |
| `normal_minimizer_unique` | Under invertible tail Gram, equality with the full minimum is equivalent to coefficient zero. |
| `normal_tail_energy` | Exact Pythagorean identity for every normal extension of a given head. |

The ambient spaces need only real inner-product structures; the column index is finite. No actual arithmetic-source estimate, RH hypothesis, completeness assumption, diagonal Gram approximation or omitted cross term appears.

### ReciprocalMaxGreen

File: `RiemannResearch/LinearAlgebra/ReciprocalMaxGreen.lean`.
Source: growing-degree ridge paper, section 14.2.

| Namespace / declaration | Exact content and assumptions |
|---|---|
| `WeightedGreen.tail_telescope` | Tail of consecutive differences, including both endpoints. |
| `WeightedGreen.prefix_initialDifference` | Prefix is a left inverse of the initial-difference operator. |
| `WeightedGreen.applyGreen_applyInverse` | Right inverse for nonzero edge weights and prescribed zero right boundary. |
| `WeightedGreen.inverse_dirichlet_identity` | Inverse quadratic energy equals the complete weighted difference energy. |
| `ReciprocalMaxGreen.weight_interior` | Interior reciprocal-time difference is `1/((i+1)(i+2))`. |
| `ReciprocalMaxGreen.weight_boundary` | Terminal weight for an `(N+1)`-point system is `1/(N+1)`. |
| `ReciprocalMaxGreen.weight_pos` | Every retained finite-system weight is strictly positive. |
| `ReciprocalMaxGreen.kernel_eq_reciprocal_max` | Green kernel is exactly `1/(max i j + 1)` in zero-based coordinates. |
| `ReciprocalMaxGreen.brownian_energy` | Complete finite cumulative-charge quadratic identity with terminal tail. |
| `ReciprocalMaxGreen.brownian_inverse` | Left inverse of the reciprocal-max Green map. |
| `ReciprocalMaxGreen.brownian_inverse_energy` | Explicit nearest-neighbor precision energy, including terminal term. |

Both namespace prefixes above are under `RiemannResearch.LinearAlgebra`. This is a finite algebraic specialization. It supplies no infinite Mellin interchange or actual CRT-source observability bound.

### FiniteCoordinateDecoding

File: `RiemannResearch/Analysis/FiniteCoordinateDecoding.lean`.
Namespace: `RiemannResearch.Analysis.FiniteCoordinateDecoding`.
Source: modular phase reconstruction paper's noisy finite-prime agenda.

| Declaration | Exact content and assumptions |
|---|---|
| `bad_triangle_subset` | Far coordinates of two candidates lie in the union of their bad-coordinate sets relative to one observation. |
| `separation_card_le` | Candidate separation count is at most the sum of their two corruption budgets. |
| `unique_of_error_budgets` | Code separation larger than that sum forces unique decoding, with unequal tolerances/budgets allowed. |
| `bad_card_le_of_good_outside` | An explicit discarded set bounds the number of bad coordinates. |

Coordinates range over a finite decidable index type and an arbitrary pseudometric space. Actual zero-code separation is an explicit application hypothesis, not a theorem proved here.

### ThreeBlockOptimizerObstruction

File: `RiemannResearch/LinearAlgebra/ThreeBlockOptimizerObstruction.lean`.
Namespace: `RiemannResearch.LinearAlgebra.ThreeBlockOptimizerObstruction`.
Source: cross-route audit's rational counterexample; strengthened here by adding the identity to every Gram block.

| Declarations | Exact content |
|---|---|
| `gram_symmetric`, `gram_lower_bound`, `gram_upper_bound`, `gram_strictly_positive` | Three real symmetric blocks satisfy I ≤ G_j ≤ 3I and have positive quadratic form on every nonzero vector. |
| `inverseGram_mul_totalGram`, `totalGram_mul_inverseGram` | Explicit complete-Gram inverse on both sides. |
| `common_normal` | Exact common-optimizer normal equations. |
| `loss_completion`, `common_loss`, `common_minimizes` | Complete square remainder, true minimum 13/6, and optimality. |
| `discardedPairwise_value`, `exact_defect`, `pairwise_formula_false` | Proposed pairwise value 55/24, signed defect −1/8 and failure even for uniformly positive blocks. |

This is a counterexample to a generic coefficient-space formula, not to the actual arithmetic bound or to the valid two-block theorem.

## Conditional research reductions and open providers

| Obligation | Status | Why these additions do not discharge it |
|---|---|---|
| Audited NB A1/A2 and actual curvature bound (23.29) | Open | The normal-equation range theorem allows arbitrary accessible alignment; arithmetic specificity is necessary. |
| Full-source reciprocal-max/CRT observability | Open | A matrix inverse and exact energy identity do not bound the prescribed source across growing conductor systems. |
| Robust zero-phase separation rate | Open | Finite-code separation is assumed, and retained data are floating-point. |
| Uniform Selberg-density provider used by `PrimePhaseWindows` | Open in the inspected provider chain | No analytic density theorem is supplied by coordinate decoding. |
| C2 odd operator positivity | External repaired computation; Lean bridge pending | Interval implementation and operator/analytic-tail reductions are not kernel-checked here. |
| C2 constrained even inequality | Open | Positive odd-sector numerical pivots do not imply the even-sector inequality. |
| F7–F11/G85–G92 absolute source observability | Open | Equal source covectors, projective alignment, upper bounds and generic Schur identities do not supply the lower bound. |
| Global V-Weil / spectralizing determinant construction | Open | Finite factors and RH-equivalent acceptance tests are not independent providers. |

## Evidence

38 theorem declarations across four exported modules. Guarded axiom checks cover ten principal results and require exactly the standard foundations `propext`, `Classical.choice`, `Quot.sound`. The [verification manifest](ResearchData/RHPart2_20261116/verification_manifest.json) records source hashes, focused jobs and their scope. The managed publication checkpoint supplies final `//:RiemannResearch` acceptance; its exact terminal commit/job is reported separately to avoid treating an earlier focused check as full-project evidence.

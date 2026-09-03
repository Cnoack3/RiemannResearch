# Combined Audited Manuscript Lean Catalog

Source: `combined_audited_manuscript(4).pdf` (August 2026).

This catalog is an addendum for the formalization in:

- `RiemannResearch/RH/CombinedAuditedInventory.lean`
- `RiemannResearch/RH/CombinedAuditedCore.lean`
- `RiemannResearch/RH/CombinedGain.lean`

The source contains 55 distinct numbered claims.  The inventory records all 55:
18 have kernel-checked algebraic or logical cores, 7 are represented by typed
statement interfaces, and 30 remain deferred at source-theorem strength.
A formalized core must not be read as certification of every analytic or
geometric assertion in the corresponding manuscript theorem.

## Arithmetic and finite-difference cores

| Declaration | Source claim | Scope |
|---|---:|---|
| `primeExponent_reconstructs` | 2.1 | Reconstruction from finite prime exponents |
| `primeExponent_mul` | 2.1 | Multiplication adds prime exponents |
| `primeExponent_le_iff_dvd` | 2.1 | Divisibility is coordinatewise comparison |
| `forwardDifference` | 2.3 | One-coordinate forward difference |
| `sum_forwardDifference` | 2.3 | Exact finite telescoping |

## Algebraic and homological obstruction cores

| Declaration | Source claim | Scope |
|---|---:|---|
| `representedOrbitEquivRange` | 3.1 | Linear first-isomorphism theorem |
| `hochschildBoundaryOne` | 3.2 | Degree-one elementary boundary |
| `hochschildBoundaryOne_eq_zero` | 3.2 | Commutative boundary vanishes |
| `onePrimeHochschildObstruction` | 3.2 | Nonzero Boolean edge is not such a boundary |

## Optimizer, Schur, and dual-frame cores

| Declaration | Source claim | Scope |
|---|---:|---|
| `scalarGluingPenalty` | 8.1 | Common-optimizer penalty |
| `scalarOptimizerAwareTotalVariance` | 8.1 | Scalar loss decomposition |
| `scalarGluingPenalty_nonneg` | 8.1 | Positivity of the penalty |
| `scalarGluingPenalty_eq_zero_iff` | 8.1 | Exact synchronization condition |
| `scalarHeadTailSchurIdentity` | 8.2 | Scalar Schur completion |
| `scalarHeadTailSchur_lowerBound` | 8.2 | Scalar Schur lower bound |
| `scalarMinimumEnergyDualFrame` | 8.3 | Scalar constrained minimum-energy lift |

## Pointed-object, shift, and telescope cores

| Declaration | Source claim | Scope |
|---|---:|---|
| `FOne` | 9.1 | Two-element pointed object |
| `fOneMap` | 9.1 | Canonical pointed map |
| `fOneMap_unique` | 9.1 | Point-preserving uniqueness |
| `unilateralShift` | 9.2 | Shift on sequences |
| `unilateralShift_injective` | 9.2 | Shift injectivity |
| `exists_unilateralShift_iff` | 9.2 | Exact range characterization |
| `finiteGeometricTelescope` | 10.2 | Finite Hardy--Ruelle/Euler telescope core |

## Positivity, spectral-parameter, and symmetry cores

| Declaration | Source claim | Scope |
|---|---:|---|
| `functionalEquationPairForm` | 12.4, 12.16 | Two-evaluation block |
| `functionalEquationPairForm_pos` | 12.4, 12.16 | Positive direction |
| `functionalEquationPairForm_neg` | 12.4, 12.16 | Negative direction |
| `scalarRenormalizationCannotRemoveNegative` | 12.6 | Persistence of a scalar negative direction |
| `deningerEigenvalue_onCriticalLine` | 12.17 | Polarization eigenvalue algebra |
| `deningerPolarizationImplication` | 12.17 | Conditional implication to RH |
| `secondOrder_im` | 12.18 | Imaginary part of `rho * (1-rho)` |
| `criticalLine_of_secondOrder_real` | 12.18 | Reality plus nonrealness forces the line |
| `arithmeticSecondOrderImplication` | 12.18 | Conditional implication to RH |
| `nonnegative_of_tendsto_nonnegative` | 12.19 | Positivity passes to a pointwise limit |
| `exactConditionalPositivityBridge` | 12.19 | Conditional Weil-positivity implication |
| `criticalReflection` | 13.1 | Critical-line reflection |
| `criticalReflection_fixed_iff` | 13.1 | Fixed-point characterization |
| `symmetryQuartet_sum` | 13.2 | Constant quartet sum |

## Typed conjectural and classical interfaces

| Declaration | Source claim | Status |
|---|---:|---|
| `RieszCriterionTarget` | 4.1 | Statement shape only |
| `NymanBeurlingTarget` | 4.2 | Statement shape only |
| `CRTToNymanTarget` | 7.2 | Statement shape only |
| `UnrestrictedCentralEstimateTarget` | 7.3 | Statement shape only |
| `PolarVanishingWeilCriterionTarget` | 12.7 | Statement shape only |
| `SupportAdaptiveCertificate` | 12.20 | Certificate data structure |
| `SupportAdaptiveSemilocalTraceBridge` | 12.20 | Conjecture as a proposition, not an axiom |
| `supportAdaptiveSemilocalTraceBridgeImplication` | 12.20 | Conditional implication to RH |
| `LiRunningMaximumCriterionTarget` | 13.3 | Statement shape only |

## Inventory integrity

`CombinedAuditedInventory.items_length` proves that the source ledger contains
exactly 55 entries.  No project-local `axiom`, `sorry`, `admit`, or `unsafe`
declaration is used by these modules.

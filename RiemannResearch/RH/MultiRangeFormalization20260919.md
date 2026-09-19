# Multi-range divisor corrections: formalization ledger

This continues the September 18 source note and supersedes the verification status in `MultiRangeSubmission20260918.md`. The mathematical source is `RH_Multi_Range_Divisor_Corrections_2026-09-18.md`; its original narrative is retained as provenance.

The Lean declarations concern the actual infinite conditional-mean energy. Coefficients are finite deterministic vectors shared by all conditional means. Signed cross terms are retained. Raw floors are converted to balanced legal residue combinations before infinite energy is formed.

## Scope

- **Construction and completeness:** `MultiRangeDivisorCorrections`, `MultiRangeCompleteness`, `MultiRangeExhaustion`, `MultiRangeFloorCoordinates`, `MultiRangeIndependence`, `MultiRangePrimorialCoordinates`, and `MultiRangePrimorialRebase` cover balanced floors, low Möbius coefficients, legal anchor corrections, exact prescribed heads, coefficient uniqueness, equality of energy sets, and conversion of positive cofinal legal families to divisor-range families. The original sieve characterization has its exact balance `sum x_d/d = -alpha`, including overlapping supports.
- **Actual finite minima:** `MultiRangeFiniteMinimum` constructs the positive-definite arithmetic Gram matrix, its inverse solution, the attained signed minimum, and uniqueness. Positivity and inverse existence are proved rather than assumed.
- **Old/new range interaction:** `MultiRangeScreening`, `MultiRangeSignedFiniteFamily`, and `MultiRangeBlockGain` retain the old/new cross matrix through exact screened Gram entries and correlations. The actual arithmetic screened family supplies positivity and the inverse solution. The attained block witness minimizes over every original old/new coefficient array; explicit original coefficients are also supplied.
- **Exhaustion and budgets:** `MultiRangeMinimumExhaustion` proves decreasing finite-dictionary infima converge to the full legal infimum. `MultiRangeGainBudget` proves telescoping reoptimized gains, the exact product identity, and geometric decay conditional on the explicitly stated fractional-gain bound. `MultiRangeEnergyCertificates` separately treats scalar projection along a supplied finite correction; that scalar procedure is not mislabeled as full block optimization.
- **Finite certificates:** `MultiRangeCertificateConvergence`, `MultiRangeTruncatedGram`, `MultiRangePrefixOptimization`, `MultiRangeOptimizerConvergence`, `MultiRangeFixedFamilyCertificates`, `MultiRangeCertifiedMinimum`, and the rational-certificate modules connect finite arithmetic computations to the real infinite objective. The explicit horizon reaches every non-anchor divisor; charge recovery gives positive definiteness. Convergence statements fix the finite dictionary, with no rate uniform in a growing dictionary.
- **Delayed corrections:** `MultiRangeDelayedFloors` proves the finite-prefix obstruction using the complete floor support. It also computes the nonzero anchor value of a distant direction, so the anchor caveat is part of the formal statements.
- **Explicit zero obstruction:** `MultiRangeTailObstruction` proves the eventual lower bound
  `E(F) - Y/(Y+2) ≥ (2 Re(s)-1)/(12 ‖s(s+1)‖²) * Y^(2 Re(s)-1)`
  conditional on an off-critical right-half-plane zeta zero, as well as the corresponding infimum bound.

## Existing results reused

The canonical Möbius witness and its stronger bound
`E(F_Y) ≤ Y(2Y+1)/(Y+2) < 2Y`
already occur in `CanonicalMobiusConditionalHead`. This is stronger than the source note's coarse `4Y` bound, but remains polynomial.

The exact smoothed-residue formula, Cesàro contraction and inversion, periodic weighted signed energy/pairing formulas, and periodic defect tail bounds are existing results in `CesaroResidueMean`, `ConditionalMeanTailNonattainment`, `CRTPeriodicEnergy`, `CRTExactSignedEnergy`, and their imports. These are reused without replacing actual conditional weights by uniform CRT averages.

The Mellin second-difference bound, dual-tail estimate, finite summation-by-parts boundary term, boundary decay, signed annihilation, and normalization already occur in `MellinDifferenceBounds`, `CesaroDualTail`, `CesaroFiniteCalculus`, `MellinCesaroSummability`, and `ConditionalMeanHeadObstruction`. The subpolynomial-family implication to mathlib's `RiemannHypothesis` already occurs in `ConditionalMeanSubpolynomial`.

## Open arithmetic construction

`MultiRangeSubpolynomialTarget` is a **definition of an unresolved existence obligation**, not a theorem. `riemannHypothesis_of_multiRangeSubpolynomialTarget` is a **conditional research reduction**. No witness for its hypothesis is supplied.

The following remain open: subpolynomial growth of the optimized family as the exact-head length grows; a uniform fraction of remaining tail energy removed by new ranges; and RH. Finite positivity, strict improvement, exact optimization, fixed-dictionary convergence, and rational computation do not imply these statements.

There are no `sorry`, `admit`, project-local axioms, or unsafe declarations in the submitted development. Proof checks and the final repository checkpoint, rather than this prose, determine publication status.

# Theorem catalog

This catalog is an orientation layer. Lean source files and successful builds
remain authoritative.

## Verified local declarations

| Declaration | Module | Statement / purpose | Status |
|---|---|---|---|
| `sanity_check` | `RiemannResearch.Basic` | Confirms arithmetic tactics and mathlib are available | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.pointFieldIndex_eq` | `RiemannResearch.AlgebraicGeometry.PointFields` | Pointwise equality of rational-point predicates implies equality of the set-gcd indices of all finite point-field degrees | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.closedPointIndex_eq_pointFieldIndex` | `RiemannResearch.AlgebraicGeometry.PointFields` | Identifies the traditional closed-point gcd with the splitting-field gcd under the residue-field and closed-image divisibility hypotheses | Kernel checked |
| `RiemannResearch.AlgebraicGeometry.point_iff_of_fixedLocus_coproduct` | `RiemannResearch.AlgebraicGeometry.PointFields` | A proper-limit map, coproduct fixed locus, and fixed-component inclusion give equality of point fields | Kernel checked |
| `RiemannResearch.GroupTheory.exists_nonzero_fixedPoint_of_isPGroup_of_not_card_modEq_one` | `RiemannResearch.GroupTheory.PGroupFixedPoints` | A finite `p`-group acting additively on finite `V` has a nonzero fixed point when `Nat.card V ≢ 1 [MOD p]` | Kernel checked |
| `RiemannResearch.E8.omegaEightPlusTwo_order` | `RiemannResearch.E8.OmegaEightPlusTwo` | `2^12 · 3^5 · 5^2 · 7 = 174182400` | Kernel checked |
| `RiemannResearch.E8.nonabelian_of_isSimpleGroup_of_card_eq_omegaOrder` | `RiemannResearch.E8.OmegaEightPlusTwo` | A simple group of order `2^12 · 3^5 · 5^2 · 7` is nonabelian | Kernel checked |
| `RiemannResearch.E8.quasisimpleCoreOfFullWeylDescent` | `RiemannResearch.E8.FullWeylCore` | Under explicit Gille, `W⁺/Z ≃ Ω₈⁺(2)`, lattice-cardinality, and marker-criterion hypotheses, proves parts (i)--(iii) and `Neutral(ξ) ↔ (Neutral(ξ_F) → Neutral(ξ_{k⁺}))` | Kernel checked, conditional on named hypotheses |
| `RiemannResearch.E8.attractingRank_properties` | `RiemannResearch.E8.WonderfulFixedLocus` | The length-plus-descent formula and Coxeter complement identities imply unique zero rank and rank duality | Kernel checked |
| `RiemannResearch.E8.e8AttractingRank_eq_zero_iff` | `RiemannResearch.E8.WonderfulFixedLocus` | On Mathlib's E8 Coxeter group, length plus the number of right descents vanishes exactly at the identity | Kernel checked unconditionally |
| `RiemannResearch.E8.universalFixedLocusAndSplittingField` | `RiemannResearch.E8.WonderfulFixedLocus` | From explicit wonderful-fixed-locus, motivic BB, CH_0, proper-limit, and Borel-reduction inputs, proves (i)--(iii), equality of all point fields and splitting-degree spectra, and equality of set-gcd indices | Kernel checked, conditional on named geometric hypotheses |
| `RiemannResearch.RH.Statement` | `RiemannResearch.RH.Basic` | Stable local name for mathlib's RH proposition | Kernel checked |

## Planned research areas

| Area | Initial target |
|---|---|
| Nyman–Beurling | Define the fractional-part generators in `L²(0,1)` |
| de Branges theory | Hermite–Biehler functions and reproducing-kernel spaces |
| Hilbert–Pólya | A precise conditional spectral formulation |
| Operator theory | Closed, densely defined, and self-adjoint operators |
| Spectral triples | Finite-dimensional prototype, then compact resolvent |
| Noncommutative geometry | C*-algebra representations and commutators |
| Field with one element | Select and encode a precise F₁ framework |
| Serre S₂ | Depth-based formulation for rings and schemes |

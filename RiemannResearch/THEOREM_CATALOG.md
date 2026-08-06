# Theorem catalog

This catalog is an orientation layer. Lean source files and successful builds
remain authoritative.

## Verified local declarations

| Declaration | Module | Statement / purpose | Status |
|---|---|---|---|
| `sanity_check` | `RiemannResearch.Basic` | Confirms arithmetic tactics and mathlib are available | Kernel checked |
| `RiemannResearch.E8.exists_nonzero_fixedPoint_of_isPGroup_of_not_card_modEq_one` | `RiemannResearch.E8.FullWeylCore` | A finite `p`-group acting additively on finite `V` has a nonzero fixed point when `Nat.card V ≢ 1 [MOD p]` | Kernel checked |
| `RiemannResearch.E8.omegaEightPlusTwo_order` | `RiemannResearch.E8.FullWeylCore` | `2^12 · 3^5 · 5^2 · 7 = 174182400` | Kernel checked |
| `RiemannResearch.E8.nonabelian_of_isSimpleGroup_of_card_eq_omegaOrder` | `RiemannResearch.E8.FullWeylCore` | A simple group of order `2^12 · 3^5 · 5^2 · 7` is nonabelian | Kernel checked |
| `RiemannResearch.E8.quasisimpleCoreOfFullWeylDescent` | `RiemannResearch.E8.FullWeylCore` | Under explicit Gille, `W⁺/Z ≃ Ω₈⁺(2)`, lattice-cardinality, and marker-criterion hypotheses, proves parts (i)--(iii) and `Neutral(ξ) ↔ (Neutral(ξ_F) → Neutral(ξ_{k⁺}))` | Kernel checked, conditional on named hypotheses |
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

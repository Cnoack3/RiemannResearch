# Montgomery horizontal Bessel theorem catalog

Date: November 10, 2026.
Starting revision: `29fa256722998cc6fa8b9b0f6682fd7788ffae85`.
Companion research ledger: [MontgomeryHorizontalBesselResearch20261110.md](MontgomeryHorizontalBesselResearch20261110.md).

There are 36 new theorem declarations and 8 definitions in four focused
modules, all under `RiemannResearch.Analysis`.
The analytic upper bounds are unconditional. The four convergence/transfer
results below retain explicit, unresolved asymptotic hypotheses.

| Module | Namespace | Main declaration | Scope and assumptions |
|---|---|---|---|
| `Analysis/MontgomeryResolventDifference.lean` | `MontgomeryResolventDifference` | `inverse_mixed_difference` | Exact four-term inverse difference; only nonzero denominator assumptions. |
| Same | Same | `differenceKernel_bound` | \(\left|\Delta_{a,b}K(id)\right|\le4|ab|w(d)\), for \(|a|,|b|\le1/2\); no zeros or density premise. |
| `Analysis/MontgomeryDifferenceGram.lean` | `MontgomeryDifferenceGram` | `difference_gram` | Complete signed Gram identity for exponential differences; arbitrary finite ordinates and coefficients, including repeated ordinates. |
| Same | Same | `pairFeature_integrable`, `weightedDifference_memLp` | Integrability and L2 membership are proved. |
| Same | Same | `difference_energy_le_of_rows` | Energy bounded by \(4D\sum_i|c_i|^2a_i^2\); explicit Cauchy row bound \(D\). |
| `Analysis/MontgomeryHorizontalBessel.lean` | `MontgomeryHorizontalBessel` | `shiftedDifferenceSignal_split` | Exact signed coefficient/feature decomposition, before estimation. |
| Same | Same | `shiftedDifference_energy_le` | General-frequency squared-coefficient perturbation bound, under a finite row bound. |
| Same | Same | `actual_shiftedDifferenceSignal` | Identification with the actual cosh correction, using actual reflection and every multiplicity. |
| Same | Same | `exists_defectIntegral_le_budget` | Actual unnormalized energy \(\le C\log(T+3)B_T(u)\), \(T\ge0\). Actual local zero counts discharge the row-bound hypothesis. |
| Same | Same | `exists_horizontalDefect_le_budget` | Actual normalized defect \(\mathcal H_T(\alpha)\le C B_T(\alpha\log T)/T\), \(T\ge9\), all real \(\alpha\). |
| Same | Same | `horizontalBudget_le_exponentialMoment` | \(B_T(u)\le(1+v^2)\sum_i\delta_i^2e^{2v|\delta_i|}\), for \(|u|\le v\). |
| Same | Same | `exists_horizontalDefect_le_exponentialMoment` | Uniform actual bound on \(|\alpha|\le A\); the full exponential weights remain. |
| `Analysis/MontgomeryHorizontalLimit.lean` | `MontgomeryHorizontalBessel` | `horizontalDefect_tendsto_zero` | **Conditional:** \(B_T(\alpha(T)\log T)/T\to0\). |
| Same | Same | `sqrt_horizontal_difference_tendsto_zero` | **Conditional:** same budget decay; compares raw/complex square roots. |
| Same | Same | `raw_limit_of_budget` | **Conditional:** budget decay and a nonnegative finite complex form-factor limit. |
| Same | Same | `raw_limit_of_exponentialMoment` | **Conditional:** eventually bounded frequencies, weighted moment decay, and a complex form-factor limit. |

## Open providers

| Obligation | Status |
|---|---|
| Actual budget or weighted-moment decay on a fixed support window | Open |
| Complex or raw form-factor asymptotic above support one | Open |
| Complete normalized gamma remainder and growing homogeneous sampling transfer | Open |
| Transition-frequency concentration and complete weak PCC | Open |
| Montgomery pair correlation conjecture | Not proved |
| Riemann Hypothesis | Not proved |

The positive all-window budget criterion is strong enough to exclude every
off-line zero; the ledger explains why it is not a globally weaker replacement
for RH. No domain-specific hypothesis is silently discharged.

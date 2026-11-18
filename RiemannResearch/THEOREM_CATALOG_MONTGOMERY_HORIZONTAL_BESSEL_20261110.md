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

## Horizontal energy and shrinking Montgomery frequencies

Write $E(T)$ for the total horizontal energy, $r(T)=(\log\log T)^2/\log T$,
and $u=\alpha\log T$. Every zero in the cutoff carries its analytic multiplicity.

| Lean declaration | Result |
|---|---|
| `horizontalEnergy_eq_reflected_pair_add` | A reflected off-line pair contributes exactly $2m(\rho)(\Re\rho-1/2)^2$, with the full sum over the remaining zeros. |
| `riemannHypothesis_iff_cofinal_horizontalEnergy_small` | RH is equivalent to arbitrarily small unnormalized $E(T)$ at arbitrarily large heights. |
| `horizontalEnergy_add_const_div_height_isBigO` | $(E(T)+c)/T=O(r(T))$ for every fixed real $c$. |
| `horizontalBudget_eq_coshMass` | $B_T(u)=E(T)+M_T(2u)-2M_T(u)$, where $M_T$ sums $\cosh(u(\beta-1/2))-1$. |
| `horizontalBudget_le_horizontalEnergy` | $B_T(u)\le(4\cosh u-3)E(T)$ at every height. |
| `horizontalBudget_le_of_strictTail` | If the two-sided tail is bounded by $M e^{-qt}$, then $B_T(u)\le 8M(1+u^2)/q^2$ for $|u|\le q/4$ and $q>0$. |
| `eventually_horizontalBudget_loglog_band` | Uniformly for $|u|\le \log T/(32\log\log T)$, one has $B_T(u)/T\ll(1+u^2)r(T)$. |
| `horizontalBudget_div_height_tendsto_zero_of_loglog`, `sqrt_formFactor_difference_tendsto_zero_of_loglog` | If $u(T)^2r(T)\to0$, then $B_T(u(T))/T\to0$ and the square-root form factors agree up to $o(1)$. Both implications are unconditional for these frequencies. |
| `raw_transition_limit_of_corrected_complex_estimate` | At $\alpha=(\log\log T+c)/(2\log T)$ the raw form factor tends to $e^{-c}$. The Lean declaration assumes `CorrectedComplexFormFactorEstimate`, the normalized version of equation (3.5) for $(0,T]$. Its proof in Lean is open. |

[RH energy criterion](RH/HorizontalEnergyCriterion.lean) · [Unconditional transfer](Analysis/MontgomeryLoglogTransfer.lean) · [Transition and analytic hypothesis](Analysis/MontgomeryTransitionFrequency.lean) · [Corrected external estimate](https://arxiv.org/abs/2501.14545)

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

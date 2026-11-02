# Mobius / Cesaro energy catalog — November 1, 2026

Baseline: `6b53ff6d66ca30dee9b96eb8f07ebf48c5975e94`.
Research memo: [Squarefree Mobius Cesaro energy](RH/SquarefreeMobiusCesaroEnergyResearch20261101.md).

## Established arithmetic declarations

Development verification: `job_uJxnlDZLirddx6QsjFtZ1hRsAY5hX3cR`,
`verified=true`, `exit_code=0`. Final saved-source status is certified by
the successful publication checkpoint receipt, not by the snippet alone.

| Owning module | Declarations / interpretation |
|---|---|
| `RH/CesaroResidueMean.lean` | `residueCesaroDefect`, `cesaro_residue_centered`, `residueCesaroDefect_abs_le`: exact positive-index formula and absolute defect bound |
| `RH/MultiRangeEnergyCertificates.lean` | `conditionalMeanTailSquare_le_centered`: full tail from a centered inverse-endpoint bound |
| `RH/SquarefreeMobiusCesaroEnergy.lean` | `mobiusPrefixSum`, `mobiusPrefixDefect`, `mobiusPrefixDefectBudget`, their bounds and `mobiusPrefix_cesaro_centered` |
| same | `mobiusHeadCesaroCenter`, `mobiusHeadCesaroRemainder`, `mobiusHeadCesaroBudget`, `squarefreeMobiusHead_cesaro_linear`, `squarefreeMobiusHead_cesaro_centered`, `mobiusHeadCesaroRemainder_abs_le` |
| same | `squarefreeMobiusHead_energy_identity`, `squarefreeMobiusHead_tail_bound`: actual complete signed weighted energy and tail |
| same | `squarefreeMobiusHead_average_cesaro_centered`, `mobiusRepairAverageBudget`, `mobiusRepairAverage_remainder_abs_le`, `squarefreeMobiusHead_average_tail_bound`, `squarefreeMobiusHead_average_cubic_tail` |
| same | `mobiusRepairWeightLeft`, `mobiusRepairWeightRight`, `mobiusRepairWeights_constraints`: explicit signed weights, exact head sum and zero mean |
| same | `meanNeutralMobiusHead`, `meanNeutralMobiusHead_exact`, `meanNeutralMobiusHead_cubic_tail`, `meanNeutralMobiusHead_coefficients`, `meanNeutralMobiusHead_mem_divisorSpan` |

All eight inspected principal endpoints depend only on `propext`,
`Classical.choice`, and `Quot.sound`. No substantive asymptotic provider is
assumed by the unconditional two-repair construction. The generic cubic-tail
theorem's scalar mean-neutrality constraint is discharged by
`mobiusRepairWeights_constraints` in the explicit pair application.

## Paper results and external computations

- Complete-energy bound `E(F_H,D) <= (2 sqrt(H)+|a_H| sqrt(D))^2`.
- Large-repair lower bound `E(F_H,D) >= a_H^2 D/128` for `D>=4H/|a_H|`.
- Comparable-scale single and mean-neutral double repairs have `E=o(H)`,
  by the existing PNT/canonical-energy results and explicit norm comparisons.
- The two-repair budget is at most `9H^2` for the specified separated scales;
  all energy past `ceil(H^(4/3))` is bounded by 162.
- Repair averaging parametrizes every finite squarefree exact-head function.
- The head-16 complete-energy intervals are external Python rational
  certificates, not newly kernel-checked finite computations.

## Conditional research reduction and Open provider

The existing lower-logarithmic-growth RH consumer is unchanged.
**Open:** prove cofinally subpolynomial growth of the explicit finite signed
transition-window energy, or supply a better admissible repair average.
The memo gives a concrete sufficient dyadic mean-square bound.
Neither `o(H)`, mean neutrality, cubic decay in a tail cutoff, nor finite
energy computations discharge that provider.

## Complete dyadic energy continuation

Source agenda: RH Cesàro P/Q squarefree research agenda, 1 November 2026.
Research memo: [Complete dyadic energy and obstruction](RH/CesaroDyadicEnergyResearch20261101.md).

Development verification: job_yofjhWXBJpzeMrM2t4x5Jz07jeITb4y7,
verified=true, exit_code=0. Separately saved-module import and 11 principal
axiom inspections: job_eYXksy5LSirAy-3hCWiRuc2zghXL0Gd9, verified=true,
exit_code=0. Final publication remains governed by the successful checkpoint.

### Established identities and comparisons

| Owning module | Declarations / interpretation |
|---|---|
| Analysis/DyadicBlockDecomposition.lean | scaledDyadicBlock, sum_scaledDyadicBlock, summable_scaledDyadicBlock, tendsto_scaledDyadicEndpoint, tsum_scaledDyadicBlock: complete regrouping with exact head |
| Analysis/LowerLogGrowthComparability.lean | lowerLogGrowth_eq_zero_of_eventually_le_add_mul: eventual affine comparison |
| RH/QCesaroDyadic.lean | qCumulativeWeight, q_weight_cumulative, q_kernel_upper, q_kernel_lower, q_kernel_block: exact n^-4 cumulative kernel and block bounds |
| same | dyadicCumulativeBlock, dyadicCumulativeBudget, cumulative_energy_summable, qConditionalMeanSquare_eq_cumulative, dyadicCumulativeBlock_summable: complete summable budget |
| same | dyadic_cumulative_block_bounds, dyadic_cumulative_tail_bounds, cumulative_energy_head, q_energy_head_dyadic_identity, q_energy_sub_head_dyadic_bounds |
| same | normalized_q_energy_sub_head_dyadic_bounds, normalized_dyadic_energy_bounds: normalized tail lies between X/(8*zetaTwo) and 2*X/zetaTwo |
| RH/SquarefreeMobiusCesaroEnergy.lean | meanNeutralMobiusRemainder, meanNeutralMobiusHead_cumulative: exact signed primitive |
| RH/QCesaroDyadicCriterion.lean | normalized_dyadic_lowerLogGrowth_zero_iff, normalized_p_dyadic_lowerLogGrowth_zero_iff: same block criterion for P and Q |
| same | meanNeutral_dyadic_budget_exact: every Möbius and repair cross term retained inside the complete signed square |

The 11 principal audited endpoints use only propext, Classical.choice,
and Quot.sound. Nonzero head amplitudes need no uniform lower bound.

### Conditional research reductions

- riemannHypothesis_of_dyadic_cumulative_lower_growth
- riemannHypothesis_of_mobiusHead_dyadic_lower_growth
- riemannHypothesis_of_meanNeutral_dyadic_lower_growth

**Open:** provide a cofinal actual legal family whose normalized complete
dyadic cumulative budget has zero lower logarithmic growth. The explicit
Möbius specializations discharge legality and exact heads, not that growth
premise. The new equivalence supplies no improved arithmetic exponent for
the family by itself. Existing cubic tail decay and paper-level o(H)
energy bounds do not discharge the Open provider.

## Certified finite-cutoff continuation — 2 November 2026

Research memo: [Finite-cutoff Cesaro criterion](RH/MeanNeutralFiniteCutoffResearch20261102.md).
Source: the prior-chat finite-cutoff recovery handoff of 1 November 2026.

### Exact identities and proved cutoff providers

| Owning module | Declarations / scope |
|---|---|
| RH/ConditionalMeanFiniteCutoff.lean | conditionalMeanPrefix: existing definition moved unchanged from MultiRangeCertificateConvergence; conditionalMeanPrefix_nonneg, conditionalMeanSquare_eq_prefix_add_tail, conditionalMeanPrefix_le |
| same | normalized_lowerLogGrowth_zero_iff_finitePrefix: exact summable split and eventual bounded normalized tail imply equivalent zero lower logarithmic growth |
| RH/MeanNeutralMobiusFiniteCutoff.lean | meanNeutralCubicBudget, meanNeutralMobiusHead_mem_fullLegal, meanNeutralMobiusHead_tail_le_one |
| same | exists_meanNeutralCubicCutoff, meanNeutralCubicCutoff, meanNeutralCubicCutoff_spec: cutoff existence and canonical choice require no asymptotic growth provider |
| same | meanNeutral_lowerLogGrowth_zero_iff_finitePrefix, meanNeutralMobiusHead_finite_certificate: complete energy lies between its finite prefix and that prefix plus one |

Saved-module import and 12 principal axiom audits: job_CzE6C_P63il_wqCJLF9KKEz9X-DqeN_-, verified=true, exit_code=0.
All inspected declarations use only propext, Classical.choice, and Quot.sound.
Final source and aggregate-project publication require the enclosing successful server checkpoint.

### Conditional research reductions

- riemannHypothesis_of_meanNeutral_finitePrefix_lower_growth: arbitrary cutoffs satisfying the finite cubic certificate.
- riemannHypothesis_of_meanNeutral_certifiedPrefix_lower_growth: canonical cutoffs discharge that certificate premise.

**Open:** zero lower logarithmic growth of the actual signed finite-prefix
energy along cofinal positive heads. The canonical cutoff theorem proves no
growth rate in the head parameter. All Mobius-prefix and repair interactions
remain inside the squares. These RH endpoints retain their substantive
finite-prefix growth hypothesis and are not unconditional RH proofs.

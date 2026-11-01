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

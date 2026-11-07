# Full-conductor CRT collocation: theorem catalog supplement

7 November 2026. See
[research memorandum](RH/CRTCollocationZeroGrowthResearch20261107.md).
All norms are complete physical Q norms. These are full-conductor spaces,
including prime powers, and not squarefree-only spaces.

## Established finite and Hilbert-space results

`Analysis/FiniteAccretiveCollocation.lean`:

- `difference_energy`, `eq_zero_of_difference_inner`: exact contraction
  identity and its injectivity consequence.
- `existsUnique_test_match`: finite collocation existence and uniqueness.
- `matched_energy`, `matched_defect_le`: the complete shift defect is retained.

`RH/QCRTFiniteCollocation.lean`:

- `trialSpace`, `cellSpace`, `conditionalProjection`, `target`: actual spaces
  and operators in the existing Q Hilbert space.
- `difference_residue`, `difference_mem_cell`: physical differences belong
  to the finite divisor-test space.
- `existsUnique_divisor_match`, `canonical`, `canonical_match`: an actual
  unique legal solution; no matrix-invertibility provider is assumed.
- `conditional_injective_on_trial`, `conditional_range`: the exact finite
  image is the gcd-cell space orthogonal to the multiples-of-L indicator.
- `canonical_conditional`, `conditional_gcd_coordinates`: conditional
  projection matching and gcd-cell measurability.
- `canonical_divisor_moment`, `canonical_dilation_moment`: exact prescribed
  moments, including the L^(-2) boundary term.
- `legal_error_identity`, `canonical_error`, `canonical_mean`, `canonical_norm`:
  complete energies and the explicit leakage remainder.
- `canonical_difference_energy`, `canonical_shift_energy`,
  `canonical_shift_defect_le`: exact identities exposing cancellation of
  leakage from the weaker shift defect.

`RH/QCRTLeakageParseval.lean`:

- `sum_divisorWavelet`: finite Hilbert-space Möbius inversion.
- `divisor_wavelet_inner`, `canonical_low_wavelet`: exact Jordan-normalized
  low coordinates, with the persisted formula in the unnormalized basis.
- `canonical_leakage_parseval`: the full infinite sum over conductors not
  dividing L, including excessive prime-power depths.

`RH/QCRTBoundedCriterion.lean`:

- `lcm_trialSpace_mono`, `iSup_lcm_trialSpace`: the increasing LCM tower
  exhausts the actual full legal span.
- `lcm_optimal_tendsto_projection`: unconditional convergence to the actual
  full legal projection, without asserting that it equals one.
- `canonical_moments_tendsto`: all fixed divisor moments converge under
  cutoff growth and divisor exhaustion.

`RH/QCRTZeroObstruction.lean`:

- `tailMellin`: the actual existing Mellin functional composed with I-T_L.
- `qMellin_trial_zero`: residue annihilation at an actual zeta zero.
- `canonical_mellin_balance`: the signed identity
  1/s = Mellin(a_L)-Mellin(F_L-h_L), retaining the entire endpoint.
- `canonical_leakage_projection_zero`: the complete leakage is orthogonal
  to the finite gcd-cell space.
- `canonical_mellin_obstruction`: the quantitative obstruction
  1/|s| <= |Mellin(a_L)| + ||tailMellin|| sqrt(leakage),
  conditional only on the stated zeta-zero and strip hypotheses.

## Conditional research reductions

| Declaration | Conclusion | Domain-specific obligation |
|---|---|---|
| `qOne_mem_of_bounded_divisor_moments` | 1 lies in the actual full legal closure | Open for an arbitrary supplied family: legal membership, uniform norm bound, and correct limiting divisor moments |
| `qOne_mem_of_bounded_canonical` | 1 lies in the actual full legal closure | Open: uniform bound on the actual canonical family; cutoff growth and divisor exhaustion are explicit |
| `riemannHypothesis_of_bounded_canonical` | Mathlib RH | Same open bound |
| `riemannHypothesis_of_bounded_leakage` | Mathlib RH | Open: bounded complete canonical leakage |
| `riemannHypothesis_of_bounded_lcm_leakage` | Mathlib RH | Open: bounded leakage along some cofinal LCM subsequence; the arithmetic exhaustion conditions are discharged |
| `optimal_tendsto_one_of_bounded_canonical` | Existing full inverse-Gram candidates converge to 1 | Same open canonical bound |
| `lcm_optimal_error_tendsto_zero_of_bounded_canonical` | Actual complete LCM optimal errors tend to zero | Same open canonical bound |
| `riemannHypothesis_of_vanishing_mellin_budget` | Mathlib RH | Open: the explicitly stated actual projected-Mellin budget tends to zero throughout the right half strip |

These implications have proofs; the open growth hypotheses do not yet have
checked providers. No converse RH-to-bounded-collocation theorem is claimed.
The standalone generic moment theorem is a sufficient-condition theorem,
not a claim that every legal bounded family has the required moments.

## Not claimed as Lean-verified in this addition

- The explicit estimate ||tailMellin(L,s)|| <= 2 sqrt(Z D_(2 Re(s))(L)).
- The endpoint rate, Euler-product tail formula, and the resulting
  subpolynomial-in-M zero-growth criterion.
- Any asymptotic bound for the canonical collocation inverse applied to its
  particular target, or any proof of RH.
- The numerical Wolfram table as an exact or interval-certified computation.
- A separate P-LCM-minimizer convergence theorem.

The memorandum gives the analytic proof and precise formalization tasks for
the explicit rates. Wolfram computations reproduce the full-period moment
system through L=2520, without truncating the physical Q tail, but remain
floating-point evidence.

## Verification provenance

The coherent candidate passed job `job_xnrn6F37zEQdZbGd1EwH_SrpUw8S45K6`
(6.963 s of server-reported verification). Its main axiom audit returned only
`propext`, `Classical.choice`, and `Quot.sound`; local growth hypotheses remain
visible in the theorem types. The actual Parseval module passed
`job_GQ6aKB-vbM_Y-9-22kDIjCgBXgCtcQrB` (5.479 s). The final checkpoint validates
the aggregate project plus changed modules and reports the exact published
commit; these earlier snippets alone are not that publication gate.

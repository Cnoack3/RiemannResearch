# Weighted CRT declaration catalog — November 1, 2026

Source: user's Cesàro/weighted-CRT manuscript, Priorities 1–3.
Each numbered principal result is published separately after server validation.
Supporting lemmas are included with their owning result.

## Established declarations

1. `RH/QWeightedResidues.lean`: `qCumulativeWeight_summable`, with
   `qCumulativeWeight_pos`. The actual primitive kernel has finite mass and
   every positive index has strictly positive weight. Defines `residueWeight`.

2. `RH/QWeightedResidues.lean`: `periodic_cumulative_energy` and
   `residue_integral`. The complete latent Q energy is exactly the finite
   residue sum; all needed summability is proved. Generic regrouping is in
   `Analysis/FiniteWeightedPushforward.lean`.

3. `RH/QWeightedResidues.lean`: `residueWeight_refinement` and
   `residueWeight_pos`. Every residue class has positive mass, and refinement
   pushes the fine arithmetic weights to the coarse weights exactly.
   The general composition law is `FiniteWeightedPushforward.pushWeight_comp`.

4. `RH/QWeightedResidueMaps.lean`: `residue_pullback_energy`. Reduction
   pullback preserves the complete arithmetic weighted energy exactly.
   General pullback energy and pairing identities live in
   `Analysis/FiniteWeightedRefinement.lean`.

5. `RH/QWeightedResidueMaps.lean`: `residue_adjoint_identity`, with
   `residue_average_pullback`. The exact weighted fiber average is the
   pullback adjoint and satisfies U*U = I. The arithmetic positivity theorem
   discharges every nonzero-denominator hypothesis.

6. `RH/QWeightedResidueMaps.lean`: `residue_pythagorean`, with
   `residue_average_energy_le`. Fine energy equals coarse-average energy plus
   the full squared residual. No cross term or fiber variance is discarded.

7. `RH/QWeightedResidueMaps.lean`: `residue_average_tower`. Successive
   weighted averages along K | M | L equal the direct K | L average.
   `FiniteWeightedRefinement.average_tower` is the generic finite theorem.

8. `RH/SquarefreeWeightedPrimitives.lean`: `legalPrimitive_pullback`.
   The actual zero-mean divisor-residue primitive space nests under reduction
   pullback. `legalPrimitive_zero` records its forced zero anchor, and
   `legalPrimitive_energy` identifies its exact energy with the existing
   complete Q Cesàro energy. Periodicity is proved from span membership and
   zero period mean, not assumed as a substitute for legality.

9. `RH/WeightedCRTLegalObstruction.lean`: `weighted_adjoint_not_legal`.
   The primitive of 4 r₂ - 3 r₃ is literally legal at period 6, but its
   weighted average modulo 2 is not legal. `average_even_exact` gives
   -ω₆(2)/ω₂(0), and `average_even_negative` proves strict negativity.
   Every legal primitive has value zero at residue 0.

## Conditional research reduction

10. `RH/WeightedResidueRHCriterion.lean`:
    `riemannHypothesis_of_legal_residue_lower_growth`. For actual legal
    divisor-residue primitives with positive exact heads, nonzero amplitudes,
    and cofinal head lengths, zero lower logarithmic growth of the complete
    normalized finite-residue energy implies Mathlib's RiemannHypothesis.
    `Pareto.divisorResidueSpan_mem_legal` supplies the seed-span bridge.
    The theorem applies in particular to squarefree periods. No uniform
    lower amplitude bound or independent summability premise is required.

## Open arithmetic provider

The existing dyadic lower-growth RH consumer is unchanged. Cofinal zero lower
logarithmic growth of legal exact-head energy remains Open. Finite residue
identities and ambient weighted projections do not discharge that estimate.

## Recovery validation

The earlier result-8 checkpoint `job_UgqMEoiGJNWK5j0cuHTlhFSCPg3d-le7`
ended with a 3600-second timeout in `lake cache put`. That publication did
not succeed. The retained source was resumed without resetting the workspace.

- Coherent recovery proof check and ten principal axiom inspections:
  `job_CE1lSpWsx9jE2YHVQDeTUAxFKVo6xL8Z`, verified=true, exit_code=0,
  server verification duration 7.968 seconds.
- Saved-module import check, ten principal axiom inspections, and exact-type
  inspection of the final criterion and counterexample:
  `job_B9BM42ZgkyL63XmHiwWjiySKJfQWxpXQ`, verified=true, exit_code=0,
  server verification duration 23.270 seconds.
- Every inspected principal endpoint used only `propext`, `Classical.choice`,
  and `Quot.sound`. The final criterion still has the substantive growth
  hypothesis in its type; the axiom audit does not discharge that hypothesis.
- Result 8 recovery publication: checkpoint
  `job_XFFdhKUzjFnGDpditVr-0uT5l7p7eQWq`, pushed commit
  `51459d3fe121aa59c3fdb4e7788953f453f71d2e`. Aggregate project plus
  PeriodicArithmeticCumulative and SquarefreeWeightedPrimitives passed.
- Result 9 publication: checkpoint
  `job_NRWoYiz4Lwx9KUZLIlS6kjv78WSiWQnr`, pushed commit
  `a043af71799bb45c6c623cfc5d5653a01bf02d14`. Aggregate project plus
  WeightedCRTLegalObstruction passed.

These durations measure the server-reported verification operation, not the
workspace-opening request, polling delay, or total publication latency.
The final saved-source publication is certified by its terminal checkpoint
receipt; the development checks alone are not publication receipts.

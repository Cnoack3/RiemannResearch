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

## Open arithmetic provider

The existing dyadic lower-growth RH consumer is unchanged. Cofinal zero lower
logarithmic growth of legal exact-head energy remains Open. Finite residue
identities and ambient weighted projections do not discharge that estimate.

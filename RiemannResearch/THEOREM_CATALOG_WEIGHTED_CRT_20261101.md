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

## Open arithmetic provider

The existing dyadic lower-growth RH consumer is unchanged. Cofinal zero lower
logarithmic growth of legal exact-head energy remains Open. Finite residue
identities and ambient weighted projections do not discharge that estimate.

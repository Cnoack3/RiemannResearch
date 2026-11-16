# Exact-head Green profiles: first verified checkpoint (2026-11-16)

Source: user attachment *Best Nyman Beurling for RH.pdf*, internally titled
*Exact-Head Green Profiles in the Nyman--Beurling Program*, 27 July 2026, 17 pages.
This is the attached memorandum, distinct from the longer A1--A2 audited revision
reviewed in RH_PART2_REVIEW_20261116.md.

## Established finite results

- `Analysis/FiniteProfileEnergy.lean`: `gram_identity` retains the full
  two-coordinate-minor remainder; `signed_profile_error_sq_le` proves the
  profile error estimate; `affine_completion` and `affine_minimizes` remove
  the affine normal-equation component exactly.
- `affine_determinant_pos`: two distinct positive-weight abscissae suffice
  at every finite stage, with no asymptotic counting input.
- `Analysis/GreenProfileBounds.lean`: `root_square_identity` retains the
  signed root equality; `energy_le_signed_root` gives q <= 2r+a rather
  than 2|r|+a; `energy_le_of_relative_profile` gives
  q <= 2B+2C+2a from r=q+tau, tau^2<=aq, (r-m)^2<=Cq, m<=B.

## Conditional research reduction

`RH/ExactHeadGreenClosure.lean`,
`riemannHypothesis_of_cofinal_profile_energy`, proves RH provided legal
approximants match every positive coordinate through their cutoff and, on a
cofinal set of cutoffs:

1. the full residual energy is terminal+q, with q>=0 and terminal<=T;
2. the signed root is q+tau, with tau^2<=a q;
3. W E<=C q, where W is finite weight mass and E is profile error energy;
4. the signed profile moment is <=B.

C and a are nonnegative constants. Weights are nonnegative and signs have
square at most one. The criterion allows arbitrary finite profiles and requires
only a one-sided moment bound, not coefficient compactness or a moment limit.
For the paper W is the squarefree harmonic mass. Thus the relative target is
E=O(q/W), weaker than E=O(q/x). No PNT hypothesis is needed for this reduction.

The actual arithmetic providers remain **Open**. A theorem with these
hypotheses is not an unconditional proof of RH. Generic positivity or normal
equations do not supply the uniform relative-energy or signed-moment estimates.

## Verification

Finite algebra and scalar bounds passed Bazel snippet job
`job_sI596T7WPi6ke2zyBUZ39xEy4l9yknvK` (29.406 seconds).
The cofinal RH reduction passed Bazel snippet job
`job_7h5QZSUYGnw0CM6Ysl9DCoV7q0-m5pYV` (76.464 seconds).
Publication requires the managed full-project checkpoint, whose terminal record
is reported with the commit. These focused checks alone are not a project checkpoint.

## Second development stage

- `RH/ExactHeadGreenProfile.lean`: exact canonical centered-residue profile,
  arbitrary-multiplier digit recursion, boundary score and finite root identity.
  `root_identity` requires the displayed inclusion-exclusion expansion,
  projection energy identity and vanishing upper scores; it does not assert an
  arithmetic optimizer provider without those hypotheses.
- `RH/MobiusAffineProfile.lean`: the actual Mobius/squarefree weights,
  profile error bound, affine signed-moment identity and normal determinant
  positivity for every integer cutoff at least two.
- `affine_moment_numerator` and `affine_moment_le_iff` reduce the required
  one-sided moment bound to a single signed normal-equation numerator.
- `frame_bound` retains the actual support mass and sharp column bounds;
  `pairing_support` and `energy_support` justify restricting to a zero-head tail.

These declarations passed focused Bazel job
`job_KWXAOf9MGXZS3HkoMvia2UEspEtlXc_x` (22.402 seconds).

First complete project checkpoint: `job__ZgORtbgGfnZSxBfkeuJqqu8gkyjgqq8`;
full `//:RiemannResearch`, Bazel/BuildBuddy, 227.504 seconds. Published commit:
`c20ca4aa4e1d728c38a2da59826d330b8834325c`.

## Low-conductor and actual-weight providers

- `RH/ExactHeadGreenLowConductor.lean`: sharp support-mass bound,
  squarefree-sum bound, polynomial bound for arbitrary D, and
  `low_conductor_relative_budget`. If W D(D+1)<=8C(x+1), the low
  contribution satisfies W E_low<=Cq. No prior bounded-q assumption is used.
- `RH/ExactHeadGreenPareto.lean`: actual full-progression normalization,
  `period_tail_mass_le`, `subset_tail_mass_le`, `tail_charge_sq_le`,
  `actual_low_conductor_bound`, and the terminal bound 2/[P(P+1)].
  The support lies in {1,...,P}, x<=P, and the residual vanishes through x.
  No tail-mass estimate is left as a hypothesis in these specializations.
- `LinearAlgebra/CumulativeGramEvents.lean`:
  `weighted_sum_eq_tail_difference`, `cumulative_product_jump`,
  `cumulative_gram_event_identity` and `cumulative_energy_event_identity`.
  Both mixed jump terms and the jump product are retained.

Low-conductor algebra passed `job_Fc3KSZAmuYk7glyYU76fn3vQOPuOxtaz`
(30.048 seconds). Actual-weight and event identities passed
`job_DslXdSzeQCewyPveruxIRx7XhSeNxevq` (43.387 seconds), both Bazel.

## Numerical agenda: external evidence only

The retained [data and reproduction sources](ResearchData/ExactHeadGreen20261116/reproduction_sources.md)
reproduce the paper through x=17 and extend the complete-period regression to
x=19 and x=23. Independent dense/chunked accumulation was compared through x=19;
double and extended-precision event accumulation were compared through x=23.

| x | q (diagnostic) | x E_aff/q (diagnostic) | W E_aff/q (diagnostic) |
|---|---:|---:|---:|
| 19 | 0.01332260069 | 0.143374 | 0.0215833 |
| 23 | 0.01118024946 | 0.147437 | 0.0192103 |

These are floating-point observations, not outward-rounded certificates.
The x=23 scaled Gram condition is about 2.49e10. A precision comparison is
not an error enclosure. R1 interval certification and uniform R4/R5 estimates
remain Open. Finite data do not establish an asymptotic conjecture.

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

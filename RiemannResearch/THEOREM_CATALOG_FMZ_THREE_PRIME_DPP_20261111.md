# FMZ three-prime Gram and zero-ordinate DPP continuation

Research note: [FMZ_Three_Prime_Gram_DPP_20261111.md](FMZ_Three_Prime_Gram_DPP_20261111.md).

Starting main: ac1bee28482212700b25cb401ff8e3263868eda1.
The exact publication checkpoint and commit are reported with the delivered result.

## Exact finite and probabilistic results

* Analysis/ThreePointGram.lean: determinant_real, determinant_imaginary,
  schur_identity, determinant_nonneg, schur_disk. The inequalities take a
  positive-semidefinite Gram hypothesis; the identities do not.
* Analysis/PrimeProbeFramePotential.lean: frame_potential_exact,
  frame_potential_lower, coordinateGram_primeFeature_diagonal,
  phase_pair_energy_exact, phase_pair_energy_lower. These extend the existing
  dual square-trace theorem with the complete nonnegative coordinate defect.
  Arbitrary finite sample labels and repeated ordinates are allowed.
* Probability/DeterminantalThreePoint.lean: IsDPP.three_point and
  IsDPP.connected_three retain both directed three-cycles.
* Probability/ZeroOrdinateProjectionDPP.lean: coordinate_inner,
  law_probability, law_isDPP, law_two_point. The law is actually constructed
  from the real Fourier-feature subspace on ActualZeroOrdinate.Copies T.
  No RH, Selberg, invertible-Gram or distinct-ordinate premise is used.

## Conditional research reductions

Analysis/ActualPrimeTorusHomogeneousGram.lean connects the actual FMZ sampler
to homogeneous Gram cancellation.

* homogeneous_gram_polynomial_eq is an unconditional algebraic identity.
* tendsto_centered_degree_zero_polynomial_div,
  tendsto_centered_homogeneous_gram_div, and
  eventually_degree_zero_polynomial_bound retain UniformSelbergDensity (1/4).
* Open formal provider: UniformSelbergDensity (1/4). The corresponding
  classical analytic theorem is published, but this change does not formalize
  its missing provider.
* The O((log T)^(-2)) fixed-family, zero-count-normalized rate in the note
  is a paper consequence of the checked quantitative bound and RvM, rather
  than a new Big-O declaration.
* Open research providers: microscopic moving-family residual bounds,
  weighted pair-tail control, and a second-factorial-moment transfer from an
  auxiliary DPP to randomly translated unfolded zero ordinates.

## Limits on interpretation

The finite DPP is an auxiliary random subset of actual zero labels.
It is not an identification of the raw zero process as determinantal.
The effective-rank obstruction, inverse-Gram whitening identity, three-prime
tensor spectral bounds and continuum pair-only convergence estimate are
paper deductions recorded with their assumptions in the research note.
No new unconditional Montgomery PCC, RH or twin-prime implication is claimed.

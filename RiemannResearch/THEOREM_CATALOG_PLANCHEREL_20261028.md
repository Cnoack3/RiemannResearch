# Prime-torus A2 Plancherel: theorem catalog supplement

28 October 2026. Continuation of [the FMZ catalog](THEOREM_CATALOG_FMZ_20261028.md).

## Definitions and scope

For a finite coordinate type and nonnegative weights ell, the native Fourier
height is H(k) = sum_i |k_i| ell_i, and w(k) = 1 + H(k).
FiniteTorusWiener.MemA2 ell f means sum_k |fhat(k)| w(k)^2 < infinity.
FiniteTorusWiener.a2Mass ell f is this weighted l1 norm. On prime coordinates,
ell_p = log p; ActualPrimeTorusFMZ.A2 P is the corresponding subtype of
continuous functions. The weight is proved equal to the project's arithmetic
primeModeWeight, not merely bounded by it.

The norm axioms, algebra bounds, exact Haar identities, and exact actual-zero
Gram identities below have no Selberg or RH premise. The asymptotic sampling
theorems explicitly assume ActualZeroOrdinate.UniformSelbergDensity (1 / 4).
This catalog does not assert that this remaining analytic provider is proved.

## Exact Fourier and algebra results

- PrimeTorusFourierProducts: character multiplication/conjugation, multiplication
  of absolutely convergent Fourier series, a continuous Fourier-coefficient
  functional, and exact aggregation of coefficients by frequency.
- WeightedFourierFibers.weighted_fiber_sum_bound: weighted absolute-sum
  contraction under aggregation; every coefficient in a fiber is retained.
- FiniteTorusWiener: positivity, definiteness, triangle inequality, scalar
  homogeneity, finite-polynomial membership, conjugation invariance, ordinary
  and conjugated multiplication closure, and submultiplicative mass bounds.
- memA2_mul_star_and_mass_le specializes to a2Mass(|f|^2) <= a2Mass(f)^2.
- norm_le_a2Mass controls the continuous-function supremum norm.
- a2Mass_character is w(k)^2. These statements concern the explicit norm
  functional; no new abstract Banach-algebra instance is introduced.

## Haar Plancherel and L2 density

In PrimeTorusPlancherel, namespace PrimeTorusHaar:

- hasSum_sq_mFourierCoeff_continuous: integral |f|^2 = sum |fhat(k)|^2,
  with actual summability, for every continuous torus function.
- hasSum_prod_mFourierCoeff_continuous: the polarized identity
  integral f conjugate(g) = sum fhat(k) conjugate(ghat(k)).
- haarIntegral_mul_star_self: the diagonal identity in the complex-valued
  integral convention used by the sampling pipeline.
- denseRange_a2_toLp and a2_toLp_injective: the A2 image is dense and
  injective in normalized-Haar L2. The local normalized volume used by
  Mathlib is explicitly identified with project Haar measure.
- a2Mass_sq_ne_haar_energy_character: a positive-height character has
  A2 norm squared different from its Haar energy. Thus the displayed
  Plancherel identity concerns L2 energy, not the weighted l1 norm.

The dense image supports completion in the inherited L2 norm. No identification
of the weighted-A2 norm completion with L2 is claimed.

## Actual zeta-zero sampling

In ActualPrimeTorusPlancherel, namespace ActualPrimeTorusFMZ:

- native_weight_eq and a2Mass_eq_weightedFourierMass connect native modes to
  the existing rational/arithmetic FMZ estimates.
- sampleFunctional_fourierSeries is exact synthesis through the continuous
  finite-sample functional.
- sampleFunctional_a2_gram and countNormalized_a2_gram retain every pair
  coefficient and the zero-ordinate exponential sum at the difference mode.
- primeFrequency_ambient_sub identifies that mode's frequency with u_h - u_k.
- sampleFunctional_energy_apply identifies f * star f with the literal
  squared norm sampled at the prime phases of every actual zero ordinate.

All existing analytic multiplicities are retained by ActualZeroOrdinate.sum.
The unsplit divided Gram formula uses Lean's totalized division and holds even
when N(T)=0; its asymptotic use has positive N(T) from the proved count bound.
No assertion that zeta ordinates form an orthogonal Fourier basis is made.

## Quantitative and uniform consequences

LogarithmicSampleNormalization first proves the exact signed normalization
identity, then its corrected and uncorrected norm bounds. The project
ActualZeroCountAsymptotics supplies c T log T <= N(T) unconditionally.

ActualPrimeTorusPlancherelRate contains:

- norm_a2_densityIntegral_le: the correction functional is bounded by a2Mass,
  unconditionally.
- eventually_a2_height_remainder_bound: the signed height-normalized FMZ
  error is O(a2Mass(g)/log T).
- eventually_a2_count_remainder_bound: after both Haar and prime-density
  corrections, the count-normalized error is O(a2Mass(g)/log(T)^2).
- eventually_a2_count_error_bound: the uncorrected error is
  O(a2Mass(g)/log T).
- eventually_a2_energy_remainder_bound: for g=|f|^2 the corrected energy error
  is O(a2Mass(f)^2/log(T)^2), with Haar energy replaced by its Fourier sum.
- eventually_a2_energy_error_bound: the uncorrected energy error is
  O(a2Mass(f)^2/log T).
- tendstoUniformlyOn_a2_energy: convergence to the Fourier-square sum is
  uniform on each bounded A2 ball.

Every eventual/rate/convergence statement in the last list takes P before
the existential constant. The proved uniformity is in all functions in the
stated bounded ball for fixed P. It is not an unrestricted growing-P claim.

## Provenance

Mathlib's finite-torus Fourier Hilbert basis supplies Haar Parseval and
Fourier-polynomial density. The arithmetic estimates are assembled from the
existing ActualPrimeTorusFMZRate and ActualZeroCountAsymptotics modules.
The source target is the user's Plancherel question and subsequent request
to formalize it. No new analytic provider, RH assumption, or novelty claim
is introduced.

## Verification

The seven-module dependency chain compiled successfully in verification job
`job_FiOYfMqp5drYQL4VhpAbv4TAIN4klY0x` (19.261 seconds of reported execution).
The six principal Haar, density, algebra, Gram, rate, and uniform-convergence
theorems were audited with `#print axioms`; each reported only `propext`,
`Classical.choice`, and `Quot.sound`. The sampling density premise remains an
explicit theorem argument. Aggregate verification and publication are handled
by the final workspace checkpoint.

# Quantitative FMZ and product-test cancellation: theorem catalog supplement

28 October 2026. This supplement records the strengthening of the current
prime-phase results, rather than the older saved audit.

## Status and comparison

The actual rational Landau provider is already proved in
`ActualUniformRationalLandau.lean`. The actual-zero results below are
**conditional research reductions**: their one open analytic obligation is
`ActualZeroOrdinate.UniformSelbergDensity (1 / 4)). No RH assumption is added.

The earlier fixed continuous-test theorem already permits Fourier decay
B > card(P) + 1. That theorem and its weaker regularity requirement are
retained. The added quantitative theorem uses B > card(P) + 2 and proves an
O(T / log T) remainder after subtracting both FMZ main terms, strengthening
the o(T) conclusion at this smoother threshold.

Source for the comparison target: Ford--Meng--Zaharescu, Theorem 1 and
Corollary 1.1, https://arxiv.org/abs/1511.06814, as cited in the user's selected
statement and in `ActualRationalFMZDomination.lean`. The quantitative estimates
are assembled from the project's proved rational Landau bound and its
conditional Selberg comparison; no novelty claim is made.

## RiemannResearch/Analysis/ActualRationalFMZRate.lean

Let w(n,m) = 1 + |log n + log m| for positive natural n,m.

- `eventually_rational_landau_error_le_inv_log`: unconditional uniform
  normalized Landau error O(1/log T) when log n <= log T / 8 and 1 <= m < n.
- `eventually_rational_ordinate_remainder_rate`: conditional uniform
  ordinate remainder bounded by K(1+log n)^2/log T.
- `eventually_centeredRationalOrdinate_remainder_rate`: conditional global
  bound K w(n,m)^2/log T for all positive n,m, with exact diagonal centering
  and conjugate negative frequencies.
- `rationalFMZMain_norm_le_weight`: unconditional arithmetic correction
  bounded by w(n,m).
- `eventually_rational_fourier_remainder_bound`: conditional absolutely
  convergent synthesis with the full squared-height Wiener mass.
- `tendsto_moving_rational_fourier_remainder`: conditional moving-test
  convergence when the squared-height mass is o(log T); rational frequencies
  and coefficients may both depend on T.

The constants and eventual threshold in the uniform estimates precede the
choice of rational modes and Fourier coefficients.

## RiemannResearch/Analysis/ActualPrimeTorusFMZRate.lean

- `fourierSeries_remainder_eq_rationalPairing`: exact signed identity for
  the literal zero sum, Haar main term and prime-Poisson correction.
- `summable_norm_of_primeModeWeight_sq`: absolute convergence from the
  squared arithmetic norm.
- `eventually_fourierSeries_remainder_bound`: conditional quantitative
  prime-torus theorem with
  W2 = sum |a_k| (1 + sum_p |k_p| log p)^2 and corrected normalized
  error at most K W2/log T.
- `tendsto_moving_fourierSeries_remainder`: the prime set itself, its
  dimension, coefficients and frequencies may vary with T, subject to
  W2(T)/log T -> 0. Every individual prime set is finite.

The correction is the complete signed product-Haar pairing with the existing
`primeDensity`; no axis or mixed-frequency terms are discarded.

## RiemannResearch/Analysis/PrimeTorusFourierDecay.lean

- `summable_weighted_sq_of_fourierDecay`
- `summable_primeModeWeight_sq_of_fourierDecay`

These unconditional summability lemmas require B > dimension + 2.

## RiemannResearch/Analysis/PrimeTorusHaarSpecialization.lean

The following are unconditional finite-product integral identities for actual
continuous functions and normalized product Haar measure:

- `productTest`, `productTest_apply`
- `haarIntegral_productTest`
- `haarIntegral_productTest_centered`
- `haarIntegral_productTest_density`
- `haarIntegral_productTest_eq_zero`
- `haarIntegral_productTest_density_eq_zero_of_two_centered`

One zero coordinate mean kills the Haar term. Two distinct zero coordinate
means kill every term of the signed prime-Poisson correction. The full product
formula is proved first, without dividing by possibly zero coordinate means.

## RiemannResearch/Analysis/ActualPrimeTorusFMZContinuous.lean

- `eventually_continuous_remainder_bound_of_selberg`: conditional
  O(T/log T) corrected remainder at B > card(P) + 2.
- `tendsto_productTest_div_zero_of_two_centered`: conditional o(T)
  actual-zero sum at B > card(P) + 1 for a product with two centered factors.
- `eventually_productTest_div_bound_of_two_centered`: conditional
  O(T/log T) actual-zero sum at B > card(P) + 2.

## RiemannResearch/Analysis/GrowingFourierGramBounds.lean

These finite algebraic identities and estimates are unconditional under their
stated elementary hypotheses:

- `finiteGramErrorPairing_sub`
- `finiteFrequencyDispersion`
- `weighted_pairwise_frequency_sq_eq`
- `finiteFrequencyDispersion_nonneg`
- `finiteFrequencyDispersion_add_const`
- `weighted_frequency_majorant_sum`
- `finiteGramErrorPairing_norm_le_frequency_dispersion`

For an entrywise bound |R_ij| <= eta (ell_i-ell_j)^2 + delta, the complete
Gram remainder has norm at most
2 eta (W0 W2 - W1^2) + delta W0^2, where Wk are the coefficient-norm-weighted
frequency moments. The negative W1^2 term and common-translation invariance
are retained. This general estimate does not itself supply its analytic
entrywise hypothesis.

## Open obligations and limits

- **Open:** a checked provider of `UniformSelbergDensity (1 / 4)`.
- Sharp indicator boxes and shrinking boxes are not established by the
  continuous Fourier-series theorems without their required norm control.
- The moving-test conclusion gives no unrestricted dimension-growth law:
  its squared-height mass condition is essential to the stated result.
- These phase results do not control the real parts of the zeros or prove RH.
- The source checkpoint determines verification and publication acceptance.

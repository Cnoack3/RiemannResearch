# Quantitative FMZ and product-test cancellation: theorem catalog supplement

For exact Haar Plancherel, the A2 algebra, actual-zero Gram identities, and uniform
energy sampling, see [the Plancherel supplement](THEOREM_CATALOG_PLANCHEREL_20261028.md).

For the Pareto/von Mangoldt normal equations, RH equivalences, and the complete
conductor-six certificate, see [the normal-equations catalog](THEOREM_CATALOG_PARETO_ORDINATE_NORMAL_20261118.md).

## Ramanujan sums sampled at actual zeta ordinates (17 November 2026)

All height cutoffs use the analytic multiplicities of the positive-height
nontrivial zeros of the actual Riemann zeta function.

| Lean declaration | Mathematical status and scope |
| --- | --- |
| `tendsto_landau_div_of_nonresonance`, `tendsto_primeRoot_landau` | Proved without a density hypothesis. The centered Landau sum at frequency `(n/d) log p` has its explicit signed prime-power coefficient, including zero when `d ∤ n`. |
| `ramanujanSum_eq_reduced_phases` | Proved for every positive conductor. The existing divisor formula equals the sum of primitive additive characters, including conductor one. |
| `tendsto_angularLaw_haar`, `exists_ordinate_sequence_all_harmonics` | `fixedStripConcentration_of_sublinearHorizontalEnergy sublinearHorizontalEnergy` supplies `FixedStripConcentration`. Haar convergence yields actual ordinates of unbounded height approaching each angle, simultaneously for every integer harmonic. |
| `exists_ordinate_ramanujan_P_and_Q` | Under the same hypothesis, one family of zero sequences converges to the Ramanujan profile in the full squared norms of both physical probability weights. |
| `exists_common_ordinate_ramanujan_of_dvd` | Under fixed-strip concentration, one actual ordinate sequence at the angle `2π/L` handles all `q ∣ L`, residues, harmonics, and summable physical weights through the integer multiplier `(L/q)an`. |
| `tendsto_ordinateDivisorProbe`, `tendsto_ramanujanSum_ordinateProbes`, `tendsto_ramanujanPacket_ordinateProbes` | `sublinearHorizontalEnergy` supplies the required energy limit. The height-normalized ordinate modes recover divisibility, the Möbius sum, and its signed physical prefix. The full-sum formula is for each fixed index. |

The first-order hypothesis says the fraction of zeros outside any fixed strip
about the critical line tends to zero. The order-`T` hypothesis says the
multiplicity-weighted sum of squared horizontal displacements is `o(T)`.
The second implies the first by `fixedStripConcentration_of_sublinearHorizontalEnergy`.
`sublinearHorizontalEnergy_of_inghamDensityBound` supplies both from Ingham's
inclusive estimate with its fifth logarithmic power. The existing
`sublinearHorizontalEnergy_of_uniformSelberg` supplies them from a uniform
Selberg estimate at any positive exponent. Hlawka and Ford–Zaharescu
establish the respective ordinate conclusions in the literature.

The unconditional theorem `ActualZeroOrdinate.sublinearHorizontalEnergy`
now supplies the height-normalized energy limit. Its proof uses
`uniformLogLossDensity_quarter_four`, which gives, uniformly for
$1/2\leq\sigma\leq1$ and all sufficiently large $T$,
$$
N(\sigma,T)\ll T(\log T)^4\exp[-(\sigma-1/2)\log T/4].
$$
The four-sided Cauchy identity for the Möbius mollifier error, the actual
critical-line mixed moment, and the local zero-count bound supply this estimate.
The actual Ingham theorem also supplies the away-line density input. The
uniform single-logarithm Selberg estimate still requires near-line control.
[Ingham density theorem](THEOREM_CATALOG_INGHAM_DENSITY_20261117.md) ·
[Contour identity](Analysis/ActualZeroDensityCauchyDetector.lean) ·
[Estimate at a zero](Analysis/ActualZeroDensityCauchyObservation.lean) ·
[Density and energy theorems](Analysis/ActualZeroCauchyDensity.lean)

[Fixed real frequencies](Analysis/ActualFixedFrequencyLandau.lean) ·
[Angular sampling](Analysis/ActualOrdinateAngularLaw.lean) ·
[Ramanujan phase limits](RH/RamanujanOrdinatePhases.lean) ·
[Prime-root Fourier coefficients](RH/RamanujanOrdinateFMZ.lean)

## Unconditional rates and one-period reconstruction

Write $L=\log T$, $\ell=\log L$, and $r(T)=\ell^2/L$. Combining the total
zero count near the central line with the Cauchy density bound farther out
gives a right-tail estimate $\ll TL\exp(-Lt/(8\ell))$. Integrating the tail
gives $E(T)/T\ll r(T)$. The reflected ordinate-to-Landau error divided by
$T$ is $O(u^2r(T))$ uniformly for $|u|\le L/(16\ell)$. In particular it tends
to zero for every moving frequency satisfying $u(T)^2r(T)\to0$.
For fixed positive $u$, the centered contour contributes
$O_u(\log^2(T+3)/T)$ after subtracting its identified main term.

| Lean declaration | Scope |
| --- | --- |
| `eventually_ordinate_landau_loglog_band`, `tendsto_ordinate_landau_of_moving_loglog` | Uniform transfer of actual ordinates, with multiplicity, over the growing band. |
| `eventually_rational_ordinate_loglog_band` | Uniform arithmetic remainder $O(1/L+u^2r(T))$ for $u=\log(n/m)$, $1\le m<n$, $\log n\le L/8$ and $u\le L/(16\ell)$. |
| `ramanujanOrdinateApprox_sub_eq`, `ramanujanOrdinateApprox_error_isBigO` | Exact signed divisor-probe error identity and an unconditional $O_{p,q,n}(r(T))$ rate for the original height-normalized sum. |
| `ramanujanPacket_ordinate_error_isBigO` | Same-height signed prefix at any fixed cutoff. |
| `periodicOrdinatePacket_error_le_one_period`, `eventually_periodicOrdinatePacket_uniform` | One period reconstructed from harmonics $1,\ldots,q-1$ controls all physical coordinates and all successive differences with an $O_{p,q}(r(T))$ error. |
| `eventually_periodicOrdinatePacket_weighted_sq` | For every nonnegative summable weight, the full squared error is at most $(\sum_k w_k) C_{p,q}^2r(T)^2$ with a common height threshold. |
| `eventually_round_periodicOrdinatePacket` | For every sufficiently large $T$, rounding real parts recovers every integer packet value and every positive harmonic Ramanujan sum simultaneously. |
| `exists_cofinal_round_periodicOrdinatePacket` | One increasing sequence of height thresholds works at stage $N$ for all primes and conductors up to $N$ and every coordinate. |

The uniform reconstruction fixes $p$ and $q>1$ and reduces the physical
coordinate modulo $q$ before taking the prefix. The raw divisor probe has a
fixed-harmonic estimate. The rounding threshold is existential.
[Horizontal concentration and transfer](Analysis/ActualZeroLoglogRate.lean) ·
[Quantitative reconstruction](RH/RamanujanOrdinateRate.lean)

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

## Horizontal moments and third coefficients (2026-10-28)

### RiemannResearch/Analysis/CoshTaylorRemainder.lean

Unconditional elementary real-series results:

- `coshTaylorRemainder_eq_tsum`: exact positive tail.
- `coshTaylorRemainder_frequency_le`: all-orders comparison-frequency bound.
- `coshTaylorHead_one`, `coshTaylorRemainder_one`: explicit quadratic head.

### RiemannResearch/Analysis/ActualZeroHorizontalRemainder.lean

- `evenHorizontalMoment`, `horizontalTaylorPolynomial`,
  `horizontalTaylorError`: actual multiplicity-weighted definitions.
- `horizontalTaylorPolynomial_eq_moments`,
  `horizontalTaylorError_eq_remainder`, `horizontalTaylorError_one`:
  unconditional exact signed identities.
- `horizontalTaylorError_of_expTail`: all-orders transfer with explicit
  strict-tail input.
- `normalized_horizontalTaylorError_of_selberg`: order J remainder
  O(T |u|^(2J+2)/(log T)^(2J+1)), uniformly on |u| <= a log T/2.
- `normalized_horizontalTaylorError_one_of_selberg`: exact quadratic
  correction and quartic remainder, with constant 32 C/(3 a^4).
- `finiteFourier_horizontalTaylorError_one_of_selberg`: signed finite
  Fourier synthesis with quartic frequency budget.

The last three are **conditional research reductions** with the explicit
actual Selberg density bound. They do not establish fixed limiting
higher-order coefficients.

### RiemannResearch/Analysis/LogarithmicRemainder.lean

- `log_mul_tendsto_zero_of_inv_log_cube`: elementary next-scale limit
  comparison from an explicit inverse-cubic-log remainder bound.

### RiemannResearch/Analysis/ActualRationalThirdCoefficient.lean

- `norm_evenHorizontalMoment_one_le`: unconditional horizontal-energy
  domination of the oscillatory second moment.
- `normalized_evenHorizontalMoment_one_le`: uniform bound 4 C/a^2 on
  log T times the height-normalized second moment, from Selberg.
- `eventually_rational_landau_error_le_inv_log_cube`: unconditional
  uniform rational Landau rate in log n <= log T/8.
- `tendsto_log_mul_horizontalTaylorError`: negligible next-scale
  horizontal remainder, from UniformSelbergDensity a.
- `tendsto_log_mul_rational_landau_error`: unconditional next-scale
  rational Landau limit.
- `tendsto_rational_thirdCoefficient_of_horizontalMoment`: conditional
  identification of the next coefficient with minus u^2/2 times the
  rescaled second-moment limit.
- `rational_thirdCoefficient_iff_horizontalMoment`: necessary-and-sufficient
  full-height convergence criterion for each rational q > 1.
- `exists_subseq_rational_thirdCoefficient`: for every divergent height
  sequence, a subsequence with moment and third-coefficient limits for a
  fixed rational mode, from UniformSelbergDensity a.

**Open:** a checked provider of UniformSelbergDensity (1/4).
**Open:** convergence of the rescaled oscillatory second moment along all
heights; it is not assumed or proved by the subsequence theorem.
The simultaneous measure-level subsequence theorem, full weighted Fourier
synthesis, and sharper scalar integral bound have ordinary proofs in
`Analysis/HorizontalThirdCoefficient.md`; those extensions are not claimed
as newly kernel-checked declarations.

# Montgomery / Parseval theorem catalog — 2026-11-10

These modules extend the actual-zero, prime-torus, and band-limited Weil baseline at `ddffaf3b485734d24423da3945cbd9be880f01a2`. They prove exact identities and explicit conditional estimates. They do **not** prove pair correlation, RH, the gamma operator bound, or a vanishing horizontal defect.

[Research ledger, corrected literature, and open estimates](MontgomeryParsevalResearch20261110.md).

| Module | Principal declarations | Exact scope / assumptions |
|---|---|---|
| [PrimeHomogeneousResonance.lean](Analysis/PrimeHomogeneousResonance.lean) | `resonance_eq_zero_of_cardFactors_eq`; `actual_zero_sum_homogeneous` | Positive natural indices, equal Omega; the Weil specialization retains its test regularity, support, and length assumptions. |
| [PrimeTorusHomogeneous.lean](Analysis/PrimeTorusHomogeneous.lean) | `haarIntegral_homogeneous_parseval` | Homogeneous finite frequency family; Poisson radii in [0,1). Signed density; no positivity assertion. |
| [PrimeTorusMoments.lean](Analysis/PrimeTorusMoments.lean) | `haar_fourth_moment`; `haarIntegral_homogeneous_power_density_zero`; `haarIntegral_homogeneous_power_parseval` | Finite torus, arbitrary complex coefficients; for the correction identity, equal total degree and the explicit radius bounds. |
| [MontgomeryPoisson.lean](Analysis/MontgomeryPoisson.lean) | `integrable_feature`; `integral_feature`; `integral_cauchy` | Bilateral transform requires abs(Re z)<a. Cauchy specialization is unconditional. |
| [MontgomeryCauchyGram.lean](Analysis/MontgomeryCauchyGram.lean) | `finite_gram`; `finite_gram_integrable`; `kernelQuadratic_nonneg` | Arbitrary finite real ordinates, repeats allowed, and arbitrary complex coefficients. |
| [MontgomeryFormFactor.lean](Analysis/MontgomeryFormFactor.lean) | `formFactor_nonneg`; `formFactor_even`; `formFactor_gram`; `actual_indexed_diagonal` | Actual zeros and all multiplicities. Nonnegativity of normalized form factor requires T>1. |
| [MontgomeryFourierPairing.lean](Analysis/MontgomeryFourierPairing.lean) | `finite_fourier_pairing`; `actual_fourier_pairing`; `normalized_fourier_pairing` | Continuous f with f and its Fourier transform integrable. No RH. |
| [MontgomeryPrimeProbe.lean](Analysis/MontgomeryPrimeProbe.lean) | `shifted_probe` | Arbitrary finite real probe frequencies and weights. Exact unnormalized pair-sum identity. |
| [MontgomeryComplexGram.lean](Analysis/MontgomeryComplexGram.lean) | `complex_gram`; `weightedSignal_memLp`; `sqrt_energy_reverse_triangle` | Finite complex frequencies with abs(Re z)<1; generic reverse triangle has explicit MemLp inputs. |
| [MontgomeryHorizontalTransfer.lean](Analysis/MontgomeryHorizontalTransfer.lean) | `sharpIntegral_eq_actualComplexPairSum`; `sharpFormFactor_eq_actualComplexPairSum`; `sqrt_horizontal_error` | Actual zeros; integrability and reflection discharged. The defect is not assumed or proved to vanish. |
| [ShortIntervalVariance.lean](Analysis/ShortIntervalVariance.lean) | `variance_decomposition`; `centeredVariance_exact`; `centeredVariance_error_identity`; `centeredVariance_error_le` | Finite identity works in every commutative ring. Error inequality explicitly assumes both signed budgets. |

## Complete declaration index

Names below are relative to their listed namespace. The source is authoritative for every binder and conclusion.

### PrimeHomogeneousResonance

Namespace: `RiemannResearch.Analysis.PrimeBandlimitedWeil`.

- `eq_of_dvd_of_cardFactors_eq` (theorem).
- `resonance_eq_zero_of_cardFactors_eq` (theorem).
- `homogeneous_resonance_quadratic_zero` (theorem).
- `actual_zero_sum_homogeneous` (theorem).

### PrimeTorusHomogeneous

Namespace: `RiemannResearch.Analysis.PrimeTorusHaar`.

- `axisMultiplier_eq_zero_of_sum_eq_zero` (theorem).
- `haarIntegral_character_mul_star_density_of_degree` (theorem).
- `haarIntegral_homogeneous_density_zero` (theorem).
- `haarIntegral_homogeneous_parseval` (theorem).

### PrimeTorusMoments

Namespace: `RiemannResearch.Analysis.PrimeTorusHaar`.

- `single_one_injective` (theorem).
- `single_one_add_eq_iff` (theorem).
- `character_add` (theorem).
- `haarIntegral_character_mul_star` (theorem).
- `haarIntegral_finite_gram` (theorem).
- `linearPolynomial` (def).
- `linearPolynomial_square` (theorem).
- `haar_fourth_moment_algebra` (theorem).
- `haar_fourth_moment` (theorem).
- `haarIntegral_homogeneous_family_density_zero` (theorem).
- `character_sum` (theorem).
- `polynomial_power_expansion` (theorem).
- `haarIntegral_homogeneous_power_density_zero` (theorem).
- `haarIntegral_homogeneous_power_parseval` (theorem).
- `haar_fourth_moment_with_density` (theorem).

### MontgomeryPoisson

Namespace: `RiemannResearch.Analysis.MontgomeryPoisson`.

- `feature` (def).
- `feature_nonneg` (theorem).
- `feature_nonpos` (theorem).
- `feature_integrableOn_Iic` (theorem).
- `feature_integrableOn_Ioi` (theorem).
- `integrable_feature` (theorem).
- `integral_feature` (theorem).
- `integral_cauchy` (theorem).

### MontgomeryCauchyGram

Namespace: `RiemannResearch.Analysis.MontgomeryPoisson`.

- `cauchyWeight` (def).
- `signal` (def).
- `kernelQuadratic` (def).
- `phase_mul_conj` (theorem).
- `feature_phase` (theorem).
- `finite_gram_integrand` (theorem).
- `finite_gram_complex` (theorem).
- `finite_gram_integrable` (theorem).
- `finite_gram` (theorem).
- `kernelQuadratic_nonneg` (theorem).

### MontgomeryFormFactor

Namespace: `RiemannResearch.Analysis.MontgomeryFormFactor`.

- `pairSum` (def).
- `pairSum_eq_kernel` (theorem).
- `pairSum_nonneg` (theorem).
- `pairSum_even` (theorem).
- `pairSum_real` (theorem).
- `pairSum_gram` (theorem).
- `indexed_diagonal` (theorem).
- `formFactor` (def).
- `formFactor_nonneg` (theorem).
- `formFactor_even` (theorem).
- `formFactor_gram` (theorem).
- `actual_indexed_diagonal` (theorem).

### MontgomeryFourierPairing

Namespace: `RiemannResearch.Analysis.MontgomeryFormFactor`.

- `integral_phase_fourier` (theorem).
- `integrable_phase_mul` (theorem).
- `finite_fourier_pairing` (theorem).
- `actual_fourier_pairing` (theorem).
- `ofReal_formFactor` (theorem).
- `normalized_fourier_pairing` (theorem).

### MontgomeryPrimeProbe

Namespace: `RiemannResearch.Analysis.MontgomeryFormFactor`.

- `probeKernel` (def).
- `phase_mul_conj_frequency` (theorem).
- `probe_energy_expansion` (theorem).
- `shifted_probe` (theorem).

### MontgomeryComplexGram

Namespace: `RiemannResearch.Analysis.MontgomeryComplexGram`.

- `complexSignal` (def).
- `complexKernel` (def).
- `feature_complex_product` (theorem).
- `complex_gram_integrand` (theorem).
- `pair_strip` (theorem).
- `complex_gram_integrable` (theorem).
- `complex_gram` (theorem).
- `complex_gram_re` (theorem).
- `weightedSignal` (def).
- `weightedSignal_sq` (theorem).
- `weightedSignal_memLp` (theorem).
- `sqrt_integral_sq_norm` (theorem).
- `sqrt_energy_reverse_triangle` (theorem).
- `complexSignal_shift` (theorem).

### MontgomeryHorizontalTransfer

Namespace: `RiemannResearch.Analysis.MontgomeryHorizontalTransfer`.

- `weightedLandau` (def).
- `weightedOrdinate` (def).
- `weighted_mul_sq` (theorem).
- `weightedLandau_memLp` (theorem).
- `weightedOrdinate_memLp` (theorem).
- `sharpIntegral` (def).
- `rawIntegral` (def).
- `defectIntegral` (def).
- `sqrt_integral_horizontal_error` (theorem).
- `sharpFormFactor` (def).
- `horizontalDefect` (def).
- `formFactor_eq_rawIntegral` (theorem).
- `sqrt_horizontal_error` (theorem).
- `complexPairTerm` (def).
- `actualComplexPairSum` (def).
- `centered_pair_reflect` (theorem).
- `centered_exp_product` (theorem).
- `actual_complex_kernel` (theorem).
- `sharpIntegral_eq_actualComplexPairSum` (theorem).
- `sharpFormFactor_eq_actualComplexPairSum` (theorem).

### ShortIntervalVariance

Namespace: `RiemannResearch.Analysis.ShortIntervalVariance`.

- `square_sum_range` (theorem).
- `triangle_by_gap` (theorem).
- `variance_decomposition` (theorem).
- `centeredMangoldt` (noncomputable def).
- `centeredVariance` (noncomputable def).
- `centeredDiagonal` (noncomputable def).
- `centeredOffDiagonal` (noncomputable def).
- `centeredVariance_exact` (theorem).
- `centeredVariance_error_identity` (theorem).
- `centeredVariance_error_le` (theorem).

## Validation evidence

Focused Bazel checks succeeded for the raw form factor and its imports (job `job_HfkKfwukOSiwd6HUxpzRnkaMriAyR7ob`), the Fourier/probe identities and torus/variance imports (job `job_P_-4vzlPFwgY8hXVTYSh8n8oyuVLDeaN`), and the complete complex/horizontal development (job `job_my_XB2iuyfC299Jf19Rz8S2_ih0LAq_Z`). Those are scoped checks. The publication checkpoint separately audits all changed sources and validates `//:RiemannResearch`, including integration revalidation. Consult its result for the final published revision.

# Montgomery analytic-provider theorem catalog — 2026-11-10

Continuation of [the Parseval checkpoint](THEOREM_CATALOG_MONTGOMERY_PARSEVAL_20261110.md).
See [the research ledger](MontgomeryAnalyticProviders20261110.md) for formulas, scope, and open estimates.

These modules supply analytic transforms, actual-zero upper bounds, and a Gaussian Fourier-damping removal limit. They do not prove pair correlation, RH, gamma-remainder decay, or vanishing horizontal defect.

| Module | Principal declarations | Exact scope |
|---|---|---|
| [ShiftedSechKernel.lean](Analysis/ShiftedSechKernel.lean) | `kernel_pos`, `integrable_kernel`, `integral_kernel` | Positive integrable kernel and mass one; |δ|<1/2. |
| [ShiftedSechSpectrum.lean](Analysis/ShiftedSechSpectrum.lean) | `spectrum_le_exp`, `integrable_spectrum`, `spectrum_le_one` | Explicit exponential profile bound; integrability on the open shift strip. |
| [SechLaplaceTransform.lean](Analysis/SechLaplaceTransform.lean) | `integral_exp_div_cosh`, `integrable_exp_div_cosh` | Complete bilateral Laplace transform; |Re z|<1. Beta substitution and gamma reflection proved/applied in Lean. |
| [ShiftedSechTransform.lean](Analysis/ShiftedSechTransform.lean) | `fourier_profile`, `inverse_kernel`, `integral_kernel_phase` | Complete transform κδ ↦ cosh(δu)/cosh(u/2); only |δ|<1/2, with integrability discharged. |
| [ActualZeroSechSmoothing.lean](Analysis/ActualZeroSechSmoothing.lean) | `density_nonneg`, `integral_density`, `integral_density_phase` | Actual multiplicities, positive density of mass Ncount(0,T), exact sech times Landau transform. No RH. |
| [MontgomeryLocalMass.lean](Analysis/MontgomeryLocalMass.lean) | `exists_actual_cauchy_row_bound`, `exists_actual_cauchy_gram_bound`, `exists_formFactor_le_log` | Actual local-count provider discharged. Cauchy rows O(log(T+3)); F_T(α)≤C log T for every α, T≥9. |
| [MontgomeryComplexSchur.lean](Analysis/MontgomeryComplexSchur.lean) | `complex_cauchy_norm_le`, `exists_actual_displaced_energy_bound`, `exists_actual_centered_energy_bound` | Entry factor 4/3 on closed half-strip. Arbitrary coefficients; actual centered-zero specialization discharges strip and ordinate conditions. |
| [MontgomeryCoshLaplace.lean](Analysis/MontgomeryCoshLaplace.lean) | `integral_coshFeature`, `integral_defectFeature`, `diagonalEnergy_nonneg` | Exact signed scalar energy q(u,d), integrable for |d|<1. |
| [MontgomeryHorizontalBound.lean](Analysis/MontgomeryHorizontalBound.lean) | `sqrt_defectIntegral_le_diagonal`, `defectIntegral_le_diagonal`, `horizontalDefect_le_horizontalEnergy` | Unconditional actual Minkowski and strip-energy bounds. No decay hypothesis or conclusion; exponential growth retained. |
| [MontgomeryGaussianSmoothing.lean](Analysis/MontgomeryGaussianSmoothing.lean) | `exists_actual_gaussian_pairing_error`, `actual_reciprocal_log_pairing_sub_tendsto_zero` | Real f∈L¹ with a²|f|∈L¹. Actual Gaussian Fourier damping error; explicit width gives O_f(1/log T) and convergence. |
| [MontgomeryComplexGram.lean](Analysis/MontgomeryComplexGram.lean) (extended) | `sqrt_energy_add_le`, `sqrt_energy_sum_le` | Generic finite L2 triangle bounds with explicit MemLp inputs. |

## Declaration index

### ShiftedSechKernel

Namespaces: `RiemannResearch.Analysis.ShiftedSech`.

- `kernel` (def).
- `cosh_shift_re` (theorem).
- `cosh_shift_im` (theorem).
- `kernel_eq` (theorem).
- `cos_pos` (theorem).
- `kernel_pos` (theorem).
- `kernel_le_reciprocal` (theorem).
- `reciprocal_cosh_le` (theorem).
- `kernel_le_exp` (theorem).
- `continuous_kernel` (theorem).
- `integrable_kernel` (theorem).
- `kernel_eq_simple` (theorem).
- `primitive` (def).
- `hasDerivAt_primitive` (theorem).
- `tendsto_sinh_atTop` (theorem).
- `tendsto_sinh_atBot` (theorem).
- `primitive_atTop` (theorem).
- `primitive_atBot` (theorem).
- `integral_kernel` (theorem).
- `kernel_neg` (theorem).
- `kernel_neg_shift` (theorem).
- `intervalIntegral_kernel` (theorem).
- `integral_kernel_Ioi` (theorem).
- `integral_kernel_Iic` (theorem).

### ShiftedSechSpectrum

Namespaces: `RiemannResearch.Analysis.ShiftedSech`.

- `spectrum` (def).
- `cosh_le_exp_abs` (theorem).
- `spectrum_pos` (theorem).
- `spectrum_le_exp` (theorem).
- `continuous_spectrum` (theorem).
- `integrable_spectrum` (theorem).
- `spectrum_le_one` (theorem).
- `spectrum_neg` (theorem).
- `spectrum_zero` (theorem).
- `ofReal_kernel_eq_average` (theorem).

### SechLaplaceTransform

Namespaces: `RiemannResearch.Analysis.SechLaplace`.

- `sigmoid_two_eq` (theorem).
- `log_sigmoid_two` (theorem).
- `log_one_sub_sigmoid_two` (theorem).
- `beta_jacobian` (theorem).
- `sigmoid_two_image` (theorem).
- `betaIntegral_eq_laplace` (theorem).
- `integral_exp_div_cosh` (theorem).
- `integrable_exp_div_cosh` (theorem).

### ShiftedSechTransform

Namespaces: `RiemannResearch.Analysis.ShiftedSech`.

- `profile` (def).
- `continuous_profile` (theorem).
- `integrable_profile` (theorem).
- `profile_neg` (theorem).
- `laplaceAtom` (def).
- `scaled_laplace` (theorem).
- `laplaceAtom_integrable` (theorem).
- `profile_phase_expansion` (theorem).
- `fourier_profile` (theorem).
- `inverse_kernel` (theorem).
- `integral_kernel_phase` (theorem).

### ActualZeroSechSmoothing

Namespaces: `RiemannResearch.Analysis.ShiftedSech`, `RiemannResearch.Analysis.ActualZeroSechSmoothing`.

- `integrable_kernel_translate` (theorem).
- `integrable_kernel_translate_phase` (theorem).
- `integral_kernel_translate_phase` (theorem).
- `density` (def).
- `density_nonneg` (theorem).
- `integrable_density` (theorem).
- `integral_density` (theorem).
- `integrable_density_phase` (theorem).
- `integral_density_phase` (theorem).

### MontgomeryLocalMass

Namespaces: `RiemannResearch.Analysis.MontgomeryLocalMass`.

- `inverseSquareEnvelope` (def).
- `inverseSquareEnvelope_nonneg` (theorem).
- `summable_inverseSquareEnvelope` (theorem).
- `tsum_inverseSquareEnvelope_le` (theorem).
- `inverseSquareEnvelope_row_le` (theorem).
- `cauchyWeight_le_cell_envelope` (theorem).
- `cauchy_row_le_of_occupancy` (theorem).
- `WindowCopies` (abbrev).
- `card_windowCopies` (theorem).
- `actual_cell_occupancy_le_count` (theorem).
- `actual_cell_occupancy_bound` (theorem).
- `cauchyWeight_nonneg` (theorem).
- `cauchyWeight_neg` (theorem).
- `kernelQuadratic_norm_le_of_rows` (theorem).
- `weighted_signal_energy_le_of_rows` (theorem).
- `exists_actual_cauchy_row_bound` (theorem).
- `exists_actual_cauchy_gram_bound` (theorem).
- `exists_formFactor_le_log` (theorem).

### MontgomeryComplexSchur

Namespaces: `RiemannResearch.Analysis.MontgomeryComplexSchur`.

- `complex_cauchy_norm_le` (theorem).
- `complexKernel_norm_le_of_rows` (theorem).
- `complex_signal_energy_le_of_rows` (theorem).
- `exists_actual_displaced_energy_bound` (theorem).
- `exists_actual_centered_energy_bound` (theorem).

### MontgomeryCoshLaplace

Namespaces: `RiemannResearch.Analysis.MontgomeryCoshLaplace`.

- `realFeature` (def).
- `feature_real` (theorem).
- `integrable_realFeature` (theorem).
- `integral_realFeature` (theorem).
- `coshFeature` (def).
- `coshFeature_expansion` (theorem).
- `integrable_coshFeature` (theorem).
- `integral_coshFeature` (theorem).
- `defectFeature` (def).
- `diagonalEnergy` (def).
- `defectFeature_expansion` (theorem).
- `integrable_defectFeature` (theorem).
- `integral_defectFeature` (theorem).
- `diagonalEnergy_nonneg` (theorem).

### MontgomeryHorizontalBound

Namespaces: `RiemannResearch.Analysis.MontgomeryHorizontalBound`.

- `cosh_abs_half` (theorem).
- `stripCoefficient` (def).
- `stripCoefficient_eq_diagonalEnergy` (theorem).
- `stripCoefficient_nonneg` (theorem).
- `defectFeature_le_strip` (theorem).
- `diagonalEnergy_le_strip` (theorem).
- `integrable_actualDefect` (theorem).
- `actualDefect_integrand_le` (theorem).
- `defectIntegral_le_horizontalEnergy` (theorem).
- `horizontalDefect_le_horizontalEnergy` (theorem).
- `weightedCopy` (def).
- `weightedCopy_sq` (theorem).
- `weightedCopy_memLp` (theorem).
- `weightedCopy_sum` (theorem).
- `sqrt_defectIntegral_le_diagonal` (theorem).
- `defectIntegral_le_diagonal` (theorem).

### MontgomeryGaussianSmoothing

Namespaces: `RiemannResearch.Analysis.MontgomeryGaussianSmoothing`.

- `continuous_formFactor` (theorem).
- `gaussian_damping_error` (theorem).
- `integrable_mul_of_abs_le` (theorem).
- `gaussian_pairing_difference_eq` (theorem).
- `gaussian_pairing_error_le` (theorem).
- `exists_actual_gaussian_pairing_error` (theorem).
- `actual_gaussian_pairing_sub_tendsto_zero` (theorem).
- `exists_actual_reciprocal_log_pairing_error` (theorem).
- `actual_reciprocal_log_pairing_sub_tendsto_zero` (theorem).

### MontgomeryComplexGram additions

Namespace: `RiemannResearch.Analysis.MontgomeryComplexGram`.

- `sqrt_energy_add_le` (theorem).
- `sqrt_energy_sum_le` (theorem).

Total added: **112 theorems/lemmas and 14 definitions/abbreviations**, across ten new modules and one extended module. Source signatures are authoritative; generic-strip and test-integrability inputs must not be omitted.

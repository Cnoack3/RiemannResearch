# Montgomery three-route continuation

Base revision: b9c9139d88001b782cc75481365633c36f43d948.

## Established identities and implications

| Module | Declaration | Content |
| --- | --- | --- |
| MontgomerySharpWeilSeparator | fixedRightZeroSharpSeparator | The actual-zero Weil test at \(1-\rho\) defines a bounded functional isolating the \(\rho\)-term in every later cutoff. Uses analytic multiplicity and no horizontal zero hypothesis. |
| MontgomerySharpWeilSeparator | fixedRightZeroSharpIntegralLower | A fixed right-half zero supplies a cutoff-independent exponential lower bound for the complex energy. |
| MontgomerySharpWeilSeparator | cofinalSharpPolynomialUpper_iff_riemannHypothesis | A common polynomial exponent above every fixed frequency floor is equivalent to RH. The reverse implication has the uniform \(O(T\log^2 T)\) bound. |
| MontgomeryWindowPairCorrelation | unfoldedWindowEnergy_secant_bounds | Exact diagonal-plus-interval decomposition gives endpoint bounds for every secant. |
| MontgomeryWindowPairCorrelation | collision_limit_of_sineWindowMoment | Precise fixed-width window limits imply normalized collision mass one. |
| MontgomeryWindowPairCorrelation | positiveGapPCC_of_sineWindowMoment | Precise fixed-width window limits imply ordinary PCC uniformly on compact positive intervals. |
| MontgomeryWindowPairCorrelation | sineWindowMoment_iff_positiveGapPCC | Ordinary PCC and the sine window moment are equivalent in the presence of the published GLSS upper moment. |
| MontgomeryOneSidedFourier | rawFormFactorTestUpper_iff_limit | The one-sided nonnegative-test bound is equivalent to the full weak raw Fourier prediction. Uses the actual-count diagonal lower bound and the exact large Fejér triangle value. |

The short-window input is Goldston, Lee, Schettler and Suriajaya, Mathematika 72 (2026), e70127, Propositions 1–2, https://doi.org/10.1112/mtk.70127.
The complex form-factor normalization follows Baluyot, Goldston, Suriajaya and Turnage-Butterbaugh, Acta Arith. 214 (2024), 357–376, https://doi.org/10.4064/aa230612-20-3, corrected for the positive cutoff in https://arxiv.org/html/2501.14545v3#S3.E5.

## Exceptional-pair estimates

- `MontgomeryExceptionalPairs.pair_dirichlet_identity` retains the complete nonnegative square in the symmetric-kernel Cauchy bound. `pair_exp_moment_add_defect_le` uses the multiplicative Hölder budget for the companion horizontal and crowding moments. `norm_signed_deletion_le_with_defect` carries this square into the finite signed deletion estimate.
- **Conditional research reduction.** `ActualMontgomeryExceptionalPairs.eventually_signed_strip_deletion_le` bounds the signed cost of deleting arbitrary zero copies with scaled horizontal displacement at least `x` by `B exp(-c x)`, uniformly in the strip width, whenever `0 < c < 8/7 - 2θ`. The result uses analytic multiplicity and the pointwise envelope specified in the declaration.
- **Open formal providers.** The Conrey–Baluyot density family at every fixed `a < 8/7` and Fujii's microscopic row moments are explicit arguments. Lamzouri, Lemmas 2.1 and 2.3, uses these published inputs in the small-gap analysis. [Small gaps paper](https://arxiv.org/abs/2611.14486)

## Moving form-factor edge

- **Conditional research reduction.** `MontgomeryHorizontalTransfer.sharpFormFactor_edgeLayer_le` bounds the sharp complex-zero form factor in the band `T ≤ x ≤ T log T / 8` by an explicit multiple of `y (1 + log(1/y))`, for `y = x/(T log T)` after subtracting `log x/log T` or 1. `sharpFormFactor_edgeLayer_tendsto` gives the limit along moving frequencies with `y → 0`. The monotonicity in `edgeSmoothingModulus_le` gives the same upper bound for an entire band using its right endpoint.
- `sharpFormFactor_edgeLayer_uniform` specializes the three estimates to the repository's `primeDiagonal`, `primeSignalEnergy`, and sharp form factor. It gives eventual uniform error below every positive tolerance throughout `T ≤ x ≤ T H` whenever `T → ∞` and `H/log T → 0`.
- **Open formal providers.** The finite diagonal estimate, the time-smoothed prime mean square, and its transfer to the sharp complex form factor are independent hypotheses. This layer has limiting normalized frequency one.

## Open actual-zero estimates

- Fixed-width sine-model variance. The known GLSS error in equation (3.7) does not vanish after dividing by \(T\) at fixed unfolded width.
- The global one-sided weak raw Fourier upper law, including possible endpoint concentration at \(\alpha=\pm1\).
- The cofinal polynomial bound for the complex energy above arbitrarily large frequency floors.
- A pair-scale estimate to close either absolute collision criterion.

Ordinary PCC and RH remain open.

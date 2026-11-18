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

## Open actual-zero estimates

- Fixed-width sine-model variance. The known GLSS error in equation (3.7) does not vanish after dividing by \(T\) at fixed unfolded width.
- The global one-sided weak raw Fourier upper law, including possible endpoint concentration at \(\alpha=\pm1\).
- The cofinal polynomial bound for the complex energy above arbitrarily large frequency floors.
- A pair-scale estimate to close either absolute collision criterion.

Ordinary PCC and RH remain open.

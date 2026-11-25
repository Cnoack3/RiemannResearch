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

- **Unconditional subunit resolvent cutoff.** `exists_normalized_cutoff_defect_bound` bounds the normalized sum of the outgoing finite-signal excess and the incoming squared error by $K e^u\log T/T$ for $T\ge5$ and $u\ge0$. `moving_band_cutoff_defect` gives uniform convergence on $0\le u\le U(T)$ whenever $e^{U(T)}\log T/T\to0$. `near_unit_cutoff_defect` specializes to $U(T)=\log T-2\log\log T$. [Resolvent boundary limits](Analysis/MontgomeryResolventBoundaryLimit.lean)

- **Conditional research reduction.** `MontgomeryHorizontalTransfer.sharpFormFactor_edgeLayer_le` bounds the sharp complex-zero form factor in the band `T ≤ x ≤ T log T / 8` by an explicit multiple of `y (1 + log(1/y))`, for `y = x/(T log T)` after subtracting `log x/log T` or 1. `sharpFormFactor_edgeLayer_tendsto` gives the limit along moving frequencies with `y → 0`. The monotonicity in `edgeSmoothingModulus_le` gives the same upper bound for an entire band using its right endpoint.
- `sharpFormFactor_edgeLayer_uniform` specializes the three estimates to the repository's `primeDiagonal`, `primeSignalEnergy`, and sharp form factor. It gives eventual uniform error below every positive tolerance throughout `T ≤ x ≤ T H` whenever `T → ∞` and `H/log T → 0`.
- **Prime diagonal.** [MontgomeryPrimeDiagonalAbel.lean](Analysis/MontgomeryPrimeDiagonalAbel.lean) gives `mangoldtSquarePrefix_abel` with the exact higher-prime-power correction. `mangoldtSquareCorrection_bound` and `mangoldtSquareCorrection_le_sqrt_log` bound that correction. `primeWeight_sq_edge_kernel` and `primeDiagonal_eq_edge_kernel` give the two branches of the squared weight, including the matching point. [MontgomeryPrimeDiagonalAsymptotic.lean](Analysis/MontgomeryPrimeDiagonalAsymptotic.lean) gives the exact signed remainder `primeDiagonal_sub_log_eq_error_integrals`, its unconditional root-log exponential bound `primeDiagonal_sub_log_isBigO_sqrtLog`, and `primeDiagonalAsymptotic_unconditional`.
- **Time smoothing.** [MontgomeryTrapezoidEstimates.lean](Analysis/MontgomeryTrapezoidEstimates.lean) gives the exact integral `trapezoidFrequencyEnvelope_integral` and the finite signed-shell inequality `trapezoidGapShell_le`. The shell's coefficient-mass bound is a hypothesis.
- **Positive-height transfer.** [MontgomerySharpEdgeTransfer.lean](Analysis/MontgomerySharpEdgeTransfer.lean) gives `edgePairNormalization` for zeros in `(0,T]` counted with multiplicity, `edgeLogEnergyBound` and `edgeTransfer_of_thirdResidual`. The last theorem requires a bound on `thirdSignalResidual`. The independent integral `edgePoleEnergy_integral` evaluates the rational pole energy on the positive half-line to `4π/3`.
- **Conditional research reduction.** [MontgomerySharpEdgeLayer.lean](Analysis/MontgomerySharpEdgeLayer.lean) gives `sharpFormFactor_edge_of_optimized_errors` and `sharpFormFactor_edge_uniform_of_optimized_errors`. The finite estimate for the error from one allows `T ≤ x ≤ T log T`. It uses separate diagonal, optimized mean-square and transfer bounds. Uniform convergence uses these bounds only on the retained frequencies and assumes `T → ∞` and `H / log T → 0`. The specialization `sharpFormFactor_edge_uniform_of_smoothing_and_transfer` supplies the diagonal from the quantitative PNT and leaves the two signal estimates as hypotheses.
- **Paper deduction.** Write `L = log T`, `y = x/(TL)`, `D = primeDiagonal x`, `M = primeSignalEnergy T x` and `F = sharpFormFactor T (log x/L)`. Weighted Abel summation and the quantitative PNT give `D − log x = o(1)`. The averaged sieve bounds the off-diagonal coefficient mass for `0 < |log(n/m)| ≤ s ≤ 1` by `O(xs)`. Bracketing the time interval by trapezoids of masses `T ± w` then gives `|M − TD| ≪ wD + x(1 + log(T/w))`. Taking `w = min(x/L,T/4)` gives `|F − 1| ≪ y log(e/y)` on `T ≤ x ≤ TL` after sharp transfer. In particular the error tends to zero uniformly on `T ≤ x ≤ TH` for `1 ≤ H = o(L)`. [Bellotti, Theorem 1.5](https://arxiv.org/pdf/2508.02041) · [Languasco–Perelli–Zaccagnini, Lemma 6 and (2.13)–(2.15)](https://doi.org/10.1090/tran/6835)
- **Paper deduction for the signed transfer.** Retaining the explicit pole in (2.3) and taking the auxiliary cutoff at `T²` in the proof of Lemma 4 gives `M − TLF = (4π/3)x + O(x exp(−c(log T/log log T)^(1/3)))` for some `c > 0`, uniformly for `x ≥ T`. The Vinogradov–Korobov region controls the truncated zero sum. The corrected published positive-height asymptotic (3.5) covers `1 ≤ x ≤ T`. [BGSTB, Lemmas 1 and 4](https://doi.org/10.4064/aa230612-20-3) · [Corrected positive-height formula](https://arxiv.org/html/2501.14545v3#S3.E5)
- **Open formal providers.** The moving-edge application still needs the arithmetic close-pair sieve and infinite-series smoothing estimate, and the explicit-formula/height-cutoff transfer.
- **Open at the critical scale.** `sharp_tendsto_one_iff_centered_prime_offDiagonal_tendsto_zero` gives the filter-wise equivalence assuming eventual `T > 1`, `D/L → 1` and vanishing normalized centered transfer. Uniform convergence through `x ≍ TL` still requires `M − TD − (4π/3)x = o(TL)` uniformly on the band. A fixed normalized frequency greater than one is outside the moving-edge limit.

## Open actual-zero estimates

- Fixed-width sine-model variance. The known GLSS error in equation (3.7) does not vanish after dividing by \(T\) at fixed unfolded width.
- The global one-sided weak raw Fourier upper law, including possible endpoint concentration at \(\alpha=\pm1\).
- The cofinal polynomial bound for the complex energy above arbitrarily large frequency floors.
- A pair-scale estimate to close either absolute collision criterion.

Ordinary PCC and RH remain open.

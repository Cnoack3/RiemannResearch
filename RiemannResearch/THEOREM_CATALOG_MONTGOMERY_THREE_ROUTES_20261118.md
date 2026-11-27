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

## Ingham-band tests and the regular structure factor

The frequency bound `|u| ≤ (4/3) log T` in A24 controls the difference of two count-normalized prime-orbit statistics. For a height-dependent finite test with absolute coefficient sum `o(T)` and admissible Taylor orders, `PrimeOrbitBandTest.tendsto_ordinate_sub_reconstructed` gives convergence of that difference to zero. Both statistics retain equal-ordinate pairs and analytic multiplicity.

**Conditional research reduction.** Choose positive unfolded probes $h_j$ tending to zero and a height sequence $T_n$ tending to infinity. At each fixed probe, use the same centering for the complete zero test and its reconstruction. If the first tends to the regular value $S(h_j)$ and the second has limiting upper bound $c h_j$ for all sufficiently large $j$, `liminf_le_of_centered_reconstruction` gives right lower slope at most $c$. The upper estimate may have any fixed $c<2$, including the triangular coefficient one.

| Statement | Scope |
| --- | --- |
| `structureFactor_liminf_lt_two_iff_eq_one` and `sine_det_of_liminf_lt_two` | For an integrable unit-mass multiplier between zero and one, lower slope below two forces ordinary right slope one, the full profile `min(abs h, 1)`, and the sine determinant at every finite order. |
| `interval_of_signedArithmeticCorrection_steps` | For the ordinary Cauchy-weighted form factor identified with this spectrum on the same heights, signed residual limits bounded above by $d h_j$ with fixed $d<1$ give a unit interval multiplier. |
| `signedArithmeticCorrection_four_thirds` | At the separately identified frequency $4/3$, a unit interval forces the signed arithmetic correction to tend to $-1/3$. |

**Open for the actual zeros.** Construct admissible probes that identify the centered full-occurrence statistic with the regular spectrum of each physical subsequential limit, and prove the arithmetic upper bound for their reconstructed values. Ordinary PCC via rigidity also needs the convolution two-point representation for each limit. A process-level determinantal representation would identify its higher correlations. [Lean transfer and residuals](Analysis/MontgomeryOrbitStructureFactor.lean) · [Spectral rigidity](Probability/DPPContinuousSpectralRigidity.lean)

## Fourier reconstruction of the full factorial statistic

Write $N=N(0,T]$, $L=\log T/(2\pi)$ and $A_T(u)=\sum_p e^{iu\gamma_p}$ over labeled occurrences. Write $R_{T,J}(u)$ for the reflected Landau sum with the signed even horizontal Taylor moments of orders $2,\ldots,2J$ subtracted. The exact remainder identity is $A_T-R_{T,J}=\mathrm{horizontalTaylorError}$. With $b\ge0$ choose

$
J(T,u,b)=\left\lceil\frac{\log(N+1)+|u|+1+b}{2\log 2}\right\rceil_+.
$

For every real frequency, the absolute amplitude error is at most $e^{-b}$ and the difference of the count-normalized squared amplitudes is at most $3e^{-b}$. For a finite family with total absolute coefficient mass at most $M$, adding $\log(1+M)$ to the order budget gives total error at most $3e^{-b}$. On every fixed band $|u|\le B\log T$, the order above is $O_B(\log T)$ when $b=\log T$. These bounds use strip support and retain all the signed moments. [Finite-height Lean bounds](Analysis/MontgomeryGapReconstruction.lean)

For a real integrable weight $w$, put $g(x)=\int w(h)\cos(2\pi hx)\,dh$ and $Q_T(h)=|R_{T,J(T,h\log T,\log T)}(h\log T)|^2/N$. At $T>1$ with $N>0$, the full reduced factorial statistic satisfies

$
\left|\frac1N\sum_{p\ne q}g\bigl(L(\gamma_p-\gamma_q)\bigr)
-\left(\int w(h)Q_T(h)\,dh-g(0)\right)\right|
\le \frac3T\|w\|_1 .
$

The test is prescribed independently of the ordinates. Only identical labels are removed. The estimate holds over the full frequency line, including frequencies past the Ingham tangent. Lean proves the Borel measurability of the order-dependent reconstruction, its integrability against $w$, and equivalence of the two height limits. [Factorial Fourier tests](Analysis/MontgomeryReconstructedGapTests.lean)

**Open arithmetic limit.** For every real even Schwartz $w$, the sine prediction for the complete reconstructed spectrum is

$
\int w(h)Q_T(h)\,dh\;\longrightarrow\;
w(0)+\int w(h)\min(|h|,1)\,dh .
$

The first term is the forward intensity atom. Fourier inversion of the unit interval gives the triangular transform of its squared sinc. Subtraction of $g(0)$ therefore gives the sine factorial density. These tests contain every smooth compactly supported even gap observable, by taking its Fourier transform. This formulation asks for the arithmetic evaluation of signed reconstructed powers. The finite-height comparison above discharges the transfer of physical test values. Passage from this statistic to stationary local limits uses fixed-window moment control. [Arias de Reyna and Rodgers](https://arxiv.org/abs/2311.13441) · [Fujii's moment estimate in Goldston, Lee, Schettler and Suriajaya, §5](https://arxiv.org/html/2503.15449v4#S5)

**Countable arithmetic input.** It suffices to test the positive integer Gaussians $g_n(x)=e^{-nx^2}$, $n\ge1$. Their Fourier weights are $w_n(h)=\sqrt{\pi/n}\,e^{-\pi^2 h^2/n}$, each of mass one, so the factorial comparison error is at most $3/T$ for every $n$. The sine target for the factorial statistic is

$
 m_n=\sqrt{\frac{\pi}{n}}
       +\frac{\sqrt n}{\pi^{3/2}}(1-e^{-\pi^2/n})
       -\operatorname{erf}\!\left(\frac{\pi}{\sqrt n}\right).
$

Indeed, integrate $w_n(h)\min(|h|,1)$ on $0<h<1$ and $h>1$, double the result, add $w_n(0)$ and subtract $g_n(0)=1$. Thus the single remaining family of arithmetic targets is $\int w_n Q_T\to1+m_n$. The Gaussian transform and the displayed elementary integral evaluation are analytic deductions.

Lean proves that convergence of these integer-power Gaussian moments to those of the sine measure gives convergence of every continuous compactly supported even test against the actual ordered distinct-label gap measure. The comparison with the sine measure and the Gaussian integrability of both measures are explicit in the application. To see how the countable family controls tails, put $z=e^{-x^2}$. Weierstrass approximation yields a polynomial $P$ with $|g(x)-zP(z)|\le\varepsilon z$ on the whole line. Convergence of the first Gaussian moment bounds this error uniformly in height. Equal-ordinate mass is visible since $g_n(0)=1$. [Relative Gaussian approximation and moment convergence](Analysis/GaussianGapTests.lean) · [Actual sine criterion](Analysis/MontgomeryReconstructedGapTests.lean)

**Fixed-band obstruction.** For every finite $B\ge0$, the lattice choice $a=1/(B+2)$ leaves the central Fourier tent unchanged and has no noncentral reciprocal atom on $[-B,B]$. Its positive-gap mass up to $a/2$ is zero, whereas the sine mass is positive. Lagarias and Rodgers give point processes with agreement at every order for this bandwidth. An independent uniform common translation gives a stationary version and preserves the pair displacements. For example, $a=1/3$ works through $B=2$, hence throughout $4/3$. [Lean pair calculation](Analysis/MontgomeryLatticeSineComparison.lean) · [Lagarias and Rodgers, Theorem 1.8(i)](https://arxiv.org/abs/1907.03391)

The stationary $a=1/3$ example also has number variance $\pi^{-2}\log R+O(1)$. For $m$ consecutive sites, projection Parseval gives $\operatorname{Var}N_m=2\sum_{k<m,\,k\ge1}k|K(k)|^2+2m\sum_{k\ge m}|K(k)|^2$ with $K(k)=\sin(\pi k/3)/(\pi k)$ for $k\ne0$. The tail is bounded and $\sin^2(\pi k/3)$ has period three and mean $1/2$. Random translation changes the number of sites in an interval by at most one and adds bounded variance. This calculation uses the discrete sine process of Lagarias and Rodgers, Theorem 4.1. It tests the inference from a bounded Fourier band and the leading number variance, without making a claim about which model describes zeta zeros.

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

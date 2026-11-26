# Zero-density, Montgomery pair-correlation and RH bounds

November 19, 2026. The starting revision is `d85004e85625dcf1811e6a66720dae4a50bc645e`. Write \(L=\log T\), \(X=L|\beta-\tfrac12|\), and count each occurrence with \(0<\gamma\le T\), with analytic multiplicity. The form-factor calculations use their stated \(TL/(2\pi)\) normalization. Physical displacement in the RH criterion is indexed by positive integers.

## Arithmetic comparison with the sampled zero ordinates

Write \(L=\log T\), \(D_T=TL/(2\pi)\), \(P_T(q)\) for the normalized count of gaps in \((0,q]\), \(G(q)=\int_0^q(1-\operatorname{sinc}^2(\pi u))\,du\), and \(C_T\) for the number of ordered equal-ordinate occurrence pairs divided by \(D_T\). All cutoffs count analytic multiplicities. The prescribed prime-power weights define \(Q_T(u)=L^{-1}\sum_{n\le T}(\Lambda(n)/n)e^{2\pi i u\log(n)/L}\) and \(B_T(q)=\int_0^q|Q_T(u)|^2du\).

* **Established arithmetic.** The finite double-sinc sum equals \(B_T\) exactly. Abel summation expresses \(Q_T-\int_0^1 e^{2\pi iuv}dv\) through the endpoint and Fourier integral of the Mertens CDF error. Plancherel gives convergence of \(B_T(q_T)-(q_T-G(q_T))\) for every eventually nonnegative \(q_T=o(L)\). For \(1<x<2\) the CDF vanishes at \(\log x/L\), giving an obstruction of exact order \(1/L\) for uniform CDF approximation. [Abel identity](Analysis/MontgomeryPrimeLogFourier.lean) · [Sinc expansion](Analysis/MontgomeryPrimeProbeSincExpansion.lean) · [Moving-width estimate](Analysis/MontgomeryPrimeProbePlancherel.lean)
* **Centered arithmetic estimate.** The classical quantitative PNT gives a constant \(C\) and a logarithmic remainder \(r(y)=S(e^y)-y-C\), with a summable block envelope and finite square integral. The shifted Abel identity keeps the term \(C/L\) frequency-independent. The integrated squared probe error is \(O(q/L^2+q^2/L^3)\), so the energy comparison holds for \(q=o(L^{3/2})\), including \(q=cL\) for every fixed \(c\ge0\). [Centered Mertens theorem](Analysis/MontgomeryCenteredMertens.lean) · [Plancherel estimate](Analysis/MontgomeryPrimeProbeCenteredPlancherel.lean)
* **Sharp arithmetic widths.** For $q/L\to\infty$, the signed energy excess divided by $q/L^2$ tends to $D=\sum_p(\log p)^2/(p^2-1)>0$. At $q/L^2\to\alpha>0$ the excess tends to $\alpha D$. For arbitrary eventually nonnegative widths it tends to zero if and only if $q/L^2\to0$. The normalized mixed term is $O(1/L)$ uniformly in width. [Sharp criterion and signed trace shift](Analysis/MontgomeryPrimeProbeSharpWidths.lean) · [Prime sum](Analysis/MontgomeryPrimeProbeDiagonalMean.lean) · [Kernel evaluation](Analysis/MontgomeryPrimeProbeMixedKernel.lean)
* **Signed lower tests.** Under upper comparisons for all fixed rational positive-gap shells, PCC is equivalent to requiring, for all \(\varepsilon>0\) and \(m\in\mathbb N\), some fixed \(n>m\) with \(A_T(n)+B_T(n)\ge-\varepsilon\) eventually. The shell comparisons and signed lower estimates for actual zeros are **Open**. At a diverging width with limiting arithmetic energy error \(\delta\), a vanishing signed trace is equivalent to \(A_T(q_T)\to-1/2-\delta\). [Cofinal lower tests](Analysis/MontgomeryCofinalPrimeProbeTrace.lean) · [Moving trace](Analysis/MontgomeryMovingPrimeProbeTrace.lean)
* **Exact PCC equivalence.** The signed trace \(A_T(q)+B_T(q)\to0\) at each positive rational width is equivalent to ordinary positive-gap PCC. The signed trace limit for actual zeros is **Open**. At a fixed positive Fourier frequency the corresponding signed residual uses the sum of the cutoff and prime off-diagonal errors minus the horizontal cross and defect terms. [Physical widths](Analysis/MontgomeryPrimeProbeEnergy.lean) · [Fixed frequencies](Analysis/MontgomeryOrdinateResidual.lean)
* **One-sided interval tests.** To obtain PCC it suffices to show that the limsup of the ordinary occurrence mass is at most the sine mass on every rational \((a,b]\) with \(a>0\) and at most \(1+G(b)\) on \([0,b]\), including the measured collision atom. The diagonal lower bound forces \(C_T\to1\). Nonnegativity of translated-window variance supplies all missing lower bounds. The converse for tests including zero uses the explicit short-window second-moment upper hypothesis in the repository. An alternative exact equivalence uses upper comparisons on strictly positive-gap shells and eventual lower bounds \(P_T(n)\ge n-\tfrac12-\varepsilon\) for arbitrarily large fixed integers. The actual one-sided majorants and the sparse lower normalization are **Open**. [One-sided criteria](Analysis/MontgomeryOrdinateIntervalUpper.lean)
* **Window polarization.** At any prescribed \(\eta(T)>0\) tending to zero, PCC is equivalent to \(P_T(\eta(T))\to0\) and convergence of the normalized three-energy contrast \([E_T(q+\eta)-E_T(q)-E_T(\eta)]/(2\eta)\) to \(G(q)\) at each positive rational \(q\). The collision terms cancel identically at finite height. Both analytic inputs are **Open**. [Smoothed sampling](Analysis/MontgomeryOrdinateWindowPolarization.lean)
* **Removing occurrences.** The exact cost of deletion is the positive-gap mass incident to the deleted set. Its convergence to zero is equivalent to vanishing of normalized exceptional positive-gap degrees. A single bounded normalized Cauchy row moment of order \(p>1\) gives uniform bounded-width loss \(O_{Q,p}(\delta^{1-1/p})\) for deleted fraction \(\delta\). The Fujii specialization takes the published row-moment interface as a premise. [Deletion](Analysis/MontgomeryPositiveGapDeletion.lean)
* **Horizontal test transfer.** Given one uniform Selberg slope \(a>0\) and Fujii row moments, every \(0\le\kappa<1-2\theta/a\) gives exceptional-pair loss \(O(\delta^\kappa)\). For \(0<2\theta<a\), vanishing of the one-sided horizontal mean, an exponential test envelope, and the retained-strip Taylor bound imply vanishing of the signed test defect. The existing Conrey–Baluyot input specializes this to \(\theta<4/7\). A larger slope, microscopic concentration, and the estimates for a literal Fourier test require separate providers as applicable. None of these transfer implications supplies the superunit ordinate information for full PCC. [Deletion exponents](Analysis/ActualMontgomeryExceptionalPairs.lean) · [Test transfer](Analysis/MontgomeryHorizontalTestConcentration.lean)

Sources for the complex-zero frequency range and the physical short-window method are [BGSTB, equation (3.5)](https://arxiv.org/abs/2501.14545) and [Goldston–Lee–Schettler–Suriajaya, §2](https://arxiv.org/abs/2503.15449). The Conrey–Baluyot and Fujii inputs for exceptional copies are stated in [Lamzouri, §2](https://arxiv.org/abs/2611.14486).

## Rational Landau estimates and prime-orbit characters

The curved Ingham estimate controls the signed horizontal Taylor remainder at every real phase $|u|\le(4/3)\log T$, including the endpoint. With $L=\log T$, retaining $J$ nonconstant even moments gives height-normalized error $O_k(L^{-k})$ when $2(J+1)\ge(k+4)(1+(4/3)\sqrt L)\log L$. For $u=\log(n/m)$ in the joint rational Landau band $\log n+3u/2\le\theta L$, $\theta<1$, the remaining horizontal error is $O(L^4(3/10)^{2(J+1)})$. The prime-orbit character identity relates the reconstructed amplitude to the unweighted cosine sum over all ordered zero pairs. [Landau comparison and prime-orbit test](Analysis/RationalLandauInghamTangent.lean)

The constant in the horizontal estimate is uniform in the precision order $k$. Taking $k\log L\ge 2L$ with the displayed Taylor order gives error $O(1/T)$ for the pair cosine sum divided by $N(T)$, uniformly over all finite prime-orbit characters in the phase range. For a finite test with real coefficients $c_b$, `eventually_weighted_primeOrbit_gap_count_precision` bounds the normalized reconstruction error by $(C/T)\sum_b|c_b|$, uniformly over height-dependent tests. Evaluating the reconstructed signed sum and obtaining the fixed-width sine law remain open. [Pair-count normalization](Analysis/RationalLandauInghamTangent.lean)

## Translation averages of positive gaps

The measured anchoring loss and the finite prime-probe energy agree asymptotically at every positive rational width exactly when ordinary positive-gap PCC holds. The signed comparison remains open. [Exact proof obligation and Lean entry point](PCC_REMAINING_PROOF.md)

If $\log T=o(R)$, $R=o(T\log T)$ and $0<w=o(R)$, the actual mass in $(s,s+w]$, averaged over $0\le s\le R$ and divided by $w$, tends to one. This includes shrinking widths. At a fixed positive rational width $q$, the average up to $R=(\log T)^2$ tends to $q$. Ordinary positive-gap PCC is equivalent to the assertion that moving the left endpoint from this translation average back to zero costs $\int_0^q\operatorname{sinc}^2(\pi u)\,du$ in the limit. This last estimate is open. [Finite identity, averaged law and equivalence](Analysis/MontgomeryTranslatedGapDensity.lean)

## Finite-law sharpness

With mass $e^{-Az}/z$ at $z\ge 1$ and all other mass at zero, the tilted first moments are at most one for every $a\le A$, and $q/[m\log(1/m)]=1/A$. At $A=8/7$ this attains the actual-zero upper coefficient for the abstract class of tilt inputs. [`two_atom_reciprocal_sharp`](Analysis/FiniteSizeBiasedSharpness.lean)

## Real-order moments and fixed strips

For every fixed real $s>1$, the actual copy law satisfies
\[
\limsup \frac{\mathbb E_T X^s}{m(\log(1/m))^{s-1}}\le (7/8)^{s-1}
\]
along a family of heights with positive mean tending to zero, under the named Conrey–Baluyot input. The previous actual-copy specialization treated $s=2$. Splitting at $k\log(1/m)$ for fixed $k>7/8$ leaves an exponentially small tilted contribution. The two-atom law attains the displayed coefficient for every $s$ at once. [`actual_realMoment_ratio_le_of_conreyBaluyot`](Analysis/ActualRealOrderHorizontalMoment.lean) · [`two_atom_realOrder_reciprocal_sharp`](Analysis/FiniteSizeBiasedRealPowers.lean)

For $M/L\to p\in(0,1]$, the curved Ingham coefficient is $3/(4+2p)$. Under the additional registered Lewko and published Guth–Maynard fixed-strip hypotheses the coefficient is $(\sigma_*(p)-1/2)/p$. Each strip is fixed before its height limit. At the $3/4$ jump the abscissae approach from above. [`actual_secondMoment_ratio_le_of_lewko_guthMaynard` and `horizontalStripCrossing`](Analysis/ActualFixedStripHorizontalMoment.lean) · [Lewko, Palomar v1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-11-000010&version=1) · [Guth and Maynard, Theorem 1.2](https://arxiv.org/html/2405.20552v2)

| $p$ | $\sigma_*(p)$ |
| --- | --- |
| $(0,5/17)$ | $(1+2p)/(2+p)$ |
| $[5/17,5/14)$ | $(15+3p)/(25-7p)$ |
| $[5/14,2/5)$ | $(5+4p)/9$ |
| $[2/5,4/9)$ | $(12+3p)/(20-5p)$ |
| $[4/9,1/2)$ | $3/4$ |
| $[1/2,1]$ | $3/(5-2p)$ |

[Focused Bazel verification and axiom checks](https://app.buildbuddy.io/invocation/c972702b-fc3e-4689-b094-87332b26f8cc) · [Full verification of the preceding moment-rate checkpoint](https://app.buildbuddy.io/invocation/fc3404e2-4dcd-424e-867e-d4ee510f79a5)

## Horizontal moment rates and moving thresholds

For a filtered family of heights tending to infinity let $m$ and $q$ be the first two moments of $X=L|\beta-1/2|$ under the actual occurrence law. Set $M=\log(1/m)$ and $\ell=\log L$. The rows below bound $q/(mM)$ eventually by every constant strictly above the stated coefficient. The mean is positive eventually.

| Prior bound | New coefficient | Exact hypotheses and declaration |
| --- | --- | --- |
| $7/8$ from subcritical size-biased tilts | $\min\{7/8,(3/4)(1+2/\lambda)\}$ | $m\to0$ and $M/\ell\to\lambda>0$ finite. The $7/8$ alternative uses the named Conrey–Baluyot hypothesis. The crossover is $\lambda=12$. [`actual_secondMoment_ratio_le_of_loglog_rate`](Analysis/ActualHorizontalMomentRates.lean) |
| $7/8$ | $3/4$ | $m\to0$ and $\ell/M\to0$. The proved Ingham bound gives a copy-law cap $K_aL^2$ at each $0<a<4/3$. [`exists_sizeBiased_log_sq_cap_of_ingham` and `actual_secondMoment_ratio_le_of_fast_mean`](Analysis/ActualHorizontalMomentRates.lean) |
| $3/4$ | $3/(4+2p)$ | $M/L\to p\in(0,1]$. For $p<1$ invert the curved Ingham exponent at a fixed cut, then take that cut down to $3p/(4+2p)$. At $p=1$ the physical support gives $1/2$. [`actual_secondMoment_ratio_le_of_fixed_cut` and `actual_secondMoment_ratio_le_of_polynomial_mean`](Analysis/ActualPolynomialHorizontalMoment.lean) |

The clean $8/7$ endpoint is equivalent to a common bound at the integer strikes $0\le k\le\min((21/2)\ell,L/2)$ at each sufficiently large height. Rounding a general strike down costs at most $e^{8/7}$. With $U=L/\ell$, $\log y=4L/7-BU$ and smoothing exponent $D/\ell$, the two logarithmic off-diagonal errors in (3.6.2), allowing a loss $KU$, are $(K+7D/2-7B/8)U$ and $(K+7D/2-7B/4)U$. Baluyot chooses the mollifier exponent before the error parameters in (3.6.3)–(3.6.7). A common residual constant and the corresponding uniform diagonal and desmoothing estimates remain open. [Integer-strike equivalence and exponent identities](Analysis/ActualSelbergEndpointMesh.lean) · [Baluyot, §3.6](https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320)

Write $S_T(u)=\mathbb E_T(X-u)_+$. The exact difference $S_T(0)-S_T(1)=\mathbb E_T\min(X,1)$ detects microscopic concentration. For every $\delta>0$ it lies between $\min(\delta,1)\Pr_T(X>\delta)$ and $\delta+\Pr_T(X>\delta)$. Its convergence to zero is equivalent to concentration without any density hypothesis. Estimating this signed difference by $o(1)$ on the actual zeros remains open. [`microscopicHorizontalConcentration_iff_clipped_excess`](Analysis/ActualClippedHorizontalConcentration.lean)

The degree-285 replay uses integer Bernstein subdivision on the compactified positive ray. The theorem `checkBernsteinRay_sound` covers every real input on that ray, including zero. [Soundness proof](Analysis/GapKernelBernsteinRay.lean)

[Focused Bazel verification of the rate, endpoint, concentration and Bernstein declarations](https://app.buildbuddy.io/invocation/4092c9d3-10e7-49ee-8702-9ed0c9b28577) · [Full verification of the preceding two-atom checkpoint](https://app.buildbuddy.io/invocation/0f596cf6-dc18-49cc-84d7-400d4cc8a1af)

## The Selberg parameter

| Result | Bound and scope |
| --- | --- |
| Selberg, Jutila, Conrey–Baluyot | Respectively \(a=1/4\), every fixed \(0<a<1\), and every fixed \(0<a<8/7\) in \(N(\sigma,T)\ll_a TL e^{-aL(\sigma-1/2)}\). The mollifier exponent is \(a/2\). `ZeroDensityLiterature.ConreyBaluyot2017` records the strict source count. `conreyBaluyot` proves the inclusive conversion. |
| Gabriel–Littlewood estimate | With \(q=3(1-\sigma)/(2-\sigma)\), the repository supplies \(N(\sigma,T)\ll\min(TL,T^qL^{2+q})\) uniformly at \(T\ge2\). `ingham_tangent_density_log_loss` gives the \(4/3\) slope with \(L^3\). [`ingham_exponent_le_affine_iff`](Analysis/NonlinearZeroDensityRate.lean) proves that \(q(\sigma)\le 1-a(\sigma-1/2)\) throughout the half-strip exactly when \(a\le 4/3\). At \(a=3/2\) and \(\sigma=5/9\), the gap is \(12/13-11/12=1/156\). |
| Endpoint interpolation | Given `ConreyBaluyotDensityHypothesis`, `endpoint_log_loss` gives \(TL^{1+\varepsilon}e^{-(8/7)L(\sigma-1/2)}\) for every \(\varepsilon>0\). `interpolated_profile` gives \(8/7<b<4/3\) with any surplus log power \(e>(21/2)(b-8/7)\). Constants can depend on the loss. |
| Clean \(8/7\) endpoint | `endpoint_density_outside_window` proves it on \(L(\sigma-1/2)\ge(21/2)\log L\). `endpoint_density_iff_window` identifies the remaining growing window. A local proof of the global single-logarithm endpoint remains **open**. The separately stated dyadic input below implies it. |
| Critical exponential moment | Under the Conrey–Baluyot input, at the exact tilt \(8/7\), `critical_exponential_moment_log_loss` bounds the average of \(e^{(8/7)X}\) by \(O_\varepsilon(L^\varepsilon)\) for every positive loss. |
| Microscopic concentration | `scaled_displacement_tendsto_zero_iff` proves that any one positive integer moment of \(X\) tends to zero exactly when \(\Pr(X>\delta)\to0\) for every fixed \(\delta>0\), assuming one positive Selberg slope. The vanishing is **open**. |
| Baluyot's normalized second moment | $(1/T)\int_T^{2T}\lvert\zeta M\rvert^2=1+O(y^{1-2\sigma})$, uniformly on the coupled evaluation strip. `ConreyBaluyot2017.of_normalizedMoments` derives the count interface using local Ingham. The moment is the external premise. |
| One-logarithm slope $4/3$ | Unconditional on $(5-4\sigma)\log L\le(4/3)(\sigma-1/2)^2L$. The full-strip conclusion uses `DyadicInghamOneLog`, the dyadic specialization of rStation 184/v1. Under that input `secondMomentRatio_of_dyadicInghamOneLog` gives every coefficient above $3/4$ along a positive vanishing microscopic mean. The analytic input remains open locally. |

[Selberg source audit, hypotheses and Lean entry points](RH/SelbergDensitySourceAudit20261119.md) · [Endpoint proof and source uniformity](RH/SelbergDensityEndpoint20261119.md) · [Baluyot, Theorem 1.2.1 and §3.6](https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320) · [Tao, Trudgian and Yang, chapter 11](https://teorth.github.io/expdb/blueprint/zero-density-chapter.html) · [Chourasiya and Simonič, preprint](https://arxiv.org/abs/2507.15184)

## Fixed strips and zero-free support

The pointwise minimum of the published Guth–Maynard and externally verified Lewko coefficients in \(N(\sigma,T)\ll_{\sigma,\varepsilon} T^{A(\sigma)(1-\sigma)+\varepsilon}\) is given below. `lewkoGuthMaynardCoefficient_eq` verifies the switches.

| Real-part interval | \(A(\sigma)\) |
| --- | --- |
| \([1/2,9/13]\) | \(3/(2-\sigma)\) |
| \((9/13,5/7]\) | \(18/(7\sigma+3)\) |
| \((5/7,11/15]\) | \(9/4\) |
| \((11/15,3/4]\) | \(15/(3+5\sigma)\) |
| \((3/4,1]\) | \(3/(2\sigma)\) |

At \(\sigma=3/4\), Guth–Maynard gives \(5/9+\varepsilon\) compared with Ingham's \(3/5\) exponent. Lewko's right limiting exponent there is \(1/2\). Its sharp uniformity requires a fixed distance from \(3/4\) on the right. Lewko's separate global coefficient is \(39/17\), improving \(30/13\) by \(3/221\). `ActualLewkoDensity` converts the two-sided external count into a bound for positive ordinates. The \(T^\varepsilon\) estimates retain their loss. [Guth and Maynard, Annals, Theorem 1.2](https://annals.math.princeton.edu/2026/203-2/p06) · [Lewko, checked statements and pins](https://palomar-registry.org/entry?id=PALOMAR-2026-10-11-000010&version=1)

The Dirichlet zero-free half-plane has boundary \(B_*\) in the open interval
\[
(0.8733458561067185768011847960650723567704,\quad
 0.8733458561067185768011847960650723567705).
\]
`ActualQuasiRiemannSupport` proves the root isolation, specializes the external Dirichlet nonvanishing source to zeta, and empties every strict tail at displacement \(B_*-1/2\) or greater. Zeros exactly at \(B_*\) are allowed by this statement. The externally checked proof uses a different Lean toolchain. [Bebel, upstream submission 143](https://github.com/GTimG/QuasiRiemannTracker/pull/143) · [Local support theorem](Analysis/ActualQuasiRiemannSupport.lean)

## Improvements on the same statistic

| Statistic | Comparison | New result |
| --- | --- | --- |
| Horizontal moments and signed Taylor series | Earlier repository finite bounds and geometric bandwidth | With fixed Selberg slope \(a\), the factorial moment envelope has coefficient \(2Ck!\). For \(r=|u|/(aL)<1\), the signed Taylor remainder is bounded by \(2CLr^{2J+2}/(1-r^2)\). Includes both reflected sides. |
| Moving prime-torus Fourier remainder | Earlier internal sufficient budget \(W(T)(\log L)^2/L\to0\) | With the literature Selberg input the sufficient budget is \(W(T)=o(L)\) for the same squared-height Wiener mass. The tests and prime sets may move with height. |
| Sparse deletion in a complex pair sum | Lamzouri Proposition 3.2 gives exponent \((1-7\theta/4)/8\) | For \(0<\theta<4/7\), every fixed \(0<\kappa<1-7\theta/4\) works. The finite incidence estimate includes multiplicities and coincident ordinates. Inputs are Selberg density, local Fujii row moments and tested-kernel domination. |
| Centered actual-ordinate pair statistic | Former §7 threshold optimization yielded \(\kappa_{\rm old}/(1+\kappa_{\rm old})\) | Paper deduction \(O_g(\epsilon_T^\kappa+L^{-1/2})\), \(\epsilon_T=\mathbb E X^2\). Power sparsity \(\ll L^{-p}\) reaches \(4/7\le\theta<2/3\) for \(p>6\theta/(2-3\theta)\). |
| One-sided mean \(\sum_\rho(\beta-1/2)_+/T\) | Conrey, Bulletin AMS, Theorem 3 gives \(\limsup\le0.0806\) | The shifted-moment deduction gives \(\le0.05323037841\) with the one-third cap and \(\le0.05258782450\) with the external ten-point distinct-ordinate cap. The derived profile and numeric enclosures are recorded separately. |
| Scaled second horizontal moment | Uncapped shifted profile gives \(49\pi^2/264\) | The capped profile yields \(\limsup\mathbb E X^2<1.586614445\) with one-third, or \(<1.577263570\) with the ten-point source. Sharp within the stated abstract moment and mass constraints. |

[Sparse pair proof and exponent table](RH/SparsePairDensityBounds20261119.md) · [Updated §7](RH/MellinModularQuadraticAttempt20261118.md) · [Stop-loss proof and enclosures](RH/OptimizedHorizontalMoments20261119.md) · [Conrey, Bulletin AMS, Theorem 3](https://doi.org/10.1090/S0273-0979-1989-15704-2) · [Conrey, shifted moment, §5](https://maths.dur.ac.uk/users/herbert.gangl/morethan2_5.PDF) · [Lamzouri, §3](https://arxiv.org/html/2611.14486v1#S3)

## Montgomery and RH

`defectIntegral_reflected_gram` includes every ordered pair in the signed Gram identity. The quartic Schur inequality uses the proved Cauchy row estimate. `exists_transition_horizontalDefect_loglog_bound` gives the unconditional horizontal defect \(O_A((\log L)^8/L^3)\) at \(u=(\log L+c)/2,\ |c|\le A\). This suffices for an \(o_A(1/L)\) raw-to-complex difference when the complex form factor is bounded. The second-order proof note specifies the prime and archimedean terms and every additional analytic input. [Gram and Schur](Analysis/MontgomeryReflectedDefect.lean) · [Actual defect](Analysis/MontgomeryTransitionHorizontalDefect.lean) · [Second-order proof](RH/MontgomerySecondOrderTransition20261119.md) · [Corrected BGSTB §3](https://arxiv.org/html/2501.14545v3#S3.E4)

Gerhold's zero-free-to-Mertens implication gives \(M(x)=O_s(x^s)\) for every \(s>B_*\). For the physical sequence \(d_n=\mathtt{qSequence\ displacement}(n)\), `riemannHypothesis_of_continuumContact_and_prefix` gives RH if
\[
\sum_{n\le k}|d_n|=O(k^{1+\gamma}),\qquad
\gamma<(1-B_*)/(2-B_*)\approx0.1124161701.
\]
The previous \(1+1/9\) exponent lies inside this interval. In particular, `riemannHypothesis_of_continuumContact_and_ninth_moment` reduces RH to \(\sum_{n\ge1}|d_n|^9/n^2<\infty\) with its named external sources. Both this physical moment and the prefix estimate are **open**. They concern physical sites, whereas \(X\) is measured at zeta zeros. [Lean RH reductions](RH/ZeroFreeMertensDisplacement.lean) · [Gerhold, zero-free implication](https://arxiv.org/abs/0905.2070)

The ordinary-ordinate PCC still requires the second-order pair asymptotic. The improved horizontal hypothesis supplies a restricted-support transfer. Above support one the signed prime-correlation input remains open. The small-gap proportion and positive finite moment caps bound different observables.

## Cofinal microscopic mean and the degree-285 finite replay

Write $m_T=\mathbb E_T[\log T\,|\beta-1/2|]$. RH holds exactly when $T m_T$ takes arbitrarily small values at cofinal heights. In particular a cofinal bound $m_T\le C T^{-1-\delta}$ with fixed $C$ and $\delta>0$ implies RH. The equivalence follows from the exact reflection and count normalizations, and uses no density estimate. The remaining analytic requirement is to prove cofinal smallness for the actual zeros. [`riemannHypothesis_iff_cofinalSmallMicroscopicMean` and `riemannHypothesis_of_cofinal_microscopic_power`](Analysis/ActualCofinalOneSidedMassRH.lean)

For the degree-285 certificate at $\lambda=0.784782678$, Lean now proves the Fourier normalization is strictly positive directly from the shared Laguerre weights. Signed base expansion gives a second exact implementation of Bernstein subdivision. A proposed shifted row can also be validated by a single integer evaluation on each side, with proved coefficient bounds that make the comparison injective. [`unit_positive`](Analysis/LamzouriGap285Normalization.lean) · [`checkPackedRay_eq` and `certifyBernsteinRight_sound`](Analysis/GapKernelPackedBernstein.lean)

[Focused Bazel verification of the RH criterion, positive normalization and signed-digit certificates](https://app.buildbuddy.io/invocation/8a08e533-16f9-4b1a-aec6-191587b0afad) · [Full verification of the preceding real-order and fixed-strip checkpoint](https://app.buildbuddy.io/invocation/271582e1-ced9-4dd3-99e1-3078f7a45a9c)

## Exact certificates for both degree-285 sign rays

For the explicit degree-285 monomial vectors generated from the Laguerre weights, Lean proves positivity of the physical polynomial at every $x\ge0$ and negativity of its Fourier polynomial at every $y\ge78/25$. Previously the numerical sign evidence for this degree came from the external Bernstein replay. For each sign the two stored integer polynomials $A,B$ have degree 142. Writing $F(x)=P(x)$ on the physical side and $F(x)=-25^{286}Q(x+78/25)$ on the Fourier side, every one of the 286 coefficients of
\[
2^{480}F(x)-A(x)^2-xB(x)^2
\]
is strictly positive in the independent integer calculation. The kernel checks a positive constant coefficient and nonnegative remaining coefficients, which suffice on the entire unbounded ray. A checked signed-radix comparison identifies the shifted Fourier row with the stated affine transform. Approximate roots were used to find the two square polynomials. Only the displayed integer identities and signs enter the proof. [Physical sign](Analysis/LamzouriGap285PhysicalSignCheck.lean) · [Fourier sign](Analysis/LamzouriGap285FourierRay.lean) · [Integer square criterion](Analysis/GapKernelSumOfSquares.lean)

The same monomial vectors satisfy the positive Fourier normalization, nonnegative primitive value at the rational radius, and strict objective inequality with the specified Taylor sum. The remaining Fourier transport identity is verified below. [`objective_data_checks`](Analysis/LamzouriGap285ObjectiveData.lean) · [`smallGapProportion_of_degree285_transport`](Analysis/LamzouriGap285FiniteSigns.lean)

[Focused verification and axiom audit for the five finite conditions](https://app.buildbuddy.io/invocation/b2ec85b0-1f66-4fbf-b708-1cf51b771107) · [Full verification of the preceding cofinal-mean checkpoint](https://app.buildbuddy.io/invocation/a426a0d3-c9f0-4743-a79a-dccb29009e0b)

Lean now identifies all 286 entries in each stored monomial vector with the coefficients defined from the original 286 Laguerre weights. A balanced lookup supplies factorials, odd products and weights. Lean checks each table entry against its defining formula, evaluates the two signed expansions in eight blocks, and assembles the lists in increasing degree order. Rewriting by these equalities transfers both sign rays and the rational objective checks to the original polynomials in `Replay`. [`physicalData_eq` and `frequencyData_eq`](Analysis/LamzouriGap285SourceVerification.lean) · [All 572 coefficient checks](https://app.buildbuddy.io/invocation/76c661ba-e9f4-4b0a-9038-52dd8705656a) · [Full verification of the five rational and sign conditions](https://app.buildbuddy.io/invocation/63678e4c-f2b9-4083-93a5-aaadc9d78206) · [Lean axiom audit and transfer of both signs](<https://app.buildbuddy.io/invocation/333ac728-ada6-4451-9d88-8cdb1dfc70ea>)

## Positive proportion of gaps at 0.784782678

The preceding degree-83 kernel certificate gave $D(0.784981)>0$. The degree-285 witness gives $D(0.784782678)>0$ under the same named compact-deletion theorem of Lamzouri. The formula counts adjacent gaps with zero occurrences repeated according to analytic multiplicity. Both sign rays, the three rational conditions and the Fourier transport equality are checked inside Lean. A single-pass form of the integer recurrence is proved equal to the original operator. Eight contiguous coefficient blocks verify all 286 steps, and the resulting row is checked against $2^{286}Q$. [`smallGapProportion_degree285`](Analysis/LamzouriGap285Certified.lean) · [Fourier identity](Analysis/LamzouriGap285TraceCheck.lean) · [Single-pass recurrence and trace soundness](Analysis/GapKernelStreamingFourier.lean) · [Lamzouri, Theorem 1.1 and Remark 1.2](https://arxiv.org/html/2611.14486v1)

The exported instance `verifiedReplay` supplies the six original fields using the coefficient equalities for both lists. Consequently the original `smallGapProportion_certified285` can be called with only `LamzouriCompactDeletion2026`. The kernel independently checks the proposed integers and retains no numerical hypothesis. [Original six-field instance](Analysis/LamzouriGap285OriginalReplay.lean) · [Focused instance and axiom audit](https://app.buildbuddy.io/invocation/6ea9e35a-c1a2-4d60-85ad-34a6c3e40578) · [Full verification of both coefficient expansions](https://app.buildbuddy.io/invocation/9d834765-a2ed-410d-a4cd-4b1490cb7b2c) · [All 286 Fourier recurrence steps](https://app.buildbuddy.io/invocation/07cbb75c-05fe-4022-afa9-9f34ca439e16)

## Gap proportions and literature comparisons

These bounds count every positive zero occurrence with analytic multiplicity. Small-gap statements concern one adjacent gap. Isolation statements require both adjacent gaps to exceed the threshold. The fixed-gap note gives the passage between common-height and local-ordinate normalization.

| Observable | Prior bound found | Repository deduction |
| --- | --- | --- |
| A positive proportion of adjacent gaps at most \(2\pi\lambda/L\), unconditionally | Lamzouri proves \(\lambda=0.7892\) and reports every \(\lambda>0.7864\) | Lean checks the finite Fourier certificates at \(0.784981\) (degree 83) and \(0.784782678\) (degree 285). The external exact program also gives \(0.784905297\) (degree 105). Each uses Lamzouri's compact-deletion theorem. |
| Both neighbors farther than \(2\pi c/L\) for \(0<c\le10^{-5}\) | Kim gives a proportion at least \(0.672468\) | At least \(0.673637381\) with the externally checked ten-point window and the new grouped trace argument. |
| Both neighbors farther at \(c=1/6\) | Lamzouri gives \(0.50875\), using local-height normalization | At least \(0.64455851\), including that normalization. |
| Consecutive moderate gaps at \(c=1/4\) | Angón–Ross–Tang–Zhao give \(0.3450014,0.1812517,0.0175021\) for runs of two, three and four | At least \(0.60369938,0.20739876,0.20739876\) respectively. The finite shifted-intersection proof uses the same starting-index normalization. |

The spectral argument for the new isolation bounds is given on paper. The external finite interval certificates bound the window integrals. Local Lean checks the stated analytic implications, the finite reflection identity and the transfer to consecutive gaps. The references give like-for-like benchmarks from the literature search. The table makes no priority claim beyond those comparisons. [Fixed-gap proof and the certified rows](RH/FixedGapIsolation20261119.md) · [Fourier proof](RH/SmallGapFourierCertificate.md) · [Executable numerical certificates](RH/BoundCertificateReplays20261119.md) · [Kim](https://hexagonmath.org/pdf/2611.00318v1) · [Angón, Ross, Tang and Zhao](https://arxiv.org/abs/2610.22927) · [Lamzouri](https://arxiv.org/abs/2611.14486)

## Exact countable RH test

Put \(a_n(q)=(\xi'/\xi)^{(n)}(1+iq)/n!\), where \(q\) runs through rational ordinates, and \(B=\sup_\rho\Re\rho\). The Lean-checked identity \(\sup_q\limsup_n |a_n(q)|^{1/n}=1/(1-B)\) expresses the horizontal boundary through pointwise Taylor growth. An open radius-one-half disk about every rational center is exactly equivalent to RH. The current continuum-contact input gives a normalized coefficient-growth ceiling of \(3.947758713\); RH corresponds to ceiling one. Ford–Zaharescu Theorem 4 gives a separate RH-equivalent limit in derivative order for smoothed Dirichlet-zero differences. The published proof also rules out pointwise subexponential growth when RH fails. [Disk criterion and Cauchy–Hadamard proof](RH/RationalTaylorRadiusRH20261119.md) · [Ford–Zaharescu](https://doi.org/10.1112/S0010437X14007659)

## Sharp constants and the mesoscopic transition

The broad BGSTB estimate (3.5) plus the internally proved fourth-moment defect gives the leading shrinking-frequency raw form factor with error \(O_A(L^{-1/2})\). The public consumer no longer has a separate Selberg premise. The same inputs give raw-minus-complex error \(o_A(1/L)\). With the centered positive-cutoff and prime-side estimates, the raw signed correction at \(u=(\log L+c)/2\) is \(-2(1+\log(2\pi))e^{-c}/L\). [Source interfaces](Analysis/ZeroDensityLiterature.lean) · [Centered calculation](Analysis/MontgomeryCenteredTransition.lean)

At \(u=\alpha L\to\infty\), \(u^3/L^2\to0\), the reconstructed raw form factor satisfies \(F_{\rm raw}/(L e^{-2u}+u/L)\to1\) with the stated quartic, positive-cutoff and prime mean-square inputs. At \(u=\log L-\tfrac12\log\log L+c\), its ratio to \(\alpha\) tends to \(1+e^{-2c}\). At still larger \(u\) in this range with \(L^2e^{-2u}/u\to0\), the ratio tends to one. [Mesoscopic calculation and precise provider types](RH/MontgomeryMesoscopicWindow20261119.md) · [Crossover declaration](Analysis/MontgomeryMesoscopicCrossover.lean)

For the two-neighbor isolation calculation using only the pair energy, a variational identity optimizes over the even test densities. This gives at least \(0.30187816\) at half mean spacing and \(0.05214801\) at three-fifths. The largest cutoff producing a strictly positive lower bound by this particular pair-energy inequality lies in \([0.61701890,0.61701891]\). [Extremizer, finite grouping and interval enclosure](RH/VariationalIsolation20261119.md) · [Directed certificate programs](RH/BoundCertificateReplays20261119.md)


### Small-gap hypotheses at larger support

| Density premise | Positive-proportion gap cutoff |
| --- | ---: |
| Every fixed one-logarithm slope below 8/7 (literature) | 0.784782678 |
| One-logarithm slope 4/3 (conditional) | 0.739922533 |
| One-logarithm slope 3/2 (conditional) | 0.70321 |
| One-logarithm slope 7/4 (conditional) | 0.65181 |
| One-logarithm slope 2 (conditional) | 0.603780886 |

At slope 2 the like-for-like Lamzouri benchmark is 0.6039. Beyond the unconditional positive-proportion support, the optimized deletion estimate gives quantitative counts: at a normalized adjacent gap of 0.74 the occurrence fraction times \(L^{7849}\) tends to infinity. This is an unconditional inverse-logarithmic abundance statement. At the easier cutoffs 0.74762 and 0.74301, any powers strictly above 78 and 198 suffice, respectively. [Exact parameters, Fourier witnesses and sparse transfer](RH/SmallGapFourierCertificate.md) · [Sparse deletion phase diagram](RH/SparsePairDensityBounds20261119.md)

## Distinct ordinates and growth of the Dirichlet phase frame

The image of the zero cutoff under the ordinate map counts a reflected pair only once. A finite grouping by ordinate, a published complex pair-energy estimate, the shifted Conrey input and directed finite interval certificates give lower proportions \(0.83392118\) (Montgomery–Taylor window) and \(0.83449280\) (ten-point window with its additional external interaction bound). The local theorem checks the implication from the specified finite-frame/energy source. The independent directed program verifies its numerical inputs. Fractions for distinct complex zeros, including the manuscript claim \(0.84000255\), count a different set. [Finite-ordinate derivation and consumers](RH/DistinctOrdinateGram20261119.md) · [Knausgård](https://arxiv.org/abs/2610.08965) · [November 18 manuscript, complex-distinct count](https://rstation.ai/problems/riemann_hypothesis/papers/178)

A November 18 research-platform manuscript claims at least \(0.67385611\) of all occurrences are simple and on the critical line. Taking that additional result as a premise yields the one-sided height-mean cap \(0.05256767631\) and the scaled second-moment cap \(1.576967913\). The stop-loss note gives the parameter tuple and the rational interval replay for both the ten-point and manuscript-conditioned bounds. [Conrey profile and all caps](RH/OptimizedHorizontalMoments20261119.md) · [November 18 manuscript, Theorem 1](https://rstation.ai/problems/riemann_hypothesis/papers/179)

For the signed correction after masking a fixed far strip, the harmonic bound improves the polynomial dimension exponent from \(16/45\) to every \(b<4/9\) at \(\sigma=3/4\). At fixed \(\sigma>3/4\), every \(b<1-3(1-\sigma)/(2\sigma)\) works with Lewko's source. Both apply to \(d(T)\le T^b\). [Signed harmonic operator](Analysis/ActualDensityHarmonicOperator.lean) · [Published Guth–Maynard estimate](https://annals.math.princeton.edu/2026/203-2/p06)

The optimal constant in the abstract quartic inequality for the individual reflected pair kernel is \(8/15\), compared with the earlier bound \(1536e\). The full proof gives equality at zero phase and ordinate difference, with both horizontal halfwidths equal to \(1/2\). This sharpness refers to the uniform kernel inequality, including its two boundary points. [Proof and rational extremizer](RH/MontgomeryReflectedKernelSharpConstant20261119.md)

The November 19 research-platform manuscript gives the stronger dyadic upper bound
\[
 \limsup_{T\to\infty}\frac{2\pi}{T}\sum_{T<\gamma\le2T}(\beta-1/2)_+\le 0.32133.
\]
Geometric summation gives a cumulative one-sided mean of at most \(0.32133/(2\pi)<0.05114125787\). Thus the preceding one-sided constants improve the peer-reviewed Conrey value but are above this manuscript benchmark. Combining the latter with Conrey's shifted profile and the one-third cap gives the strictly stronger conditional second and fourth moment bounds \(1.555657148\) and \(16.342166486\), and the optimized tail coefficient \(3.298233009\). The author's request for independent checks of the Gram normalization and entropy arguments remains relevant. [Manuscript 182](https://rstation.ai/problems/riemann_hypothesis/papers/182) · [Exact rational replay and derivation](RH/OptimizedHorizontalMoments20261119.md)

For each small-gap witness of Fourier support \(\theta\), a one-logarithm slope strictly above \(2\theta\) suffices. The threshold \(0.603780886\) already holds under a cofinal family of fixed slopes below 2, and \(0.73995708\) requires only a slope strictly above \(4/3-2\times10^{-8}\). [Exact rational choices](RH/SmallGapFourierCertificate.md)

With the J21 energy and interaction estimates from the newer research-platform manuscripts, the tiny-gap two-neighbor lower bound increases from \(0.673637381\) to \(0.67385114\) for \(0<c\le10^{-5}\). The finite outward-rounded calculation tests the necessary eigenvalue inequality against a Montgomery–Taylor reference density. [J21 proof, inputs and certificate](RH/J21Isolation20261119.md)

The ordinate fibre partition keeps every multiplicity and identifies the singleton contribution to \(2D(T)-N(T)\) exactly. Under microscopic first-mean collapse and the ten-point finite-frame estimate, \(D(T)/N(T)\) has lower limit at least \((1+\kappa_{10})/2=0.83681964408330198\ldots\). Combined with the finite exponential-polynomial zero count of Langer, the Dirichlet phase Gram matrix on the frequencies \(\log 1,\ldots,\log d\) in dimension \(d(T)\le T^b\) is eventually invertible whenever the distinct-ordinate lower proportion is \(\kappa\) and \(0\le b<\kappa\). The distinct-ordinate input counts heights, including repeated occurrences and reflected pairs. This criterion gives no quantitative lower eigenvalue. [Fibre decomposition](Analysis/ActualDistinctOrdinateGram.lean) · [Actual Dirichlet phase Gram theorem and scoped Langer input](Analysis/ActualLangerPhaseFrame.lean)

At fixed complex-statistic support \(\alpha\in[a,b]\subset(0,1)\) the prime diagonal with the signed cross-term estimate yields \(F_{\rm sharp}(\alpha)-\alpha=O_{a,b,\kappa}(e^{-\kappa V(T)}/\log T)\) at the closed endpoint \(\kappa=d_* a^{3/5}\), where \(d_*=[5^6/(2^2 3^4(48.0718)^3)]^{1/5}=0.212579202120942\ldots\) and \(V(T)=(\log T)^{3/5}(\log\log T)^{-1/5}\). At \(\alpha=1\) the error is \(O(\log\log T/\log T)\). The proof note specifies the estimates on \(\Lambda\), the prime diagonal, and the mean square. A raw ordinate asymptotic at the same fixed support still needs a horizontal comparison. [Complex-statistic derivation](RH/MontgomerySecondOrderTransition20261119.md) · [Garunkštis and Paliulionytė](https://web.math.pmf.unizg.hr/glasnik/vol_60/no2_03.html)

Under one fixed positive Selberg slope, the condition \(T^{-1}\sum_{0<\gamma\le T}(\beta-\tfrac12)_+\to0\) is equivalent to the vanishing of the scaled quadratic horizontal mean. Najnudel and Nikeghbali give this same small-o condition as a sufficient hypothesis for the actual logarithmic derivative on the critical line to have its Cauchy limit law. The projected-ordinate law in their paper holds unconditionally. The actual horizontal small-o estimate remains open. [One-sided mean equivalence](Analysis/ActualOneSidedHorizontalDisplacement.lean) · [Najnudel and Nikeghbali, Theorem 8.7](https://arxiv.org/abs/2609.15862)

The relative raw form-factor estimate has the explicit shape \(K/u+B u^{3/2}/L\) in its range. With the internal Ingham estimate in place of a global one-logarithm Selberg input, \(u^3(\log L)^4/L^2\to0\) still gives the combined raw asymptotic. This covers every moving power \(u=L^q\) for \(0<q<2/3\). The positive-cutoff and prime mean-square inputs are explicit in both statements. [Relative rate](Analysis/MontgomeryMesoscopicRelativeRate.lean) · [Internal Ingham consumer](Analysis/MontgomeryMesoscopicInghamSlope.lean)

For the November 19 dyadic manuscript input, the third scaled horizontal moment is at most \(4.553304064\) using the same optimal stop-loss comparison as the second and fourth moments. [Full rational enclosures](RH/OptimizedHorizontalMoments20261119.md)

For each positive slope \(a\), a global inclusive density estimate with any fixed logarithmic power implies \(|\beta-1/2|\le1/a\) for every nontrivial zero. A cofinal family of such slopes is **equivalent to RH**, even if the logarithmic power and constants depend on the slope. The converse uses the actual total zero count at the inclusive threshold. Improving the external contact boundary by this argument alone requires \(a>1/(B_*-1/2)=2.678481583880647807110182550204092347620\ldots\). [Cofinal density theorem](Analysis/ActualSelbergSlopeRH.lean) · [Reciprocal threshold enclosure](Analysis/ActualSelbergSlopeContact.lean)

On the actual ordinate Dirichlet phase Gram matrix, \(\log d=o(\sqrt{\log T})\) suffices for convergence to the identity in operator norm. Eventual invertibility still follows if \(\log d\le c\sqrt{\log T}\) with \(c<\sqrt{(4/3)\operatorname{arcosh}2}=1.32512032003\ldots\). The theorem uses the internal Ingham route. The larger polynomial dimension range from Langer gives invertibility without a norm estimate. Bui–Florea–Milinovich Theorem 3.1 gives a polynomial-range quantitative estimate under RH. [Square-root range](Analysis/ActualSquareRootPhaseGram.lean) · [Bui et al., Theorem 3.1](https://doi.org/10.1112/blms.13092)

The interpolation exponent above is sharp for the two numerical input envelopes: for \(8/7\le b<4/3\), equality \(e=(21/2)(b-8/7)\) generally fails. A family of two-point probability laws simultaneously realizes the \(4/3\) envelope and obeys each strict \(a<8/7\) bound. At the intermediate edge its ratio to the predicted bound grows exponentially in the family parameter. This gives an explicit obstruction to optimizing the actual-zero endpoint with these bounds alone. [Extremal profiles](RH/SelbergDensityEndpoint20261119.md)

The transition-scale Bellotti coefficient also holds at its closed endpoint \(2^{-3/5}d_*=0.1402499694321865\ldots\). The additional saving comes from the log-log factor in \(V(e^{c/2}\sqrt L)\) and absorbs the logarithmic loss from partial summation. [Closed coefficient analysis](RH/MontgomerySecondOrderTransition20261119.md) · [Bellotti, Corollary 1.6](https://arxiv.org/abs/2508.02041)

For \(M_k(v)=\sum_{0<\gamma\le T}|\beta-1/2|^k e^{v|\beta-1/2|}\), exact integration of the minimum of the off-line count cap and its exponential majorant gives compensated bounds at every order. The all-order provider includes the positive-tilt fourth moment used in the raw Gram transfer. The comparison note details the earlier factorial/Taylor constants, the critical tilt and the respective analytic premises. [All-order comparison](RH/ZeroMomentSlopeFindings20261119.md) · [Actual moments](Analysis/ActualZeroDisplacementMoments.lean)

**Existing repository bound retained.** The compensated quadratic horizontal-energy expression already integrates the pointwise minimum of the off-line mass cap and the exponential tail. At \(k=2,v=0\) the optimized all-order formula gives the same expression. A distribution with that survival function attains it under the stated abstract constraints. Replacing it by the standalone exponential literature majorant would lose this sharpness. [Compensated moments and comparison](RH/ZeroMomentSlopeFindings20261119.md)

## Small gaps below the positive-proportion threshold

Write \(d_T(\lambda)\) for the small-gap count through \(T\) divided by the number of zero occurrences. Using the curved fixed-strip density envelopes in the sparse deletion estimate gives \(T^p d_T(\lambda)\to\infty\) in the following cases. A finite partition in the real part retains the strict exponent margin before the height limit.

| Gap cutoff \(\lambda\) | Power \(p\) | Density input |
| --- | ---: | --- |
| 0.70 | 0.273 | Curved Ingham |
| 0.65 | 0.4305 | Guth–Maynard |
| 0.603780886 | 9/16 | Peer-reviewed Bourgain–Huxley bounds as cataloged by Tao–Trudgian–Yang |
| 0.603780886 | 1/2 | Lewko's independently registered Lean proof beyond \(\sigma=3/4\) |

Thus gaps below \(0.603780886\) have counts growing faster than \(T^{7/16}\log T\) on the peer-reviewed density inputs, or faster than \(\sqrt T\log T\) using the Lewko input. A positive limiting *fraction* at that gap uses the substantially stronger density premise in the earlier table. At gap \(0.74\) the degree-149 witness lowers the unconditional **logarithmic** abundance exponent from 15000 to 14176, and the degree-251 witness lowers it further to 7849. These are paper deductions with exact finite objectives and scalars. [Proof with the fixed-strip ranges](RH/SparsePairDensityBounds20261119.md) · [Numerical objectives](RH/SmallGapFourierCertificate.md) · [Tao–Trudgian–Yang](https://doi.org/10.1090/mcom/4138)

Montgomery and Vaughan's author-posted *Volume III*, Theorem 30.1, already gives the signed lower-order correction and the fixed-support/endpoint errors under RH, in the normalization \(T\log(T/(2\pi))/(2\pi)\). Equations (30.10) and (30.12) retain both the prime diagonal and the reflected Dirichlet square before taking their coarser error. These parts have published or publicly documented precedents. The repository comparisons track the unconditional complex estimate, the raw transfer at shrinking frequency, and the exact residual after retaining the prime diagonal. [Montgomery–Vaughan, chapter 30](https://personal.science.psu.edu/rcv4/Vol3/Vol3.pdf) · [Normalization and prior results](RH/MontgomerySecondOrderTransition20261119.md)

## Verification records

| Scope | Verification |
| --- | --- |
| Initial 93-file integration, including the cofinal RH criterion, surviving-gap finite comparison, literature interface and moving raw form-factor estimates | [Full repository build at 27b221c](https://app.buildbuddy.io/invocation/fb65c660-c5b9-4f08-9b71-ee98c71a1e67) · [Commit](https://github.com/Cnoack3/RiemannResearch/commit/27b221c773fdb670f1b4d6fedb3c3b25a51bc9ea) |
| Cofinal density slopes and 39-decimal half-plane comparison, all-order tilted moment provider | [Focused Bazel result](https://app.buildbuddy.io/invocation/5c1bedf7-7303-4364-98fa-08b29021ee05) |
| Critical Ingham tilt, explicit linear tilt and the minimum inclusive logarithmic power | [Focused Bazel result](https://app.buildbuddy.io/invocation/c3aed39f-7888-4947-a520-b10c29cfb3e8) |
| Finite degree-83 polynomial signs | [Kernel certificate](https://app.buildbuddy.io/invocation/2e7cf170-c5e5-4b9d-b904-e6d08b490c4e) |
| Actual distinct-ordinate fibre identity, with the finite interaction input for the resulting numerical lower proportions | [Kernel certificate](https://app.buildbuddy.io/invocation/55fa807f-4d21-443d-80c8-f40184df03e3) |
| Langer phase rank and unconditional square-root support | [Finite exponential zero-count consumer](https://app.buildbuddy.io/invocation/b1c0f8a7-71be-4ff6-bf4a-39c2b32bfc4b) · [Operator-norm check](https://app.buildbuddy.io/invocation/0cc4477a-acc3-4442-adac-d373ce8d335b) |
| All six Fourier witnesses and their fourteen extra scalar tests, optimal stop-loss values, and isolation certificates | [Replay programs and their arithmetic](RH/BoundCertificateReplays20261119.md) |

An external source assumption in a checked declaration remains an explicit parameter. A paper deduction or a Python interval certificate has its own designation in the corresponding note.

The finite Dirichlet phase correction also has a sharp model constant. For a displacement cutoff \(0<a<1/2\), the largest real root of
\[
z^3-\frac{3z}{(1-4a^2)(1-a^2)}-\frac{1}{(1-4a^2)(1-a^2)^2}=0
\]
gives the optimal coefficient for its one-occurrence norm bound in dimension \(d\). The proof uses a compression to normalized step functions and a limiting cubic for the three-dimensional range. This assertion concerns the comparison kernel. [Finite constants, proof and conditional RH benchmark](RH/ActualPhaseFrames20261119.md)

For the actual Taylor coefficients of \(\xi'/\xi\), Lean proves the pointwise radius is the infimum of the distances to all nontrivial zeros, that the global reciprocal boundary is at least 2, and that equality to 2 is **exactly RH**. The companion paper transfers the same threshold to the signed, absolutely convergent Chebyshev-error moments
\[
 I_n(q)=\frac1{n!}\int_0^\infty u^n[e^{-u}\psi(e^u)-1]e^{-iqu}\,du,\qquad q\in\mathbb Q.
\]
The open target is \(\limsup_n |I_n(q)|^{1/n}\le2\) for each rational \(q\). The conditional external contact boundary gives an upper bound of \(7.895517425\) on the unnormalized Taylor growth. [Lean coefficient proof](RH/XiTaylorCoefficientRadius.lean) · [Bazel receipt](https://app.buildbuddy.io/invocation/bce61214-154a-4c49-9962-889e50f86fa1) · [Signed prime-error transfer](RH/RationalTaylorRadiusRH20261119.md)

The sharpness model for the Selberg interpolation edge and the Montgomery–Vaughan normalization conversion are individually kernel-checked. [Profiles](Analysis/SelbergDensityProfileSharpness.lean) · [Draft's RH-conditional source and conversion](Analysis/MontgomeryVaughanDraftComparison.lean) · [Joint Bazel receipt](https://app.buildbuddy.io/invocation/2cbe7913-ba3c-418a-94b4-77bd1390ffe0)

The complete local reflected-kernel proof establishes that the uniform quartic inequality holds **if and only if** its constant is at least \(8/15\). The production horizontal-defect Schur estimate now uses \(8/15\) times its row constant. The displacement-specific majorant is attained at zero frequency and ordinate difference for every fixed pair of halfwidths. [Sharp kernel](Analysis/MontgomeryReflectedKernelOptimal.lean) · [Actual Schur consumer](Analysis/MontgomeryReflectedDefect.lean) · [Joint kernel check](https://app.buildbuddy.io/invocation/9271e9ae-d0af-4caf-92be-84adc52a9a32)

The manuscript dyadic input alone now implies the actual cumulative one-sided bound \(0.32133/(2\pi)\), and the mean scaled mark bound \(0.64266\). The finite-copy count supplies the initial compact-height majorant in the dyadic iteration. The named manuscript proposition is the only external mean premise. [Dyadic transfer](Analysis/DyadicHorizontalMean.lean) · [Normalized mark](Analysis/DyadicMicroscopicMean.lean) · [Combined verification with uniform raw crossover](https://app.buildbuddy.io/invocation/450a6a33-78ee-436a-978e-ccb49ac33c4e)

For the reflected Gram matrix in growing dimension, the componentwise Bui–Florea–Milinovich estimate gives an eventual operator error at most \(b+\varepsilon\) at \(d\le T^b\) for \(b<1\), and convergence to zero when \(d\log d=o(T)\). Under RH the ordinary Gram form is consequently bounded below by \((1-b-\varepsilon)\|v\|^2\). Convergence of the least eigenvalue to \(1-b\) is derived in the accompanying paper comparison. [Lean deduction](Analysis/ActualBuiFloreaMilinovichFrame.lean) · [Growing correction](Analysis/ActualGrowingPhaseGram.lean) · [Focused Bazel verification](https://app.buildbuddy.io/invocation/4825380a-ed38-472e-aaa7-4b98563a2511)

`smallGapProportion_certified83` proves a positive lower proportion of actual adjacent zero gaps at normalized cutoff \(0.784981\). The sole external input is Lamzouri's compact deletion estimate. The polynomial signs, cosine transform identity, strict objective, smooth cutoff and deduction for actual zero occurrences are all checked in Lean. [Final theorem](Analysis/LamzouriActualGap83.lean) · [Full focused certificate](https://app.buildbuddy.io/invocation/5e35f79a-2825-4475-abc3-bfe156c67e10)

At the unit-slope crossover `raw_unit_slope_crossover_log_correction` gives the next-order coefficient \(e^{-2c}/2\) after rescaling by \(\log\log T/\log\log\log T\). The precise centering, source hypotheses and normalization are in the declaration. [Crossover rate](Analysis/MontgomeryMesoscopicCrossoverRate.lean) · [Bazel verification](https://app.buildbuddy.io/invocation/a0a0584d-2d5f-471b-8707-5db459db4918)

Each positive displacement radius has a sharp corner bound. Its affine refinement has prefactor \(3/8+(19/60)(a^2+b^2)\), with the slope \(19/60\) necessary at that intercept. [Radius and affine proof](Analysis/MontgomeryReflectedKernelAffine.lean) · [Kernel verification](https://app.buildbuddy.io/invocation/e02a2003-d9a9-484c-a442-fc0f9e27e248)

The uniform band coefficient at \(|a|,|b|\le r\le1/2\) is \(3/[2(4-r^2)(1-r^2)]\). A separate symbolic calculation reproduces \(3/8\), \(8/15\), and \(19/60\) from that expression. The Lean proof above establishes the inequality and sharpness, including all real values of the ordinate difference and frequency.

`smallGapProportion_certified285` gives the stronger threshold \(0.784782678\) from Lamzouri's scoped compact deletion estimate and six finite `Replay` statements about the displayed integer polynomials. A separate exact rational program checks all six statements, including the 572 coefficients, both signed polynomial rays and the 32-term exponential bound. The certified objective is in \([1.000000000452054486,1.000000000452054487]\). [Lean implication](Analysis/LamzouriActualGap285.lean) · [Bazel receipt](https://app.buildbuddy.io/invocation/58274281-12ed-450b-93bb-21910ebdbe17) · [Exact external replay](RH/BoundCertificateReplays20261119.md)

The normalized finite Frobenius-square limit for one displacement is \(6a^4/[(1-4a^2)(1-a^2)]\). It yields a uniform bound over smaller displacements and, on a sufficiently narrow strip, any coefficient exceeding \(\sqrt6\). [Finite Lean asymptotic](Analysis/FiniteCoshFrobeniusAsymptotics.lean) · [Kernel verification](https://app.buildbuddy.io/invocation/3f197d39-db28-4b21-9f63-7451cdf285f3)

Let \(m_T=\mathbb E_T X\), \(q_T=\mathbb E_T X^2\), and \(X=|\beta-1/2|\log T\). If \(m_T\to0\), the uniform Selberg bounds imply \(q_T\le(7/8+o(1))m_T\log(1/m_T)\). The coefficient is optimal for the available uniform tails in the abstract class of distributions. The equivalent one-sided height mean \(H_T\) gives coefficient \(7\pi/2\). If \(\log(1/m_T)\gg\log\log T\) with their ratio tending to infinity, the coefficient for \(m_T\) improves to \(3/4\). At polynomially small means the paper gives the six fixed-strip coefficients and their exact source assumptions. The premise \(m_T\to0\) remains open. [Proof, extremizers and rate comparisons](RH/SparseHorizontalMomentModulus20261119.md)

For the Bui–Florea–Milinovich Gram bound, the absolute upper-triangle arithmetic estimate with its natural weights implies the reflected quadratic estimate. The factor of two comes from Hermitian symmetry. The earlier frame conclusions now use that primitive scalar source directly. [Lean arithmetic adapter](Analysis/ActualBuiUpperTriangle.lean) · [Bazel verification](https://app.buildbuddy.io/invocation/d30165e1-0567-4864-b96a-a7ee26e34368)

For arbitrary finite nonnegative weights and marks, Lean proves the unnormalized and normalized size-biased Jensen inequality. With mean \(m>0\), second moment \(q\), and tilted first moment bounded by \(K\), it gives \(q\le(m/a)\log(K/m)\) for \(a>0\). [Finite lemma and log inversion](Analysis/FiniteSizeBiasedExponential.lean) · [Lean verification](https://app.buildbuddy.io/invocation/19bfe9a3-b4b5-4a2b-824e-09383d8c2383)

The finite rational Schur certificate gives \(\|C_d(a)\|\le1.87938524158(d+1)a^2\) for all sufficiently large \(d\) and all \(|a|\le10^{-7}\), with a matching rational Rayleigh comparison above \(1.87938524157\). These bounds on the finite model are kernel-checked. [Finite Schur and Rayleigh comparison](Analysis/FiniteRationalCoshSchur.lean) · [Weighted Schur inequality](Analysis/FiniteWeightedSchurBound.lean) · [Bazel verification](https://app.buildbuddy.io/invocation/ecae4ddc-2e55-48d1-a1a3-05ac4715a060)

The actual-copy height-normalized estimate supplies the input to size-biased Jensen. With \(0<a<b\), the existing Selberg tilt estimate supplies \(K=2C_b b/(b-a)^2\) for the height-normalized sum. [Actual-zero specialization](Analysis/ActualSizeBiasedDisplacement.lean) · [Lean verification](https://app.buildbuddy.io/invocation/5800feb3-754b-4781-bbf7-dc10b1ec33c9)

The actual normalized difference of the reflected and ordinary Gram matrices now has the verified rational Schur correction on the central strip and the observed, multiplicity-weighted harmonic contribution outside it. [Actual Schur estimate](Analysis/ActualSchurHorizontalCorrection.lean) · [Bazel verification](https://app.buildbuddy.io/invocation/8d315a58-23ea-4034-815b-7eef9350099f)

The finite size-biased lemma now gives the eventual ratio bound for every \(c>7/8\) when the mean tends to zero and the subcritical tilted moments are bounded, with a separate constant for each tilt. [Lean endpoint deduction](Analysis/FiniteSizeBiasedExponential.lean) · [Bazel verification](https://app.buildbuddy.io/invocation/ac754e8e-53eb-445f-8691-5b48f403a3d5)

The integrated sharp reflected-kernel, actual small-gap and Taylor-radius declarations passed the full repository target together. [Published checkpoint](https://github.com/Cnoack3/RiemannResearch/commit/ecbc16de526600da54d895c7491eacb1f4d1a77e) · [Repository Bazel verification](https://app.buildbuddy.io/invocation/00b44dd7-cf07-4302-ad23-1a9fb9cb57a6)

Lean proves RH is equivalent to the following total-mass test with no external analytic estimate. For every \(\varepsilon>0\) and every baseline height \(B\), some \(T\ge B\) has \(T H_T<\varepsilon\). A fixed zero to the right contributes its displacement at every later height, and reflection and conjugation cover the other zeros. [Cofinal total-mass equivalence](Analysis/ActualCofinalOneSidedMassRH.lean) · [Bazel check and axiom inspection](https://app.buildbuddy.io/invocation/87225d2e-4598-474b-b958-ad7d0a816cab)

The complete actual-zero consumer now directly discharges the tilted moment from `ConreyBaluyotDensityHypothesis`. For every fixed \(c>7/8\), the actual second-to-first moment ratio is eventually at most \(c\) if \(m_T\to0\) and \(m_T>0\) eventually. Zero mean gives zero second moment directly. [Actual Selberg-to-PCC rate](Analysis/ActualSizeBiasedDisplacement.lean) · [Full focused verification](https://app.buildbuddy.io/invocation/45da235c-31b5-4908-b9d2-a6b3defc8ea9)

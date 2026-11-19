# Zero-density, Montgomery pair-correlation and RH bounds

November 19, 2026. The starting revision is `d85004e85625dcf1811e6a66720dae4a50bc645e`. Write \(L=\log T\), \(X=L|\beta-\tfrac12|\), and count each occurrence with \(0<\gamma\le T\), with analytic multiplicity. The form-factor calculations use their stated \(TL/(2\pi)\) normalization. Physical displacement in the RH criterion is indexed by positive integers.

## The Selberg parameter

| Result | Bound and scope |
| --- | --- |
| Selberg, Jutila, Conrey–Baluyot | Respectively \(a=1/4\), every fixed \(0<a<1\), and every fixed \(0<a<8/7\) in \(N(\sigma,T)\ll_a TL e^{-aL(\sigma-1/2)}\). The mollifier exponent is \(a/2\). `ZeroDensityLiterature.ConreyBaluyot2017` records the strict source count. `conreyBaluyot` proves the inclusive conversion. |
| Gabriel–Littlewood estimate | With \(q=3(1-\sigma)/(2-\sigma)\), the repository supplies \(N(\sigma,T)\ll\min(TL,T^qL^{2+q})\) uniformly at \(T\ge2\). `ingham_tangent_density_log_loss` implies the \(4/3\) slope with \(L^3\). |
| Endpoint interpolation | `endpoint_log_loss` gives \(TL^{1+\varepsilon}e^{-(8/7)L(\sigma-1/2)}\) for every \(\varepsilon>0\). `interpolated_profile` gives \(8/7<b<4/3\) with any surplus log power \(e>(21/2)(b-8/7)\). Constants can depend on the loss. |
| Clean \(8/7\) endpoint | `endpoint_density_outside_window` proves it on \(L(\sigma-1/2)\ge(21/2)\log L\). `endpoint_density_iff_window` identifies the remaining growing window. The global single-logarithm endpoint is **open**. |
| Critical exponential moment | At the exact tilt \(8/7\), `critical_exponential_moment_log_loss` bounds the average of \(e^{(8/7)X}\) by \(O_\varepsilon(L^\varepsilon)\) for every positive loss. |
| Microscopic concentration | `scaled_displacement_tendsto_zero_iff` proves that any one positive integer moment of \(X\) tends to zero exactly when \(\Pr(X>\delta)\to0\) for every fixed \(\delta>0\), assuming one positive Selberg slope. The vanishing is **open**. |

[Endpoint proof and source uniformity](RH/SelbergDensityEndpoint20261119.md) · [Baluyot, Theorem 1.2.1 and §3.6](https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320) · [Tao, Trudgian and Yang, chapter 11](https://teorth.github.io/expdb/blueprint/zero-density-chapter.html) · [Chourasiya and Simonič, preprint](https://arxiv.org/abs/2507.15184)

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

## Gap proportions and literature comparisons

These bounds count every positive zero occurrence with analytic multiplicity. Small-gap statements concern one adjacent gap. Isolation statements require both adjacent gaps to exceed the threshold. The fixed-gap note gives the passage between common-height and local-ordinate normalization.

| Observable | Prior bound found | Repository deduction |
| --- | --- | --- |
| A positive proportion of adjacent gaps at most \(2\pi\lambda/L\), unconditionally | Lamzouri proves \(\lambda=0.7892\) and reports every \(\lambda>0.7864\) | Exact finite Fourier certificates give \(0.784981\) (degree 83), \(0.784905297\) (degree 105) and \(0.784782678\) (degree 285), combined with Lamzouri's compact-test theorem. |
| Both neighbors farther than \(2\pi c/L\) for \(0<c\le10^{-5}\) | Kim gives a proportion at least \(0.672468\) | At least \(0.673637381\) with the externally checked ten-point window and the new grouped trace argument. |
| Both neighbors farther at \(c=1/6\) | Lamzouri gives \(0.50875\), using local-height normalization | At least \(0.64455851\), including that normalization. |
| Consecutive moderate gaps at \(c=1/4\) | Angón–Ross–Tang–Zhao give \(0.3450014,0.1812517,0.0175021\) for runs of two, three and four | At least \(0.60369938,0.20739876,0.20739876\) respectively. The finite shifted-intersection proof uses the same starting-index normalization. |

The spectral argument for the new isolation bounds is given on paper. The external finite interval certificates bound the window integrals. Local Lean checks the stated analytic implications, the finite reflection identity and the transfer to consecutive gaps. The references give like-for-like benchmarks from the literature search. The table makes no priority claim beyond those comparisons. [Fixed-gap proof and the certified rows](RH/FixedGapIsolation20261119.md) · [Fourier proof](RH/SmallGapFourierCertificate.md) · [Executable numerical certificates](RH/BoundCertificateReplays20261119.md) · [Kim](https://hexagonmath.org/pdf/2611.00318v1) · [Angón, Ross, Tang and Zhao](https://arxiv.org/abs/2610.22927) · [Lamzouri](https://arxiv.org/abs/2611.14486)

## Exact countable RH test

Put \(a_n(q)=(\xi'/\xi)^{(n)}(1+iq)/n!\), where \(q\) runs through rational ordinates, and \(B=\sup_\rho\Re\rho\). The paper identity \(\sup_q\limsup_n |a_n(q)|^{1/n}=1/(1-B)\) expresses the horizontal boundary through pointwise Taylor growth. An open radius-one-half disk about every rational center is exactly equivalent to RH. The current continuum-contact input gives a normalized coefficient-growth ceiling of \(3.947758713\); RH corresponds to ceiling one. Ford–Zaharescu Theorem 4 gives a separate RH-equivalent limit in derivative order for smoothed Dirichlet-zero differences. The published proof also rules out pointwise subexponential growth when RH fails. [Disk criterion and Cauchy–Hadamard proof](RH/RationalTaylorRadiusRH20261119.md) · [Ford–Zaharescu](https://doi.org/10.1112/S0010437X14007659)

## Sharp constants and the mesoscopic transition

The broad BGSTB estimate (3.5) plus the internally proved fourth-moment defect gives the leading shrinking-frequency raw form factor with error \(O_A(L^{-1/2})\). The public consumer no longer has a separate Selberg premise. The same inputs give raw-minus-complex error \(o_A(1/L)\). With the centered positive-cutoff and prime-side estimates, the raw signed correction at \(u=(\log L+c)/2\) is \(-2(1+\log(2\pi))e^{-c}/L\). [Source interfaces](Analysis/ZeroDensityLiterature.lean) · [Centered calculation](Analysis/MontgomeryCenteredTransition.lean)

At \(u=\alpha L\to\infty\), \(u^3/L^2\to0\), the reconstructed raw form factor satisfies \(F_{\rm raw}/(L e^{-2u}+u/L)\to1\) with the stated quartic, positive-cutoff and prime mean-square inputs. At \(u=\log L-\tfrac12\log\log L+c\), its ratio to \(\alpha\) tends to \(1+e^{-2c}\). At still larger \(u\) in this range with \(L^2e^{-2u}/u\to0\), the ratio tends to one. [Mesoscopic calculation and precise provider types](RH/MontgomeryMesoscopicWindow20261119.md) · [Crossover declaration](Analysis/MontgomeryMesoscopicCrossover.lean)

For the two-neighbor isolation calculation using only the pair energy, a variational identity optimizes over the even test densities. This gives at least \(0.30187816\) at half mean spacing and \(0.05214801\) at three-fifths. The largest cutoff producing a strictly positive lower bound by this particular pair-energy inequality lies in \([0.61701890,0.61701891]\). [Extremizer, finite grouping and interval enclosure](RH/VariationalIsolation20261119.md) · [Directed certificate programs](RH/BoundCertificateReplays20261119.md)


### Small-gap hypotheses at larger support

| Density premise | Positive-proportion gap cutoff |
| --- | ---: |
| Every fixed one-logarithm slope below 8/7 (literature) | 0.784782678 |
| One-logarithm slope 4/3 (conditional) | 0.73995708 |
| One-logarithm slope 3/2 (conditional) | 0.70321 |
| One-logarithm slope 7/4 (conditional) | 0.65181 |
| One-logarithm slope 2 (conditional) | 0.603780886 |

At slope 2 the like-for-like Lamzouri benchmark is 0.6039. Beyond the unconditional positive-proportion support, the optimized deletion estimate gives quantitative counts: at a normalized adjacent gap of 0.74 the occurrence fraction times \(L^{15000}\) tends to infinity. This is an unconditional inverse-logarithmic abundance statement. At the easier cutoffs 0.74762 and 0.74301, any powers strictly above 78 and 198 suffice, respectively. [Exact parameters, Fourier witnesses and sparse transfer](RH/SmallGapFourierCertificate.md) · [Sparse deletion phase diagram](RH/SparsePairDensityBounds20261119.md)

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

At fixed complex-statistic support \(\alpha\in[a,b]\subset(0,1)\) the prime diagonal with the signed cross-term estimate yields \(F_{\rm sharp}(\alpha)-\alpha=O_{a,b,\kappa}(e^{-\kappa V(T)}/\log T)\) for \(\kappa<0.212579 a^{3/5}\), where \(V(T)=(\log T)^{3/5}(\log\log T)^{-1/5}\). At \(\alpha=1\) the error is \(O(\log\log T/\log T)\). The proof note specifies the estimates on \(\Lambda\), the prime diagonal, and the mean square. A raw ordinate asymptotic at the same fixed support still needs a horizontal comparison. [Complex-statistic derivation](RH/MontgomerySecondOrderTransition20261119.md) · [Garunkštis and Paliulionytė](https://web.math.pmf.unizg.hr/glasnik/vol_60/no2_03.html)

Under one fixed positive Selberg slope, the condition \(T^{-1}\sum_{0<\gamma\le T}(\beta-\tfrac12)_+\to0\) is equivalent to the vanishing of the scaled quadratic horizontal mean. Najnudel and Nikeghbali give this same small-o condition as a sufficient hypothesis for the actual logarithmic derivative on the critical line to have its Cauchy limit law. The projected-ordinate law in their paper holds unconditionally. The actual horizontal small-o estimate remains open. [One-sided mean equivalence](Analysis/ActualOneSidedHorizontalDisplacement.lean) · [Najnudel and Nikeghbali, Theorem 8.7](https://arxiv.org/abs/2609.15862)

The relative raw form-factor estimate has the explicit shape \(K/u+B u^{3/2}/L\) in its range. With the internal Ingham estimate in place of a global one-logarithm Selberg input, \(u^3(\log L)^4/L^2\to0\) still gives the combined raw asymptotic. This covers every moving power \(u=L^q\) for \(0<q<2/3\). The positive-cutoff and prime mean-square inputs are explicit in both statements. [Relative rate](Analysis/MontgomeryMesoscopicRelativeRate.lean) · [Internal Ingham consumer](Analysis/MontgomeryMesoscopicInghamSlope.lean)

For the November 19 dyadic manuscript input, the third scaled horizontal moment is at most \(4.553304064\) using the same optimal stop-loss comparison as the second and fourth moments. [Full rational enclosures](RH/OptimizedHorizontalMoments20261119.md)

For each positive slope \(a\), a global inclusive density estimate with any fixed logarithmic power implies \(|\beta-1/2|\le1/a\) for every nontrivial zero. A cofinal family of such slopes is **equivalent to RH**, even if the logarithmic power and constants depend on the slope. The converse uses the actual total zero count at the inclusive threshold. Improving the external contact boundary by this argument alone requires \(a>1/(B_*-1/2)=2.678481583880647807110182550204092347620\ldots\). [Cofinal density theorem](Analysis/ActualSelbergSlopeRH.lean) · [Reciprocal threshold enclosure](Analysis/ActualSelbergSlopeContact.lean)

On the actual ordinate Dirichlet phase Gram matrix, \(\log d=o(\sqrt{\log T})\) suffices for convergence to the identity in operator norm. Eventual invertibility still follows if \(\log d\le c\sqrt{\log T}\) with \(c<\sqrt{(4/3)\operatorname{arcosh}2}=1.32512032003\ldots\). The theorem uses the internal Ingham route. The larger polynomial dimension range from Langer gives invertibility without a norm estimate. Bui–Florea–Milinovich Theorem 3.1 gives a polynomial-range quantitative estimate under RH. [Square-root range](Analysis/ActualSquareRootPhaseGram.lean) · [Bui et al., Theorem 3.1](https://doi.org/10.1112/blms.13092)

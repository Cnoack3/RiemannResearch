# RH and Montgomery positive-gap pair correlation

Initial source audit at `cdb1db95f32f9e40123f12a1df359bae704c9d8f`. A theorem with a hypothesis is evidence for the stated implication. The final column records the input still required on the indicated route.

| Route | Declarations already in the Lean tree | Remaining mathematical input |
| --- | --- | --- |
| Centered categorical tower | [CenteredMeanRHCriteria](RH/CenteredMeanRHCriteria.lean), `categoricalMean_tfae`, `riemannHypothesis_of_stageUnit_zero` | Show the actual stage unit has zero boundary. The reverse implication from RH to that unit criterion in `stageUnit_zero_iff_riemannHypothesis` explicitly takes the Báez-Duarte approximation implication. |
| Nyman–Beurling and finite Gram systems | [CenteredMeanGramUpperBound](RH/CenteredMeanGramUpperBound.lean), [CenteredMeanDyadicGram](RH/CenteredMeanDyadicGram.lean) | Verify the required quadratic cost bound for arbitrarily small positive tolerances at cofinal cutoffs. A fixed positive tolerance cannot supply this quantifier. |
| Differences of two thresholds | [ParetoCenteredFirstSite](RH/ParetoCenteredFirstSite.lean), `riemannHypothesis_of_thresholdContrast_mem` | Put the difference of any two distinct positive normalized threshold steps in the closed legal space. Its explicit Mellin symbol is nonzero everywhere in the open right half-strip. Its exact-head approximation power lower bound detects a hypothetical right zero. |
| Screened Möbius parity test | [MobiusParityInterchange](RH/MobiusParityInterchange.lean), `screened_pairing_tendsto_zero`, `screened_tail_error_tendsto` | The actual moving tail tends to the first physical value of the screened section minus one. Vanishing of this tail would determine that coordinate. Equality of the entire screened section with the constant requires a further argument. |
| Actual zero ordinates | [MontgomeryWindowVarianceCriterion](Analysis/MontgomeryWindowVarianceCriterion.lean), `positiveGapPCC_of_rationalTriangleWidthAverages` | Prove the specified triangle width-average limit for the actual zeta-zero occurrences on every rational interval in the theorem. |
| Horizontal comparison for xi | [XiHorizontalComparison](Analysis/XiHorizontalComparison.lean), `riemannHypothesis_iff_rational_horizontal_xi_comparison` | Establish the norm inequalities for every rational triple with left abscissa in [1/2,1). Comparison to its right is already unconditional when the left endpoint is at least one. |
| Unit representatives in the original centered quotient | [MixedConductorL1Closure](RH/MixedConductorL1Closure.lean), `boundary_zero_iff_bounded_representative_heads` | Find one finite Hilbert norm bound on representatives of the actual unit boundary, with arbitrarily many initial coordinates zero. Exact heads and L¹ approximation are established. |
| Fixed-width positive-gap PCC | [MontgomeryWindowPairCorrelation](Analysis/MontgomeryWindowPairCorrelation.lean), `positiveGapPCC_iff_rationalIntegratedGapDeficit` | Show `integratedGapDeficit T q → 0` for each positive rational q as T tends to infinity. This equivalence retains every equal-ordinate collision. |
| Determinantal comparison | [ZeroDPPProjectionBridge](Analysis/ZeroDPPProjectionBridge.lean) | Verify the actual limiting projected statistic and control any omitted-pair contribution under this route's hypotheses. |

## Published Lean verification

| Commit | Declarations covered | Full aggregate build |
| --- | --- | --- |
| [c8988b5](https://github.com/Cnoack3/RiemannResearch/commit/c8988b5e085580c3ebf2e9bfd07934d46785d4b6) | Iterated projection–Möbius limits and the rational integrated PCC criterion | [BuildBuddy](https://app.buildbuddy.io/invocation/a78051c1-4fae-4b5d-934c-70ac77591f60) |
| [c6df6d2](https://github.com/Cnoack3/RiemannResearch/commit/c6df6d2947b0a3f46c5a34e0b5c09a7c6e7ede6d) | Natural-cell energy, quotient norm losses, finite Gram bounds and collision-corrected argument variance | [BuildBuddy](https://app.buildbuddy.io/invocation/a1d2560f-77b2-4338-b7b6-ef41eaabe697) |
| [190a82e](https://github.com/Cnoack3/RiemannResearch/commit/190a82ec60c50b4a252875bd331c4a7703835c2f) | Direct cumulative zero counts, macroscopic pair limits, the prime mean square, horizontal xi comparison and finite Gram cutoff order | [BuildBuddy](https://app.buildbuddy.io/invocation/350ffbd8-6e25-4271-92c0-c068b4693150) |
| [4d4b787](https://github.com/Cnoack3/RiemannResearch/commit/4d4b787b0b3f8b5347788940d51c4362b43edd6a) | Actual mesoscopic pair counts, categorical Mellin characters, legal Gram bounds, shifted zeta and reciprocal-charge limits | [BuildBuddy](https://app.buildbuddy.io/invocation/7edbb01f-4cf5-4ea2-beae-1ad4d37f0ac0) |

## Projection and Möbius cutoff order

For the complete signed pairing C(M,N) of the projection residual at M with the canonical Möbius residual at N, each fixed row tends to zero, while every column tends to the same limiting energy E. In fact C(M,N) equals the finite energy E_M whenever N ≤ M. Agreement of these two iterated limits is equivalent to membership of the constant in the closed legal space. The unconditional calculations leave E undetermined. See [CanonicalMobiusProjectionLimits](RH/CanonicalMobiusProjectionLimits.lean).

## Collision-corrected pair correlation

[MontgomeryWindowPairCorrelation](Analysis/MontgomeryWindowPairCorrelation.lean) proves `positiveGapPCC_iff_rationalIntegratedGapDeficit`. Exact subtraction of all equal-ordinate mass gives a criterion on every positive rational width. A proof that the resulting actual integrated deficits tend to zero is still needed.

## Centered quotient and finite Gram systems

- `hasSum_coordinate_quotient_norm_loss` identifies the sum of the nonnegative coordinate losses with E. By `boundary_zero_iff_coordinate_norms`, preservation of each centered coordinate norm is equivalent to vanishing of the boundary. A proof of norm preservation for the actual quotient map would close this route. [CenteredMeanQuotientNorm](RH/CenteredMeanQuotientNorm.lean)
- `finite_endpoint_remainder_norm_sq` and `finite_endpoint_root_interval` keep the full remainder for two finite projection stages. `parityAdjointPacket_first_site_coupling` ties the signed adjoint pairing to the limiting energy and first physical residual. The finite identities leave the cofinal upper estimate open. [FiniteEndpointGram](RH/FiniteEndpointGram.lean) and [ParetoParityAdjointCriterion](RH/ParetoParityAdjointCriterion.lean)

## Signed parity at two finite Gram cutoffs

The pairing of the actual upper Gram residual with the doubled lower-stage residual has an exact signed expression. Projecting the parity observation off all doubled lower-stage vectors gives a computable nonnegative determinant. Along $n=2k+1$ its limit yields a cofinal determinant test for the categorical unit and a direct sufficient condition for RH. To apply that condition one must attain every prescribed positive tolerance. [Two-stage parity Gram test](RH/DyadicParityTwoStageGram.lean)

## Uniform drift through a finite range of Gram solves

For $B\le A$, the complete drift outside cutoff $N$ is bounded both by the reciprocal packet-mass gain and by that gain multiplied by a cubic polynomial in $A$ divided by $N+1$. For any prescribed finite range of later Gram solves one can choose a physical cutoff schedule that makes its scaled drift small uniformly on that range. The RH criterion still requires a bound as the actual later solves grow beyond the proved finite ranges. [Gram cutoff estimates](RH/CenteredMeanDriftCutoffs.lean)

## Dilation tests of the screened representative

Interchange along the dyadic dilation orbit is equivalent to invariance of the screened representative under the adjoint of dilation by two. That invariance together with the triadic nonincrease condition characterizes the constant representative. Eventual interchange along the adjacent threshold differences also characterizes it. For any fixed adjacent pair a hypothetical right zero imposes a power lower bound on exact-head errors. The simultaneous dyadic and triadic conditions, and the subpower errors needed to exclude a right zero, remain open. [Dilation tests](RH/MobiusParityInterchange.lean)

## Cost of repairing the mean without disturbing a fitted head

The least complete squared Hilbert error with the mean constraint is attained. The conductor-241 certificate bounds it by $1009/1000$ times the least squared error over legal adjustments with zero head, uniformly in the physical cutoff and the residual. If $q_K$ is the resulting tail capacity, its normalized value satisfies $1-E\le (K+1)q_K\le1$, with $E$ the limiting legal energy. The finite factor quantifies the cost of imposing the mean. Establishing arbitrarily small legal errors, or the required saturation theorem on the spectral route, remains open. [Legal tail mean capacity](RH/LegalTailMeanCapacity.lean)

## Natural-dilation cell energy

`naturalError_eq_continuumCorrection` identifies the finite natural-dilation error with the complete reciprocal-cell integral. `naturalError_eq_charge_quadratic` gives its signed quadratic in the exterior coefficient charge. `naturalError_insert_one_minimum` attains the minimum over conductor-one coefficients explicitly. The transfer from complete natural error to centered squared error has a factor strictly smaller than 6/5. This resolves the finite natural-error identification left open in the October cell-energy note. The remaining density step is to make the actual errors arbitrarily small. [BaezDuarteNaturalCellTransfer](RH/BaezDuarteNaturalCellTransfer.lean)

## Bare argument increment criterion

`positiveGapPCC_iff_collisionCorrectedPureArgument` identifies positive-gap PCC with the rational-width limits of the zeta argument increment mean square after subtracting the sine-model variance and measured equal-ordinate excess. The comparison between the triangle energy and this mean square is unconditional. A provider for the stated mean-square asymptotic is still needed. [MontgomeryArgumentWindowVariance](Analysis/MontgomeryArgumentWindowVariance.lean)

## Adjacent dilations of the Möbius approximants

At every cutoff the sum of squared screened pairing errors over the adjacent-dilation tail basis is exactly E/(1−E). The approximants have exact heads, and their physical L¹ errors converge to zero uniformly in the moving scale. Interchange for the screened probe on the entire basis is equivalent to the screened section being the ambient constant. The L¹ convergence alone does not prove that interchange. [MobiusParityInterchange](RH/MobiusParityInterchange.lean)

## Quantified finite tail test for the centered boundary

`boundary_zero_iff_cofinal_finiteSectionTailCost` requires one finite C, arbitrarily large physical cutoffs N, and for each such N arbitrarily late Gram cutoffs B with N times the finite cost at most C. The cost is the screened squared displacement computed from packet mass minus the explicit weighted first-N-site loss. The declarations compute its limit at fixed N and prove the equivalence. The uniform two-cutoff inequality remains open. [CenteredMeanGramTail](RH/CenteredMeanGramTail.lean) and [CenteredMeanQuotientTail](RH/CenteredMeanQuotientTail.lean)

## The actual prime mean square below the transition

`primeSignalMeanSquareSource_unconditional` supplies the previously assumed prime off-diagonal estimate using a bound of order x log x for the full prime-power sum. At x = T^α for every fixed 0 < α < 1, the normalized actual prime-signal energy tends to α. The zero-side residual and the microscopic positive-gap law are further analytic obligations. [MontgomeryPrimeMeanSquare](Analysis/MontgomeryPrimeMeanSquare.lean)

## Rational secants, quadrature and the equal-ordinate correction

Three finite width averages bound the signed pointwise gap error. A grid of order (log T)² suffices for integrating the actual positive-gap statistic at each fixed rational width. The rational sampled deficit must still tend to zero. The infimum of the normalized bare zeta argument variance over widths in (0,1] recovers the equal-ordinate mass asymptotically, with no simplicity hypothesis. The resulting fixed rational-width variance criteria have no explicit collision input. [Window pair correlation](Analysis/MontgomeryWindowPairCorrelation.lean), [gap quadrature](Analysis/MontgomeryCauchyGapMesh.lean) and [argument slope](Analysis/MontgomeryArgumentSlope.lean)

## Actual cumulative zero counts

`smoothCount_main_variation` bounds the signed integrated gamma remainder between u and v by C(1/u−1/v) for 1 ≤ u ≤ v. Together with the repository’s unconditional Backlund discrepancy this proves `actual_cumulativeRvM`. The dyadic height bias and scaled height mean now use the theorem directly. The sharp Wasserstein declarations retain their separate horizontal and approximation hypotheses. [Height laws](Analysis/DyadicZeroWassersteinLaws.lean) and [Wasserstein estimates](Analysis/DyadicZeroWasserstein.lean)

## Horizontal comparison for the completed zeta function

The multiplicity-weighted paired Hadamard product gives weak horizontal norm monotonicity of xi under RH. Conversely, horizontal comparison on every line to the right of the critical line would exclude a right-hand zero by countability. The full comparison property remains to be proved without RH. Its completed-zeta prefactors are retained exactly for applications to shifted quotients. [XiHorizontalComparison](Analysis/XiHorizontalComparison.lean)

## Changing the order of the Gram and height cutoffs

With the Gram fit fixed, the scaled physical tail tends to its period mean, at least the reciprocal of the period. The signed change in tail cost when the Gram fit is updated is exact. These declarations provide both an obstruction to exchanging cutoffs without an estimate and finite expressions for testing that estimate. A common cofinal estimate for the updated solves is still required. [CenteredMeanPeriodicGramTail](RH/CenteredMeanPeriodicGramTail.lean)

## The right derivative of the bare argument variance

At every fixed upper height T > 1, the right derivative at width zero equals the normalized count of all pairs sharing an ordinate. Multiplicity of a zero is retained throughout. The near-zero variance inequality in `cofinal_pureArgument_fixedHeight_iff_RH` is equivalent to RH when required at arbitrarily large T. Its cofinal inequality and the positive rational-width limits required for PCC remain distinct open inputs. [MontgomeryFixedHeightArgumentSlope](Analysis/MontgomeryFixedHeightArgumentSlope.lean)

## A signed complex-zero criterion for RH

At every fixed 0 < α < 1, the normalized third-signal residual tends to zero if and only if the sharp complex-zero form factor tends to α. At any fixed α > 0, its plateau at one is equivalent to a limit of 1−α for the signed third-signal and prime off-diagonal expression. At arbitrarily high fixed frequencies a cofinal logarithmic upper bound for that signed expression is equivalent to RH. The actual cofinal bound, the spectral residual limit, and the positive-gap ordinate law remain separate obligations. [MontgomeryFixedFrequencyResidual](Analysis/MontgomeryFixedFrequencyResidual.lean)

## Actual macroscopic pair counts

Put D(T) = T log T/(2π) and let P(T,r) be the normalized strict positive-gap count. Uniformly over 0 ≤ c ≤ 1, P(T,cD(T))/D(T) tends to c−c²/2. The proof counts actual positive zero occurrences with multiplicity, using their uniform rescaled cumulative height distribution. This establishes the macroscopic pair law. Positive-gap PCC asks for the sine-kernel law at fixed unfolded widths. [MontgomeryMacroscopicGap](Analysis/MontgomeryMacroscopicGap.lean)

## Physical L¹ density and Hilbert norms

Among ambient Pareto Hilbert vectors, physical L¹ approximation by the mixed subspace is equivalent to mean zero. The legal subspace approximates every ambient vector in L¹. The distance to the mixed subspace in this norm is the absolute value of the mean. Every mean-zero target admits a finite mixed-packet fit with any prescribed finite head matched exactly and arbitrarily small complete L¹ error. For the categorical unit boundary, a uniform Hilbert norm bound on representatives with arbitrarily long zero heads is equivalent to vanishing of the boundary. That uniform bound remains open. [MixedConductorL1Closure](RH/MixedConductorL1Closure.lean)

## Improved finite Gram estimates

The exact minimum squared distance from the parity packet with its first site removed to the range of doubled dilation is π²/16−1/2. This yields the cofinal projected-parity Gram criterion for the centered unit. The actual first-site quadratic Gram inequality holds at tolerance 49/2000 for every stage n ≥ 481, improving the earlier 1/40. The proof of a cofinal bound for arbitrarily small tolerances remains open. [Dyadic moments](RH/ParetoParityDyadicMoments.lean), [projected Gram criterion](RH/CenteredMeanDyadicGram.lean) and [uniform finite bound](RH/CenteredMeanGramUpperBound.lean)

## Two moving Gram solves

For a suitable positive damping exponent and a calibrated sequence of physical cutoffs, the base Gram solve already has uniformly bounded scaled cost. Its drift to a later solve is exactly the change in reciprocal packet mass minus the weighted head displacement. The centered boundary vanishes if and only if this scaled drift is bounded by one common constant at arbitrarily large base solves and, for each of those, arbitrarily late updated solves. The individual fixed-solve decay is proved. The nested bound for the actual solves remains open. [CenteredMeanMovingGramTail](RH/CenteredMeanMovingGramTail.lean)

For B ≤ A, the complete drift also equals a finite sum over residue classes in one period. When N is no larger than that period, the drift lies between the cost of the first shifted period and three times that cost. The same open cofinal inequality can therefore be tested with the explicit positive finite period sums. [CenteredMeanProgressionGramTail](RH/CenteredMeanProgressionGramTail.lean)

With the base solve and physical cutoff fixed, the omitted drift tends to zero for every later-solve window length tending to infinity. The closure criterion therefore permits arbitrarily slowly growing windows, still with one common constant for cofinally many base solves and, for each such base, cofinally late updates. `riemannHypothesis_of_bounded_driftWindows` applies this same bound directly to Mathlib’s RH statement. [CenteredMeanDriftWindows](RH/CenteredMeanDriftWindows.lean)

## The damping scale at an individual critical-line zero

For every real $a,u$, write $m$ for the order of zeta at $1/2+ia$. At height $a+\varepsilon u$ the quotient of zeta by its horizontally shifted value converges to $(iu/(1+iu))^m$ as $\varepsilon\downarrow0$. At a simple zero the rescaled squared defect is $1/[(1+u^2)(1/4+a^2)]$. This is an unconditional local limit. A global upper estimate on the natural finite truncation for small damping remains necessary for the prescribed Báez-Duarte fits. [Critical damping profile](RH/ParetoShiftedZetaZeroProfile.lean)

## The contribution of a simple zero to the damping budget

At a simple critical zero of ordinate $a$, the energy of the shifted quotient defect in $[a-L\varepsilon,a+L\varepsilon]$, divided by $\varepsilon$, tends to $2\arctan(L)/(1/4+a^2)$ for every $L\ge0$. This local formula is unconditional. Under RH the full-line energy $J_\varepsilon$ satisfies $J_\varepsilon>b\varepsilon$ eventually for every $b<\pi/(1/4+a^2)$. The repository’s existence theorem for simple critical zeros therefore gives a positive linear lower bound alongside the proved limit $J_\varepsilon\to0$. On the natural truncation route the missing estimate concerns the separate finite polynomial tail. [Damping windows](RH/ParetoShiftedZetaSimpleWindow.lean) and [full-line lower bound](RH/ParetoShiftedZetaSimpleLower.lean)

## The logarithmic derivative inside the right half-strip

Under RH, for each $0<\eta\le1/2$ there is a constant $C_\eta$ such that $|\zeta'/\zeta(\sigma+it)|\le C_\eta\log|t|$ uniformly on $1/2+\eta\le\sigma\le3/2$ and $|t|\ge2$. This uses the repository’s translated-disk estimate after its finite zero sum vanishes. It gives height-uniform control away from the critical line for the complex damping parameter in the approximation problem. Convergence or closure of the small-damping squarefree approximants requires a further argument. [Interior logarithmic derivative](Analysis/RHInteriorLogDerivative.lean)

## Complex perturbations of the damping parameter

The holomorphic representative of $1/\zeta$ has a zero of derivative one at $s=1$. Its analyticity at every $\Re s>1/2$ is equivalent to RH. Under RH the change in zeta modulus across an interior displacement $v$ is bounded by a factor $(2|t|)^{C_\eta\|v\|}$. Around every real damping center $0<d\le3/4$, there is a complex disc of shifts on which the actual critical-line quotient is bounded by $K(2|t|)^{13/32}$ for $|t|\ge3$. The exponent below one half permits square-integrable domination after division by the critical-line variable. Passing from these analytic bounds to membership in the closed squarefree residue space requires the actual annihilator or truncation argument. [Reciprocal zeta](Analysis/AnalyticReciprocalZeta.lean), [variation along segments](Analysis/RHInteriorZetaVariation.lean) and [complex damping bound](RH/ParetoComplexDampingNeighborhood.lean)

## Uniform zero counts down to height zero

For D(T) = T log T/(2π), the cumulative height distribution satisfies

\[
\sup_{0\le x\le 1}\left|\frac{N(0,xT)}{D(T)}-x-\frac{x(\log x-\log(2\pi)-1)}{\log T}\right|\le \frac{K}{T}
\]

at every sufficiently large T, interpreting x log x as zero at x = 0. Lean proves this for the actual zeros with multiplicity, starting from the integrated gamma remainder and Backlund discrepancy. This supplies the one-point input for second-order macroscopic pair tests. [DyadicZeroWassersteinLaws](Analysis/DyadicZeroWassersteinLaws.lean)

## The first Balazard–de Roton budget under RH

Under RH, the full weighted critical-line energy of $1-\zeta(s)/\zeta(s+\varepsilon)$ tends to zero as positive damping tends to zero. For every cutoff schedule the norm of the finite physical error differs from the square root of the corrected tail energy by a quantity tending to zero. Thus the corrected tail alone decides convergence of the prescribed fits under RH. The exact tail includes the finite reciprocal charge. The Lean repository supplies cutoff convergence for damping at least one half. The remaining conditional Báez-Duarte step needs a schedule for small damping on which the corrected tail vanishes. An unconditional proof by these fits would need control of the complete physical error without invoking RH. [Shifted quotient budget](RH/ParetoShiftedZetaBudget.lean), [corrected tail equivalence](RH/BalazardDeRotonBiasUnderRH.lean) and [existing cutoff range](RH/DampedMobiusSquarefreeClosure.lean)

## A countable test for RH through the completed zeta function

RH is equivalent to weak horizontal norm comparison for xi when both abscissae and the common height are rational and the left abscissa is at least one half. The proof extends these rational tests by continuity. The same norm comparison is unconditional when the left abscissa is at least one, from the critical-strip bound for every nontrivial zero. The open inequality lies between the critical line and abscissa one. [XiHorizontalComparison](Analysis/XiHorizontalComparison.lean)

## A prescribed shrinking width for RH

At the single unfolded width $r(T)=T^{-2}$, the cofinal bare argument-variance upper bound in `riemannHypothesis_of_inverseSquareWidthArgument` implies RH. The finite estimate retains the multiplicity-weighted count of off-line zeros. The general variant permits a fixed margin strictly below two and widths satisfying $D(T)r(T)\to0$. Proving the stipulated upper bound at arbitrarily large actual heights remains open. [Prescribed-width criterion](Analysis/MontgomeryPrescribedArgumentWidth.lean)

## Continuous tests of the actual ordinates

For each continuous real score $g$ on the normalized height interval, the multiplicity-weighted empirical sum of $g(\gamma/T)$ divided by $D(T)$ tends to its integral on the unit interval. This supplies continuous one-point tests for macroscopic pair expansions. [Scaled height tests](Analysis/MontgomeryScaledHeightTests.lean)

## Clipped rows and the error of a continuous pair model

`clipped_height_row_sum_eq_backward_count` transposes a clipped pair sum over actual zeros into an integral against the backward counting increment. If a model cumulative distribution with integrable density $w$ approximates the actual scaled zero count uniformly to error $\eta$, the resulting macroscopic pair model differs from $P(T,cD(T))/D(T)$ by at most $2\eta(N(0,T)/D(T)+\int_0^1|w|)$. Strict lower endpoints and the actual multiplicities are retained. This supplies the finite comparison for a quantitative pair expansion. [Clipped-row duality](Analysis/MontgomeryGapRowDuality.lean)

## The unconditional mesoscopic pair law

For the actual zero occurrences, $P(T,R(T))/R(T)\to1$ whenever $R(T)/\log T\to\infty$ and $R(T)/D(T)\to0$. For example, the theorem applies to $R(T)=(\log T)^2$. The result uses the actual uniform one-point counting estimate and handles all multiplicities. At fixed width, `positiveGapPCC_iff_centeredOrdinateWindowCounts` states exactly how the average centered count in windows starting at the zero ordinates must recover the sine-kernel deficit. The required fixed-width limit remains open. [Mesoscopic counts and fixed-width equivalence](Analysis/MontgomeryMesoscopicGapCount.lean)

## What a right-hand zero would force in the original category

At a zeta zero $s$ with real part $\sigma>1/2$, the descended Mellin functional evaluates the centered boundary of a scalar $a$ as $-a/s$. The normalized real part gives an explicit left inverse of the boundary arrow. Every representative $z$ of this class with its first $K-1$ coordinates zero satisfies
\[
\|z\|^2\ge(2\sigma-1)|a/s|^2K^{2\sigma-1}.
\]
Consequently, for the unit boundary, finding representatives below $cK^p$ for every $c,p>0$ would prove RH. Those representatives with the required Hilbert budgets remain to be constructed. The separate epimorphism test in the quotient identifies the disappearance of the common mean-orthogonal subspace. [Signed Mellin descent](RH/CenteredMeanMellinDescent.lean) and [quotient epimorphism](RH/CenteredMeanQuotientNorm.lean)

## The continuous reciprocal truncation and the discrete charge

For any positive damping tending to zero and any cutoff schedule tending to infinity, the actual finite charge tends to zero unconditionally. Finite Abel summation and the repository’s PNT for signed reciprocal Möbius sums give this joint limit, with no rate condition coupling damping and cutoff. The complete critical-line energy of the difference between the corrected and natural tails is exactly the squared charge modulus times $\log(2\pi)-\gamma$. Under RH, convergence of the finite discrete fits is therefore equivalent to decay of the paper’s natural reciprocal-zeta truncation energy on every divergent cutoff schedule. The small-damping truncation estimate is the remaining input to this RH-to-approximation direction. [Charge limit](RH/BalazardDeRotonChargeLimit.lean) and [natural tail equivalence](RH/BalazardDeRotonNaturalTail.lean)

## Conductor six and the finite parity Gram systems

The mixed packet of conductor six by itself captures strictly more than half of the entire mean-zero variance of the dyadic parity adjoint. Its inner product is exactly $2\log 2-(1-1/\sqrt3)\pi$. At every finite legal Gram cutoff the centered source yields a lower bound on its squared fitting error by $(2/5-1/(10\sqrt3))^2E$. To prove RH along this route one must show that the actual inverse Gram capacities approach the explicit source squared norm $2\log2-\pi^2/8+11/450$. [Conductor-six capture](RH/CenteredMeanParityGramSix.lean) and [finite Gram capacity](RH/DyadicParityGramCapacity.lean)

## The categorical cokernel at multiple right zeros

The normalized evaluations at the right zeros are linearly independent complex-valued functionals. On the image of the centered boundary they all evaluate the scalar $a$ to $-a$. Consequently two distinct right zeros give a nonzero functional on the cokernel of that arrow. The epimorphism hypothesis on the original centered boundary by itself implies RH. Establishing the actual epimorphism remains open. [CenteredMeanMellinCharacters](RH/CenteredMeanMellinCharacters.lean)

## The finite resolvent outside the height interval

The full real pair sum for the finite zero cutoff has an exact nonnegative excess over the integral of its squared resolvent on $[0,T]$. For every $u\ge0$ the excess is at most $C e^u\log^2(T+3)$. At $u=\alpha\log T$ with fixed $0\le\alpha<1$, it vanishes after division by $T\log T$. The passage from this finite signal to the full contour formula must still account for zeros outside the cutoff contributing inside $[0,T]$. The signed functional-equation remainder on the line of real part $-1/2$ is controlled separately. [Finite resolvent](Analysis/MontgomeryFiniteResolventSignal.lean) and [left contour](Analysis/MontgomeryLeftContour.lean)

## Cutoffs that remove endpoint clipping

Every sufficiently high physical interval of length one contains a cutoff with an empty forward band of a common positive unfolded width. At these cutoffs, all shorter forward windows have zero clipping error. For any prescribed width with $D(T)r(T)\to0$, the bare argument statistic admits a decomposition into the actual same-ordinate count and the strict positive-gap primitive with an absolute error tending to zero on the pair-count scale. Both the signed microscopic average and the cofinal collision bound for RH remain open. [Gap-free cutoffs](Analysis/MontgomeryGapFreeCutoffs.lean)

## The actual Weil test and its heat representation

For every real frequency and height, the zero-side transform of the modulated exponential test is absolutely summable over all nontrivial zeta zeros with multiplicity. The heat-parameter integral equals the actual zero sum. To obtain the subunit-frequency complex-zero form factor from this identity, the prime and gamma integrals must also be identified and the finite height boundary controlled. Fixed-width positive-gap PCC requires further estimates. [Resolvent Weil test](Analysis/MontgomeryResolventWeilTest.lean)

## The logarithmic correction to macroscopic gap counts

At each fixed fraction $0\le c\le1$, the actual normalized count has an explicit next coefficient: $\log T\,[P(T,cD)/D-c+c^2/2]$ converges to `macroscopicGapSecondCoefficient c`. At full width the coefficient is $-1-\log(2\pi)$. The actual equal-ordinate collision term divided by $D^2$ still tends to zero after multiplication by $\log T$. The logarithmic correction concerns widths proportional to $D$; the sine-kernel limit at fixed positive widths remains open. [Macroscopic second term](Analysis/MontgomeryMacroscopicGapSecondTerm.lean)

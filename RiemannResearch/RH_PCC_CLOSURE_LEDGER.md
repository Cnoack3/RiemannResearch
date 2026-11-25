# RH and Montgomery positive-gap pair correlation

Initial source audit at `cdb1db95f32f9e40123f12a1df359bae704c9d8f`. A theorem with a hypothesis is evidence for the stated implication. The final column records the input still required on the indicated route.

| Route | Declarations already in the Lean tree | Remaining mathematical input |
| --- | --- | --- |
| Centered categorical tower | [CenteredMeanRHCriteria](RH/CenteredMeanRHCriteria.lean), `categoricalMean_tfae`, `riemannHypothesis_of_stageUnit_zero` | Show the actual stage unit has zero boundary. The reverse implication from RH to that unit criterion in `stageUnit_zero_iff_riemannHypothesis` explicitly takes the Báez-Duarte approximation implication. |
| Nyman–Beurling and finite Gram systems | [CenteredMeanGramUpperBound](RH/CenteredMeanGramUpperBound.lean), [CenteredMeanDyadicGram](RH/CenteredMeanDyadicGram.lean) | Verify the required quadratic cost bound for arbitrarily small positive tolerances at cofinal cutoffs. A fixed positive tolerance cannot supply this quantifier. |
| Screened Möbius parity test | [MobiusParityInterchange](RH/MobiusParityInterchange.lean), `screened_pairing_tendsto_zero`, `screened_tail_error_tendsto` | The actual moving tail tends to the first physical value of the screened section minus one. Vanishing of this tail would determine that coordinate. Equality of the entire screened section with the constant requires a further argument. |
| Actual zero ordinates | [MontgomeryWindowVarianceCriterion](Analysis/MontgomeryWindowVarianceCriterion.lean), `positiveGapPCC_of_rationalTriangleWidthAverages` | Prove the specified triangle width-average limit for the actual zeta-zero occurrences on every rational interval in the theorem. |
| Determinantal comparison | [ZeroDPPProjectionBridge](Analysis/ZeroDPPProjectionBridge.lean) | Verify the actual limiting projected statistic and control any omitted-pair contribution under this route's hypotheses. |

## Projection and Möbius cutoff order

For the complete signed pairing C(M,N) of the projection residual at M with the canonical Möbius residual at N, each fixed row tends to zero, while every column tends to the same limiting energy E. In fact C(M,N) equals the finite energy E_M whenever N ≤ M. Agreement of these two iterated limits is equivalent to membership of the constant in the closed legal space. The unconditional calculations leave E undetermined. See [CanonicalMobiusProjectionLimits](RH/CanonicalMobiusProjectionLimits.lean).

## Collision-corrected pair correlation

[MontgomeryWindowPairCorrelation](Analysis/MontgomeryWindowPairCorrelation.lean) proves `positiveGapPCC_iff_rationalIntegratedGapDeficit`. Exact subtraction of all equal-ordinate mass gives a criterion on every positive rational width. A proof that the resulting actual integrated deficits tend to zero is still needed.

## Centered quotient and finite Gram systems

- `hasSum_coordinate_quotient_norm_loss` identifies the sum of the nonnegative coordinate losses with E. By `boundary_zero_iff_coordinate_norms`, preservation of each centered coordinate norm is equivalent to vanishing of the boundary. A proof of norm preservation for the actual quotient map would close this route. [CenteredMeanQuotientNorm](RH/CenteredMeanQuotientNorm.lean)
- `finite_endpoint_remainder_norm_sq` and `finite_endpoint_root_interval` keep the full remainder for two finite projection stages. `parityAdjointPacket_first_site_coupling` ties the signed adjoint pairing to the limiting energy and first physical residual. The finite identities leave the cofinal upper estimate open. [FiniteEndpointGram](RH/FiniteEndpointGram.lean) and [ParetoParityAdjointCriterion](RH/ParetoParityAdjointCriterion.lean)

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

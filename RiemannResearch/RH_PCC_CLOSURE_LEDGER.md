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

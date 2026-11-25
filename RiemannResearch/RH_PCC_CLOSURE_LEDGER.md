# RH and Montgomery positive-gap pair correlation

Initial source audit at `cdb1db95f32f9e40123f12a1df359bae704c9d8f`. A theorem with a hypothesis is evidence for the stated implication. The final column records the input still required on the indicated route.

| Route | Declarations already in the Lean tree | Remaining mathematical input |
| --- | --- | --- |
| Centered categorical tower | [CenteredMeanRHCriteria](RH/CenteredMeanRHCriteria.lean), `categoricalMean_tfae`, `riemannHypothesis_of_stageUnit_zero` | Show the actual stage unit has zero boundary. The reverse implication from RH to that unit criterion in `stageUnit_zero_iff_riemannHypothesis` explicitly takes the Báez-Duarte approximation implication. |
| Nyman–Beurling and finite Gram systems | [CenteredMeanGramUpperBound](RH/CenteredMeanGramUpperBound.lean), [CenteredMeanDyadicGram](RH/CenteredMeanDyadicGram.lean) | Verify the required quadratic cost bound for arbitrarily small positive tolerances at cofinal cutoffs. A fixed positive tolerance cannot supply this quantifier. |
| Screened Möbius parity test | [MobiusParityInterchange](RH/MobiusParityInterchange.lean), `screened_pairing_tendsto_zero`, `screened_tail_error_tendsto` | The actual moving tail tends to the first physical value of the screened section minus one. Vanishing of this tail would determine that coordinate. Equality of the entire screened section with the constant requires a further argument. |
| Actual zero ordinates | [MontgomeryWindowVarianceCriterion](Analysis/MontgomeryWindowVarianceCriterion.lean), `positiveGapPCC_of_rationalTriangleWidthAverages` | Prove the specified triangle width-average limit for the actual zeta-zero occurrences on every rational interval in the theorem. |
| Determinantal comparison | [ZeroDPPProjectionBridge](Analysis/ZeroDPPProjectionBridge.lean) | Verify the actual limiting projected statistic and control any omitted-pair contribution under this route's hypotheses. |

# Innovation inverse-Gram and growth catalog — 29 October 2026

Source base: 933fb43028951dd503c7ec2a14808f365bad7e72.
See [research memorandum](RH/CRTInverseGramHeadFirstResearch20261029.md) for definitions, full proofs, and the agenda audit.

## Established declarations

- [OrthogonalObservationHeadFirst](Analysis/OrthogonalObservationHeadFirst.lean):
  adjusted_inner, adjusted_norm, gain_norm, gain_pairing,
  joint_source_sq_le, signed_transition_le, adjusted_gram.
  Exact complete-Hilbert norm, joint-source, and rank-one Gram identities.
- [FiniteHilbertGramHeadFirst](Analysis/FiniteHilbertGramHeadFirst.lean):
  headShear_injective, headShear_independent, headShear_mem, headShear_gain,
  adjusted_source, headFirstGain_projection, headFirst_inverseGram.
  The full adjusted basis, its actual projection, and inverse-Gram identity.
- [QCRTHeadFirstSource](RH/QCRTHeadFirstSource.lean):
  next_lt_oldPeriod, old_normal_pairing, oldCapacity_pos,
  dense_joint_source_sq_le, dense_headFirst_inverseGram.
  The full actual moving optimizer is used. Old capacity positivity is proved
  at every squarefree next site after the initial step. Zero innovation
  capacity and empty blocks remain allowed.
- [QCRTInnovationPairGap](RH/QCRTInnovationPairGap.lean):
  screened_pair_identity, screened_pair_gap_bound,
  scaled_pair_gap_bound, pair_coercivity_bound.
  Exact anchor cancellation and complete-Q close-conductor energy estimates.
  The coercivity result restricts any proposed normalized lower coefficient bound.
- [DiscreteGronwall](Analysis/DiscreteGronwall.lean):
  energy_le_exp_cumulative, one_add_energy_le_exp_cumulative,
  log_one_add_energy_le, relativeLog_tendsto_zero.
  General finite inequalities and a limit implication with explicit hypotheses.

## Conditional research reductions

[QCRTOptimizerGrowth](RH/QCRTOptimizerGrowth.lean):

- riemannHypothesis_of_subpolynomial_stageEnergy.
  **Open provider:** subpolynomial complete norm of the actual dense optimizer.
- riemannHypothesis_of_stageEnergy_gronwall.
  **Open providers:** an actual recurrence with nonnegative alpha and beta;
  cumulative alpha is o(log(N+2)); log(1+cumulative beta) is o(log(N+2)).

No provider above is discharged by finite invertibility, the pair estimate,
or the head-first change of coordinates. RH is not proved.

## Paper-level consequences, not newly Lean-verified

The memorandum proves an exact CRT/Haar tensor comparison for B, a finite
normalized inverse upper bound 48 L/(1-p^(-2)), and normalized least-eigenvalue
collapse along primorial prime-enlargement stages. The finite pair inequality
is checked; the CRT covariance/tensor argument and divisor-pigeonhole
asymptotics are not represented as Lean-verified.

## Verification

The coherent isolated candidate passed job_cfN03C2JXjyISgKnEPsZjN5yO55u-HRA.
The actual inverse identity and the conditional growth consumer have only
propext, Classical.choice, and Quot.sound in the selected axiom audit.
Saved-source validation and publication must pass the final checkpoint.

## Full squarefree trial continuation — 30 October 2026

See [full-squarefree research memorandum](RH/FullSquarefreeTrialResearch20261030.md).

Established finite and structural results:

- [QCRTSquarefreeExhaustion](RH/QCRTSquarefreeExhaustion.lean):
  squarefree_conductor_mem, every_squarefree_conductor_eventually,
  every_finite_squarefree_support, dense_iSup_eq_squarefreeSpan,
  dense_closure_eq_squarefreeClosure.
  The entire squarefree dictionary, including composite conductors, is exhausted.
- [FiniteGramTrialCertificate](Analysis/FiniteGramTrialCertificate.lean):
  capacity_eq_inverseGram, inverseGram_trial_completion,
  inverseGram_trial_lower, inverseGram_direction_lower.
  Literal matrix trial identities retain the exact loss square.
- [QCRTTrialCertificate](RH/QCRTTrialCertificate.lean):
  jointFamily_independent, jointFamily_gram, dense_trial_completion,
  dense_step_le_trialCertificate, dense_direction_gain_lower,
  dense_full_completion, dense_trial_telescope, dense_energy_le_trial_sum.
  All added squarefree conductors and actual complete-Q moving sources are used.
- [QCRTPrimePairTrial](RH/QCRTPrimePairTrial.lean):
  primePair_sequence, primePair_head, primePair_anchor_cancellation,
  binary_base_norm_sq, primePair_norm_sq_le, primePair_mem_divisorStage.
  Explicit g_p−2g_(2p) has complete energy at most 3/(4p).
- [QCRTPrimePairCertificate](RH/QCRTPrimePairCertificate.lean):
  primePair_completion, primePair_step_le_cost_sub_source_sq,
  dense_new_prime_pair_bound.
  The actual old-dictionary next-head optimizer supplies the signed source.
  This is a finite-stage gain bound, not a cumulative growth estimate.
- [QCRTPrimeInnovation](RH/QCRTPrimeInnovation.lean):
  rawDirection_floor_block, screenedDirection_floor_block.
  Exact floor-block coordinates retain every positive old divisor and all cross terms.

Conditional research reductions:

- QCRTOptimizerGrowth.riemannHypothesis_of_cofinal_subpolynomial_stageEnergy.
  **Open:** subpolynomial actual energy along physical heads tending to infinity.
- QCRTTrialCertificate.riemannHypothesis_of_cofinal_trial_budget.
  **Open:** a full-family signed cofinal trial budget and its physical-head
  relative-log growth limit.

Selected candidate checks succeeded in job_GDB5Pf7hgyFldirLhkF8EjBEiaHY80rt,
job_ruHDm8oqDx-6K2CN5q6Y8eTdzxY5GqbU,
job_dNX3t9eMTc9_pDjexj3ZPTtyIH5o2b0e, and
job_5yiMw6Df2HEac2b34ki1e1nUIvGID7IP.
Selected full-trial, cofinal-consumer, prime-pair, and exhaustion axiom audits
reported only propext, Classical.choice, and Quot.sound.
Publication remains gated by saved-source checkpoint validation.
The numerical diagnostic source in the memorandum is exploratory floating-point
computation; it is not a Lean certificate or an arithmetic provider. RH remains open here.

## Full divisor coordinates and vanishing dyadic overhead — 30 October 2026

See [continuation and research agenda](RH/FullSquarefreeDyadicResearch20261030.md).

Established structural and finite-energy results:

- [QCRTDivisorBlock](RH/QCRTDivisorBlock.lean): primeDivisorEquiv,
  trialCertificate_arithmetic, divisorTrial_certificate,
  addedConductors_empty_of_nonprime. Full new-conductor indexing includes 1;
  source and adjusted Gram transport retains every cross term.
- [QFloorDilationHeadEnergy](RH/QFloorDilationHeadEnergy.lean):
  floorDilation_norm_sq_head_defect, floorDilation_norm_sq_le_head,
  headAdjustedEnergy_pos, headBlockDefect_ge_pareto_gap.
  Exact complete-Q head-tail defect and a stronger explicit norm denominator.
- [QCRTFullFloorTrial](RH/QCRTFullFloorTrial.lean): floorDilation_coefficients,
  floorTrial_completion, selfDilation_step_le, selfDilation_step_le_head.
  Actual unrestricted old-optimizer trials with exact competitor loss and
  head-refined gain. No source lower bound or asymptotic budget is assumed.
- [DyadicGronwall](Analysis/DyadicGronwall.lean):
  relativeLog_tendsto_zero_of_vanishing_multiplier,
  relativeLog_dyadic_of_eventual_recurrence.
  Nonnegative overhead a_m tending to zero suffices for subpolynomial growth
  in physical dyadic heads; a finite starting index is allowed.
- [QCRTDyadicBudget](RH/QCRTDyadicBudget.lean): dense_trial_interval,
  dense_energy_le_interval_certificate. All intervening stages are retained.

Conditional research reductions:

- QCRTDyadicBudget.riemannHypothesis_of_vanishing_dyadic_trial_budget.
  **Open arithmetic provider:** eventual full signed block certificate sum
  at most a_m E_(2^m)+B, with a_m nonnegative tending to zero and fixed B>=0.
- QCRTDyadicBudget.riemannHypothesis_of_harmonic_dyadic_trial_budget.
  The original handoff target is a special case; its budget remains **Open**.

Candidate checks succeeded in job_L_9qR6if92eUK5UQy2GRV4dLd7KPcBmy,
job_j-LYflBA8X2wA--fY9fWd7qwGvbyhM5e, and
job_yKz32OfbJVgtcLGeOZQMGBKwyCsktbLX. Selected audits use only
propext, Classical.choice, and Quot.sound. Final saved-source validation is
gated by the single publication checkpoint reported with delivery.
Complete-period floating diagnostics are saved with the memorandum; they
are not interval certificates or providers of the open arithmetic budget.

## Screened mixed trials — 30 October 2026

See [research memorandum](RH/ScreenedMixedTrialResearch20261030.md).

Established finite results:

- [QCRTScreenedFloorTrial](RH/QCRTScreenedFloorTrial.lean):
  screen_source, screen_energy, screen_gram, jointFamily_eq_screen,
  headFirst_eq_repair, trialCertificate_physical, jointSynthesis_eq_screen,
  trialCertificate_screen_transport. Exact next-head screening is transported
  into the same full adjusted trial certificate, including removed projection energy.
- [TwoDirectionTrial](Analysis/TwoDirectionTrial.lean): quadratic_completion,
  gain_sub_first, gain_sub_second, norm_completion, regularized_determinant_pos.
  Exact two-by-two algebra with all cross terms and diagonal-defect losses.
- [QCRTMixedFloorTrial](RH/QCRTMixedFloorTrial.lean):
  exists_oldVector, floorCoefficients_raw, mixedSynthesis, selfFloor_energy,
  selfFloor_not_prime_multiple, exact_determinant_pos, exact_mixedGain_ge_raw,
  exact_mixed_step, actualCoefficients_spec, actualCertificate_formula.
  The actual full-squarefree optimizer supplies the screened dilation.
  The compensated-prime direction is retained. Exact determinant positivity
  has no extra spectral premise; exact mixed gain dominates the prior
  head-refined raw gain at eligible prime stages. Every other stage remains
  in the global actualTrials certificate.

Conditional research reduction:

- QCRTDyadicBudget.riemannHypothesis_of_normalized_dyadic_excess.
  **Open provider:** for some fixed B>=0, the positive part of the entire
  signed dyadic certificate sum minus B, divided by 1+E_(2^m), tends to zero.
  Apply with QCRTMixedFloorTrial.actualTrials. No provider is proved here.

The complete candidate passed job_DiQ3HsQPTmR_XPaGCwTE9YfIvQsca8ou.
Selected audits use only propext, Classical.choice, and Quot.sound.
Saved-source checks passed job_PZEhdEBtvwnDEZzKOFYa5d5d8H834sYQ and
job_KHvtvCpXyUFCLc9XOsXXK9avJIb5PtIg. Final publication remains subject to
the single aggregate checkpoint reported with delivery.

[Complete-period floating diagnostics](RH/ScreenedMixedDiagnostics20261030.md)
are exploratory. The separate [rational small-period certificate](RH/CertifiedSmallEnergyDiagnostics20261030.md)
has exact arithmetic assertions but is not Lean-verified. The abstract mean-zero
comparison in the memorandum is paper-level. RH remains open in this program.

## Signed dyadic arithmetic continuation — 30 October 2026

See [signed arithmetic memorandum](RH/SignedDyadicArithmeticResearch20261030.md)
and [complete-Q diagnostics](RH/EndpointSourceDiagnostics20261030.md).

Paper-level results, not newly Lean-verified:

- Both mixed sources are expanded in the complete divisor dictionary. Charge
  normalization fixes the compensated-prime coefficient at minus one.
- Moving normal equations cancel the charge multiplier and all shared low
  coefficients, leaving an exact endpoint pairing on the new head band.
- The signed certificate block equals twice that pairing minus the complete
  endpoint distance square plus every unused full-family trial loss.
- Discrete summation by parts gives a finite squarefree-band dual difference
  energy bound, with an exact head completion square and physical tail square.
- A positive-part sandwich separates endpoint growth from normalized trial loss.

**Open provider:** the resulting full signed dyadic expression has normalized
positive excess tending to zero for some fixed additive allowance. No source
alignment, dual difference-energy rate, or accumulated-loss estimate is proved.
The numerical checks are exploratory, not interval certificates.

## Mixed-trial loss transport and source variation — 30 October 2026

See [the paper continuation](RH/MixedTrialLossTransportResearch20261030.md)
and [complete-Q diagnostics](RH/MixedTrialLossTransportDiagnostics20261030.md).

Paper-level results, not newly Lean-verified:

- Minimum old-dictionary repairs to the final dyadic head turn the actual
  unused mixed residuals into mutually orthogonal differences. Their summed
  squared norm minus the exact old repair squares equals the full loss sum.
- A signed block identity retains the initial final-head cost, moving repair
  pairings, and a negative global completion square.
- Complete divisor normal equations and signed summation by parts isolate the
  source drift. A common composite anchor and finite Bessel give a uniform
  bound by an explicit weighted moment of actual coefficient defects.
- No normalized asymptotic estimate for that moment or the remaining signed
  head/trial work is proved. The RH provider remains **Open**.

Lean retry job_jaLoqWLh0iqcPljrbo8giEQ0CtW0YGa5 timed out after 180.058 seconds
with verified=false. This continuation publishes documentation only.

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

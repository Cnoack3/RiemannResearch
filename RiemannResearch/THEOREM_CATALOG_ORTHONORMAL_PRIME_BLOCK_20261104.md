# Orthonormal prime-block research: verified declarations and open inputs

Date: 2026-11-04.

## Group 1: actual primorial projection gains

Files: Analysis/ResidualPrimeGain.lean and RH/QPrimorialRelativeGain.lean.

- New scalar theorem: not_summable_of_shifted_prime_lower.
- Actual-family declarations: gain, relativeGain, error_step, relativeGain_nonneg,
  relativeGain_lt_one, gain_eq_error_mul_relativeGain, error_relativeGain_step,
  error_eq_product, error_eq_initial_sub_gain_sum, error_le_exp_neg_gain_sum,
  closure_iff_relativeGain_not_summable.
- Conditional research reductions: riemannHypothesis_of_relativeGain_not_summable,
  riemannHypothesis_of_prime_gain_lower, riemannHypothesis_of_prime_energy_gain.
- Open: divergent sum of actual relative gains.
- Open sufficient target: one fixed c>0 lower-bounds incoming-prime relative
  gains by c/p. This is not asserted equivalent to RH.
- Indexing: primorialStage n uses primorial(n+3); step n introduces n+4
  only when n+4 is prime.
- Candidate verification: job_-B6p9yWKTvDQkR--vrfiakTsYVZIxEPF,
  verified=true, exit_code=0, server elapsed 5.888 seconds.
  Project publication requires the checkpoint's successful terminal result.
- Reused results: exact primorial cofinality/projection convergence;
  finite Schur identities; squarefree Q-to-Pareto RH transfer.

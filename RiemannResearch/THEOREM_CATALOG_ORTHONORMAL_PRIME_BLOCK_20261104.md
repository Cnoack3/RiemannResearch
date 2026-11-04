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
  Publication is confirmed below under Group 1 publication.
- Reused results: exact primorial cofinality/projection convergence;
  finite Schur identities; squarefree Q-to-Pareto RH transfer.

## Group 1 publication

- Full-project checkpoint job_5LM7gTXSB4l-2BPp7OU1J-PNANmST-uq succeeded.
- Build scope: full; aggregate project plus two explicitly changed modules.
- Build duration reported by server: 70.246 seconds; cache preflight 8.490 seconds.
- Published commit: 2ed0a319a49cf20428d854b286dd1aab6dfd6a13.

## Group 2: concrete examples and a full common-period remainder

RH/QModThreeTensorLegality.lean:
- fourSite is Delta f(4)-Delta f(2), a four-coordinate annihilator.
- coprimeThree and characterThree have their literal mod-3 physical values.
- residue_three_decomposition: g3 = coprimeThree/2 - characterThree/6.
- coprimeThree_not_mem, characterThree_not_mem, residue_four_not_mem.
- legalClosure_ne_top: the squarefree closure is a proper ambient subspace.
- No inference that the target 1 is excluded: fourSite_one = 0.
- Infinite tensor convergence and quantitative distance constants are paper
  deductions, not newly formalized by this module.

RH/QCommonPeriodError.lean:
- inner_divisor_zero_of_mem_span.
- error_exact_of_inner_divisor_zero and error_lower_of_mem_span.
- primorial_inner_divisor_zero.
- primorialError_exact and primorialError_lower.
- Exact identity: E = L^(-2) + norm(1 - optimizer - indicator(L divides n))^2.
  The whole common-multiple contribution and the full remainder are retained.

RH/QPrimorialRelativeGain.lean additions:
- stage_succ_eq_of_not_prime; relativeGain_eq_zero_of_not_prime.
- riemannHypothesis_of_eventual_prime_gain_lower: arbitrary finite exceptions
  are allowed; the eventual arithmetic estimate remains Open.

Candidate verification:
- Tensor candidate job_2-JS5_k1s98pMD77e1_xgnRmTZj79o9M succeeded, 7.178 seconds.
- Combined candidate job_AuX6X2cI5ztX8HKXq5CwTdI2lMs40LVO succeeded,
  verified=true, exit_code=0, server elapsed 16.658 seconds.
- Inspected axioms of proper closure, common-period identity, and eventual
  RH consumer: propext, Classical.choice, Quot.sound only.
- Source publication is confirmed below under Group 2 publication.

## Symbolic and numerical diagnostics

Wolfram exactly returned zero for the scalar Schur inverse-gain identity
and for the full quadratic completion under a>0 and a*c-b^2>0.
The mod-3 decomposition is exact on all three classes.
The four-site values on coprimeThree, characterThree, and g4 are 1, 3, -1.
The functional squared norm is 30*zeta(2) = 5*pi^2.

Complete periodic Q moments evaluated at 45 digits gave:
p=2, L=2, dim=1, E=.25, relative gain=.75, p*gain=1.5.
p=3, L=6, dim=3, E=.05476694337026223565, p*gain=2.34279667955685317216.
p=5, L=30, dim=7, E=.02540022543571815946, p*gain=2.68106234594880059018.
p=7, L=210, dim=15, E=.01687043606102304074, p*gain=2.35070849170113467761.
p=11, L=2310, dim=31, E=.01354948106541300642, p*gain=2.16535629663476107530.
These are numerical diagnostics, not interval certificates or an asymptotic proof.

## Prioritized open research and formalization work

1. Identify concrete new-prime atoms and block basis with the abstract projection increment.
2. Specialize the existing full Schur formula to all actual prime-block moments.
3. Seek a target-weighted lower bound t^T S^(-1) t / E.
4. Seek a divergent packet-averaged relative-gain lower bound if pointwise c/p is too strong.
5. Prove a chosen-path regularization budget J_lambda <= C*lambda.
6. Turn finite numerical computations into rational interval certificates.
7. Formalize the full valuation tensor map separately from legality of its images.
8. Use radical compatibility for search-space reduction without confusing finite
   interpolation with Hilbert closure.
9. Keep standard projection/Parseval/Schur/spectral facts as reusable dependencies.
10. The exact arithmetic obligation is actual gain nonsummability; no provider
    is established here.

Published sources: Bagchi (2006), Remark 8, DOI 10.1007/BF02829783;
von Neumann (1939), Compositio 6, 1-77, Section 4.1;
Boyd-Vandenberghe (2004), Appendix A.5.5;
Axler (2020), Chapter 8;
Albani-Elbau-de Hoop-Scherzer (2016), DOI 10.1080/01630563.2016.1144070,
with the explicit range hypothesis retained.

## Group 2 publication

- Full-project checkpoint job_XLAuH1vAH26sEihBV7zHW0AUcJpIZIqb succeeded.
- Build scope: full; aggregate project plus QCommonPeriodError,
  QModThreeTensorLegality, and QPrimorialRelativeGain.
- Build duration reported by server: 78.519 seconds; cache preflight 8.558 seconds.
- Published commit: 61824beb6e3b42c95fe5f9e55fe50be3071063bf.
- Both groups together add 38 theorem declarations and five definitions.
- No sorry/admit or additional project axioms were introduced.
- The numerical prime-gain pattern is not a theorem, and no open arithmetic
  provider has been discharged by these conditional consumer proofs.

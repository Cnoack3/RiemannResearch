# Signed covariance minimum and reciprocal Möbius bridge — 22 September 2026

Source: user-provided `Pareto_Direct_Attempt_Sublinear_Energy_2026-09-22_Continued (2).md`, Sections 7–9.
This continuation adds 34 theorem declarations in four modules. It does not prove RH.

## Actual finite covariance optimization

For any nonempty finite indexed family of positive canonical indices k_i, at a tail cutoff N, set
C_ij = <tail_N u_(k_i), tail_N u_(k_j)>.
These are the entire infinite Pareto tails, with every signed cross term.

`Analysis/FiniteGramRange.lean` proves solvability of a possibly singular finite Gram system when every synthesis-null vector has coefficient sum zero. The actual arithmetic provider is the previously verified finite-periodicity obstruction.

`RH/CanonicalMobiusCovarianceMinimum.lean`, namespace
`RiemannResearch.RH.Pareto.CoefficientStabilization.SignedCovariance`, constructs:
- `normal N k hk`, an actual solution z to C z = 1;
- `capacity N k hk` = sum z_i > 0;
- `optimizedAverage N k hk`, with coefficients z_i / capacity.

Solvability and positivity are established, not assumed. Repeated indices and singular matrices are permitted. `capacity_eq_sum_of_normal` proves that the scalar does not depend on which normal solution is chosen.

`Analysis/FiniteGramAffineMinimum.lean` proves exact completion:
Q(c) = 1/capacity + Q(c - z/capacity), when sum c_i = 1.
It proves the attained minimum and uniqueness of the synthesized minimizing tail vector. Coefficients themselves need not be unique.

The concrete `covariance_isLeast` proves
min_(sum c_i = 1) sum_ij c_i c_j C_ij = 1/capacity.
When every k_i >= N, `optimizedAverage_norm_sq` gives the full norm:
||optimizedAverage||^2 = N/(N+1) + 1/capacity.

## Exact remaining capacity estimate

`riemannHypothesis_of_capacity_frequently_ge` proves actual Mathlib RH if, for growing finite nonempty index families with k_(N,i) >= N and k_(N,i) > 0, there is epsilon > 0 with
capacity_N >= epsilon for arbitrarily large N.

This result has no PNT or sublinear-energy hypothesis. The positive cofinal capacity lower bound is the open research provider. Finite-stage positivity does not establish it.

`capacity_tendsto_zero_of_not_RH` proves the contrapositive asymptotic obstruction:
not RH implies capacity_N -> 0 for every such sequence of finite index families.
No converse is asserted for an arbitrary chosen sequence of families.

## One arithmetic premise instead of two

`RH/CanonicalMobiusCesaro.lean` proves the exact identity
M(N) = N m_N - sum_(k<N) m_k.
Cesàro convergence gives m_N -> L (any finite L) implies M(N)/N -> 0.
Consequently `canonicalMobiusHilbert_sublinear_of_reciprocal_cancellation` retains only m_N -> 0.

`riemannHypothesis_of_reciprocal_cancellation_and_bounded_tail` therefore derives RH from that single arithmetic input and a bounded cofinal normalized residual-tail energy.
The classical input m_N -> 0 still lacks a checked unconditional provider here.
The residual-tail upper bound remains an open research estimate.

## Verification

Combined source check `job_34kmcXEa1WzzZYzdUfnL9CLldbHPdLIc` succeeded:
exit code 0, verified true, no warnings.
Axiom audits for the attained covariance minimum, capacity-to-RH criterion,
not-RH capacity decay, and one-input residual-tail RH criterion reported only
`propext`, `Classical.choice`, and `Quot.sound`.
These audits do not discharge explicit hypotheses.

Workspace: `ws_YCBn4_yOwTvJ6_8f5sZf9beWp7vIYaNZ`.
Base commit: `32028c1d9b8ac4d2e2fb8cd89dc78a0706e7fd53`.
Final acceptance is the affected-module publication checkpoint; its result and commit are reported with the delivered handoff.

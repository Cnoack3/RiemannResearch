# Joint signed-head limits at the Burnol endpoint

Date: 2026-09-27. Project: RiemannResearch, Lean 4 / Mathlib.

**Subsequent strengthening:** `DampedMobiusHalfHilbertConvergence.lean`
now proves full natural-order Hilbert norm convergence, including the
infinite physical tail, and removes the relative-rate condition on the
cutoffs. See `HalfHilbertConvergence20260927.md`. The original theorem
and its proof are documented below.

## What was discharged

The previous signed-head result took the residue cutoff to infinity before
the physical head. The new result proves an actual simultaneous limit in
the full unconditional range epsilon >= 1/2, including equal cutoffs at
epsilon = 1/2. Its statement assumes no off-diagonal bound, RH, or
unproved arithmetic estimate.

For fixed epsilon, write
`c = Re(1/zeta(1+epsilon))`,
`g(n) = dampedMobiusPrefix epsilon n - n*c`,
`E = sum_n positiveWeight(n)*g(n)^2`,
and `Delta = sum_m ||arithmeticResidueTerm(dampedMobiusWeight epsilon,m)||^2`.
Let `O(H,M)` denote the repository's signed off-diagonal finite Gram sum;
both orientations of every distinct pair are retained.

The principal theorem proves

`O(H(j),M(j)) -> E - Delta`

whenever epsilon >= 1/2, both natural-number cutoffs tend to infinity, and
H(j) <= M(j) eventually. In particular, there is a finite B with
`O(H,H) <= B` for every H. B may depend on epsilon.

## Checked proof components

- `Analysis.sum_weighted_mul_sq_le`: weighted finite Cauchy--Schwarz.
- `Analysis.sum_weighted_sq_sub_tendsto_zero`: vanishing weighted square
  error transfers moving finite energies when target energies are bounded.
- `Pareto.dampedMobius_headDiagonal_joint_tendsto`: the actual diagonal
  converges for every epsilon > 0 and any two diverging cutoffs, with no
  ordering or relative-rate requirement.
- `Pareto.dampedMobius_offDiagonal_joint_tendsto_of_head_error`: a general
  transfer from actual finite energy and vanishing head error to the exact
  signed limit. These two premises are explicit.
- `Pareto.dampedMobius_half_density_tail_log_bound`: the existing
  unconditional Mertens estimate and signed Abel tail theorem supply
  `|c - sum_{d<=M} mu(d)/d^(3/2)| <= D*M^(-1/2)*(6+log M)^(-3/2)`.
- `Pareto.dampedMobius_half_head_error_log_bound`: for H <= M and M >= 1,
  the weighted squared head error is at most
  `K*(6+log M)^(-3)`. The entire signed density tail is combined before
  squaring. This tends to zero even for H=M, where the previous elementary
  absolute-tail majorant supplied only a constant bound.
- `Pareto.dampedMobius_half_head_error_tendsto` and
  `Pareto.dampedMobius_half_offDiagonal_joint_tendsto`: endpoint providers.
- `Pareto.dampedMobius_head_error_tendsto_of_half_lt`: the elementary
  bound suffices for epsilon > 1/2, since
  `H*M^(-2*epsilon)/epsilon^2 <= M^(1-2*epsilon)/epsilon^2 -> 0`.
- `Pareto.dampedMobius_offDiagonal_joint_tendsto_of_half_le`: assembly
  throughout epsilon >= 1/2.
- `Pareto.dampedMobius_equal_cutoff_signed_bound_of_half_le`: a proved
  unconditional signed bound, obtained from convergence.

The generic estimates extend `Analysis/FiniteWeightedEnergyComparison.lean`.
The diagonal theorem extends `RH/DampedMobiusExactSignedHeadLimits.lean`.
The arithmetic and signed-limit assembly is in
`RH/DampedMobiusJointHeadLimits.lean`.

## Exact remaining scope

**Open:** actual finite energy or a suitable signed upper bound for specified
subhalf damping 0 < epsilon < 1/2. The existing positive-damping sequence
criterion approaching zero still has its arithmetic hypothesis.

The small-damping hypotheses remain open. Full natural-order Hilbert
convergence at epsilon=1/2 has subsequently been established in
`DampedMobiusHalfHilbertConvergence.lean`, together with unrestricted
joint signed limits and a uniform bound for every pair of cutoffs.
Absolute off-diagonal summability is not asserted.

The unconditional half-damping membership was already established.
This change closes the simultaneous-cutoff and endpoint approximation
dependencies; it does not claim a new zero-free region or a proof of RH.

## Provenance and verification

The underlying endpoint statement is Burnol, *On an analytic estimate in
the theory of the Riemann zeta function and a theorem of Baez-Duarte*,
Section 4, Lemma 4.1, https://arxiv.org/abs/math/0202166.
The repository's PNT, logarithmic Mertens, Abel-tail, and endpoint modules
supply the arithmetic inputs. The simultaneous-limit argument is an
elementary consequence of those checked inputs; no novelty claim is made.

The complete combined source check returned exit_code=0 and verified=true
without warnings (job_MoSfhmWgo-1spUbjRJ3ThEj9WWlyaCAF). The generic weighted
energy lemmas also passed with their focused imports alone. Final
module and reverse-dependent validation is performed by the publication
checkpoint. No
`sorry`, `admit`, project-local axiom, or unsafe declaration is used.
The principal axiom checks contain only `propext`, `Classical.choice`,
and `Quot.sound`; the theorem types, rather than axiom reports alone,
show which domain-specific assumptions have been discharged.

# Pareto sublinear-energy continuation in Lean — 22 September 2026

Source: user-provided `Pareto_Direct_Attempt_Sublinear_Energy_2026-09-22.md`.
This note records exact formal coverage; it does not claim a proof of RH.

## Actual family and unconditional full energy

`RH/CanonicalMobiusFullEnergy.lean` defines `canonicalMobiusHilbert N`
as the actual finite combination
\[
u_N=-\sum_{d=1}^N\mu(d)g_d+(N+1)m_N g_{N+1}.
\]
The zero conductor-one atom makes this identical to the source formula.

Established declarations identify its physical sequence with
`canonicalMobiusHead N`, prove membership in `finiteSpace N` and
`closedSpace`, and retain its exact value one at every positive coordinate
through N. `canonicalMobiusHead_floor_expansion` proves the floor formula
at **every** coordinate, including the infinite tail.

The pointwise bound `canonicalMobiusHead_abs_le_two_mul` is |u_N(j)| ≤ 2N.
The exact full-norm split `canonicalMobiusHilbert_norm_sq_split` is
\[
\|u_N\|^2=\frac{N}{N+1}+
\sum_{j>N}\frac{|u_N(j)|^2}{j(j+1)}.
\]
For N>0, `canonicalMobiusHilbert_norm_sq_le` and
`canonicalMobiusHilbert_norm_sq_lt_four_mul` give
\[
\|u_N\|^2\le\frac{N(4N+1)}{N+1}<4N.
\]
These are unconditional full Pareto norms, not conditional-mean energies.

## Sublinear-energy implications

`Analysis/SublinearEnergyLimits.lean` proves:

- `tendsto_atTop_of_pos_le_mul_tendsto_zero`: a fixed positive lower
  bound c ≤ t_N b_N, with b_N ≥ 0 and b_N → 0, forces t_N → +∞.
- `tendsto_zero_of_fixed_cutoff_remainder`: if nonnegative e_N satisfies,
  for every fixed integer K≥2, e_N ≤ b_{K,N}+C/K eventually with
  b_{K,N}→0, then e_N→0. No uniformity of b in K is required.

The concrete consumer `canonicalMobiusHilbert_sublinear_of_cutoff_bounds`
applies the latter theorem to e_N=‖u_N‖²/N. The actual arithmetic cutoff
bounds remain an explicit provider hypothesis.

`RH/ParetoSublinearResidualTail.lean` uses the existing exact theorem
`residual_tail_product_lower`:
\[
\delta^2\le T_N\|\mathbf1-F_N\|^2,
\qquad \delta=\|r\|^2,\quad
T_N=\sum_{j>N}\frac{|r(j)|^2}{j(j+1)}.
\]
Here r is the actual canonical projection residual, and F_N is an actual
legal Hilbert vector equal to one through N.

The new `error_energy_div_tendsto_zero_of_energy` passes from full
candidate energy o(N) to error energy o(N). Then
`normalized_residual_tail_tendsto_atTop_of_sublinear_energy` proves
\[
\delta>0,\quad\|F_N\|^2/N\longrightarrow0
\quad\Longrightarrow\quad N T_N\longrightarrow+\infty.
\]
`canonical_normalized_tail_tendsto_atTop` discharges the legality and head
hypotheses for the explicit Möbius family. It **retains** the sublinear
energy limit as a hypothesis.

`limitEnergy_zero_of_frequently_bounded_normalized_tail` proves δ=0
under the sublinear-energy hypothesis and
\[
\exists C<\infty:\quad N T_N\le C
\text{ for arbitrarily large }N.
\]
`riemannHypothesis_of_frequently_bounded_normalized_tail` derives actual
Mathlib `RiemannHypothesis` from those inputs.

## Stronger bounded-subsequence criterion

`riemannHypothesis_of_frequently_bounded_exact_head_energy` proves:
for any legal exact-head family, a fixed finite upper bound for its full
energies along arbitrarily large cutoffs suffices for actual Mathlib RH.
No sublinear-energy premise is needed for this theorem.

`riemannHypothesis_of_canonical_frequently_bounded_energy` specializes
this result to the explicit Möbius family, discharging its representation
hypotheses. The bounded subsequence is not constructed.

`not_RH_exact_head_energy_tendsto_atTop` proves that failure of RH forces
the full energies of every such family to diverge. Its proof uses the
previously established divergence of exact-head errors.

## Open providers and exact limits of this formalization

- **Not yet formalized here:** the source's PNT-driven proof
  ‖u_N‖²/N→0, including intermediate-window cancellation. The ordinary
  mathematical argument in the source is not contradicted by this limitation.
- **Open research estimate:** a bounded cofinal subsequence of candidate
  full energies, or the required bounded cofinal normalized residual tails.
- **Not proved:** vanishing projection residual, convergence of optimal
  errors to zero, or RH.
- The quantitative epsilon/log refinement, the dual-Gram comparison
  obstruction, and the signed-covariance optimization are not newly
  formalized in these modules.

All new proof declarations have explicit hypotheses. No `sorry`, `admit`,
new axiom, or unsafe declaration is used. The ordinary mathematical
foundations reported by the checked core axiom audits are `propext`,
`Classical.choice`, and `Quot.sound`; these do not discharge the explicit
arithmetic hypotheses.

# Residual-projection estimate investigation — 14 November 2026

## Status of the requested estimate

The requested uniform estimate

\[
\|P_{W_L}r_L\|^2\ge \frac{\|r_L\|^2}{C\log L}
\]

**remains open for the actual arithmetic correction spaces.** This development
does not prove RH. It adds unconditional lower bounds that retain the signed
head obstruction, and makes the consequence of a proposed logarithmic gain
precise for the actual full-Q projections.

The correction space must be specified. A residual is orthogonal to its
current approximation space, so that space gives zero projection. For a
nested enlargement, the relevant correction space is the later space (or
equivalently its component orthogonal to the old space).

## Actual two-seed Pareto lower bounds

Module: `RH/CoupledResidualHeadBounds.lean`.
Namespace: `RiemannResearch.RH.Pareto.CoupledResidual`.

Use the existing actual two-seed budgets, not substitute Hilbert spaces:

\[
r_M=\mathbf1-P_{V_M}\mathbf1,\quad E_M=\|r_M\|^2,\quad
G_M=E_M-E_{2M}=\|P_{V_{2M}}r_M\|^2.
\]

Define the exact earlier-scale gains

\[
D_{M,p}=E_{\lfloor M/p\rfloor}-E_{\lfloor2M/p\rfloor},\qquad
T_M=2D_{M,2}+3D_{M,3},
\]

and the explicit lower sources

\[
B_{M,2}=(2-\sqrt2)E_M-r_M(1),
\]
\[
B_{M,3}=3E_M-\frac32r_M(1)-\frac12r_M(2)
 -\sqrt3\,\|r_M\|\,\|r_{\lfloor2M/3\rfloor}\|,
\qquad H_M=[B_{M,2}]_+^2+[B_{M,3}]_+^2.
\]

The new unconditional results are

\[
[B_{M,2}]_+^2\le2D_{M,2}G_M,\qquad
[B_{M,3}]_+^2\le3D_{M,3}G_M,\qquad H_M\le T_M G_M.
\]

When `T_M > 0`, this gives `G_M ≥ H_M / T_M`.
The undivided bounds also cover zero trace. Zero trace does not imply that
every other fresh direction has zero gain.

Proof: retain the imported complete signed source identities; bound only
the dilation correlation by Cauchy–Schwarz and the exact dilation norm;
then use the imported actual interscale source inequalities. Thus the head
coordinates are not discarded, and the positive parts may be zero.

Principal declarations:

- `binaryHeadLower_le_source`, `ternaryHeadLower_le_source`.
- `binary_positivePart_gain`, `ternary_positivePart_gain`.
- `headSourceSquare_le_sourceSquare`, `headSourceSquare_le_trace_gain`.
- `gain_ge_headSourceSquare_div_trace`.
- `projected_error_norm_sq_eq_gain`.
- `residual_projection_ge_head_certificate`.
- `binary_head_obstruction_of_zero_gain`.
- `logarithmic_gain_of_head_certificate`.

The final theorem consumes the explicit sufficient certificate
`E_M T_M ≤ C log(L) H_M`, with `C > 0`, `L > 1`, and `T_M > 0`.
**Open:** prove such certificates uniformly, or establish the desired gain
by a sharper signed-source argument. No uniform positive head estimate is
asserted. This sufficient certificate need not be necessary.

## Exact scalar loss accounting and quantitative exhaustion

Module: `Analysis/ResidualLossBounds.lean`.
Namespace: `RiemannResearch.Analysis.ResidualGain`.

`loss_accounting` preserves the full equality

\[
d_0=d_n\left(1+\sum_{i<n}a_i\right)
 +\sum_{i<n}a_i(d_i-d_n)
 +\sum_{i<n}(d_i-d_{i+1}-a_i d_i).
\]

For nonnegative energies and `a_i d_i ≤ d_i-d_(i+1)`, the verified finite
bound is

\[
d_n\le d_0\exp\!\left(-\sum_{i<n}a_i\right).
\]

For nonnegative `a_i`, eventual lower-loss inequalities and nonsummability
of `a` imply `d_n → 0`. Finite termination is allowed; no strict residual
positivity or bound `a_i ≤ 1` is required. A nonzero limiting residual forces
infinitely many failures of every such nonsummable proposed loss bound.

Principal declarations: `residual_mul_one_add_cumulative_loss_le`,
`residual_le_div_one_add_cumulative_loss`,
`residual_le_exp_neg_cumulative_loss`,
`tendsto_zero_of_cumulative_loss`, `tendsto_zero_of_not_summable_loss`,
`tendsto_zero_of_eventually_not_summable_loss`, and
`frequently_loss_lt_of_nonzero_limit`.

## Actual full-Q assembly and scale condition

Module: `RH/QFullResidualProjectionBounds.lean`.
Namespace: `RiemannResearch.RH.QFullResidualCorrectionCost`.

These are the original complete-Q inverse-Gram candidates, with all
conductors 2 through N+1 at stage N. For N ≤ M the exact identity is

\[
\|P_{V_M}r_N\|^2=\|r_N\|^2-\|r_M\|^2.
\]

The conditional theorem `riemannHypothesis_of_logarithmic_projection_gain`
requires a monotone stage sequence N_j, C > 0, L_j > 1, the eventual actual
projection lower bound, and

\[
\sum_j\frac1{C\log L_j}=\infty.
\]

It proves RH through vanishing of the actual residual and the already
established implication from full-Q closure membership. It does not assume
an RH-to-density provider. Cofinality of N_j is unnecessary once vanishing
error has been obtained. Cofinality of the scale L_j alone does not prove
the reciprocal-logarithm divergence condition.

Other declarations: `projected_residual_energy_eq_difference`,
`riemannHypothesis_of_residual_energy_tendsto_zero`,
`residual_energy_le_exp_neg_projection_loss`,
`riemannHypothesis_of_eventual_nonsummable_projection_gain`, and
`frequently_logarithmic_projection_bound_fails_of_not_RH`.

**Open:** the lower projection gain for these actual arithmetic vectors.
The scalar and Hilbert-space consumers do not discharge that input.

## Published bounds checked during the investigation

- Burnol, *A lower bound in an approximation problem involving the zeros of
  the Riemann zeta function*, Adv. Math. 170 (2002), 56–70,
  <https://arxiv.org/abs/math/0103058>. This is a lower bound on remaining
  Nyman–Beurling approximation error, not on the gain from one enlargement.
- Bettin–Conrey–Farmer, *An optimal choice of Dirichlet polynomials for the
  Nyman–Beurling criterion*, Theorem 1,
  <https://arxiv.org/html/1211.5191v1>. Its optimal logarithmic approximation
  theorem assumes RH and a negative-moment estimate for zeta derivatives
  at the zeros. It cannot serve as an unconditional provider here.

These source comparisons are literature review, not a new Lean
formalization of the cited analytic theorems.

Even an asymptotic E(N) ~ kappa/log N would not by itself imply the proposed
local dyadic gain. As an elementary scalar example, put
E(N)=kappa/(2j log 2) for 4^j ≤ N < 4^(j+1), j≥1. It has that asymptotic,
with O(1/log² N) error, while E(4^j)-E(2·4^j)=0. This observation is informal
and concerns generic decreasing energy sequences, not a counterexample to
the actual arithmetic residual bound.

## Verification

The new modules contain no domain-specific axioms or unfinished proofs.
Focused Bazel/BuildBuddy checks precede the final checkpoint, which must
validate the full project before publication. The final chat records the
terminal checkpoint job and exact published commit. Conditional theorem
types still contain the gain/certificate hypotheses listed above.

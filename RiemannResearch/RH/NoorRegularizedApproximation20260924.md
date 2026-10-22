# Finite arithmetic shifted lifts: unconditional convergence and the missing rate

Date: 2026-09-24.
Continuation of commit `8a7abbde985f0c4e39e1dc75bfc574b4aa45e914`;
source workspace base `03fe9ad489706ef2005b61762f4d0281b69ec0c6`.

## Established bridge

At repository stage N, let

\[
U_N=\operatorname{span}\{\operatorname{hardyCoordinates}(g_2),\ldots,
\operatorname{hardyCoordinates}(g_{N+1})\},\qquad
a_N=\operatorname{hardyCoordinates}(\mathbf1-\operatorname{projection}(N)).
\]

Thus stage zero is the zero subspace. Let S be the unilateral right shift,
D=I-S, and define, retaining the complete Hilbert norm,

\[
J_N(t)=\inf_{v\in U_N}\{\|Dv-a_N\|^2+t^2\|v\|^2\}.
\]

The new unconditional arithmetic statement is

\[
\boxed{\quad t_N\longrightarrow0
\quad\Longrightarrow\quad J_N(t_N)\longrightarrow0.\quad}
\]

It holds along every cutoff N, for every prescribed vanishing real parameter
schedule. Positivity is not needed for this convergence assertion. If
t_N>0, each infimum is attained, and there is a family v_N in U_N with

\[
\boxed{\quad
\|Dv_N-a_N\|^2+t_N^2\|v_N\|^2=J_N(t_N)\longrightarrow0.
\quad}
\]

This supplies the requested cofinal finite arithmetic family with cutoff
N_j=j, and is stronger than selecting an unspecified cofinal subsequence.
For example it applies to t_N=1/(N+1). Selection of minimizers is
noncomputable; no effective cutoff or coefficient bound is asserted.

The inputs are already proved arithmetic shifted density and unconditional
convergence of the finite projection residuals. There is no hypothesis of
RH, unshifted density, actual-residual regularity, or a quantitative
arithmetic rate.

## Why the bridge is unconditional

Write a=hardyCoordinates(limitResidual). The existing projection theorem
gives a_N -> a, whether or not a=0. Noor.shiftedResidue_density gives, for
every positive epsilon, a single finite lift v in some U_M with
\|Dv-a\|^2 < epsilon. Nestedness gives v in U_N for all N >= M. For that
fixed lift, continuity gives

\[
\|Dv-a_N\|^2+t_N^2\|v\|^2\longrightarrow\|Dv-a\|^2.
\]

The minimum is nonnegative and at most this competitor's energy at every
N >= M. Since epsilon was arbitrary, J_N(t_N) tends to zero. The proof
never exchanges uncontrolled limits or assumes a bound on the selected
minimizers' norms.

For t>0, the energy is coercive on the finite-dimensional U_N. A minimum
is obtained on a closed ball. This discharges attainment without a
normal-equation hypothesis. The general theorem
regularizedInf_eq_norm_sq_sub_pairing also connects the infimum to the
exact normal-solution formula from commit 8a7abbde whenever such a
solution is supplied.

## Exact remaining arithmetic rate

Set E_N=\|a_N\|^2. Orthogonality of the actual finite residual and
isometry of S give the verified inequalities

\[
\boxed{\qquad E_N\le\frac{1+t}{t}J_N(t),\qquad
\frac{E_N}{1+t}\le\frac{J_N(t)}{t}\quad(t>0).\qquad}
\]

Here E_N tends to \|limitResidual\|^2 unconditionally. Thus a nonzero
limit residual imposes a positive limiting lower bound on the divided
energies even though the unscaled energies vanish.

The precise missing provider is a cofinal sequence N_j and positive
t_j -> 0 such that

\[
\boxed{\qquad \frac{J_{N_j}(t_j)}{t_j}\longrightarrow0.\qquad}
\]

The new Lean reduction proves that this provider forces limitResidual=0
and then Mathlib.RiemannHypothesis. It does not construct this provider.
For the particular choice t_j=1/(j+1), the missing assertion is exactly
(j+1)J_{N_j}(1/(j+1)) -> 0. The stronger proposed bound
J_{N_j}(1/(j+1)) <= 1/(j+1)^2 would suffice but remains unproved.

Vanishing t_N\|v_N\| follows from the established unscaled energy
convergence; it does not give vanishing
\|Dv_N-a_N\|\|v_N\|. No unconditional zero-residual or RH result has
been obtained. No RH converse is claimed.

## Lean declarations

- Analysis/CoefficientShift.lean:
  rightShiftLinear and rightShift_norm.
- Analysis/ShiftedLiftApproximation.lean:
  regularizedInf, regularizedInf_tendsto_zero,
  finite_lift_approximation_of_dense,
  exists_regularizedEnergy_minimizer,
  regularizedInf_eq_norm_sq_sub_pairing.
- RH/NoorRegularizedApproximation.lean, namespace
  RiemannResearch.RH.Pareto.Noor:
  finiteMinimum_tendsto_zero, exists_finite_minimizing_lifts,
  energy_le_scaled_finiteMinimum, energy_div_le_finiteMinimum_div,
  residual_zero_of_finiteMinimum_div_parameter_tendsto_zero,
  riemannHypothesis_of_finiteMinimum_div_parameter_tendsto_zero.

The complete candidate group passed Lean with exit code 0. Axiom inspection
of finite attainment, the arithmetic convergence theorem, the minimizing
family, the rate obstruction, and the RH reduction reported only
propext, Classical.choice, and Quot.sound. The open hrate hypothesis
remains explicit in the reduction's type; the axiom report does not
discharge it.

Source attribution: the arithmetic density input is the repository's
formalization of S. Waleed Noor, "A Hardy space analysis of the Baez-Duarte
criterion for the RH", Theorem 9, https://arxiv.org/abs/1809.09577.
The new minimization and limiting arguments are elementary deductions
from the inspected repository results; no mathematical novelty is claimed.

# Literature routes for the remaining squarefree-closure providers

Search date: 2026-10-09.

## Search result

The reviewed literature supplies nearby RH criteria and lower bounds, but no
source located here proves the repository's remaining squarefree-only converse
or the positive signed-correction decay for its actual optimizer stages. The
references below therefore guide provider work; none is treated as a Lean
hypothesis discharged by citation.

## Integer-dilation criterion

Luis Báez-Duarte, “A strengthening of the Nyman-Beurling criterion for the
Riemann Hypothesis,” arXiv:math/0202141,
<https://arxiv.org/abs/math/0202141>, proves an RH-equivalent closure criterion
using all positive integer dilations of the fractional-part function.

The repository's target is closure under its squarefree residue family.
The all-integer theorem does not by itself imply membership in the smaller
squarefree-generated closure. Thus it cannot close the formal
RH-to-squarefree-approximation direction; that direction stays Open.

## Burnol's approximation lower bound

Jean-François Burnol, “A lower bound in an approximation problem involving the
zeros of the Riemann zeta function,” *Advances in Mathematics* 170 (2002),
56–70, arXiv:math/0103058,
<https://arxiv.org/abs/math/0103058>, studies a continuous Nyman-Beurling
approximation family and gives a lower bound for its distance problem.

The project proposition `BurnolDistanceLowerEnvelope` concerns a
project-specific Pareto residual distance in `CoupledResidualCorrections`.
A norm comparison or subspace identification connecting that quantity to
Burnol's continuous family is not present. The source therefore suggests a
route for a logarithmic lower-bound provider but does not close it yet.

## Recent Möbius Fourier-moment reformulation

Alberto Verjovsky, “How Random Is the Möbius Function? Smoothing, Probability,
and the Riemann Hypothesis,” arXiv:2607.25002v2 (14 August 2026),
<https://arxiv.org/abs/2607.25002>, states RH-equivalent smoothed and local
Fourier-moment criteria. The paper is a preprint and presents equivalences;
it does not establish the unconditional moment bounds required by those
criteria. It is an alternate formulation of the arithmetic difficulty, not
a provider for the current optimizer cancellation estimate.

## Formal all-stage obstruction

The new theorem
`RiemannResearch.RH.ZetaTwoOptimizerStage.secondMoment_tendsto_exact_positive_limit_of_not_mem_closure`
shows that if `qOne` is outside the closed squarefree span, the actual
normalized screened moment converges over all integer stages to the explicit
positive quotient `‖D r∞ - P_C(D r∞)‖² / ‖r∞‖²`. This is an all-stage limit
theorem; no finite list of numerical stages is used as a substitute for it.
The positive signed-correction provider needed to force the limit to zero
remains Open, so RH is not claimed.

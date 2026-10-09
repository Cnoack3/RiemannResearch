# Literature routes for the remaining squarefree-closure providers

Search date: 2026-10-09.

## Search result

Bagchi's Remarks 4 and 8 establish the squarefree-only converse at paper
level. The missing dependency is its kernel-verified analytic provider in this
repository. No reviewed source establishes positive signed-correction decay
for the actual optimizer stages. No citation is used as a Lean hypothesis
discharged by literature alone.

## Integer-dilation criterion

Luis Báez-Duarte, “A strengthening of the Nyman-Beurling criterion for the
Riemann Hypothesis,” arXiv:math/0202141,
<https://arxiv.org/abs/math/0202141>, proves an RH-equivalent closure criterion
using all positive integer dilations of the fractional-part function.

The repository's target is closure under its squarefree residue family.
The all-integer theorem does not by itself imply membership in the smaller
squarefree-generated closure. Thus it cannot close the formal
RH-to-squarefree-approximation direction; that formal provider stays Open.

## Published squarefree converse

B. Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation
of the Riemann hypothesis*, <https://arxiv.org/pdf/math/0607733>, Remark 4
(PDF p.6) identifies squarefree support of the damped Mobius approximants;
Remark 8 (PDF p.9) states the squarefree target-closure equivalence for the
exact Pareto residue model. Real coefficients suffice by taking real parts.

For Q(k)=1/(zeta(2) k^2), the full norms obey
||x||_P^2 <= zeta(2)||x||_Q^2 <= 2||x||_P^2. Thus identical squarefree
approximants converge in either norm. Their Gram matrices are not identified.
The published analytic converse is established; its unconditional kernel
provider remains Open. Squarefree target membership does not assert
squarefree totality in the ambient Hilbert space.

See RH/TargetSpecificReciprocalAdvance20261009.md.

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

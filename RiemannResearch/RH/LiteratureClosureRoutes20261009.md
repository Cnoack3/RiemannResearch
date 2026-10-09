# Literature routes for the remaining squarefree-closure providers

Search date: 2026-10-09.

## Search result

Bagchi's Remarks 4 and 8 establish the squarefree-only converse at paper
level. The missing dependency is its kernel-verified analytic provider in this
repository. No reviewed source establishes positive signed-correction decay
for the actual optimizer stages. No citation is used as a Lean hypothesis
discharged by literature alone.

## Bagchi proof reconstruction and formal status

Bagchi's RH-to-closure proof uses two strong limits in the Hardy space. Set
`G_d(s)=(d^(-s)-d^(-1))*zeta(s)/s` and `E(s)=1/s), and form
`H_{L,epsilon}=sum_{d<=L} mu(d)*d^(-epsilon)*G_d`. Its Mellin transform is

```text
H_{L,epsilon}(s) = zeta(s)/s *
  (sum_{d<=L} mu(d)*d^(-s-epsilon) - sum_{d<=L} mu(d)*d^(-1-epsilon)).
```

For each fixed positive epsilon, RH is used through Littlewood's uniform
estimate
`sum_{d<=L} mu(d)*d^(-s) = O((|t|+1)^delta)`, uniformly in L and
Re(s) > 1/2 + eta, together with the RH Lindelof bound for zeta(s). These
give an integrable majorant on the critical line. Dominated convergence
then yields H_{L,epsilon} -> H_epsilon in H², where

```text
H_epsilon(s) = zeta(s)/s *
  (1/zeta(s+epsilon) - 1/zeta(1+epsilon)).
```

For epsilon down to zero, the proof uses the RH Hadamard product inequality
|xi(s)| <= |xi(s+epsilon)|, Stirling's bound for the Gamma ratio, and
Lindelof again to obtain |H_epsilon(s)| <= C*|s|^(-3/4), a
square-integrable majorant. This gives H_epsilon -> E in H². Bagchi's
Remark 4 restricts each finite cutoff to squarefree d because mu(d)=0
off squarefree support. Theorem 7's Mellin isometry and Remark 8 transfer the
limit to the discrete squarefree residue closure.

The repository now has unconditional formal bridges for the finite and
Hilbert-space parts:

- `bagchiMobiusCutoff` is the explicit finite cutoff in the actual Pareto
  residue Hilbert space; `bagchiMobiusCutoff_eq_squarefree` proves its exact
  squarefree support, and `bagchiSquarefreeMobiusCutoff_mem` proves packet
  membership.
- `squarefreeCenteredApproximation_of_bagchi_two_stage_limit` transfers the
  two displayed strong limits to the exact repository target. The limits
  themselves remain explicit theorem premises; no analytic estimate is an
  axiom.
- The Pareto and inverse-square weights now have both pointwise and complete
  norm comparisons: `P(k) <= zeta(2)*Q(k) <= 2*P(k)`.
- The finite Bagchi cutoffs need not have ordinary mean one individually.
  The existing fresh-prime repair proves equality of unrestricted and
  mean-one squarefree closures, and the new limit transfer also concludes
  `MeanOneSquarefreePacketApproximation`.

A repository search found no checked provider for Littlewood's uniform
truncated reciprocal-zeta estimate, the RH Lindelof bounds, or the uniform
Hadamard/Gamma domination needed for the two limits. The required
`RiemannHypothesis -> SquarefreeCenteredApproximation` theorem therefore
remains Open. This work does not address optimizer cancellation or prove RH.
See Bagchi, proof of Theorem 2, Lemma 3 and Remarks 4 and 8:
<https://arxiv.org/pdf/math/0607733>.

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

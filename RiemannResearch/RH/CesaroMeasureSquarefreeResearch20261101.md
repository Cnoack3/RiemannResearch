# Cesàro averaging under P, Q, and squarefree restrictions

1 November 2026. Source: the user's request to advance the conditional-iid
Cesàro program using P/Q change of measure and squarefree structure.
This continues `ConditionalIIDCesaroResearch20261101.md`.

## Answer and distinctions

For positive physical sample indices,
$$
P(n)=\frac1{n(n+1)},\qquad Q(n)=\frac1{\zeta(2)n^2},\qquad
(Cg)(n)=\frac1n\sum_{k=1}^n g(k).
$$

The ordinary Cesàro operator is bounded in both marginal Hilbert spaces.
It is a conditional-expectation contraction when the output is measured
with the corresponding latent-endpoint law. These are different statements.

| Setting | What is established |
| --- | --- |
| All conductors, P or Q | The same ordinary C is bounded; a uniform-interval conditional-iid model exists under either marginal. |
| Squarefree conductors, all sample indices retained | The same bounds and normalized RH reduction apply to these legal inputs. |
| Preservation of the squarefree conductor closure | False for C, even after adjoining constants; a conductor-2 counterexample is checked. |
| Sample law conditioned to squarefree integers | Ordinary C does not descend to equality on this support; it uses values at nonsquarefree sites. |

Squarefree conductors include composite squarefree conductors.
Changing the measure does not enlarge that dictionary to all conductors,
and equivalent norms do not identify the two orthogonal projections.
The existing `QSquarefreeMeasureRigidity.lean` makes this last distinction precise.

## Exact Q mixture and full probability-space change of law

Write z=ζ(2). The new positive endpoint distribution is
$$
\lambda_Q(n)=n\bigl(Q(n)-Q(n+1)\bigr)
 =\frac{2n+1}{z n(n+1)^2}.
$$
The previously constructed Pareto endpoint law is
$$
\lambda_P(n)=\frac2{(n+1)(n+2)}.
$$

`RH/QUniformMixture.lean` proves normalization and the complete marginal identity
$$
\sum_{t=n}^{\infty}\frac{\lambda_Q(t)}t=Q(n).
$$
Its finite versions retain the terminal terms:
$$
\sum_{t=1}^N\lambda_Q(t)=\sum_{t=1}^NQ(t)-NQ(N+1),
\qquad
\sum_{t=n}^{n+R-1}\frac{\lambda_Q(t)}t=Q(n)-Q(n+R).
$$

`Probability/QConditionalIIDModel.lean` constructs an actual infinite-path
probability measure, reusing the existing uniform iid path kernel.
It proves the exact global measure identity
$$
\mathbb Q=\mathbb P.\mathrm{withDensity}\bigl(r(T)\bigr),
\qquad r(n)=\lambda_Q(n)/\lambda_P(n),
\qquad \frac1z\le r(n)\le\frac9{4z}.
$$
The marginal of every row is Q, the rows are conditionally independent given T,
and the conditional mean of every integrable arithmetic observable is Cg(T).
The density depends on T alone; no conditional kernel is replaced.

The two full path measures have the same almost-sure properties.
`Probability/QConditionalIIDLimits.lean` therefore transfers:
- the simultaneous strong law, on one event for every real arithmetic observable;
- eventual recovery of T from the running maximum of the observations.

These are statements about the constructed measures, not abstract model hypotheses.

## Complete energy identity and moving-head improvement

For the *same* arithmetic input g, define
$$
J_P(g)=\sum_{n\ge1}\lambda_P(n)(Cg(n))^2,\qquad
J_Q(g)=\sum_{n\ge1}\lambda_Q(n)(Cg(n))^2.
$$
In Lean these are `Pareto.conditionalMeanSquare` and
`QCesaroEnergy.qConditionalMeanSquare`.

The new exact identity is
$$
zJ_Q(g)-J_P(g)=
\sum_{n\ge1}\frac{3n+2}{n(n+1)^2(n+2)}(Cg(n))^2.
$$
All tail terms remain present. The two energies have the same summability domain, and
$$
\frac49zJ_Q(g)\le J_P(g)\le zJ_Q(g).
$$

There is a stronger comparison when Cg vanishes through H:
$$
z\frac{H+1}{H+3}J_Q(g)\le J_P(g)\le zJ_Q(g).
$$
It comes from the exact identity
$$
\lambda_P(n)=\frac n{n+2}z\lambda_Q(n)
+\frac1{(n+1)^2(n+2)}.
$$
Thus the complete latent norms on a moving zero-head error become equivalent
with ratio tending to z, not merely a fixed coarse comparison factor.

`RH/QCesaroEnergy.lean` also proves finite and infinite Q contractions.
The exact finite formula retains both Jensen deficits and the boundary:
$$
\sum_{n=1}^N Q(n)g(n)^2
=\sum_{n=1}^N\lambda_Q(n)(Cg(n))^2
 +\sum_{n=1}^N\lambda_Q(n)\bigl(C(g^2)(n)-(Cg(n))^2\bigr)
 +Q(N+1)\sum_{n=1}^N g(n)^2.
$$

## Same-marginal bounds and noncontraction

`RH/CesaroSameMeasureBounds.lean` proves
$$
\|Cg\|_P^2\le\tfrac32\|g\|_P^2,\qquad
\|Cg\|_Q^2\le\tfrac43\|g\|_Q^2.
$$
No optimality of these constants is asserted.
For g=1_{\{1\}}, Cg(1)=1 and Cg(2)=1/2: the first output coordinate already
retains the entire input energy, and the second adds strictly positive energy.
The complete infinite-sum proof establishes strict expansion under both marginal
laws. Consequently neither same-marginal map is a contraction.

## RH consumer, including the explicit squarefree family

`Analysis/LowerLogGrowthComparability.lean` establishes the general comparison
principle for the extended nonnegative lower logarithmic growth definition:
for nonnegative E,F, H tending to infinity, and eventual fixed multiplicative
comparisons in both directions,
$$
\operatorname{lowerLogGrowth}(E,H)=0
\quad\Longleftrightarrow\quad
\operatorname{lowerLogGrowth}(F,H)=0.
$$

`RH/QCesaroLowerGrowth.lean` applies this to the normalized complete energies
$$
\frac{J_P(g_j)}{|c_j|^2},\qquad
\frac{J_Q(g_j)}{|c_j|^2}.
$$
The zero-growth criterion is unchanged by this measure change.
For legal g_j, exact heads g_j(n)=c_j for 1≤n≤Y_j, Y_j tending to infinity,
and c_j≠0, zero lower growth of the Q-latent energy implies the actual Mathlib
`RiemannHypothesis`. No positive lower bound on |c_j| is required.

The specialized theorem
`riemannHypothesis_of_mobiusHead_q_lower_growth` uses the explicit
`squarefreeMobiusHead` family from the preceding agenda. Choosing squarefree
repair conductors gives the established literal squarefree support. The consumer
is more general and only needs repair conductors beyond the exact head.

Classification: **conditional research reduction**.
**Open:** a checked arithmetic provider of zero lower growth for an actual
cofinal legal family, including the explicit Möbius family or signed repair averages.
The comparison theorem transports this obligation; it does not discharge it.

## A checked obstruction to preserving the squarefree space

Let g(n)=(n mod 2)/2, a genuine squarefree-conductor residue.
Its four averaged values are
$$
Cg(1)=\tfrac12,\quad Cg(2)=\tfrac14,\quad
Cg(3)=\tfrac13,\quad Cg(4)=\tfrac14.
$$
The square-jump functional gives
$$
(Cg(4)-Cg(3))-(Cg(2)-Cg(1))=\tfrac16.
$$
The existing square-jump witness annihilates the entire squarefree closure
even after constants are adjoined.

`RH/SquarefreeCesaroObstruction.lean` proves, for every f in that enlarged closure,
the complete orthogonal decomposition
$$
\|Cg-f\|_Q^2=\frac1{1080z}+
\left\|Cg-f-\frac{W_2}{180z}\right\|_Q^2.
$$
It also retains the exact P/Q norm correction and proves
$$
\|Cg-f\|_P^2\ge\frac1{2160}.
$$
Thus working with Cesàro-smoothed squarefree inputs requires their image space.
One cannot silently reuse the unsmoothed squarefree projection.
This does not obstruct the RH consumer: legality is required of the input g,
not of its Cesàro mean Cg.

For the separate sample-support restriction, δ_4 vanishes at every squarefree
integer but Cδ_4(5)=1/5. This proves that ordinary Cesàro does not preserve
equality restricted to squarefree samples. A prescribed zero extension or a mean over squarefree sample sites
would define a different operator and has not been supplied as an RH criterion here.

## Research consequence

The promising route is to optimize the complete Cesàro energy of legal
squarefree exact-head inputs in their actual smoothed image, retaining all
signed Gram terms, Jensen deficits, and endpoint remainders. Q offers a genuine
alternate probability model and exact inverse-square marginals; it cannot
improve the zero-growth condition of a fixed family merely by reweighting.

Still Open in this continuation:
- the cofinal arithmetic energy-growth provider;
- the agenda's localized dyadic energy estimate;
- any RH-to-density converse beyond those already present in the project.

No unconditional RH proof, equality of P/Q optimizers, or preservation of
the squarefree conductor closure is asserted.

## Formal verification

All eight saved modules passed import job
`job_LDrF17e3Q5mU1RjSymaTNbOGdsVwCRIj` (exit 0; reported server verification
duration 16.964 seconds).
The 18-endpoint axiom/type audit `job_LOP7tu-AcCKROV85zTY1M9mza-XpaFR-`
passed (exit 0; 5.125 seconds). A short supplementary audit
`job_aPKHRHs2QjdHrRC-eEYy-IejEtdX-jVu` retained the two results omitted from the
long output tail. The audited endpoints use only `propext`,
`Classical.choice`, and `Quot.sound`; no project-specific axiom is present.
The two displayed RH theorem types retain their actual arithmetic growth premise.

These durations are server verification reports, not workspace-opening,
transport, queue, or polling latency. The existing workspace was resumed at
commit `6b53ff6d66ca30dee9b96eb8f07ebf48c5975e94`.
Publication integration preserves newer main work through
`055e8e41beb7da54a55b1daeda022f1785510b10`; the eight Lean sources are unchanged
from the audited versions.

Only the terminal successful publication checkpoint certifies the aggregate
project and exact published source. Its commit and validation scope are supplied
with the final response; the saved-module audit alone is not a whole-project claim.


Historical context only: Luis Báez-Duarte,
[A strengthening of the Nyman–Beurling criterion for the Riemann hypothesis, 2](https://arxiv.org/abs/math/0205003).
The P/Q identities and the concrete Cesàro squarefree obstruction above were
developed from the user's question and existing checked project declarations;
this reference supplies background, not a proof of the remaining arithmetic bound.

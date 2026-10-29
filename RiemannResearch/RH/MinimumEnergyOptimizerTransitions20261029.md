# Minimum-energy optimizer transitions and prediction budgets

29 October 2026. Research continuation of the supplied **RH Minimum Energy Optimizer Research Agenda**.

## Result and unresolved objective

The complete signed recurrence, its physical squarefree realization, and an actual arithmetic transition bound are formalized. The new nested schedule has head \(H=i+1\) and conductor dictionary consisting of the divisors of \(\operatorname{primorial}(2H)\). Its head-extension costs satisfy

\[
 C_i\le \frac{4b_i^2}{\zeta(2)(i+1)},\qquad
 E_N\le E_0+\frac4{\zeta(2)}
       \sum_{i<N}\frac{b_i^2}{i+1}-\sum_{i<N}G_i.
\]

Here \(b_i\) is the next physical-site mismatch of the actual old-head minimum after dictionary enlargement, and \(G_i\) is the actual complete energy saved by that enlargement. All feasibility and nearby-prime existence conditions are discharged. If \(i+2\) is not squarefree, then \(b_i=C_i=0\).

A separate Lean theorem proves that a uniform bound on these actual \(b_i\) implies RH. More generally it is enough that the displayed nonnegative prediction budget has subpolynomial growth. Neither arithmetic premise has been proved. No uniformly bounded cofinal energy family, vanishing residual, or unconditional proof of RH is claimed.

The attached agenda has therefore been addressed at every step, but its central open arithmetic objective remains open.

## 1. Source reconciliation

The workspace began from main at [c72b4967335f32894cac0ef61f14f97560473a49](https://github.com/Cnoack3/RiemannResearch/commit/c72b4967335f32894cac0ef61f14f97560473a49), later than the handoff's pinned 35ef0f4 baseline. Current source already contained substantial parts of the proposed infrastructure.

| Existing module | Reused result |
| --- | --- |
| [AffineEnergyMinimum](../Analysis/AffineEnergyMinimum.lean) | Affine minimum iff orthogonality to its tangent |
| [FiniteGramRange](../Analysis/FiniteGramRange.lean) | Range solvability for a finite-dimensional self-adjoint operator |
| [FiniteFeasibleGramRepair](../Analysis/FiniteFeasibleGramRepair.lean) | Completion for feasible, potentially dependent finite observations |
| [QPrimorialOptimizerCoalescence](QPrimorialOptimizerCoalescence.lean) | Actual Q/P minimizers, prime schedule, legality, exact heads, and coalescence |
| [QCRTPeriodHeadBalance](QCRTPeriodHeadBalance.lean) | Complete-norm minimumAt, exact period gain/head cost, signed recurrence, telescope |
| [QCRTMinimumHeadCost](QCRTMinimumHeadCost.lean) | Exact one-site cost from complete-Q capacity, including coefficient mismatch |
| [QSquarefreeHeadStep](QSquarefreeHeadStep.lean) | Literal compensated residue direction and complete infinite-tail norm bound |
| [QSquarefreeFiniteDualClosure](QSquarefreeFiniteDualClosure.lean) | Radical compatibility of legal vectors |
| [QSquarefreeExactHeadResidualBarrier](QSquarefreeExactHeadResidualBarrier.lean) | Bounded cofinal exact-head subsequence kills the fixed residual; nonzero residual forces energy divergence |
| [QSquarefreeCapacity](QSquarefreeCapacity.lean) | Closure/capacity identification and checked forward RH consumer |
| [QExactHeadSubpolynomial](QExactHeadSubpolynomial.lean) | Subpolynomial complete-error criterion via Mellin zeros |
| [QSquarefreeQuantitativeRepair](QSquarefreeQuantitativeRepair.lean) | Actual signed finite repair operator and error amplification |

The exact period/head recurrence and residual argument are thus reused results, not first established by this continuation. The additions identify the agenda's tangent projection and actual head-observation Gram system, connect the optimizer implementations, and derive a discharged nearby-anchor estimate for a specified dense schedule.

Earlier finite certificates and their validation status are unchanged.

## 2. General affine transition and the prime schedule

[Analysis/AffineEnergyTransition.lean](../Analysis/AffineEnergyTransition.lean) defines
\[
 \operatorname{minimumOff}(K,F)=F-\Pi_KF.
\]
It proves normal equations, uniqueness, exact completion with a squared remainder, and the enlargement/extension decomposition. With \(N\subseteq K\), \(G-F\in K\), \(u=\Pi_KF\), \(Z=F-u\), and \(s\) the least-norm member of \(G-Z+N\),
\[
 F_{\rm next}=Z+s,\qquad
 \|F_{\rm next}\|^2-\|F\|^2=\|s\|^2-\|u\|^2.
\]
The signed cross term is retained explicitly. This is a Hilbert projection theorem; it does not estimate an arithmetic sequence of gains or costs.

[RH/QPrimorialEnergyTransition.lean](QPrimorialEnergyTransition.lean) instantiates the construction with
\[
 K_{H,J}=\operatorname{span}\{g_d:d\mid\operatorname{primorial}(J+1)\}
                   \cap\ker P_H,\qquad H\le J,
\]
assuming squarefreeness of \(H+1\) and \(J+1\). These assumptions hold at every prime-schedule stage.

The module proves:

- Monotonicity of the least-prime anchor and its head schedule.
- Feasibility, enlarged old-head normal equations, and the unique least-energy extension correction.
- The exact complete-Q energy identity and its signed cross-term form.
- Equality of qOptimizer \(H\) with minimumAt \((H-1)\,H\) when \(H\ge1\) and \(H+1\) is squarefree. This bridges two existing implementations of the same minimum.
- The prime-schedule telescope and equivalence between bounded energy and bounded cumulative net increments.
- Conditional residual/RH consequences of bounded cumulative net increments or summable positive parts.

Repeated primes cause repeated stages and zero transition; strict increase is unnecessary.

For the actual Q/P minima on the same affine feasible set, the new comparison theorem proves
\[
 \zeta(2)E_{Q,j}\le 2E_{P,j},\qquad E_{P,j}\le\zeta(2)E_{Q,j}.
\]
Here \(E_{P,j}\) is the squared Pareto norm of the P-minimizer. Thus boundedness transfers in either direction. These inequalities and existing coalescence do not supply boundedness.

## 3. Actual complete-Q observation Gram system

[Analysis/AdjointConstraintMinimum.lean](../Analysis/AdjointConstraintMinimum.lean) proves that for a real Hilbert continuous linear map \(A:E\to F\), any solution
\[
 AA^*y=b
\]
produces the unique least-norm solution \(s=A^*y\) of \(Ax=b\), with
\[
 \|s\|^2=\langle b,y\rangle,\qquad
 \|x\|^2=\|s\|^2+\|x-s\|^2 \quad(Ax=b).
\]
If the observation space \(F\) is finite-dimensional, feasibility \(Ax=b\) proves existence of such a multiplier. Different multipliers give the same minimizing vector. No invertibility or row independence is assumed.

[RH/QPrimorialExtensionGram.lean](QPrimorialExtensionGram.lean) defines the literal physical map
\[
 A_{H,J}:K_{H,J}\longrightarrow\mathbb R^{J-H},
 \qquad (A_{H,J}x)_i=x(H+i+1),
\]
with the inherited complete-Q inner product on its domain and the Euclidean metric on its codomain. It proves:

1. The actual extension correction has observations \(b_i=1-Z(H+i+1)\).
2. Equal observations leave precisely a zero-full-head tangent difference.
3. A Gram multiplier exists for these actual data.
4. Every solved Gram equation yields this same extension correction.
5. The signed transition becomes
   \[
   E_J-E_H=\langle b,y\rangle-\|\Pi_{K_{H,J}}F_H\|_Q^2.
   \]

This realizes the handoff's matrix formulation without selecting or constructing a Moore–Penrose pseudoinverse. It is equivalent to using any feasible Gram multiplier, and remains valid for dependent physical head constraints. No finite-prefix norm substitutes for the complete infinite-tail norm.

As an external exact algebra sanity check, Wolfram evaluated the singular finite system
\[
 G=\begin{pmatrix}2&1&0\\1&3&1\\0&1&2\end{pmatrix},\quad
 A=\begin{pmatrix}1&0&1\\0&1&1\\1&1&2\end{pmatrix},\quad
 b=(1,2,3)^{\mathsf T}.
\]
For \(M=AG^{-1}A^{\mathsf T}\), its rank is two and
\(s=G^{-1}A^{\mathsf T}M^\dagger b=(-2,5,9)^{\mathsf T}/7\).
The exact checks give \(As=b\), orthogonality to \(\ker A\), and
\(s^{\mathsf T}Gs=b^{\mathsf T}M^\dagger b=45/7\).
This is an abstract finite sanity check, not a numerical certificate for an actual squarefree stage. The Lean results do not rely on it.

## 4. A genuine nested arithmetic transition family

[RH/QSquarefreeEnergyTransitions.lean](QSquarefreeEnergyTransitions.lean) defines
\[
 \sigma(i)=2i,\quad
 F_i=\operatorname{minimumAt}(2i,i+1),\quad
 Z_i=\operatorname{minimumAt}(2i+2,i+1).
\]
Thus \(F_i\) is the complete-Q minimum at head \(i+1\) in the divisor dictionary of \(\operatorname{primorial}(2i+2)\); \(Z_i\) is the old-head minimum in the next dictionary. Define
\[
 E_i=\|F_i\|_Q^2,\quad G_i=\|F_i-Z_i\|_Q^2,\quad
 C_i=\|F_{i+1}-Z_i\|_Q^2,\quad b_i=1-Z_i(i+2).
\]
The schedule is nested, legal, feasible at every stage, and cofinal. In particular it does not incorrectly extend the canonical prime-type feasibility lemma to every head.

The existing exact recurrence gives \(E_{i+1}-E_i=C_i-G_i\). The new unconditional arithmetic estimate is
\[
 \boxed{C_i\le\frac{4b_i^2}{\zeta(2)(i+1)}}.
\]

For \(n=i+2\) squarefree, Bertrand supplies a prime \(n<r\le2n\). Both \(n\) and \(r\) divide the new primorial. The actual legal trial direction
\[
 v_{n,r}=g_n-\frac rn g_r
\]
vanishes through \(n-1\), has value \(-1\) at \(n\), and satisfies the complete-tail estimate
\[
 \|v_{n,r}\|_Q^2\le
 \frac1{\zeta(2)}\frac{(r/n)^2}{n-1}
 \le\frac4{\zeta(2)(n-1)}.
\]
The correction \(-b_iv_{n,r}\) is feasible, and the existing complete-energy capacity formula bounds the actual minimum correction by this trial cost. This does not discard the negative period gain in the recurrence.

For nonsquarefree \(n\), radical compatibility gives
\[
 F(n)-F(n-1)=F(\operatorname{rad} n)-F(\operatorname{rad} n-1).
\]
Since \(2\le\operatorname{rad}n<n\), a constant old head already forces \(F(n)=1\). Lean proves equality of the two minima, not merely a zero upper bound. Hence \(b_i=C_i=0\).

With the literal prediction budget
\[
 B_N=\sum_{i<N}\frac{b_i^2}{i+1},
\]
the checked telescope yields
\[
 \boxed{E_N\le E_0+\frac4{\zeta(2)}B_N-\sum_{i<N}G_i.}
\]
The norms, cross terms, gains, and prediction errors are all those of actual legal vectors.

## 5. What arithmetic estimate would now suffice?

There are two distinct sufficient routes.

**Bounded complete energy and constant membership.** For the prime schedule, bounded cumulative exact net increments, or summability of their positive parts, implies bounded energy. Existing fixed-residual tail convergence then gives \(r=0\) and constant membership in the closed squarefree legal span. A bounded cofinal subsequence is sufficient. Only the forward checked closure/capacity implication to RH is invoked; no claim that the full orthogonal complement vanishes is made.

**Subpolynomial prediction budget and RH.** The dense schedule need not have bounded energy for the existing Mellin-zero criterion to apply. [RH/QCRTPredictionBudget.lean](QCRTPredictionBudget.lean) proves
\[
 \frac{\log(1+B_N)}{\log(N+2)}\longrightarrow0
 \quad\Longrightarrow\quad \mathrm{RH}.
\]
It also proves the stronger-premise corollary
\[
 \boxed{(\exists B\ge0\ \forall i,\ |b_i|\le B)\ \Longrightarrow\ \mathrm{RH}.}
\]
Indeed \(B_N\le B^2\sum_{k=1}^N1/k\), so \(E_N=O(\log N)\), and
\[
 \|qOne-F_N\|_Q^2
 \le2+2E_0+\frac8{\zeta(2)}B_N.
\]
Every positive power eventually dominates this complete error. The code supplies the legal exact-head family and all normalization/cofinality hypotheses to the existing QExactHeadSubpolynomial consumer.

The logarithmic/subpolynomial route is an RH reduction. It does not use the bounded-energy residual argument to claim strong convergence or bounded energy.

The remaining quantifiers are explicit: prove the displayed limit for the literal moving budget, prove a uniform moving mismatch bound, or exploit sufficient signed gain cancellation. None has been discharged.

## 6. Why the elementary estimates do not finish the task

The exact one-site coefficient formula from QCRTMinimumHeadCost identifies the mismatch as \(a_n+\mu(n)\) for the actual enlarged old-head minimum, in its conductor expansion.

A canonical small-support exact-head vector can have \(a_n=0\), so its mismatch is bounded by \(|\mu(n)|\). That vector does not satisfy the enlarged-tangent normal equations. Reoptimization provides those normal equations but can introduce a coefficient at the new conductor. Combining the canonical coefficient value with the optimized orthogonality would use properties of different vectors.

The elementary coordinate estimate
\[
 |Z(n)|\le\sqrt{\zeta(2)}\,n\,\|Z\|_Q
\]
only gives
\[
 |1-Z(n)|^2\le2+2\zeta(2)n^2\|Z\|_Q^2.
\]
Substitution into the nearby-anchor bound is too weak to control cumulative energy. Fixed-conductor asymptotics do not control a conductor \(n\) moving with the head.

Likewise \(E_j=o(H_j)\), Q/P coalescence, fixed-input tail contraction, and finite successful energy certificates do not supply a cofinal bounded or subpolynomial energy provider. No proof step uses \(qOne\) as a finite legal competitor.

## 7. Additional paper estimate

[MinimumEnergyLinearRepairBound20261029.md](MinimumEnergyLinearRepairBound20261029.md) records an independently derived complete-norm estimate for the existing finite repair operator:
\[
 \|T_{H,p}\|_{\rm op}\le17H,\qquad
 \|qOne-\operatorname{repaired}(H,p,f)\|_Q
 \le18H\|qOne-f\|_Q
\]
when \(H\ge1\) and \(H<p\le2H\). The argument uses divisor rearrangement and weighted Cauchy–Schwarz, improving the earlier paper bound \(15H^{3/2}\) for integer \(H\ge2\).

This estimate is a paper proof, not a Lean declaration. It makes the required raw input accuracy explicit: error at most \(1/(72H^2)\) would yield a legal exact-head vector with energy at most \(1+5/(8H)\), provided the separate squarefree legality assumptions hold. Existence of such accurate raw legal inputs remains unproved.

## 8. Research task accounting

| Agenda task | Outcome |
| --- | --- |
| Reconcile current source | Completed; later recurrence, capacity, residual and subpolynomial results reused |
| Verify enlargement/extension | General projection theorem and actual prime-head instantiation formalized |
| Handle dependent Gram constraints | Actual physical observation map; feasible multiplier existence and exact energy formalized |
| Estimate actual arithmetic transitions | Dense primorial schedule, nonsquarefree zero costs, nearby-prime complete-cost bound formalized |
| Prove cofinal energy bound | Open; exact sufficient signed and prediction-budget premises isolated |
| Use Q/P comparison correctly | Complete minimum-energy comparison formalized; no boundedness inferred |
| Close residual and apply RH | Checked conditional consumers; their arithmetic premises remain unproved |

## 9. Sources and verification record

Sources are the supplied agenda, the named current repository modules, and Mathlib's adjoint, Bertrand, harmonic, and real-power asymptotic APIs. Primary literature consulted for context:

- Báez-Duarte, *A strengthening of the Nyman–Beurling criterion for the Riemann hypothesis*, [arXiv:math/0202141](https://doi.org/10.48550/arXiv.math/0202141).
- Báez-Duarte, *Arithmetical aspects of the Beurling–Nyman criterion for the Riemann hypothesis*, [arXiv:math/0011254](https://arxiv.org/abs/math/0011254).
- [Mathlib real-power asymptotics documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.html).

These references were not treated as providers of the missing squarefree moving-prediction estimate. The specialized formal theorem is checked against the repository's existing consumer.

Successful focused checks (all server jobs were serialized):

| Scope | Job | Server execution |
| --- | --- | --- |
| Prime transition and optimizer implementation bridge | job_gLrrOJg4fxIcobYEPDW5xe64nf9FnJt6 | 7.342 s |
| Dense arithmetic/harmonic bounds and generic adjoint completion | job_3151KIuwIAw1htQ3Lne3sYzp40O_KVef | 8.556 s |
| Conditional prediction-budget RH consumers | job_pxojZ0XitMeASyqtYHlpEZQ89lv7njM- | 6.585 s |
| Actual physical Gram integration, after generic feasibility build | job_M9l-8T4MbzukrrJ9k3yYfAE8ZaUHgmv- | 7.885 s |
| Saved-module import and axiom audit of all six additions | job_AiP4-z2P5_bYGQwbyF5dB1jRHB4nxbuI | 21.955 s |

The last check imported the saved modules and audited these 16 declarations:

- RiemannResearch.Analysis.AffineEnergyTransition.energy_transition
- RiemannResearch.Analysis.AdjointConstraintMinimum.exists_gram_solution_of_feasible
- RiemannResearch.Analysis.AdjointConstraintMinimum.gram_solution_completion
- RiemannResearch.RH.QPrimorialEnergyTransition.qOptimizer_eq_minimumAt
- RiemannResearch.RH.QPrimorialEnergyTransition.optimizer_energy_transition
- RiemannResearch.RH.QPrimorialEnergyTransition.energy_bounded_iff_net_sums_bounded
- RiemannResearch.RH.QPrimorialEnergyTransition.prime_minimum_measure_bounds
- RiemannResearch.RH.QPrimorialEnergyTransition.residual_eq_zero_of_frequently_bounded
- RiemannResearch.RH.QPrimorialEnergyTransition.riemannHypothesis_of_summable_positive_increments
- RiemannResearch.RH.QPrimorialExtensionGram.exists_multiplier
- RiemannResearch.RH.QPrimorialExtensionGram.optimizer_transition_of_gram_solution
- RiemannResearch.RH.QSquarefreeEnergyTransitions.minimumAt_eq_of_nonsquarefree
- RiemannResearch.RH.QSquarefreeEnergyTransitions.dense_headCost_bound
- RiemannResearch.RH.QSquarefreeEnergyTransitions.dense_energy_signed_bound
- RiemannResearch.RH.QCRTPredictionBudget.riemannHypothesis_of_bounded_nextMismatch
- RiemannResearch.RH.QCRTPredictionBudget.riemannHypothesis_of_subpolynomial_predictionBudget

Every audited declaration reported only propext, Classical.choice, and Quot.sound. No sorry, admit, unsafe declaration, or new custom axiom was introduced. The new modules are exported by the aggregate import. Existing dependency linter warnings were replayed; the saved new modules built without their earlier local linter warnings. The temporary audit snippet had two long-line warnings.

Timing categories are separate: the workspace-open request yielded after approximately 31 seconds, and total opening latency was not instrumented. The saved audit's submitted-to-started queue delay was about 0.0005 seconds; its server verification took 21.955 seconds. Status polling respected the service's 30-second minimum retry interval and was interleaved with drafting; elapsed client polling latency was not separately measured.

Two initial publication attempts (job_cvLYX04a6YvfoNlbPlu_4crFTL4YWzvQ and job_r3TPwMDIi6RzNsgJwcZKeafZDI7E0nFJ) stopped in the source audit before Lean validation: its text scan classified the prose word “admit” in the Gram-existence documentation as a placeholder. The first attempted comment edit did not apply. The comment was then successfully changed to “have” and read back; the proof term was unchanged.

These records verify the saved Lean additions, not the separate 17H paper estimate or either unproved arithmetic premise. The required final publication checkpoint separately validates the aggregate and affected-module build before committing and publishing. Its returned commit and scope identify the published result.

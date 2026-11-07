# Lean continuation handoff: crossed distances, square-root correction, and RH

Date: 6 November 2026

## Purpose and verified baseline

Continue Christian Noack's full-conductor RH research from this chat.
The original isometric-transport handoff's Section 5 has now been formalized,
with additional quadratic-error and complete-tail certificates.

Published mathematical commit:
[3473ba7c75c1306acb013d07ae4fad2257499b02](https://github.com/Cnoack3/RiemannResearch/commit/3473ba7c75c1306acb013d07ae4fad2257499b02).

The commit adds 39 theorems and 7 definitions in three new modules.
This handoff is documentation; it does not introduce additional Lean proofs.

**RH and d=0 remain unproved.** The new RH implications retain explicit
distance-decay, signed-cancellation, or second-inverse membership hypotheses.

## Resume the retained Lean workspace

- Workspace token: ws_Zc2GDeYR_6AQeljCtBv0mJCOjS-pFNK_
- Absolute project root:
  /home/cri_2025/lean-agent-workspaces/ws_Zc2GDeYR_6AQeljCtBv0mJCOjS-pFNK_/RiemannResearch
- Repository: Cnoack3/RiemannResearch.
- Branch: main.
- Last observed mathematical HEAD: 3473ba7c75c1306acb013d07ae4fad2257499b02.
- Its publication returned rehydrate_on_next_workspace_call=false.
- No verification job from this chat remains pending.

In a new chat, call agent_workspace_open once with this resume_token.
Retain the returned token and absolute root; follow a continuation workspace
if the server returns one. Inspect Git status and current main before edits.
Do not replace or reset a dirty retained workspace.

Read root AGENTS.md and the lean-research-workflow instructions. Use bounded
declaration searches, focused outlines and source reads. Serialize all Lean
verification jobs, including checks, diagnostics that launch Lean, and builds.
A timeout does not free a pending job: recover its ID and terminal status.

Publish only through agent_workspace_checkpoint with push enabled, after
its source audit and required server validation. GitHub-hosted CI is not
the verification path. Use GitHub for current sources and publication evidence.
Use symbolic tools when they materially help; basic arithmetic and algebra
should use Lean or ordinary exact computation.

## Read these files first

All paths below are relative to the project root.

| File | Role |
|---|---|
| RiemannResearch/RH/QParetoIsometricTransport.lean | The isometry A, physical action, distance and projection transport |
| RiemannResearch/RH/QParetoSquareRootEnergy.lean | T, positive energy, square identity, correction J, and tail bounds |
| RiemannResearch/RH/QFullCrossedDistances.lean | Actual residual identities, crossed bounds, head certificates, conditional RH |
| RiemannResearch/Analysis/OrthogonalDistanceBound.lean | General residual-pairing bound by distance |
| RiemannResearch/RH/QFullDisplacement.lean | Full-conductor displacement and original normal equations |
| RiemannResearch/RH/QFullCofinalHarmonic.lean | Existing d=0 to Mathlib RiemannHypothesis implication |
| RiemannResearch/RH/QFullReciprocalLimits.lean | Reciprocal defect limits and commutation criteria |
| RiemannResearch/RH/CrossedDistanceContinuation20261106.md | Detailed account of the results of this chat |

The three new modules are exported from RiemannResearch.lean.
The new catalog entry is at the end of
RiemannResearch/THEOREM_CATALOG_FULL_CONDUCTOR_20261106.md.
Do not read the complete repository theorem catalog for discovery.

## Spaces and operator types: preserve these distinctions

Let Z=zeta(2),
\[
Q(n)=\frac1{Zn^2},\qquad P(n)=\frac1{n(n+1)},\qquad n\ge1.
\]
Use all atoms g_m(n)={n/m}, m>=2.
Let V_Q and V_P be the closed spans of these same physical atoms in Q and P.

| Map | Source and target | Meaning |
|---|---|---|
| I | H_Q to H_P | Same physical sequence; Lean toPareto |
| A | H_Q to H_P | Isometry; physical multiplier sqrt((n+1)/(Zn)) |
| T=A^{-1}I | H_Q to H_Q | Physical multiplier sqrt(Zn/(n+1)); inversePhysical |
| R | H_Q to H_Q | Physical multiplier 1/(n+1); QShiftedReciprocal.B |
| J=Id-T/sqrt(Z) | H_Q to H_Q | rootDefect |

W=A(V_Q) is not identified with V_P.

Both spaces use the same normalized lp carrier. A is the identity on
encoded coordinates, but not on physical sequences. T reencodes the
same-sequence map as an endomorphism of H_Q. It is not I^{-1}.
Interpret an informal A^{-2}d physically as T(Td), retaining the intervening
same-sequence conversions.

The namespaces differ from the new filenames:
- General measure-specific additions: RiemannResearch.RH.QParetoIsometricTransport.
- Full application: RiemannResearch.RH.QFullCrossedDistances.
- General distance lemma: Submodule.

## Checked identities and estimates

Let
\[
f_Q=\Pi_{V_Q}^Q1,\quad f_P=\Pi_{V_P}^P1,\quad
d=f_Q-f_P,\quad r_Q=1-f_Q,\quad r_P=1-f_P=r_Q+d.
\]
Residuals and d use the common physical-sequence interpretation.
The actual full displacement belongs to V_Q.

Define
\[
q(f)=\langle f,Tf\rangle_Q,\quad
a(g)=\operatorname{dist}_P(Ag,V_P),\quad
b(g)=\operatorname{dist}_P(Ig,W),
\]
\[
\Delta(g)=\|r_P\|_P a(g)+\|r_Q\|_Q b(g).
\]

The general API proves symmetry of T and
\[
\sqrt{Z/2}\|f\|_Q^2\le q(f)\le\sqrt Z\|f\|_Q^2.
\]
For every g, the exact signed identity is
\[
F(g):=\langle Ir_P,Ag\rangle_P-\langle r_Q,Tg\rangle_Q
=\langle d,Tg\rangle_Q.
\]
Then F(g)<=Delta(g), and
\[
\sqrt{Z/2}\|d\|_Q^2\le\Delta(d),\qquad
d=0\iff(Ad\in V_P\ \text{and}\ Id\in W).
\]

The exact polarization and its quantitative consequence retain q(g):
\[
q(d)+q(g)=2F(g)+q(d-g),
\]
\[
\boxed{\sqrt{Z/2}\|d\|_Q^2+q(g)
\le2\Delta(g)+\sqrt Z\|d-g\|_Q^2.}
\]
The handoff's original linear-error bound is also checked.
The quadratic estimate trades a factor 2 on Delta for a quadratic
approximation penalty; it is not uniformly stronger for every trial.

For G_M -> d in Q, Lean proves
\[
d=0\iff\Delta(G_M)\to0,\qquad d=0\iff F(G_M)\to0.
\]
The corresponding RH implications are conditional.

The exact second-inverse identity and membership criterion are
\[
T^2=Z(\mathrm{Id}-R),\qquad d=0\iff T^2d\in V_Q.
\]
Membership Td in V_Q alone is not promoted to membership of T^2d.

## Checked common-target and full-tail certificates

The correction has physical multiplier
\[
j(n)=1-\sqrt{\frac n{n+1}},\qquad Jf(n)=j(n)f(n).
\]
If the first N positive coordinates of f vanish, Lean proves
\[
\boxed{\|Jf\|_Q\le\frac{\|f\|_Q}{N+2}.}
\]
The hypothesis in Lean is f n=0 for zero-based encoded indices n<N.

For g,h,k in V_Q,
\[
a(g)\le\|Jg-Th\|_Q,\qquad
b(g)\le\sqrt Z\|Jg-k\|_Q.
\]
The explicit competitors are I(g/sqrt(Z)+h) in V_P and
A(sqrt(Z)(g-k)) in W.

For any v agreeing with g in the first N encoded coordinates, define
E=||g-v||_Q/(N+2). No legality of v is assumed. The theorem
two_distance_head_certificate proves
\[
\begin{aligned}
\sqrt{Z/2}\|d\|_Q^2+q(g)
\le{}&2\{\|r_P\|_P(\|Jv-Th\|_Q+E)\\
&+\|r_Q\|_Q\sqrt Z(\|Jv-k\|_Q+E)\}
+\sqrt Z\|d-g\|_Q^2.
\end{aligned}
\]
Every correction norm and the entire infinite remainder are retained.

## Principal declaration names

In QParetoIsometricTransport:
inversePhysical_apply, toPareto_A_inner, inversePhysical_symmetric,
inverseEnergy_lower, inverseEnergy_upper, inverseEnergy_eq_zero_iff,
inverseEnergy_polarization, inversePhysical_square, rootDefect_apply,
rootDefect_weight_bounds, rootDefect_norm_le_of_head_zero,
rootDefect_head_trial_bound.

In QFullCrossedDistances:
signedTest_eq, signedTest_le_budget, two_distance_bound,
two_distance_trial_bound, quadratic_two_distance_bound,
displacement_eq_zero_iff_crossed_membership,
displacement_eq_zero_iff_budget_tendsto_zero,
displacement_eq_zero_iff_signedTest_tendsto_zero,
forwardDistance_le_rootDefect_trial, inverseDistance_le_rootDefect_trial,
two_distance_head_certificate, displacement_eq_zero_iff_second_inverse_mem,
riemannHypothesis_of_crossed_distance_limits,
riemannHypothesis_of_signedTest_limit,
riemannHypothesis_of_second_inverse_mem.

## Verification and publication evidence

1. Assembled-module import and seven axiom audits:
   job_Odin6V3Y3pnftimYSpdTePhqM2miJeiF.
   Status succeeded; verified=true; exit code 0.
   Server-reported elapsed: 20.679 seconds.
   All three new modules were built.
2. Final source-audited publication checkpoint:
   job_87bLg-Le-O312EtTC_3ARTcUd3C5GlDX.
   Status succeeded; committed=true; pushed=true.
   Published commit: 3473ba7c75c1306acb013d07ae4fad2257499b02.
   Validation scope: full aggregate RiemannResearch plus
   Analysis.OrthogonalDistanceBound, RH.QParetoSquareRootEnergy,
   and RH.QFullCrossedDistances.
   Server-reported build elapsed: 112.428 seconds.
   No newer-main integration was needed.

Seven principal audits contain only propext, Classical.choice, and Quot.sound.
No new project axiom, sorry, admit, or unsafe declaration was introduced.
Ordinary axiom audits do not discharge hypotheses in theorem types.

An initial workspace request timed out, but subsequent operations recovered
the same workspace and completed the source checks and publication.
That transport delay was not a mathematical or kernel-verification failure.

## Research agenda for the next chat

### Priority 1: use the complete certificates on actual approximants

Construct or reuse legal G_M -> d. Choose finite coordinate truncations v,
and seek finite legal corrections h,k making both full norms
||Jv-Th||_Q and ||Jv-k||_Q small with the explicit E remainder.

Use complete P/Q Gram objectives, including correction tails.
For a finite target Jv, target pairings are finite sums; the Gram matrices
are still the complete Hilbert Gram matrices.
Finite-head interpolation alone does not control these objectives.

**Open provider:** a cofinal family whose complete certificate errors vanish.
A proved provider would feed the existing conditional RH theorems.

### Priority 2: formalize compactness and improve the convergence hypothesis

The proved tail estimate suggests finite-rank approximation of J and
compactness. Formalize this and bounded coordinatewise/weak convergence
implying JG_M -> Jd strongly. Investigate exact distance identities for
legal g that express both crossed distances through Jg.

These topological statements were not newly formalized in this chat.
Convergence to Jd does not establish that Jd has zero distance from the
required spaces. Keep that last assertion separate.

### Priority 3: retain signed cancellation

Seek arithmetic control of F(G_M), allowing cancellation between its two
residual pairings. The already checked identity only identifies its limit
with q(d). Setting that limit to zero using the identity itself is circular.

**Open provider:** actual signed-test decay, or a justified nonpositive
limiting bound combined with positivity.

### Priority 4: control the second inverse application

Use T^2=Z(Id-R) on a specific legal approximation family.
Try to prove T^2d in V_Q or a complete approximation to it.
Do not assume T preserves V_Q globally, or infer the second application
from the first membership without another argument.

### Priority 5: improve complete estimates without dropping terms

The current tail bound uses j(n)<=1/(n+1). Sharper bounds from the exact
square-root coefficient may improve constants. Preserve the exact signed
identity and nonnegative q(g) term before taking estimates.
Do not confuse improvements to constants with a proof of decay.

## Ready-to-paste continuation prompt

> Continue from CrossedDistanceLeanHandoff20261106.md in Cnoack3/RiemannResearch.
> Resume the retained workspace and inspect current main. Read
> QParetoSquareRootEnergy and QFullCrossedDistances, keeping the actual
> full-conductor displacement throughout. The two-distance criterion is
> already checked. Prioritize actual legal corrections for the common
> target Jg using two_distance_head_certificate and complete Gram norms.
> Also formalize compactness of J and test whether weaker convergence or
> signed cancellation helps supply the missing provider. Keep RH in mind,
> but do not identify A(V_Q) with V_P or assume invariant-subspace legality.
> Use Lean and GitHub, serialize verification, and publish useful proved
> results through the required source-audited checkpoint. Clearly separate
> checked identities from unresolved RH hypotheses.

# Parity, squarefree dilation, and exact-head target criteria

Research continuation — 20 October 2026

## Scope and verification boundary

This continues the user-provided `Two_Prime_Mellin_Parity_Handoff_2026-10-20(1).md`.
The target space is the complete-Q Hilbert space with physical weights
`Q(n)=1/(zeta(2)n^2)` for positive integers, and auxiliary coordinate zero
anchored to zero. Write H for the closed squarefree residue span and
C=closure(H+R*1). The finite algebraic dictionary is denoted S.

The new Lean declarations below must be accepted by the final server
checkpoint before they count as integrated verified results. Neither
F_2 in C nor F_3 in C is supplied, and RH is not proved unconditionally.

The working base was `497c83d7c88a323b617ebccc6b7394fe2077b39e`.
Current main was also inspected at
`ed3d1f662c8b8f6e215f9b43859ee019a5612e04`; the final checkpoint integrates
newer main and verifies the integrated source before publication.

The complete import/axiom job `job_V1ORfCjJCzEEYVieSp3Bzzs8XbKOaTBI`
succeeded with exit code zero and `verified:true`. The seven inspected key
declarations, including the exact-head equivalence and conditional RH
consumer, depend only on `propext`, `Classical.choice`, and `Quot.sound`.
The final checkpoint remains the authority for integrated validation.

## 1. Exact parity equivalence and residuals

`RH/QEvenClosure.lean` proves, for every real submodule V containing g_2,

\[
 E_2\in V\iff 1\in V,
 \qquad (I-P_V)E_2=(I-P_V)1.
\]

The projection statement assumes that V has an orthogonal projection.
Its complete squared-error identity is specialized to the actual exhaustive
squarefree stages, as well as to the limiting projection onto H.
`qEven_mem_closure_iff` is a membership equivalence, not a proof of either side.

The enlarged closure C contains both 1 and E_2 unconditionally. Thus the
automatic parity membership in C cannot replace the separate F_2 target
membership in the two-prime criterion.

## 2. Quantitative failure of floor-dilation invariance

`RH/QSquarefreeDilationObstruction.lean` reuses the actual bounded operator
`QFloorDilation.floorDilation`, whose sequence is f(floor(n/2)). No new
Hilbert model or dilation construction is introduced.

For a>=2 the existing witness represents

\[
 L_a(f)=\Delta f(a^2)-\Delta f(a),\qquad
 D_a=\|h_a\|_Q^2=2\zeta(2)(a^4-a+1).
\]

Every vector of C is annihilated by L_a. The new exact error identity is

\[
 \|x-f\|_Q^2=\frac{L_a(x)^2}{D_a}
 +\left\|x-f-\frac{L_a(x)}{D_a}h_a\right\|_Q^2,
 \qquad f\in C.
\]

At a=2, L_2(D1)=L_2(Dg_2)=-1 and D_2=30*zeta(2). Hence

\[
 \|D1-f\|_Q^2\ge\frac1{30\zeta(2)},\qquad
 \|Dg_2-f\|_Q^2\ge\frac1{30\zeta(2)}\quad(f\in C).
\]

The complete remainder is retained before taking either lower bound.
Consequently D(C) is not contained in C, and D(H) is not contained in H.
The actual F_2 target satisfies L_2(F_2)=0. These results exclude an
invariant-subspace argument, not the target itself.

## 3. A genuine exact-head equivalence

The generic continuous finite-observation repair theorem was already
available in `Analysis/FiniteObservationApproximation.lean`. It supplies a
finite-dimensional continuous section for each fixed head. Its norm is
not assumed uniform as the head expands.

The extension to `RH/QExactHeadAverages.lean` proves

\[
 z\in\overline S\quad\Longleftrightarrow\quad
 \exists B\in\mathbb R\ \forall M\in\mathbb N\ \exists g\in S:
 \quad g(n)=z(n)\ (1\le n\le M),\quad \|g\|_Q^2\le B.
\]

The reverse implication reuses the existing bounded-head weak-convergence
consumer. The forward implication repairs a sufficiently close algebraic
approximant while retaining the finite head exactly; B=(||z||+1)^2 suffices.
This is existential in the support and does not bound a predetermined
cutoff schedule or the previously selected least-feasible cutoff family.

`RH/QPrimePowerHeadClosure.lean` defines
`finiteWithConstants = qSquarefreeCRTSpan sup span {qOne}` and identifies
its closure with C. It then proves the displayed equivalence for every
actual F_p, p>1, both in C and in the stronger squarefree closure H.
For C the finite candidates are genuine finite squarefree combinations
plus a real constant. For H the constant is absent.

The resulting two-target RH consumer uses these exact finite-head data
for p=2 and p=3. Both uniform full-energy budgets remain Open. The
equivalences do not discharge them.

## 4. Sharp coefficient instability of balanced sieve rows

`Analysis/SignedBalancedRows.lean` derives the finite inequality below
from the unconditional exact identity

\[
 (a-b)\sum_i|w_i|-(a+b)\sum_iw_i+2\sum_iw_i s_i
 =\sum_i\bigl[(|w_i|+w_i)(s_i-b)+(|w_i|-w_i)(a-s_i)\bigr].
\]

Every displayed slack term is nonnegative when the slopes lie in [b,a].
Imposing the two balance constraints therefore yields

\[
 \sum_iw_i=1,\quad \sum_iw_i s_i=0,\quad b\le s_i\le a
 \ \Longrightarrow\ a+b\le(a-b)\sum_i|w_i|.
\]

For 0<b<a, this gives TV>= (a+b)/(a-b). The endpoint pair
(-b/(a-b),a/(a-b)) has exactly mass one, moment zero, and that variation.
The bound is sharp among all row lengths. If TV<=M and a>0, b<a, M>=0,
then b/a<=(M-1)/(M+1).

The extension to `RH/QPrimePowerSignedSieve.lean` specializes these
inequalities to the actual primorial sieve slopes. Adding intermediate
cutoffs within the same slope interval cannot reduce this coefficient
variation bound. It can still change the full Gram energy; no vector norm
bound or norm divergence is inferred from coefficient variation alone.

Wolfram was used only for the finite checks
`sum([1,-1,-1,1]^2 * [1,2,3,4]^2)=30` and the endpoint absolute-value
identity under 0<b<a. It returned `{30, True}`. Lean is the verification
authority for the declarations above.

## 5. Updated research direction from newer main

The older handoff's near-equal-slope two-stage escape is now excluded by
the subsequent current-main theorem
`QPrimePowerSieve.sieveTwoStageVector_norm_tendsto_atTop` in
`RH/QPrimePowerTwoStageObstruction.lean`. Its exact type was inspected at
commit ed3d1f6. It treats every nondegenerate two-stage family whose
minimum cutoff tends to infinity, including coalescing positive slopes.
This is prior work, not a new theorem of the present continuation.

The useful next target is arbitrary signed rows with unbounded support size.
For an exactly drift-balanced row, the existing actual Mellin formula gives

\[
 \Phi_\sigma(B)=\zeta(\sigma)\sum_H w_H E_{p,H}(\sigma),\qquad
 E_{p,H}(\sigma)=p^{-\sigma}\prod_{q\le H,\ q\ne p}(1-q^{-\sigma}),
\]

for 1/2<sigma<1 and sufficiently large support cutoffs. The new main
`primePowerEulerFactor_scaled_tendsto_zero` supplies Euler-factor decay.
Uniformly bounded total variation and cofinal supports therefore force
this Mellin transform to zero. The target transform is nonzero.

Combining exact head matching with the existing Mellin-tail estimate should
give, for all sufficiently large minimum cutoffs H,

\[
 \frac{2\sigma-1}{4\zeta(2)\sigma^2(p^\sigma-1)^2}
 H^{2\sigma-1}\le\|B-F_p\|_Q^2.
\]

This multi-stage deduction is a mathematical next step, not a new checked
Lean theorem in the present change. A proof draft was developed separately;
it must be checked against the integrated current-main arithmetic modules.

An additional proposed refinement concerns rows with one sign change and
strictly ordered negative-before-positive slopes. Such rows may be written
as convex combinations of two-stage balanced corrections, using transport
of positive slope mass. This could exclude them without a TV bound. Equal
slopes require an explicit plateau argument; no division by a zero slope
gap is permitted. This refinement is also unformalized.

The remaining positive task is to produce a cofinal family of finite legal
exact-head candidates with a uniform full-Q energy bound, or identify a
better target-specific construction. The entire infinite tail and every
signed Gram cross term must remain in that estimate.

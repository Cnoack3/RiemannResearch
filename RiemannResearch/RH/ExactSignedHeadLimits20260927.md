# Exact signed-head limits and the actual diagonal

Date: 2026-09-27. Continuation of commit
675fd95c20ab449d6b840bee6e46ad18d162d5d7.

## What is strengthened

The previous sparse signed-head theorem is retained and its quantitative
conclusion is tightened. Define the actual diagonal
\[
 \Delta_\varepsilon=\sum_{d\ge1}\|u_{\varepsilon,d}\|_P^2,
 \qquad
 u_{\varepsilon,d}(n)=\mu(d)d^{-1-\varepsilon}(n\bmod d).
\]
For every epsilon>0 its series converges, and
\[
 0\le\Delta_\varepsilon
 \le 2\sum_{d\ge1}d^{-1-2\varepsilon}.
\]

The existing sparse hypothesis, at any M(H) tending to infinity, now gives
\[
 E_\varepsilon\le\Delta_\varepsilon+B.
\]
Thus the actual arithmetic diagonal replaces the p-series majorant.
No claim of a strict improvement for every epsilon or of an optimal
off-diagonal bound is needed.

## Exact finite-head residue limit

Use the definitions of g_epsilon, E_epsilon, and O_epsilon from
SparseSignedHeadDichotomy20260927.md. Put
\[
 E_\varepsilon(H)=\sum_{n<H}\frac{g_\varepsilon(n)^2}{n(n+1)},\qquad
 \Delta_\varepsilon(H)=
 \sum_{d\ge1}\sum_{n<H}\frac{u_{\varepsilon,d}(n)^2}{n(n+1)}.
\]
The zero coordinate has weight zero. For every epsilon>0 and fixed H,
\[
 \boxed{
 \lim_{M\to\infty} O_\varepsilon(H,M)
 =E_\varepsilon(H)-\Delta_\varepsilon(H).
 }
\]
The limit exists unconditionally at every positive damping, including
below one half. It is a limit on each finite physical head; it does not
assert finite total physical energy.

Proof. The exact finite Gram identity is
\[
 O_\varepsilon(H,M)
 =\sum_{n<H}\frac{F_{\varepsilon,M}(n)^2}{n(n+1)}
   -D_\varepsilon(H,M).
\]
The first term converges to E_epsilon(H) by the already proved scalar
coordinate convergence. The second is a partial sum of a nonnegative
series dominated term by term by
\(\|u_{\varepsilon,d}\|_P^2\), whose sum is finite. It converges to
Delta_epsilon(H). Subtracting the two convergent sequences proves
the equality without rearranging an infinite signed double series.

## Exact iterated limit

The diagonal has the unconditional limit
\[
 \Delta_\varepsilon(H)\longrightarrow\Delta_\varepsilon.
\]
For each atom the finite-head squared norm tends to its full squared norm.
Those full norms form a summable dominating sequence, so dominated
convergence for series gives the displayed limit.

Consequently, whenever the actual energy is finite,
\[
 \boxed{
 \lim_{H\to\infty}\lim_{M\to\infty}O_\varepsilon(H,M)
 =E_\varepsilon-\Delta_\varepsilon.
 }
\]
Equivalently, the exact energy decomposition is
\[
 E_\varepsilon=
 \Delta_\varepsilon+
 \lim_{H\to\infty}\lim_{M\to\infty}O_\varepsilon(H,M).
\]
The residue cutoff tends to infinity first. These results do not assert
that the order of the two limits may be reversed, or that the signed
double series is absolutely summable.

The full iterated-limit formula is unconditional for epsilon>=1/2,
using the existing checked endpoint and strict-range energy providers.
For 0<epsilon<1/2, its finite-total-energy premise remains explicit.

## Lean declarations

New module: RH/DampedMobiusExactSignedHeadLimits.lean.

- dampedMobiusExactDiagonal and its nonnegativity and majorant bound;
- dampedMobiusHeadDiagonal_le_exact;
- dampedMobiusCompletedHeadDiagonal;
- dampedMobius_headDiagonal_summable and dampedMobius_headDiagonal_tendsto;
- dampedMobius_completedHeadDiagonal_tendsto;
- dampedMobiusSignedHeadLimit;
- dampedMobius_offDiagonal_fixed_head_tendsto;
- dampedMobius_signedHeadLimit_tendsto_of_summable;
- dampedMobius_signedHeadLimit_tendsto_of_half_le.

The existing
centered_damped_energy_of_frequently_bounded_moving_heads
is strengthened in RH/DampedMobiusSparseHeadDichotomy.lean to use
dampedMobiusExactDiagonal. Its proof and the dependent RH reductions
remain explicit about the signed boundedness hypothesis.

## Scope and provenance

This is an elementary strengthening using the repository's previously
verified signed Gram identities, actual Mobius coordinate limits,
summable diagonal, and Mathlib dominated convergence for series.
No mathematical novelty is claimed.

The endpoint provider's source is J.-F. Burnol, On an analytic estimate
in the theory of the Riemann zeta function and a theorem of Baez-Duarte,
Section 4, Lemma 4.1:
https://arxiv.org/abs/math/0202166.
No external theorem is introduced as an axiom.

Open: prove an actual uniform signed bound at small positive damping.
The unconditional finite-energy range remains epsilon>=1/2, and RH
is not proved by the present strengthening.

Verification: combined candidate job_kF9DdWukUqnEEctCNCXFpIDt8ucaxcp3
returned verified=true, exit_code=0 in 4.874 seconds, with no warnings.
Five principal dependency checks report only propext, Classical.choice,
and Quot.sound. The candidate includes the strengthened sparse theorem
and its RH reduction. The publication checkpoint validates the final
separate modules and affected dependents before commit and push.

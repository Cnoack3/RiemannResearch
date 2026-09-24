# Quantitative Möbius energy and moving Hardy boundaries

## Outcome and scope

Both requested bridges have been formalized without a new arithmetic hypothesis:

1. An exact weighted head–tail identity, with its nonnegative defect retained.
2. A quantitative bound for the complete critical energy of the actual canonical Möbius approximants.

Their combination gives unconditional uniform residual convergence on explicit
half-planes with boundaries strictly below 1 and tending to 1. It does not give
boundaries tending to 1/2, and does not prove RH.

Source: the user's continuation request after commit e2518b1, using the existing
formal PNT and exact Möbius identities. No mathematical novelty claim is made.

## Notation and existing providers

Write F_N for canonicalMobiusHilbert N, r_N=1-F_N, and b=N+1. For a physical
step profile f, put

\[
E_u(f)=\int_1^\infty |f(\lfloor x\rfloor)|^2x^{-u-1}\,dx.
\]

The new declaration complexPhysicalStep_critical_energy identifies E_1(f)
exactly with the full Pareto squared norm. The existing Hardy identification
uses vertical points sigma+2*pi*i*t, so there is no missing 2*pi factor.

The quantitative arithmetic provider already present is

\[
\exists C\ge0,\quad |M(y)\log y|\le Cy
\quad\text{for all sufficiently large }y,
\]

together with the simultaneous finite-cutoff consequence

\[
|m_N|\le\frac1J+\frac1{NJ}+\frac{C(H_J+1)}{\log N}
\quad(J\ge1,\ N\text{ sufficiently large}).
\]

These are supplied by MobiusQuantitativeRate and MobiusReciprocalCutoff.
The pre-existing full-energy result was E_1(F_N)/N -> 0; the new result supplies
an explicit rate for that limit.

## 1. Complete arithmetic energy, with both cutoffs free

For one C>=0, every sufficiently large N, every K>=2 and J>=1, define

\[
D_{N,K,J}=\frac1J+\frac1{NJ}
 +\frac{C(H_K+H_J+2)}{\log N}.
\]

Then Lean proves

\[
\boxed{\frac{E_1(F_N)}N\le \frac3N+2K D_{N,K,J}^{\,2}+\frac4K.}
\]

Declaration: canonicalMobiusHilbert_eventual_quantitative_energy in
[CanonicalMobiusQuantitativeEnergy.lean](CanonicalMobiusQuantitativeEnergy.lean).

The proof improves the window estimate before summing its energy. If
|M(t)|<=At for t>=N and |m_N|<=B, the exact quotient-level identity gives,
for N<n<=KN,

\[
|F_N(n)|\le1+n\{A(H_K+1)+B\}.
\]

Indeed, with q=floor(n/(N+1)), the signed floor tail is the sum of
M(floor(n/k))-M(N) over 1<=k<=q. Here q<=K, qN<=n, and the reciprocal
quotient sum is at most H_K. The boundary correction is at most Bn.
This is canonicalMobiusHead_harmonic_window_bound.

The critical head has energy N/(N+1)<=1. In the middle window,
(1+nD)^2<=2+2n^2D^2 and n^2/[n(n+1)]<=1. Its energy is at most
2+2KN D^2. The complete far tail is at most 4N/K, by the existing
global bound |F_N(n)|<=2N. No infinite tail is discarded.

## 2. Explicit optimization

For N>=2 put

\[
L_N=\log N,\qquad Q_N=1+\log(L_N+3),\qquad
x_N=\frac{Q_N}{L_N},\qquad A=2+4C,
\]

\[
B_C(N)=\frac3N+(4+2A^2)x_N+4A^2x_N^2.
\]

Choose the integers

\[
J_N=\lfloor L_N\rfloor+1,\qquad
K_N=\lfloor L_N/Q_N\rfloor+2.
\]

The proof establishes D_{N,K_N,J_N}<=A x_N,
K_N<=1/x_N+2, and 1/K_N<=x_N. Consequently,

\[
\boxed{E_1(F_N)/N\le B_C(N)}
\quad\text{eventually},\qquad
x_N\longrightarrow0,\quad B_C(N)\longrightarrow0.
\]

Declarations: canonicalMobiusHilbert_eventual_optimized_energy,
canonicalMobiusEnergyRate_tendsto_zero, and
canonicalMobiusEnergyCeiling_tendsto_zero.

These are inequalities with an explicit expression, not just qualitative
convergence or a finite computational experiment.

## 3. Exact weighted identity and intermediate Hardy bound

For u>=1, define the full tail defect

\[
\Delta_{b,u}(F)=\int_b^\infty |F(\lfloor x\rfloor)|^2x^{-2}
       \bigl(b^{1-u}-x^{1-u}\bigr)\,dx\ge0.
\]

Because F_N has its exact head equal to 1,

\[
\boxed{
E_u(F_N)=\frac{1-b^{-u}}u+
 b^{1-u}\left(E_1(F_N)-1+\frac1b\right)-\Delta_{b,u}(F_N).
}
\]

This is canonicalMobius_weighted_energy_exact, based on the generic
energy_eq_exact_head_add_power_tail_sub_defect. The code defines the defect
by the algebraically identical difference of its two integrable densities.

In particular, for the same arithmetic C and all sufficiently large N,
simultaneously for every u>=1 and sigma>u/2,

\[
\int_{\mathbb R}|\mathcal M F_N(\sigma+2\pi it)|^2\,dt
\le \frac{1-b^{-u}}u+
 b^{1-u}\left(NB_C(N)-1+\frac1b\right).
\]

Declaration: canonicalMobius_eventual_intermediate_hardy_bound in
[CanonicalMobiusMovingBoundary.lean](CanonicalMobiusMovingBoundary.lean).

The zero head of the residual supplies the simpler bound

\[
E_u(r_N)\le b^{1-u}\|r_N\|_P^2.
\]

See [ExactHeadWeightedEnergy.lean](ExactHeadWeightedEnergy.lean) and the generic
[WeightedMellinHeadTail.lean](../Analysis/WeightedMellinHeadTail.lean).

## 4. Unconditional explicit moving half-planes

Set

\[
q_C(N)=2B_C(N)+\frac3N.
\]

The arithmetic module proves, eventually,

\[
\|r_N\|_P^2\le(N+1)q_C(N),\qquad
\frac1{N+1}\le q_C(N),\qquad q_C(N)\longrightarrow0.
\]

It also follows in Lean that 1/log(N+1)<=q_C(N) for N>=2. Define

\[
u_N=2+\frac{\log q_C(N)}{2\log(N+1)},\qquad
\beta_N=\frac{u_N}{2}
       =1+\frac{\log q_C(N)}{4\log(N+1)}.
\]

Then, unconditionally, for the supplied C,

\[
\boxed{
\beta_N<1,\quad \beta_N\longrightarrow1,\quad
\forall\sigma>\beta_N,\quad
\int_{\mathbb R}|\mathcal M r_N(\sigma+2\pi it)|^2\,dt
\le\sqrt{q_C(N)}\longrightarrow0.
}
\]

All inequalities about the schedule hold for sufficiently large N.
The final theorem also states u_N>1 eventually.

Principal declaration: canonicalMobiusResidual_explicit_moving_hardy.
The uniform bound is over all lines in the moving half-plane, not merely
one selected line. canonicalMobiusResidual_moving_lines_tendsto separately
formalizes convergence along arbitrary admissible line choices.

The finite scheduling family is stronger than this square-root specialization:
for 0<=theta<=1, 1/b<=q<=1 and ||r_N||^2<=bq,

\[
u=2+\theta\frac{\log q}{\log b},\qquad
E_u(r_N)\le q^{1-\theta},
\]

and the same bound holds on every line sigma>u/2.
For fixed 0<theta<1 this trades a larger leftward shift against a slower
vanishing power. See canonicalMobiusResidual_scheduled_line_bound and
cutoff_power_log_schedule. No optimality is asserted for theta=1/2.

## 5. Exact remaining RH gap

The original RH reduction requires a boundary 1/2+alpha_N with alpha_N->0
and one uniform bound on the approximants. Our explicit boundary instead
has alpha_N=beta_N-1/2 -> 1/2.

At u=1+2alpha_N the upper estimate contains the complete tail ceiling

\[
(N+1)^{-2\alpha_N}N B_C(N).
\]

The proved logarithmic improvement does not make this uniformly bounded
when alpha_N tends to zero. This is a limitation of the available upper
estimate; it is not a proof that the actual energy diverges.

The next substantive arithmetic task remains control of the complete energy
with substantially smaller growth, or direct cancellation in the weighted
tail/defect identity. Compactness or selecting a subsequence alone does not
supply that estimate.

## Verification and integration

The combined-source Lean check returned exit code 0. Axiom checks for the
unconditional explicit moving-Hardy theorem, intermediate Hardy bound,
parameterized arithmetic bound, and exact defect identity reported only
propext, Classical.choice, and Quot.sound. There are no admissions or added
project-local axioms.

The publication checkpoint validates the separated modules and their
reverse dependents, including the root export.

The initial baseline rebuild exposed an unrelated root-import collision:
OptimalProjectionDilationGaps and TailCapacityDilationCorrection both defined
CoefficientStabilization.dilationCorrection for different constructions.
The former operator was renamed optimalProjectionDilationCorrection, with
all its local uses updated. Its mathematical definition and theorem
statements' content are preserved.

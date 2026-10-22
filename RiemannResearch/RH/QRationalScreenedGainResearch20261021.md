# Recovered rational-stage signed and screened gain certificates

Date: 21 October 2026.
Source: user-provided signed-tail/metric-refinement handoff of 20 October 2026;
recovery of the five continuation drafts. No novelty claim is made.

## Scope and notation

Let L_n be the repository's primorial cutoff period, V_n the full divisor legal
space, f_n its actual rational minimizer, R_n the minimum, and G_n its rational
weight gap. All composite squarefree divisors remain included. For M=L_m,

\[
U_M(v,w)=\sum_{a=1}^{M}u_M(a)v(a)w(a),\qquad
\Delta_{n,m}=U_M(f_m-f_n,f_m-f_n).
\]

The representative a=M is retained. The rational weights continue to bound
complete infinite Q fibers. No numerical primorial experiment was performed.

## Exact signed correlation certificate

For v in V_m, normal equations give C=U_M(1-f_n,v)=U_M(f_m-f_n,v).
For N=U_M(v,v)>0 the exact identity is

\[
\Delta_{n,m}=\frac{C^2}{N}
 +U_M\left(f_m-f_n-\frac C N v,f_m-f_n-\frac C N v\right).
\]

Thus Delta >= C^2/N. If n<=m and L_m=k L_n, k>=2, the existing quartic refund
combines with it to give

\[
R_n-R_m\ge\left(1-\frac{20}{3k}\right)G_n+\frac{C^2}{N}.
\]

Owner: `QRationalStageCorrelation.lean`.
Principal declarations: `rationalStageDisplacement_completion`,
`rationalStageDisplacement_ge_correlation`,
`rationalMinimum_drop_ge_refund_correlation`, and
`rationalStageDisplacement_ge_divisor_correlation`.

## Actual reoptimization and genuine new-space gain

An old-space projection in the later rational metric is constructed from an
actual finite weighted Euclidean normal-equation solution. Singular dictionaries
are allowed. Let tilde-f=P_(V_n)^(U_M) 1 and put

\[
T_{n,m}=U_M(f_n-\widetilde f,f_n-\widetilde f),\qquad
J_{n,m}=U_M(f_m-\widetilde f,f_m-\widetilde f).
\]

For n<=m the exact orthogonal decomposition is

\[
\Delta_{n,m}=T_{n,m}+J_{n,m}.
\]

The first term is movement from the metric change within the old space. The
second is gain from enlarging the legal space while holding the metric fixed.
For q=v-P_(V_n)^(U_M)v,

\[
J_{n,m}\ge\frac{U_M(1,q)^2}{U_M(q,q)}
\]

whenever the screened denominator is positive.

For every new conductor e>=2 with e|L_m and e not dividing L_n, that positivity
is supplied by a concrete site: all old legal fits vanish at L_n, whereas

\[
q(L_n)=g_e(L_n)=\frac{L_n\bmod e}{e}>0.
\]

The site lies in the later representative interval and has positive weight.
The resulting actual new-divisor certificate has no assumed nondegeneracy.
Positivity of the denominator does not establish a nonzero or large numerator.

Owner: `QRationalReoptimization.lean`.
Principal declarations: `rationalStageDisplacement_split`,
`rationalScreened_residue_energy_pos`, and
`rationalLegalGain_ge_new_divisor_charge`.

## Transfer to the complete-Q metric

For n<=m,

\[
\zeta(2)\|f_m-f_n\|_Q^2\le\Delta_{n,m}
 \le\frac53\zeta(2)\|f_m-f_n\|_Q^2.
\]

Writing h_j for the true Q projection and e_j=f_j-h_j, the signed mismatch is
retained exactly:

\[
\|f_m-f_n\|_Q^2=E_n-E_m+\|e_m-e_n\|_Q^2
 +2\langle h_m-h_n,e_m-e_n\rangle_Q.
\]

The proof respects the auxiliary-zero convention: it applies the periodic
sequence comparison to the plain sequence 1-qSequence(v), avoiding the false
periodicity assertion for qSequence(qOne-v) at zero.

Owner: `QRationalDisplacementComparison.lean`.

## Conditional gain-provider reduction

The general additive budget proves the finite terminal estimate

\[
\left(1+\sum_{j<N}c_j\right)R_N
 \le R_0+\sum_{j<N}\varepsilon_j
\]

from antitonicity, c_j>=0, c_j R_j-epsilon_j<=a_j, and
sum_(j<N) a_j<=R_0-R_N. With nonnegative summable errors and divergent cumulative
c_j, the limiting residual vanishes.

`qOne_mem_closure_of_chain_gain_provider` in `QRationalGainProvider.lean` is located in
namespace `RiemannResearch.RH.QRationalCoprimeTail` and specializes this argument
to an actual monotone cofinal chain with successive period ratios at least 14,
using a_j=G_(sigma j)/2+Delta_(sigma j,sigma(j+1)).

This is a **conditional research reduction**. The domain-specific obligation is
**Open**: establish the displayed lower provider for actual gains, with divergent
cumulative coefficients and summable error. No such arithmetic provider is
constructed here. The closure conclusion is not an unconditional RH proof.

General owner: `Analysis/GainBudgetConsumer.lean`; application owner:
`RH/QRationalGainProvider.lean`.

## Recovery and verification

The original ephemeral job `job_WL3ZkRA7OnY6vJZyJyfSAbvzXBYkV2Ol` was recovered
as terminal `wall_timeout`, exit -9, after 180 seconds restoring dependencies.
It had not certified the drafts. The same workspace was resumed, and the
source was saved for targeted verification before the final checkpoint.
The initial saved correlation module check `job_Nh0FnZXz87vM_44ilx097Tp7GNZ5Efc7`
succeeded with verified=true and exit 0 in 6.443 seconds.

The saved-module audit `job_7uUbWVqzl_rqNRanC4PlJCKv7-K7N1I5` succeeded
with verified=true, exit 0, and elapsed 13.103 seconds. It imported all five
recovered modules and inspected eight principal declarations. Their only axioms
were `propext`, `Classical.choice`, and `Quot.sound`. No placeholders or
project-local axioms were introduced. The arithmetic provider remains a local
hypothesis in the conditional theorem type.

The first checkpoint `job_pxJBtf7y7sFUwjd86-99DKaFAiysbxln` created local
commit `da3eac6041e0a92536bbcfbc1bae22ab0e58b383` after validation, then failed
during integration with newer main because the theorem catalog had changed.
It did not push. That workspace and commit were preserved. The same recovered
source was integrated in a fresh workspace based on current main
`914f1d2a3b0d1722dbef04b3e53f31a1c1f679ac`, placing the catalog entry beside
its older rational-stage results to avoid the conflicting leading insertion.

The final checkpoint is the acceptance gate for all recovered source and any
integration with newer main. Its terminal result and published commit are
reported separately to avoid presenting an accepted job as verification.

## Next arithmetic target

Estimate actual signed charges U_M(1,g_e-P_(V_n)^(U_M)g_e), individually or as
blocks, strongly enough to supply the cumulative gain provider. A fixed-old-
stage asymptotic is not uniform control of moving optimizers. Retain signed
terms and complete-Q tails. The unconditional ratio S/R -> -1 remains compatible
with zero or positive limiting defect. Trigamma convergence is excluded.

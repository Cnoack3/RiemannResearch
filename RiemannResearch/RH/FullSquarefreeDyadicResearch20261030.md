# Full-squarefree arithmetic coordinates and weaker dyadic RH target

Continuation of the 30 October 2026 full-squarefree handoff.
Base: `c108bfabbb94c5c07272185a830fcc85cb441fef`, confirmed on GitHub main and
in the resumed Lean workspace before modification.

## Conclusion and status

The full new-conductor arithmetic representation is now proved. The proposed
conditional dyadic argument is proved under a weaker hypothesis: any
nonnegative relative overhead tending to zero suffices, rather than the
specific harmonic rate A/(m+1). An actual-optimizer floor-dilation trial has
an exact competitor identity and an improved complete-Q energy bound that
subtracts the entire known head defect.

**No unconditional signed dyadic budget, subpolynomial optimizer growth, or
RH is proved here.** All remaining arithmetic obligations are stated below.
No prime-only optimizer or finite physical-tail cutoff is substituted.

## 1. Actual objects retained

For n≥1, use Q(n)=1/(ζ(2)n²), g_d(n)=(n mod d)/d, and the complete Q Hilbert
norm. Let

\[
L_i=\operatorname{primorial}(2i+2),\qquad
U_i=\operatorname{span}\{g_d:1<d\mid L_i\}.
\]

F_i is the minimum-Q-norm vector in U_i with F_i(n)=1 for 1≤n≤i+1;
E_i=||F_i||². The actual old-dictionary next-head minimum is
Fhat_i=minimumAt(2i,i+2), and C_i^old=||Fhat_i||²−E_i.
This is not the enlarged-dictionary old-head minimum.

All squarefree composite conductors remain available. The former exhaustion
theorem is reused, not strengthened into a constant-closure assertion.

## 2. Full added-conductor block: Priority 1 completed

At a prime p=2i+3, Lean proves L_(i+1)=p L_i and the finite-type equivalence

\[
\{d:d\mid L_i\}\longleftrightarrow\operatorname{addedConductors}(i),
\qquad d\longmapsto pd.
\]

It includes d=1. At nonprime transitions the added set is empty.
The actual optimizer still carries its head constraint at those stages.

Write v_d for the screened compensated direction at pd, z=v_1, and
u_d=screening(D_p g_d), where (D_p f)(n)=f(floor(n/p)). Then

\[
v_d=u_d+d^{-1}z,\qquad u_1=0.
\]

Let a=oldMismatch(i), K=oldCapacity(i), c_d=v_d(i+2). The actual source and
adjusted Gram entries become

\[
s_d=\langle u_d,F_i\rangle+d^{-1}\langle z,F_i\rangle-a c_d/K,
\]
\[
M_{de}=\langle u_d,u_e\rangle+e^{-1}\langle u_d,z\rangle
+d^{-1}\langle z,u_e\rangle+(de)^{-1}\|z\|^2+c_dc_e/K.
\]

For any coefficient array t on ALL old divisors, including 1,

\[
\mathcal C_i(t)=a^2/K-2\sum_{d\mid L_i}t_ds_d
+\sum_{d,e\mid L_i}t_dM_{de}t_e.
\]

The transport retains every off-diagonal term and the compensated-prime
coordinate. No spectral estimate is assumed. The former trial completion
still supplies its exact nonnegative loss square at eligible squarefree sites.

Module: [QCRTDivisorBlock.lean](QCRTDivisorBlock.lean).
Principal declarations: `primeDivisorEquiv`, `trialCertificate_arithmetic`,
`divisorTrial_certificate`, `addedConductors_empty_of_nonprime`.

## 3. Exact head-defect improvement

Put

\[
w_p(k)=\sum_{r=0}^{p-1}Q(pk+r),\qquad
\delta_p(k)=Q(k)/p-w_p(k)\ge0\quad(k\ge1),
\]
\[
D_{p,H}=\sum_{k=1}^H\delta_p(k),\qquad
R_{p,H}(f)=\sum_{k>H}\delta_p(k)|f(k)|^2.
\]

For every exact-head vector f with f(k)=1 for 1≤k≤H, the new checked equality is

\[
\boxed{\|D_pf\|_Q^2=\|f\|_Q^2/p-D_{p,H}-R_{p,H}(f).}
\]

The complete tail is summable and nonnegative. Consequently
||D_p f||²≤||f||²/p−D_(p,H). If H≥1, this refined denominator is positive:
(D_p f)(p)=f(1)=1 makes the dilated vector nonzero.

The checked Pareto comparison also gives

\[
D_{p,H}\ge\frac{1-1/p}{p}
\sum_{k=1}^H\left(Q(k)-\frac{P(k)}{\zeta(2)}\right),
\qquad P(k)=\frac1{k(k+1)}.
\]

The Lean statement spells the same expression as (G_H−G_H/p)/p.
Elementary paper simplification gives
G_H=ζ(2)⁻¹Σ_(k=1)^H 1/[k²(k+1)], so D_(p,H)>0 for p>1 and H≥1.
This simplified positivity statement is a paper consequence; the checked
declarations are the exact split, nonnegativity, denominator positivity, and
the displayed finite-sum lower bound.

Module: [QFloorDilationHeadEnergy.lean](QFloorDilationHeadEnergy.lean).
Principal declarations: `floorDilation_norm_sq_head_defect`,
`floorDilation_norm_sq_le_head`, `headAdjustedEnergy_pos`,
`headBlockDefect_ge_pareto_gap`.

## 4. A full-coefficient actual-optimizer trial

For any f=Σ_d c_d g_d in the old full dictionary, the exact coefficients are

\[
D_p f=\sum_d c_dg_{pd}-\left(\sum_d c_d/d\right)g_p.
\]

This explicit prime coefficient cancels the reciprocal slope. All pd are legal
at a prime enlargement, and D_pf vanishes below p. Hence for i>0,
Fhat_i−tD_pf preserves the next head because i+2<p=2i+3.

With S=〈Fhat_i,D_pf〉, Lean retains the complete competitor identity

\[
C_i^{old}-2tS+t^2\|D_pf\|^2-(E_{i+1}-E_i)
=\|Fhat_i-tD_pf-F_{i+1}\|^2.
\]

For f=F_i and H=i+1, let A_i=E_i/p−D_(p,i+1)>0. Choosing t=S/A_i and using
the exact head-tail identity yields the stronger bound

\[
\boxed{E_{i+1}-E_i\le C_i^{old}-S^2/A_i.}
\]

Before dropping nonnegative terms, direct substitution gives the exact paper
identity C_i^old−S²/A_i−(E_(i+1)−E_i)=competitor_loss+
(S²/A_i²)R_(p,i+1)(F_i). Its two constituent equalities are checked; the
substituted single-line identity is recorded here as algebraic exposition.

The baseline pS²/E_i bound is checked too. The improved denominator is no
larger than E_i/p, so its certified gain is at least as large. These are
finite-stage certificates; there is no asserted positive lower bound on S.

Module: [QCRTFullFloorTrial.lean](QCRTFullFloorTrial.lean).
Principal declarations: `floorDilation_coefficients`, `floorTrial_completion`,
`selfDilation_step_le`, `selfDilation_step_le_head`.

## 5. Weaker sufficient dyadic target: Priority 4 completed and strengthened

For the existing global `fullCertificate` and `fullLoss`, the new exact interval
identity, for EVERY 0≤M≤N, is

\[
E_N=E_M+\sum_{i=M}^{N-1}\mathcal C_i-\sum_{i=M}^{N-1}\mathcal L_i,
\qquad\mathcal L_i\ge0.
\]

All stages are included. At nonsquarefree observations the exact negative
period gain is retained; squarefree observations without prime enlargement
still contribute their head cost. Trials in this identity are the original
adjusted full-family trials. Section 4's raw competitor certificates are
separate upper bounds; no equality between the two types is asserted.

It now suffices to find t, B≥0, m0, and a_m≥0 with a_m→0 such that, for all m≥m0,

\[
\boxed{\sum_{i=2^m}^{2^{m+1}-1}\mathcal C_i(t_i)
\le a_mE_{2^m}+B.}\tag{OPEN}
\]

The interval identity implies e_(m+1)≤(1+a_m)e_m+B for e_m=E_(2^m).
After shifting past m0, discrete Gronwall gives

\[
\log(1+e_n)\le\log(1+e_0)+\log(1+nB)+\sum_{j<n}a_j.
\]

Cesàro convergence makes the last sum o(n), and log(1+nB)=o(n). Meanwhile the
physical-head denominator is at least (n+1)log2 along S_n=2^(n+m0+1).
Thus log(1+E_(S_n))/log(S_n+2)→0, and the existing checked cofinal theorem gives RH.

This establishes a CONDITIONAL implication. It does not supply the boxed
arithmetic estimate. In general it gives exp(o(m)) growth in the dyadic
index, not polynomial growth in m. The handoff's A/(m+1) hypothesis is a
checked corollary. No interpolation, monotonicity, or optimizer positivity
assumption is used.

Modules: [DyadicGronwall.lean](../Analysis/DyadicGronwall.lean) and
[QCRTDyadicBudget.lean](QCRTDyadicBudget.lean).
Principal declaration: `riemannHypothesis_of_vanishing_dyadic_trial_budget`;
the harmonic version is `riemannHypothesis_of_harmonic_dyadic_trial_budget`.

## 6. Complete-period numerical diagnostics: exploratory only

The [reproducible source and output](FullFloorDiagnostics20261030.md) use every
conductor and aggregate the entire infinite tail by trigamma period weights
ψ₁(r/L)/(ζ(2)L²).
These are double-precision calculations, not interval certificates or Lean
proofs of the printed inequalities. Condition numbers reach about 4.18e6;
maximum head residuals are about 4.8e−15. Those residuals alone do not bound
the error in energies or sources.

For the trial f=F_i, representative computed gains are:

| p | Old head cost | Actual full gain | Baseline gain | Head-refined gain | Exact-direction optimum, numerical |
|---:|---:|---:|---:|---:|---:|
| 5 | .25224968 | .18526149 | .07253427 | .11293752 | .11424775 |
| 7 | 0 | .01113813 | .00154291 | .00243661 | .00247450 |
| 11 | .02841482 | .00594893 | .00045137 | .00074433 | .00074515 |
| 13 | .02589571 | .00296443 | .00017503 | .00028749 | .00028788 |
| 17 | 0 | .00356932 | .00024316 | .00039879 | .00039958 |

The last column optimizes the scalar along D_pF_i using its numerically
evaluated full norm, without old-tangent screening. At p=11,13 the refined
norm bound is already close to that norm, while the direction captures only
a small part of the full available gain. This suggests prioritizing better
source directions or screening rather than further refining this norm bound.
It does not rule out an aggregate argument using such trials.

Consecutive-stage block totals, including intervening stages, are:

| Interval [M,N) | Actual E_N−E_M | Sum of head-refined self-trial upper bounds |
|---|---:|---:|
| [1,2) | .06698819 | .13931216 |
| [2,4) | .00674362 | .01544513 |
| [4,8) | .04182785 | .05287993 |

For example, stage i=3 has no new prime and adds about .01788174 of head cost.
It cannot be omitted. At nonsquarefree sites the table uses the raw trial's
upper bound, which may be weaker than the exact negative fullCertificate.
Finite data cannot prove or refute the eventual bound with freely chosen B,m0.

## 7. Remaining research agenda

1. **Open arithmetic provider:** prove the signed block estimate (OPEN), or
   another cofinal subpolynomial complete-energy bound. Only a_m→0 is required.
2. Use `divisorTrial` to build arithmetic coefficient arrays on every old divisor.
   Include the d=1 anchor and all off-diagonal terms. The exact transport work
   no longer needs repeating.
3. Improve source capture with several floor directions and their complete
   mixed Gram form, or screen them against the old next-head tangent. Start
   with actual optimizer directions and structured divisor layers.
4. Keep complete interval accounting. Record head costs, actual gains,
   certified trial gains, loss squares, and signed totals separately.
5. Upgrade promising small-period calculations to interval enclosures or
   another explicit error certificate before using them to refute universal
   statements. Small floating residuals are not such a certificate.
6. Do not assume optimizer positivity, a uniform inverse-Gram bound, or that
   exhaustive dictionary indexing itself implies constant approximation.

An optional paper reformulation of (OPEN): seek fixed B≥0 and trials with
R_m=(Σ_block C_i−B)_+/(1+E_(2^m))→0. Eventually R_m≤1, so Σ_block C_i≤
R_m E_(2^m)+B+1. Conversely (OPEN) implies R_m≤a_m. Take the positive part
AFTER the signed sum. This reformulation is not separately formalized here.

## 8. Sources and verification

The proof inputs are the attached handoff, the pinned project declarations,
and Mathlib. Web review included Báez-Duarte's
[A strengthening of the Nyman–Beurling criterion](https://arxiv.org/abs/math/0202141),
which treats integer dilations in a continuous L² model. It is background
context, not a provider of the discrete optimizer budget or an unchecked
identification with this Q model. Wolfram confirmed the elementary scalar
substitution c−2(ps/e)s+(ps/e)²e/p=c−ps²/e; Lean checks the actual inequalities.

Serialized candidate checks:

- `job_L_9qR6if92eUK5UQy2GRV4dLd7KPcBmy`: full divisor transport, baseline
  actual-optimizer trial, general dyadic consumer and harmonic corollary;
  success, server-reported Lean time 6.775 seconds.
- `job_j-LYflBA8X2wA--fY9fWd7qwGvbyhM5e`: exact head-tail identity,
  denominator positivity, and refined actual-optimizer trial;
  success, server-reported Lean time 6.930 seconds.
- `job_yKz32OfbJVgtcLGeOZQMGBKwyCsktbLX`: explicit finite-head Pareto-gap
  lower bound; success, server-reported Lean time 5.679 seconds.

Selected axiom audits report only propext, Classical.choice, and Quot.sound.
This does not discharge the explicit arithmetic hypothesis of the RH theorem.
Opening/request round trips and queue/polling delays were not separately
timed; the quoted times are server verification durations only.

Final saved-source project validation and publication are performed by the
single server checkpoint reported with delivery. Isolated checks are not
represented as whole-project validation. The resumed workspace token is
`ws_TwRqvO23-6zktAShLltSEtGhXbW-qxTY`; retain any continuation workspace
returned by that checkpoint rather than replacing or resetting the clone.

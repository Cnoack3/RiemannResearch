# Crossed-distance continuation for the full-conductor displacement

Date: 6 November 2026
Researcher: Christian Noack
Base: c5048493b640fa6d8b395b4384fefbbeee5ea33d

Source: the user-provided Isometric_Transport_Lean_Handoff_2026-11-06.md,
Section 5 and research priorities 1--5. The square-root correction,
polarization estimate, and complete head certificates develop that argument.
No mathematical priority claim is made.

## Status

The previously paper-only two-distance result now has Lean proofs using the
actual full-conductor displacement and both normal equations. There is also
a quadratic trial-error estimate and a shared corrected target for the two
crossed approximation problems.

This does not establish vanishing of the actual distances, d=0, or RH.
The new RH implications are conditional research reductions.

## Definitions and exact signed identity

Retain Z=zeta(2), Q(n)=1/(Z n^2), P(n)=1/(n(n+1)), and all conductors m>=2.
Let V_Q be the full Q closure, V_P its same-physical-sequence Pareto image,
A:H_Q -> H_P the isometry, and I:H_Q -> H_P the map preserving physical
sequences. W=A(V_Q) is kept separate from V_P.

Define
\[
T=A^{-1}I,\quad (Tf)(n)=\sqrt{\frac{Zn}{n+1}}f(n),\quad
q(f)=\langle f,Tf\rangle_Q.
\]
T is named inversePhysical in Lean; it is not the inverse of I.
The exact coordinate formula and symmetry imply
\[
\sqrt{Z/2}\|f\|_Q^2\le q(f)\le\sqrt Z\|f\|_Q^2.
\]

With d=f_Q-f_P and r_P=r_Q+d, define
\[
a(g)=\operatorname{dist}_P(Ag,V_P),\quad
b(g)=\operatorname{dist}_P(Ig,W),\quad
\Delta(g)=\|r_P\|_P a(g)+\|r_Q\|_Q b(g).
\]
For every g, not merely legal g,
\[
F(g):=\langle Ir_P,Ag\rangle_P-\langle r_Q,Tg\rangle_Q
=\langle d,Tg\rangle_Q.
\]
Both residual terms remain. Orthogonality and Cauchy--Schwarz give
F(g)<=Delta(g).

## Checked criterion and quadratic estimate

The handoff's exact-target inequality and membership criterion are checked:
\[
\sqrt{Z/2}\|d\|_Q^2\le\Delta(d),\qquad
d=0\iff(Ad\in V_P\ \text{and}\ Id\in W).
\]
Both crossed memberships are used.

For e=||g-d||_Q, the requested trial estimate is also checked:
\[
\sqrt{Z/2}\|d\|_Q^2
\le\|r_P\|_P(a(g)+e)+\|r_Q\|_Q(b(g)+\sqrt Z\,e).
\]
The exact polarization identity
\[
q(d)+q(g)=2F(g)+q(d-g)
\]
gives the additional estimate
\[
\boxed{\sqrt{Z/2}\|d\|_Q^2+q(g)
\le2\Delta(g)+\sqrt Z\|d-g\|_Q^2.}
\]
The positive trial energy is retained. This trades a factor 2 on Delta
for a quadratic approximation penalty; it need not dominate the linear
estimate for every trial.

For any G_M -> d in Q, Lean proves
\[
d=0\iff\Delta(G_M)\to0,\qquad d=0\iff F(G_M)\to0.
\]
Thus simultaneous a(G_M)->0 and b(G_M)->0 imply RH. The signed formulation
permits cancellation without separate absolute estimates on both
pairings. These are equivalent criteria under the convergence hypothesis,
not unconditional vanishing results.

## Shared corrected target and complete tails

Define
\[
J=1-Z^{-1/2}T,\qquad
(Jf)(n)=\left(1-\sqrt{\frac n{n+1}}\right)f(n).
\]
The proved zero-based coordinate bounds are
\[
0\le1-\sqrt{\frac{n+1}{n+2}}\le\frac1{n+2}.
\]
If the first N positive physical coordinates of f vanish,
\[
\boxed{\|Jf\|_Q\le\frac{\|f\|_Q}{N+2}.}
\]
This controls the entire remaining infinite tail.

For legal g,h,k in V_Q, the explicit legal competitors yield
\[
a(g)\le\|Jg-Th\|_Q,\qquad
b(g)\le\sqrt Z\|Jg-k\|_Q.
\]
The competitors are I(Z^(-1/2)g+h) in V_P and A(sqrt(Z)(g-k)) in W.

If an arbitrary v matches the first N coordinates of g, set
E=||g-v||_Q/(N+2). Lean proves the complete certificate
\[
\begin{aligned}
\sqrt{Z/2}\|d\|_Q^2+q(g)
\le{}&2\{\|r_P\|_P(\|Jv-Th\|_Q+E)\\
&+\|r_Q\|_Q\sqrt Z(\|Jv-k\|_Q+E)\}
+\sqrt Z\|d-g\|_Q^2.
\end{aligned}
\]
No legality of v is assumed. For a finite coordinate truncation v, target
pairings are finite sums, but correction norms still use complete
Gram matrices including the infinite tails.

## Second inverse application

The exact operator equality and its full-displacement consequence are
\[
T^2f=Z(f-Rf),\qquad d=0\iff T^2d\in V_Q.
\]
R is still named QShiftedReciprocal.B. Membership Td in V_Q alone is not
promoted to membership of T^2d. No global invariance is assumed.

## Declaration map

| Module | Principal declarations |
|---|---|
| Analysis/OrthogonalDistanceBound.lean | Submodule.abs_real_inner_le_norm_mul_infDist_of_mem_orthogonal |
| RH/QParetoSquareRootEnergy.lean | inversePhysical, inverseEnergy_lower, inverseEnergy_upper, inverseEnergy_polarization, inversePhysical_square |
| RH/QParetoSquareRootEnergy.lean | rootDefect_apply, rootDefect_weight_bounds, rootDefect_norm_le_of_head_zero, rootDefect_head_trial_bound |
| RH/QFullCrossedDistances.lean | signedTest_eq, two_distance_bound, two_distance_trial_bound, quadratic_two_distance_bound |
| RH/QFullCrossedDistances.lean | displacement_eq_zero_iff_crossed_membership, displacement_eq_zero_iff_budget_tendsto_zero, displacement_eq_zero_iff_signedTest_tendsto_zero |
| RH/QFullCrossedDistances.lean | forwardDistance_le_rootDefect_trial, inverseDistance_le_rootDefect_trial, two_distance_head_certificate |
| RH/QFullCrossedDistances.lean | displacement_eq_zero_iff_second_inverse_mem, riemannHypothesis_of_crossed_distance_limits, riemannHypothesis_of_signedTest_limit, riemannHypothesis_of_second_inverse_mem |

The general measure-specific declarations retain the namespace
RiemannResearch.RH.QParetoIsometricTransport. The application namespace is
RiemannResearch.RH.QFullCrossedDistances.

## Verification

The assembled module import and seven principal axiom audits passed
job_Odin6V3Y3pnftimYSpdTePhqM2miJeiF:
verified=true, exit code 0, server-reported elapsed 20.679 seconds.
The job built all three new modules. Every audited declaration depends
only on propext, Classical.choice, and Quot.sound.

This source check is distinct from the publication checkpoint.
Publication is gated by aggregate and changed-module server validation.
No new axiom, unsafe declaration, sorry, or admit is present in these additions.

## Remaining RH obligations

1. **Open:** construct actual legal h_M,k_M for legal G_M -> d with both
   complete J-target errors tending to zero. The tail estimate controls
   the remainder but does not make the head correction costs vanish.
2. **Open:** prove signed cancellation F(G_M)->0 using arithmetic input.
   The normal equations identify its limit with q(d); reusing that
   identity alone would be circular.
3. **Open:** establish T^2d in V_Q, or control the second inverse application
   on a particular legal approximating family.
4. For finite experiments, minimize ||Jv-Th||_Q^2 and ||Jv-k||_Q^2 using
   the same head target and complete P/Q Gram matrices. Retain E.
   Exact head interpolation without the complete energies is insufficient.
5. Compactness of J and weak-to-strong transfer for bounded approximants
   are possible further formalizations. They are not newly formalized
   here and would yield convergence to Jd, not zero distance of Jd.

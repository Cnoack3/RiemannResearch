# Selberg Gaussian rays and Estermann convergence — research continuation

Prepared 15 November 2026, America/Los_Angeles.

## What this work closes

The ray-rotation obligation from the uploaded continuation is proved. For
\(\Delta,\omega>0\), arbitrary real \(l,u\), \(\tau\in\{1,-1\}\), and
\(0\le\theta<\pi\),
\[
E_{\tau\pi/2}(\omega)=\omega^{1-2l}\mathcal R_\tau(\omega,\theta).
\]
Both rays point outward. The definition includes the principal complex power,
the principal logarithm, frequency \(2\pi\omega\), and Jacobian
\(e^{i\tau\theta}\). This strengthens the requested sector and includes
the oscillatory endpoint \(\theta=0\). The logarithmic kernel is invariant
even on the closed half-sector \(0\le\theta\le\pi\);
the ray theorem excludes the negative-real principal-log cut.

The exact actual-moment formula is now a paired ray series, preserving
the original finite mollifier coefficients and the signed residue
\(-(2\sqrt\pi/\Delta)R_1\). The paired integrated series is absolutely
summable, including at angle zero.

Joint absolute convergence for the damped Estermann representation is
proved separately for \(0<\theta<\pi\). It supports arbitrary complex
exponents \(\alpha,\beta\), every positive modulus, and every residue class.
It does not require coprimality for convergence.

## Principal declarations

| Module | Declaration | Content |
| --- | --- | --- |
| Analysis/GaussianHorizontalShift.lean | Complex.integral_horizontal_eq_of_gaussian_bound | Cauchy rectangle, absolute convergence, both vertical limits |
| Analysis/GaussianRayRotation.lean | Complex.norm_gaussianRayLogKernel | Exact norm with signed center and damping |
| Analysis/GaussianRayRotation.lean | Complex.gaussianRayIntegrand_exp | Principal-log exponential substitution with Jacobian |
| Analysis/GaussianRayRotation.lean | Complex.gaussianRayIntegral_angle_independent | Both outward rays, all angles in [0,pi) |
| Analysis/ConreyBaluyotGaussianRays.lean | gaussianArithmeticEulerBranch_eq_ray | Actual Euler branch and exact frequency normalization |
| Analysis/ConreyBaluyotGaussianRays.lean | mollifiedGaussianMoment_eq_ray_series | Actual finite coefficients, paired rays, original residue |
| Analysis/ConreyBaluyotEstermannDampedSeries.lean | norm_estermannDampedTerm_le_shift | Explicit factorial damping majorant |
| Analysis/ConreyBaluyotGaussianEstermannIntegrability.lean | summable_integral_norm_gaussianEstermannRayTerm | Summability of integrals of norms in the radial variable |
| Analysis/ConreyBaluyotGaussianEstermannIntegrability.lean | integral_gaussianRay_mul_estermannDampedSeries | Exact outward-ray sum/integral exchange |

Unqualified declarations are in RiemannResearch.Analysis.ConreyBaluyot.

## Why degeneration of damping at the origin is controlled

For \(N\in\mathbb N\) and \(\operatorname{Im}w>0\), the proved bound is
\[
|\mathrm{Term}_{\alpha,\beta}(w;m,n)|
\le |\mathrm{Term}_{\alpha+N,\beta+N}(m,n)|
 \frac{N!}{(2\pi\operatorname{Im}w)^N}.
\]
Choose \(N\) large enough that both shifted real parts exceed one.
On the signed ray put
\[
w_\tau(r)=\tau a(re^{i\tau\theta}-1),\quad a>0.
\]
For either sign, \(\operatorname{Im}w_\tau(r)=a r\sin\theta>0\).
Writing \(r=e^x\), the extra factor is a constant times \(e^{-Nx}\).
It is absorbed exactly by replacing \(l\) with \(l+N\) in the undamped
Gaussian logarithmic kernel. The resulting norm is integrable on all
of \(\mathbb R\). This proves the sum of the norm integrals is finite
before applying Fubini.

The general logarithmic theorem allows any continuous profile \(w(x)\)
with \(\operatorname{Im}w(x)=d e^x\), \(d>0\), and arbitrary real line
height. The radial specialization explicitly proves the exponential
change of variables. No unproved convergence or tail provider occurs
among these theorem hypotheses.

The constants depend on fixed parameters. They do not establish uniform
bounds as \(u,\Delta\), mollifier length and evaluation line vary together.
The Fubini theorem requires positive damping and must not be specialized
to \(\theta=0\).

## Next concrete task: exact rational-twist assembly

The analytic exchange is available, but the actual finite mollifier
expression has not yet been identified with the final rational-twist
Estermann formula. Complete this as an exact identity, before estimating it:

1. For positive mollifier indices \(h,k\), set \(H=h/\gcd(h,k)\),
   \(K=k/\gcd(h,k)\). Prove positivity, coprimality and \(h/k=H/K\)
   with the actual Lean cast conventions.
2. Prove the coefficient identity for positive \(m,n,h,k\):
   \[
   \frac{a_h a_k n^{2l-1}}{k^{2l}}
    \left(\frac{mnh}{k}\right)^{1-2l}
   =\frac{a_h a_k h^{1-2l}}{k}\,m^{-(2l-1)}.
   \]
   In the actual estermannTerm, the first index has exponent alpha
   and the second has exponent beta, hence alpha = 2*l-1, beta = 0.
3. Identify ZMod.stdAddChar exactly with the rational phase
   \(\exp(\tau 2\pi i mnH/K)\), including the negative residue class.
4. Use
   \[
   e^{\tau2\pi i mn(H/K)z}
   =e^{\tau2\pi i mnH/K}
    e^{2\pi i mn\,\tau(H/K)(z-1)}
   \]
   and the proved ray Fubini theorem to assemble the actual finite
   \(h,k\) expression. Check the zero-index convention separately.
5. Retain the original signed Gaussian residue. A modulus-one zeta-product
   identity or an equality only of absolute values is insufficient.

## Downstream agenda, in dependency order

| Priority | Obligation | Acceptance criterion |
| --- | --- | --- |
| 1 | Actual rational-twist assembly above | Exact finite coefficients, both signs, reduced modulus, zero indices, residue |
| 2 | Global Estermann Mellin contour shift | Crossed poles, both remote sides, vertical convergence, coincident-pole cases |
| 3 | Complete signed decomposition | Define and identify M1 + M2 + D1 + D2 + E exactly |
| 4 | Complete and multilinear Kloosterman estimates | Full modulus/gcd/coefficient/range hypotheses; complete-sum input proved |
| 5 | Cofinal uniform Gaussian moment provider | One eta,C,H for every later T,sigma and every padded center |
| Independent | Actual Ingham provider | Fourth moment, moving line, strip interpolation, zero detection and actual counts |
| 6 | Existing density assembly | Apply the proved cofinal assembly only after both providers exist |

Do not restart the Gamma/Euler/Fubini transform, Gaussian rightward shift,
ray rotation, damped-ray absolute convergence, or Ingham I2 as open work.
I2 is closed by ActualInghamMollifierMoment.lean.
The independent target ActualZeroOrdinate.InghamDensityBound remains a
classical theorem needing a complete formal provider. It must not be
obtained by assuming the desired Selberg conclusion.

The cofinal UniformGaussianMollifiedMoment requirement, including all
padded centers, remains open in this formalization. The checked parameter
budgets are not providers of the analytic bounds. No RH proof follows
from the identities and fixed-parameter convergence proved here.

## Source and verification conventions

Primary source for the arithmetic strategy:
S. A. C. Baluyot, *On the Zeros of Riemann's Zeta-function* (2017),
Lemma 3.1.7 and Section 3.3, printed pp. 104–105 and 116–117:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320

The logarithmic-coordinate rectangle proof follows the user-provided
continuation note. The widened sector is a strengthened formal statement;
no mathematical novelty claim is made.

The first publication is commit d04324c890889106d080f059b3b302ebe1adbe03,
full checkpoint job_oM0RgjSeqy80Kf3p8bNHcdDW-4dtOkGY, BuildBuddy
https://app.buildbuddy.io/invocation/a1417206-4fce-45d0-84ed-f5b329f9d693 .
The guarded ray/Euler/moment axiom audit passed as
job_hbFbFyV7gSjovhEPeKoA-THtgfExtb0Y, with only
propext, Classical.choice, and Quot.sound.

The second publication is commit 82f398c798c4183b28dd2eb3f793584c983a8531,
full checkpoint job_Iv0MPxeRJV_rDTL8TiUcjTGsAfk6t01e, BuildBuddy
https://app.buildbuddy.io/invocation/bdf544f7-5233-4d95-9763-04973ff41150 .
The joint-convergence module passed focused check
job_ow_aO7e7_CW8BdGBWCNCWJsWVWoRVvWw, BuildBuddy
https://app.buildbuddy.io/invocation/8b845221-8a90-467b-bd92-bb01b94d5d34 .

Every publication uses the full Bazel //:RiemannResearch target with
--config=buildbuddy. Inspect the final checkpoint record and current
main before continuing; focused checks alone do not validate downstream
consumers. There are no added placeholders or project-local axioms.

Retained workspace: ws_31tMKAR46tiC_VssdKfGnvEjQdQcWlPf.

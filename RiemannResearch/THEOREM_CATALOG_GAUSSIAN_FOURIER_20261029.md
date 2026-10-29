# Gaussian polynomial Fourier transform: theorem catalog supplement

29 October 2026.

## Established Gaussian analysis

The new module
[Analysis/GaussianPolynomialFourier.lean](Analysis/GaussianPolynomialFourier.lean)
uses the normalization
\[
T f(u)=\frac1{2\pi}\int_{\mathbb R}e^{-iux}f(x)\,dx.
\]
It is independent of the contour argument and of the actual zeta zeros.

For \(R>0\), define
\[
F_R(u)=\frac{e^{-u^2/(4R)}}{\sqrt{4\pi R}},\qquad
M_k(R,u)=\frac1{2\pi}\int_{\mathbb R}x^k e^{-Rx^2}e^{-iux}\,dx.
\]
The Lean definition `density` is complex-valued, with
`density_eq_real` proving that it is precisely the complexification
of the displayed real function. Derivatives are with respect to the real
frequency variable.

All names in the following table belong to
`RiemannResearch.Analysis.GaussianPolynomialFourier`.

| Declaration | Exact content |
|---|---|
| `transform_eq_fourier` | \(Tf(u)=(2\pi)^{-1}\mathcal F_{\rm Mathlib}f(u/(2\pi))\); valid for every complex-valued function. |
| `gaussian_integral` | \(\int_{\mathbb R}e^{-Rx^2}\,dx=\sqrt{\pi/R}\), complexified. |
| `gaussian_prefactor`, `real_normalization` | Complex square-root branch and real \(2\pi\) normalization identities. |
| `integrable_momentFunction` | \(x^k e^{-Rx^2}\) is Bochner integrable for every \(k\in\mathbb N\). |
| `norm_phase`, `integrable_transformIntegrand` | The Fourier phase has norm one; multiplying an integrable function by it preserves integrability. |
| `moment_zero` | \(M_0(R,u)=F_R(u)\). |
| `hasDerivAt_density` | \(F_R'(u)=-uF_R(u)/(2R)\). |
| `hasDerivAt_transform` | \((Tf)'=-iT(xf)\), with the explicit general assumptions \(f,xf\in L^1\). |
| `hasDerivAt_moment` | \(M_k'=-iM_{k+1}\), with those general assumptions discharged by the Gaussian integrability theorem. |
| `iteratedDeriv_density`, `moment_eq_iteratedDeriv` | \(D^kF_R=(-i)^kM_k\), equivalently \(M_k=i^kD^kF_R\), for every \(k\). |
| `moment_one` | \(M_1=-iuF_R/(2R)\). |
| `moment_two` | \(M_2=(1/(2R)-u^2/(4R^2))F_R\). |
| `transform_const_mul`, `transform_add`, `transform_sum` | Scalar and finite-sum rules; addition and sums carry the needed integrability assumptions. |
| `transform_sub` | Translation by \(\tau\) gives exactly the multiplier \(e^{-i\tau u}\). |
| `polynomialFunction_eq_sum`, `integrable_polynomialFunction` | Every real polynomial times the Gaussian is the finite sum of its integrable moments. |
| `transform_polynomial` | Exact finite polynomial moment formula at \(\tau=0\). |
| `integrable_test`, `transform_test` | Integrability and the full shifted formula for every real polynomial. |
| `polynomialTransform`, `polynomialTransform_X_pow` | The actual transform is a real linear map on polynomials, with its monomial values identified analytically. |

In particular, for an arbitrary `B : Polynomial ℝ`, the main theorem
`transform_test` establishes
\[
\boxed{\frac1{2\pi}\int_{\mathbb R}
 B(t-\tau)e^{-R(t-\tau)^2}e^{-itu}\,dt
=e^{-i\tau u}\sum_{k\in\operatorname{support}(B)}
 b_k i^kD^kF_R(u).}
\]
Only \(R>0\) is required. The center and frequency are arbitrary real numbers.
There are no Gaussian domination, differentiability, or integrability assumptions
left for the caller to prove.

The proof reuses Mathlib's real and complex Gaussian integrals,
`integrable_rpow_mul_exp_neg_mul_sq`, and
`Real.hasDerivAt_fourier`. The arbitrary-order formula follows
by induction from the first-derivative identity. The optional explicit
factorial/Hermite expansion in equation (2.2) of the memorandum is not needed
for this theorem and has not been formalized here.

## Established connection to finite matrix algebra

[Analysis/GaussianFourierMatrix.lean](Analysis/GaussianFourierMatrix.lean)
has namespace `RiemannResearch.Analysis.GaussianFourierMatrix`.

For fixed \(R>0,\tau,u\), `realFunctional` is the actual functional
\[
L_u(B)=\Re\,T\!\left(B(\,\cdot-\tau)e^{-R(\,\cdot-\tau)^2}\right)(u).
\]
`realMoment` is its explicitly computed monomial sequence.
The declarations `realFunctional_X_pow`,
`fourier_quadratic`, and
`fourier_poleReduced_quadratic` instantiate the existing finite
Hankel and pole-reduced Hankel identities for this concrete analytic functional.

In particular,
\[
L_u(P^2)=c^{\mathsf T}H_uc,\qquad
L_u((D_\tau P)^2)=c^{\mathsf T}
 H(\operatorname{poleReducedMoment}(\mu,\tau))c,
\quad \mu_k=L_u(w^k).
\]
This identifies the Fourier contribution used by the arithmetic matrix. It does
not identify \(L_u\) with the complete explicit-formula functional (5.1).
No positivity is asserted.

## Verification evidence and publication gate

The complete analysis and matrix bridge were checked together by Lean server job
`job_O96lrQPCXRTE__PwrE1fPxpt6nlRtDVX`: exit code 0,
`verified: true`, reported verification duration 5.702 seconds.
The earlier analysis-only check
`job_sj9K4qWYKp0Ttx33aJVGuOllGrwBQAdO` also succeeded.

Axiom inspection of the shifted polynomial theorem, both low-order moments,
and the pole-reduced bridge reported only
`propext`, `Classical.choice`, and `Quot.sound`.
There are no project-local axioms or proof placeholders.

The saved matrix module and its Gaussian-analysis dependency also passed
server file-check job `job_ghu2oamjUVMv_srioD5WRVZd1xNjvYAD`: exit code 0,
`verified: true`, reported duration 12.869 seconds. Its output records the
Gaussian-analysis module build.

Final publication is gated by the separate server checkpoint, which audits source,
builds the changed modules and required dependents, and publishes only on
success. A snippet alone does not certify the aggregate project.

The combined snippet's recorded server queue delay was about 0.006 seconds.
Its 5.702-second verification duration is not a workspace-opening or request
round-trip measurement. Workspace-opening and client polling latency were not
separately instrumented; no cause for that wall-clock delay is inferred.

## Remaining analytic obligations: Open

The following parts of the actual-zeta connection remain outside this
formalization:

1. Uniform Gaussian-polynomial bounds on horizontal complex strips and the
   complex-argument inverse Fourier formula.
2. Absolute convergence of the infinite prime-power contribution, the
   archimedean gamma-weighted integral, and the multiplicity-weighted zero sum.
3. The completed-zeta contour argument, including good-height estimates,
   vanishing horizontal edges, residues, and legitimate contour shifts.
4. Identification of the complete arithmetic functional with actual zeta zeros,
   with both pole terms present before the pole-factor restriction.
5. Assembly of that actual-zero identity with the existing conditional
   localization theorems, supplying their summability and majorant providers.
6. The independent universal signed lower bound needed for the RH criterion.

The finite Fourier and matrix theorems above make no RH assumption and do not
discharge these obligations.

## Provenance

- [GaussianActualZetaExplicitFormula20261029.md](RH/GaussianActualZetaExplicitFormula20261029.md),
  Section 2, supplies the intended Fourier statements and normalization;
  Sections 5--6 supply the matrix application.
- Mathlib revision `51e6992efd06126df61a496bebf8f49482a4e129`
  (project toolchain v4.33.0-rc2), especially
  `Analysis/SpecialFunctions/Gaussian/{GaussianIntegral,FourierTransform}.lean`
  and `Analysis/Fourier/FourierTransformDeriv.lean`,
  supplies the analytic proof infrastructure.

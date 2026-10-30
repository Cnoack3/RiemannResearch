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

## Established strip bounds and inverse-transform admissibility

[Analysis/GaussianPolynomialStrip.lean](Analysis/GaussianPolynomialStrip.lean)
proves the uniform complex-strip estimate, including complex coefficients.
The general polynomial constant and bound belong to namespace Polynomial;
the other declarations belong to
RiemannResearch.Analysis.GaussianPolynomialStrip.

| Declaration | Exact content |
|---|---|
| stripGrowthConstant, stripGrowthConstant_nonneg | Explicit nonnegative coefficient constant Σ_k ‖P.coeff k‖(1+b)^k for b ≥ 0. |
| norm_eval_le_stripGrowthConstant | Degree-sharp polynomial bound on a horizontal strip. |
| norm_gaussian, norm_test | Exact complex Gaussian and polynomial-Gaussian modulus identities. |
| norm_test_le, norm_real_test_le | Uniform strip bound, with R ≥ 0 and b ≥ 0; real and complex coefficients. |
| test_ofReal, differentiable_test | Agreement with the existing real test and an entire extension. |
| integrable_abs_pow_gaussian, integrable_one_add_abs_pow_gaussian | Integrability of absolute polynomial Gaussian moments for R > 0. |
| integrable_majorant, integrable_weighted_majorant | Integrable common strip envelope, including every fixed polynomial weight. |
| strip_domination, integrable_horizontal | Packaged uniform domination and integrability on every horizontal line. |
| tilt_exponent_identity, exp_tilt_gaussian_le | Exact completed square and the resulting exponential-tilt estimate. |
| integrable_tilted_majorant | Integrability after every fixed exponential tilt and polynomial weight. |
| norm_inverse_phase, norm_inverse_phase_le | Exact inverse-phase modulus and its strip bound. |
| norm_inverse_moment_le_of_bound, integrable_inverse_moment_of_bound | Reusable inverse-kernel results with an explicit Gaussian-envelope hypothesis. |

For a real polynomial B of degree M (natDegree, including B = 0), the constant is
\[
 C_{B,b}=\sum_{k\in\operatorname{support}(B)}|b_k|(1+b)^k,
\]
and the checked result is
\[
 |B((x-\tau)+iy)e^{-R((x-\tau)+iy)^2}|
 \le C_{B,b}(1+|x-\tau|)^M e^{Rb^2}e^{-R(x-\tau)^2}.
\]
The bound holds for every |y| ≤ b. The constant is independent of R and τ.

[Analysis/GaussianPolynomialFourierGrowth.lean](Analysis/GaussianPolynomialFourierGrowth.lean)
supplies the envelope for the actual transform. Its namespace is
RiemannResearch.Analysis.GaussianPolynomialFourierGrowth.

| Declaration | Exact content |
|---|---|
| derivativePolynomial, iteratedDeriv_density_eq_polynomial | Exact recurrence Q₀ = 1, Qₖ₊₁ = Qₖ′ - XQₖ/(2R), and DᵏF_R = Qₖ F_R. |
| frequencyPolynomial, transform_test_eq_frequencyPolynomial | Exact finite polynomial A giving g_B(u) = exp(-iτu) A(u) F_R(u). |
| frequencyConstant, frequencyConstant_nonneg, norm_transform_test_le | Explicit Gaussian envelope for the actual Fourier transform. |
| continuous_transform_test, integrable_transform_test, continuous_real_test | Continuity/integrability inputs for inversion. |
| integrable_inverse_transform_moment | Absolute integrability of u^N exp(izu) g_B(u) for every complex z and natural N. |
| inverseMajorant, integrable_inverseMajorant, norm_inverse_transform_moment_le | A common explicit integrable envelope on every fixed horizontal strip. |

With L = natDegree(A) and K = Σ_j |A.coeff j| / sqrt(4πR), that envelope is
\[
 |u^N e^{izu}g_B(u)|
 \le K e^{2Rb^2}(1+|u|)^{L+N}e^{-u^2/(8R)}
 \quad (|\operatorname{Im}z|\le b).
\]
It is uniform in real τ. The frequency-degree bound L ≤ M is not separately
formalized; the actual finite degree L is sufficient.

These are unconditional analytic inputs for the inverse theorem. The
frequency-scaling assembly, holomorphy of the inverse parameter integral,
and complex inverse identity are now checked in the companion inversion modules
listed below. The actual-zeta identity, zero-sum convergence, contour theorem,
and RH conclusion remain separate obligations.

See [GaussianPolynomialStripBounds20261029.md](RH/GaussianPolynomialStripBounds20261029.md)
for the full argument, exact hypothesis map and remaining obligations.

### Strip and growth verification

Combined snippet job job_WTRmOeGGXhGP78sl2VqB9o2v_Zk9G5gz succeeded with
exit code 0, verified true and reported server verification duration 5.716 s.
Eight main declarations were inspected: only propext, Classical.choice and
Quot.sound occurred. No project-local axiom or proof placeholder was used.

Saved-file job job_8ja17-4p31eZrOrb75A9G4OYWecD36Cm checked the growth file
and built its strip dependency: exit code 0, verified true, reported 13.524 s.
Only copyright-header style warnings were reported. Final publication remains
gated by the separate checkpoint audit and affected-project validation.

The combined snippet's queue delay was about 0.002 s. Workspace-opening and
client polling delays were not separately instrumented; the server duration
does not measure either delay.

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

## Established complex Gaussian-polynomial inversion

[Analysis/GaussianFourierInversion.lean](Analysis/GaussianFourierInversion.lean)
adds general results in namespace
RiemannResearch.Analysis.GaussianPolynomialFourier:

| Declaration | Exact content |
|---|---|
| fourier_eq_scaled_transform | Mathlib F f(v) = 2π transform f(2πv). |
| inverse_integral_eq_fourierInv | Exact inverse-kernel substitution, including its Jacobian. |
| integrable_fourier_of_integrable_transform | Integrability transfers to Mathlib's transform. |
| inverse_integral_eq | Real inversion for arbitrary f with f and transform f integrable, at a continuity point. |

[Analysis/GaussianPolynomialFourierInversion.lean](Analysis/GaussianPolynomialFourierInversion.lean)
assembles the Gaussian-polynomial application in namespace
RiemannResearch.Analysis.GaussianPolynomialFourierInversion:

| Declaration | Exact content |
|---|---|
| inverse | The actual inverse parameter integral. |
| hasDerivAt_inverse, differentiable_inverse | Derivative under the integral and entire differentiability, with the actual first-moment majorant. |
| inverse_ofReal | Real inversion using the checked Gaussian providers. |
| inverse_eq_test, test_eq_inverse_integral | h_B(z) = integral exp(izu) g_B(u) du for every complex z. |
| test_eq_laplace_integral | h_B((s-1/2)/i) = integral exp((s-1/2)u) g_B(u) du for every complex s. |
| integrable_laplace_kernel | Absolute integrability of the Laplace kernel for every complex s. |

The specialized statements require only R > 0, real τ and a real polynomial B.
They include the zero polynomial and all complex arguments. They impose no
zeta, zero-counting, contour, summation, positivity or RH hypothesis.

The saved modules passed server job job_HqGBlxJ5_GZ3Q2Nwk388PWI7LL87vBwa:
exit code 0, verified true, reported duration 12.576 seconds. Both modules were
built, and five inspected declarations reported only propext, Classical.choice
and Quot.sound. The initial coherent proof candidate passed
job_0X92M-JVt_H39SKGu7OcNB0GqFgVyJDd (5.268 seconds).
Final publication is gated separately by checkpoint audit and affected-module
validation. These durations exclude workspace-opening and client polling latency,
which were not measured separately.

See [GaussianPolynomialFourierInversion20261029.md](RH/GaussianPolynomialFourierInversion20261029.md)
for the self-contained proof, precise hypothesis map and remaining research agenda.

## Established Gaussian prime-power convergence and right-line interchange

The 30 October 2026 development adds the following modules.

| Module / namespace under RiemannResearch.Analysis | Declarations and exact scope |
|---|---|
| GaussianLogDecay | completed_square retains the exact square remainder; polynomial_gaussian_le gives the global explicit Gaussian-to-exponential bound; exp_neg_nat_mul_log converts it to inverse powers. |
| GaussianPolynomialPrimePower | norm_transform_log_le and norm_transform_neg_log_le bound the actual transform at both signs of log n by C_k/n^k, with C_k=frequencyConstant R B * exp(R*(M+k)^2). |
| GaussianPolynomialPrimePower | absoluteTerm_le gives the global 2*C_3/n^2 majorant; summable_absoluteTerm proves absolute prime-power convergence over all natural numbers. |
| GaussianPolynomialPrimePower | summable_term proves summability of the unchanged complex two-sided contribution; term_prime_pow retains every p^k with coefficient log(p)/sqrt(p^k). |
| VonMangoldtVerticalIntegral | integrable_mul_term_vertical and summable_integral_norm_mul_term discharge the Bochner series-integral hypotheses for any L1 test on Re(s)=sigma>1. |
| VonMangoldtVerticalIntegral | integral_mul_neg_logDeriv_eq_tsum interchanges the actual -zeta'/zeta Dirichlet series with the real-parameter vertical integral, using Mathlib's actual zeta identification. |
| GaussianPolynomialPrimePower | integral_right_neg_logDeriv_eq_tsum specializes that interchange to h_B(t+i*(1/2-sigma)); horizontal Gaussian integrability is supplied, not assumed. |

The specialized summability theorems assume only R>0, a real center and a real
polynomial (zero included). The right-line theorem additionally assumes
sigma>1. There are no RH or zero-location assumptions. The constants are
uniform in the real center, not asserted uniform in R or B.

See [GaussianPolynomialPrimePowerSummability20261030.md](RH/GaussianPolynomialPrimePowerSummability20261030.md)
for the proof, exact hypothesis map, verification records and remaining steps.
The shifted-transform term evaluation is separate from the proved interchange.

## Remaining analytic obligations: Open

The following parts of the actual-zeta connection remain outside this
formalization:

1. The shifted-transform term evaluation, the archimedean gamma-weighted
   integral, and the multiplicity-weighted zero sum. Absolute convergence of
   the full prime-power contribution and the sigma>1 sum-integral interchange
   are now supplied by the checked Gaussian prime-power modules above.
2. The completed-zeta contour argument, including good-height estimates,
   vanishing horizontal edges, residues, and legitimate contour shifts.
3. Identification of the complete arithmetic functional with actual zeta zeros,
   with both pole terms present before the pole-factor restriction.
4. Assembly of that actual-zero identity with the existing conditional
   localization theorems, supplying their summability and majorant providers.
5. The independent universal signed lower bound needed for the RH criterion.

The Fourier, strip, growth, inversion and matrix results make no RH assumption.
The remaining obligations listed here are not discharged by them.

## Provenance

- [GaussianActualZetaExplicitFormula20261029.md](RH/GaussianActualZetaExplicitFormula20261029.md),
  Section 2, supplies the intended Fourier statements and normalization;
  Sections 5--6 supply the matrix application.
- Mathlib revision `51e6992efd06126df61a496bebf8f49482a4e129`
  (project toolchain v4.33.0-rc2), especially
  `Analysis/SpecialFunctions/Gaussian/{GaussianIntegral,FourierTransform}.lean`
  and `Analysis/Fourier/FourierTransformDeriv.lean`,
  supplies the analytic proof infrastructure.

# Gaussian polynomial strip bounds and inverse-transform admissibility

29 October 2026.

## Result and scope

The strip estimate from Section 3 of
[GaussianActualZetaExplicitFormula20261029.md](GaussianActualZetaExplicitFormula20261029.md)
is proved with an explicit constant. The development also gives a finite
polynomial representation of the actual Fourier transform and integrable
majorants for every complex inverse kernel and every fixed frequency moment.
These results are unconditional for R > 0 and contain no zeta or RH assumption.

The full complex inverse-transform equality and actual-zeta explicit formula
are not declarations in this development.

## 1. Definitions and exact identity

Let R > 0, τ ∈ ℝ, b ≥ 0, and let B(w) = Σ b_k w^k be a real polynomial.
Put M = natDegree(B), using M = 0 for the zero polynomial, and define
\[
 h_B(z)=B(z-\tau)e^{-R(z-\tau)^2},\qquad
 C_{B,b}=\sum_{k\in\operatorname{support}(B)}|b_k|(1+b)^k.
\]
The constant is nonnegative and independent of R and τ.
The formal result also allows complex coefficients, with their complex norms.

For real t,y, the exact identities are
\[
 -R(t+iy)^2=-Rt^2+Ry^2-2iRty,\qquad
 \boxed{|e^{-R(t+iy)^2}|=e^{-Rt^2+Ry^2}.}
\]
The theorem norm_gaussian proves the modulus equality for every real R.
Nonnegativity of R is used only when replacing y² by b².
The theorem norm_test preserves the exact factor
\[
 |h_B(x+iy)|=|B((x-\tau)+iy)|e^{-R(x-\tau)^2+Ry^2}.
\]

## 2. Explicit polynomial growth

If |y| ≤ b, then
\[
 |t+iy|\le |t|+b\le(1+b)(1+|t|).
\]
For each nonzero coefficient, k ≤ M, and hence
\[
 |B(t+iy)|
 \le\sum_k |b_k||t+iy|^k
 \le C_{B,b}(1+|t|)^M.
\]
Combining this with the exact modulus gives
\[
 \boxed{
 |h_B(x+iy)|
 \le C_{B,b}(1+|x-\tau|)^M e^{Rb^2}e^{-R(x-\tau)^2}
 \quad (|y|\le b).
 }
\]
The declaration norm_real_test_le is this statement, and norm_test_le allows
complex coefficients. Zero polynomials and strip boundary values are included.

The theorem differentiable_test proves complex differentiability everywhere.
The theorem test_ofReal identifies the extension on ℝ with the existing
GaussianPolynomialFourier.test. These bounds concern the same test as the
existing transform_test theorem.

## 3. Integrable physical-space majorants

Set
\[
 D_{B,R,\tau,b}(x)
  =C_{B,b}e^{Rb^2}(1+|x-\tau|)^M e^{-R(x-\tau)^2}.
\]
For every integer N ≥ 0, the development proves
\[
 D_{B,R,\tau,b}\in L^1(\mathbb R),\qquad
 (1+|x-\tau|)^ND_{B,R,\tau,b}(x)\in L^1(\mathbb R).
\]
Expand (1+|t|)^L by the binomial formula. Each |t|^k e^{-Rt²} is integrable,
as the norm of the already checked GaussianPolynomialFourier.momentFunction.
Translation and finite linear combinations complete the proof.

The declaration strip_domination packages a common integrable majorant for all
y in the strip. The declaration integrable_horizontal handles every horizontal
line. The weighted majorants support dominated integration with any fixed
polynomial weight.

The displayed bound also implies super-polynomial decay uniformly in the strip
by the ordinary Gaussian tail argument. A separate Lean uniform-limit theorem
or Schwartz-space instance is not claimed here. There is no claimed domination
uniform as R → ∞: the factors e^{Rb²} grow with R.

## 4. Exact frequency-polynomial representation

The normalization is
\[
 g_B(u)=\frac1{2\pi}\int_{\mathbb R}h_B(t)e^{-itu}\,dt,\qquad
 F_R(u)=\frac{e^{-u^2/(4R)}}{\sqrt{4\pi R}}.
\]
Define complex polynomials
\[
 Q_0(X)=1,\qquad Q_{k+1}(X)=Q_k'(X)-\frac{X}{2R}Q_k(X),\qquad
 A_{B,R}(X)=\sum_k b_k i^kQ_k(X).
\]
The product rule and the existing derivative of F_R give the exact checked
identities
\[
 D^kF_R(u)=Q_k(u)F_R(u),\qquad
 \boxed{g_B(u)=e^{-i\tau u}A_{B,R}(u)F_R(u).}
\]
The names are iteratedDeriv_density_eq_polynomial and
transform_test_eq_frequencyPolynomial. Every finite signed/complex summand is
retained. No factorial expansion is assumed.

Let
\[
 L=\operatorname{natDegree}(A_{B,R}),\qquad
 K_{B,R}=\frac{\sum_j|[X^j]A_{B,R}|}{\sqrt{4\pi R}}.
\]
The checked bound is
\[
 \boxed{|g_B(u)|\le K_{B,R}(1+|u|)^Le^{-u^2/(4R)}.}
\]
It is uniform in the real center τ. The implementation uses the actual degree L;
a separate checked theorem L ≤ M is not needed or claimed.

## 5. Exponential tilts and complex inverse kernels

For a > 0 retain the exact completed-square remainder:
\[
 b|u|-au^2
 =\frac{b^2}{2a}-\frac a2u^2-\frac{(a|u|-b)^2}{2a}.
\]
Consequently,
\[
 e^{b|u|}e^{-au^2}\le e^{b^2/(2a)}e^{-(a/2)u^2}.
\]
The declarations tilt_exponent_identity and exp_tilt_gaussian_le prove these
statements. The declaration integrable_tilted_majorant proves that every
(1+|u|)^M e^{b|u|}e^{-au²} is integrable.

For |Im z| ≤ b,
\[
 |e^{izu}|=e^{-\operatorname{Im}(z)u}\le e^{b|u|}.
\]
For every N ≥ 0 and a = 1/(4R), this gives
\[
 \boxed{
 |u^Ne^{izu}g_B(u)|\le
 E_{B,R,b,N}(u)
 :=K_{B,R}e^{2Rb^2}(1+|u|)^{L+N}e^{-u^2/(8R)}.
 }
\]
The majorant E is integrable and is uniform over the entire strip and all real τ.
The checked declarations are norm_inverse_transform_moment_le and
integrable_inverseMajorant. The theorem integrable_inverse_transform_moment
proves absolute integrability for every complex z. The N = 0, z = 0 case is
integrable_transform_test.

These are providers for the actual integral-defined g_B. The reusable
inverse-kernel lemmas in GaussianPolynomialStrip accept a Gaussian envelope
for an arbitrary function; GaussianPolynomialFourierGrowth supplies that
envelope for g_B by the exact recurrence.

## 6. Precise inverse-Fourier status

Mathlib's MeasureTheory.Integrable.fourierInv_fourier_eq requires f ∈ L¹,
its Mathlib-normalized Fourier transform in L¹, and continuity at the point.
Its normalization and ours are related by the already checked identity
\[
 g_B(u)=(2\pi)^{-1}\mathcal F_{\mathrm{Mathlib}}h_B(u/(2\pi)).
\]

| Requirement | Checked provider or remaining obligation |
|---|---|
| Real restriction of h_B is integrable | Existing GaussianPolynomialFourier.integrable_test |
| Real restriction of h_B is continuous | New continuous_real_test |
| g_B is integrable and continuous | New integrable_transform_test and continuous_transform_test |
| h_B has an entire extension agreeing with the real test | New differentiable_test and test_ofReal |
| Complex inverse kernels are absolutely integrable | New integrable_inverse_transform_moment |
| Common domination on fixed strips, including fixed frequency moments | New inverseMajorant, integrable_inverseMajorant and norm_inverse_transform_moment_le |
| Conversion to Mathlib's frequency scale and real inversion | Assembly still open; no new real inversion declaration is claimed |
| Holomorphy/differentiation of the complex parameter integral | Domination inputs supplied; applying the parameter-integral theorem remains open |
| Equality of the complex inverse integral with h_B | Still open as a project formalization; use real inversion and analytic continuation, or a direct Gaussian proof |

The last three rows are remaining assembly work. The Gaussian integrability and
domination estimates are actual checked providers, but do not themselves
constitute a checked inverse identity.

## 7. Remaining actual-zeta obligations

| Obligation | Supplied here | Still required |
|---|---|---|
| Prime-power sum | Gaussian envelope for g_B | Arithmetic comparison at u = log n, summability and interchange |
| Gamma-weighted integral | All polynomially weighted physical majorants | Growth of the actual gamma logarithmic derivative and integral assembly |
| Multiplicity-weighted zero sum | Test bound on the strip of half-width 1/2 | Actual zero location, multiplicities and counting bound, then shell summation |
| Horizontal contour edges | Gaussian strip estimate | Good heights, logarithmic-derivative bounds and vanishing-edge limit |
| Residues and contour shifts | Test-function estimates | Meromorphic data, residues, orientations, both pole terms and limits |
| RH | No signed positivity assertion | Independent universal signed lower bound |

Lebesgue integrability alone does not prove summability over zeta zeros.
Test-function decay alone does not control the zeta logarithmic derivative
at zeros. None of the remaining contour or RH assertions is a consequence
of these estimates alone.

## 8. Lean files and verification

- [GaussianPolynomialStrip.lean](../Analysis/GaussianPolynomialStrip.lean):
  explicit constants, exact modulus, strip bounds, real-test bridge, integrable
  polynomial weights, exact tilt identity and general inverse bounds.
- [GaussianPolynomialFourierGrowth.lean](../Analysis/GaussianPolynomialFourierGrowth.lean):
  exact derivative and frequency polynomials, actual-transform bounds, inverse
  majorants, and real-test/transform continuity and integrability.
- Both modules are exported by RiemannResearch.lean.

The combined development passed snippet job
job_WTRmOeGGXhGP78sl2VqB9o2v_Zk9G5gz: exit code 0, verified true,
server verification duration 5.716 seconds. The eight inspected main declarations
depend only on propext, Classical.choice and Quot.sound.

The saved growth file and its strip dependency passed file-check job
job_8ja17-4p31eZrOrb75A9G4OYWecD36Cm: exit code 0, verified true,
reported duration 13.524 seconds. Output records the strip module build.
There were copyright-header style warnings, not proof failures.

This evidence is distinct from final checkpoint validation. Publication is gated
by a separate checkpoint that audits and validates the unpublished source delta
and required dependents before pushing. A snippet is not a whole-project check.

The snippet's queue delay was about 0.002 seconds. Workspace-opening latency
and client polling delays were not separately instrumented. Server verification
duration is not end-to-end wall time.

## 9. Next formalization target

Prove
\[
 h_B(z)=\int_{\mathbb R}e^{izu}g_B(u)\,du\quad(z\in\mathbb C).
\]
Use inverseMajorant for compact neighborhoods and fixed derivative orders.
First handle Mathlib's frequency scaling, then verify holomorphy of the
parameter integral and the analytic-continuation step. Keep the prime-power,
gamma, zero-counting and contour providers as separately named obligations.

## Sources

- User-provided argument and the repository memorandum, Section 3: statement
  and intended actual-zeta consumer.
- GaussianPolynomialFourier.lean from commit 1905e5b: exact normalization,
  derivative identities and moment integrability.
- [Mathlib GaussianIntegral](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.html):
  underlying Gaussian integrability infrastructure.
- [Mathlib complex exponential](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Exponential.html):
  the modulus-of-exponential identity.
- [Mathlib Fourier inversion](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/Inversion.html):
  requirements used to identify the remaining assembly.

The formal sources specify the exact checked statements. No mathematical
novelty claim or completed actual-zeta formula is asserted.

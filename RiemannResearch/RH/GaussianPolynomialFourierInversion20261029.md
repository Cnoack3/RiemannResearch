# Complex Gaussian-polynomial Fourier inversion

29 October 2026.

30 October update: the full absolute prime-power sum and the actual
sum-integral interchange on every line Re(s)>1 are now formalized in
[GaussianPolynomialPrimePowerSummability20261030.md](GaussianPolynomialPrimePowerSummability20261030.md).
The open-status table and agenda below record the inversion-stage status;
the new memorandum and current theorem catalog supersede the prime-power
summability and right-line interchange entries. The shifted-transform term
evaluation remains a separate formalization step.

## Result and scope

For every R > 0, real center τ, real polynomial B (including the zero polynomial),
and z in C, the repository's actual integral-defined normalized Fourier
transform satisfies the unconditional identity
\[
 h_B(z)=\int_{\mathbb R}e^{izu}g_B(u)\,du,\qquad
 h_B(z)=B(z-\tau)e^{-R(z-\tau)^2},\qquad
 g_B(u)=\frac1{2\pi}\int_{\mathbb R}e^{-iut}h_B(t)\,dt.
\]
Every inverse integral here converges absolutely. The inverse parameter integral
is entire, and its first complex derivative is the absolutely convergent integral
\[
 \frac{d}{dz}\int_{\mathbb R}e^{izu}g_B(u)\,du
 =\int_{\mathbb R}iu\,e^{izu}g_B(u)\,du.
\]
No symmetry of the test, nonvanishing condition on B, bound on its degree,
zeta hypothesis, or RH hypothesis is required.

This completes the three assembly steps left open in
[GaussianPolynomialStripBounds20261029.md](GaussianPolynomialStripBounds20261029.md):
normalization and real inversion, holomorphy of the inverse integral, and
extension from real to arbitrary complex arguments. The actual-zeta explicit
formula, its convergence and contour providers, and its signed positivity
consumer remain separate obligations.

## 1. Existing providers, with no replacement transform

Write h for the real restriction of h_B. The earlier modules prove that h and
the actual g_B are continuous and integrable, and that h_B is an entire extension
of h. They give the exact frequency-polynomial representation
\[
 g_B(u)=e^{-i\tau u}A_{B,R}(u)
        \frac{e^{-u^2/(4R)}}{\sqrt{4\pi R}}.
\]
Let L be the actual natural degree of A_{B,R}, and let K be the nonnegative
frequencyConstant from GaussianPolynomialFourierGrowth. Then
\[
 |g_B(u)|\le K(1+|u|)^L e^{-u^2/(4R)}.
\]
In particular, for every b >= 0 and N >= 0, the same module supplies
\[
 \boxed{|u^N e^{izu}g_B(u)|\le E_{b,N}(u)
 :=K e^{2Rb^2}(1+|u|)^{L+N}e^{-u^2/(8R)}
 \quad (|\operatorname{Im}z|\le b),}
\]
and E_{b,N} is integrable. These are bounds for the actual transform, rather
than assumptions about an independently chosen function.

The exact completed-square identity behind this estimate is retained:
with a=1/(4R),
\[
 b|u|-au^2=\frac{b^2}{2a}-\frac a2u^2
          -\frac{(a|u|-b)^2}{2a}.
\]
Its last term is nonpositive after subtraction. Dropping it only constructs
a dominating function; no signed summand of g_B or of the inversion identity
is removed.

## 2. Exact normalization and real inversion

Mathlib uses
\[
 \mathcal F f(v)=\int_{\mathbb R}e^{-2\pi itv}f(t)\,dt,\qquad
 \mathcal F^{-1}F(x)=\int_{\mathbb R}e^{2\pi ivx}F(v)\,dv.
\]
The existing transform_eq_fourier, and the new rearranged identity, give
\[
 g_B(u)=(2\pi)^{-1}\mathcal Fh(u/(2\pi)),\qquad
 \mathcal Fh(v)=2\pi g_B(2\pi v).
\]
The second equality and scaling of Lebesgue measure prove that
the Mathlib transform of h is integrable.

For every real x, the substitution u=2πv, including its positive Jacobian,
therefore gives the exact equality
\[
 \begin{aligned}
 \int_{\mathbb R}e^{ixu}g_B(u)\,du
 &=\int_{\mathbb R}e^{2\pi ixv}\mathcal Fh(v)\,dv\\
 &=\mathcal F^{-1}(\mathcal Fh)(x)
 =h(x).
 \end{aligned}
\]
The last equality is Mathlib's Integrable.fourierInv_fourier_eq, using
integrability of h, integrability of its Mathlib transform, and continuity at x.
There is no missing factor of 2π and no change of sign.

GaussianFourierInversion.lean proves the scaling and real inversion statements
for arbitrary complex-valued functions with these explicit hypotheses.
It does not require Gaussian structure.

## 3. Holomorphy of the inverse integral

Define J(z)=integral_R e^{izu}g_B(u) du. Fix any z_0 in C and use the open
ball |z-z_0|<1. Every z in that ball satisfies
\[
 |\operatorname{Im}z|\le|\operatorname{Im}z_0|+1=:b.
\]
For fixed u, F(z,u)=e^{izu}g_B(u) is entire, with exact derivative
\[
 \partial_z F(z,u)=iu\,e^{izu}g_B(u).
\]
The norm of this derivative is bounded throughout the ball by E_{b,1}(u),
which is integrable and independent of z. The integrand is measurable in u
at every z, and F(z_0,.) is integrable. The derivative is measurable as well;
the previously checked N=1 integrability also supplies this input.

Apply hasDerivAt_integral_of_dominated_loc_of_deriv_le over the scalar field C.
It gives
\[
 J'(z_0)=\int_{\mathbb R}iu\,e^{iz_0u}g_B(u)\,du.
\]
Because z_0 was arbitrary, J is complex differentiable everywhere and hence
entire. This argument uses local domination for the derivative, not merely
pointwise convergence of the inverse integrals.

The estimates for higher N also justify repeated differentiation on paper:
\[
 J^{(N)}(z)=\int_{\mathbb R}(iu)^N e^{izu}g_B(u)\,du.
\]
The new Lean module explicitly proves the first derivative and entire
differentiability. A separate general theorem for all iterated derivatives is
not claimed as a newly checked declaration.

## 4. Extension to all complex arguments

The two entire functions J and h_B agree on every real number by Section 2.
Their equality set contains the nonzero real sequence 1/(n+1), which tends to 0.
The complex identity theorem on the connected domain C therefore gives
\[
 \boxed{J(z)=h_B(z)\quad\hbox{for every }z\in\mathbb C.}
\]
The Lean proof explicitly verifies convergence in the punctured neighborhood
of zero and applies AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq on
the whole complex plane.

This completes the ordinary proof and its formalization. Equality at nonreal
arguments follows from a proved identity theorem, not from a formal
substitution into a real-only inversion statement.

## 5. Exact actual-zeta coordinate and both pole values

For any s in C, set z=(s-1/2)/i. The algebraic equality iz=s-1/2 gives the
checked bilateral Laplace identity
\[
 \boxed{
 h_B((s-\tfrac12)/i)
 =\int_{\mathbb R}e^{(s-\frac12)u}g_B(u)\,du.
 }
\]
The new integrable_laplace_kernel proves absolute integrability for every s.

Consequently, this identity is available at each nontrivial zeta zero rho,
whether or not rho lies on the critical line:
\[
 h_B(z_\rho)=\int_{\mathbb R}e^{(\rho-\frac12)u}g_B(u)\,du.
\]
This is a pointwise specialization of a theorem for arbitrary complex s.
It does not sum over zeros or establish any property of zeta.

The same identity retains both completed-zeta pole evaluations:
\[
 h_B(i/2)=\int_{\mathbb R}e^{-u/2}g_B(u)\,du,\qquad
 h_B(-i/2)=\int_{\mathbb R}e^{u/2}g_B(u)\,du.
\]
These two displayed equalities follow on paper by s=0 and s=1.
The general Laplace identity and its integrability are checked in Lean;
no separately named pole-specific corollaries are asserted.

## 6. Exact hypothesis map for the actual-zeta program

| Requirement | Status after this development | Scope or remaining work |
|---|---|---|
| Compatibility with Mathlib Fourier normalization | Checked | Exact frequency scaling, Jacobian, and sign conversion. |
| Real inverse Fourier identity for h_B and its actual g_B | Checked | Continuity and both L1 inputs are supplied by existing lemmas. |
| Holomorphy of the inverse parameter integral | Checked | First-moment domination on a neighborhood and differentiation under the integral. |
| Complex inverse identity for every z | Checked | Entire continuation of real inversion. |
| Reconstruction at every possible z_rho and both pole arguments | Supplied by the checked theorem for every complex s | Pointwise reconstruction only; no assertion about the zero set is needed. |
| Prime-power sum and exchange with the vertical integral | Open as a formalization | Arithmetic comparisons, summability, and interchange must still be proved. |
| Actual gamma-weighted integral | Open as a formalization | Growth and pole data for the actual logarithmic derivative of Gamma, plus integral assembly. |
| Multiplicity-weighted zero-sum convergence | Open as a formalization | Actual zero location, multiplicities, counting bound, and shell summation. |
| Horizontal edges and contour shifts | Open as a formalization | Good heights, zeta/completed-zeta logarithmic-derivative estimates, vanishing edges, and legitimate shifts. |
| Residue theorem and full explicit formula, with both pole terms | Open as a formalization | Meromorphic providers, residues, orientations, and limits. |
| Actual arithmetic matrix equals the actual-zero matrix | Open as a formalization | Assemble the complete explicit formula with pole removal and finite matrix algebra. |
| Localization and RH conclusion | Open | Supply the actual-zero providers and the independent universal signed lower bound. |

Here "Open as a formalization" distinguishes these obligations from the
ordinary arguments recorded in GaussianActualZetaExplicitFormula20261029.md.
This development does not re-audit or newly verify those separate arguments.

In particular, evaluating the inverse identity at every rho is not a
justification for interchanging a zero sum with an integral. Nor does the
identity itself prove the termwise contour-shift formula (4.4) in the earlier
memorandum: that formula still requires its contour argument or another
separately justified route. No assertion uniform as R tends to infinity is made.

## 7. Lean declarations and verification

The reusable normalization and real inversion are in
[GaussianFourierInversion.lean](../Analysis/GaussianFourierInversion.lean),
namespace RiemannResearch.Analysis.GaussianPolynomialFourier:

- fourier_eq_scaled_transform;
- inverse_integral_eq_fourierInv;
- integrable_fourier_of_integrable_transform;
- inverse_integral_eq.

The Gaussian-polynomial assembly is in
[GaussianPolynomialFourierInversion.lean](../Analysis/GaussianPolynomialFourierInversion.lean),
namespace RiemannResearch.Analysis.GaussianPolynomialFourierInversion:

- inverse and hasDerivAt_inverse;
- inverse_ofReal and differentiable_inverse;
- inverse_eq_test and test_eq_inverse_integral;
- test_eq_laplace_integral and integrable_laplace_kernel.

For the specialized inversion and Laplace theorems the only substantive
hypotheses are R > 0, real τ, and B a finite real polynomial. The argument z,
or s in the Laplace form, is arbitrary complex. There is no domain-specific
hypothesis about zeta, contours, infinite sums, positivity, or RH.

The complete first candidate passed coherent snippet job
job_0X92M-JVt_H39SKGu7OcNB0GqFgVyJDd: exit code 0, verified true,
reported server verification duration 5.268 seconds. Axiom inspection of the
complex inversion, derivative-under-integral, and Laplace identity reported only
propext, Classical.choice, and Quot.sound. The persistent modules separate the
general real-normalization lemmas from their Gaussian-polynomial application.

The saved normalization and complex-inversion modules passed import/axiom-check
job job_HqGBlxJ5_GZ3Q2Nwk388PWI7LL87vBwa: exit code 0, verified true,
reported total server duration 12.576 seconds. The output records both modules
being built (reported Lake durations 1.9 and 1.0 seconds). Five inspected
declarations, including the general real inversion and absolute Laplace-kernel
integrability, reported only propext, Classical.choice and Quot.sound.
The only warning was a pre-existing copyright-header style warning in
GaussianPolynomialFourierGrowth.lean.

Publication is gated separately by agent_workspace_checkpoint, with server
source audit and required changed-module/dependent validation before a push.
A successful snippet does not certify the aggregate project. Workspace opening
and client polling latency were not measured separately; server durations do
not measure either delay.

## 8. Next formalization targets

1. Prove the arithmetic comparison and absolute summability of the full
   prime-power contribution for the actual g_B.
2. Supply the growth and meromorphic facts needed for the actual gamma term.
3. Package the actual zeta zeros, multiplicities and unconditional counting
   bound, then prove Gaussian shell summability.
4. Formalize good heights, residue data, vanishing horizontal edges and the
   legitimate contour shifts for the completed zeta function.
5. Assemble the full explicit formula, preserving both pole terms, and only
   then specialize to the pole-reduced matrix and existing localization lemmas.
6. Keep the universal signed lower bound as an independent unresolved RH
   obligation; Fourier inversion supplies no positivity assertion.

## Sources and provenance

- User-provided target and
  [GaussianActualZetaExplicitFormula20261029.md, Sections 1--4](GaussianActualZetaExplicitFormula20261029.md):
  the statement, normalization and intended zeta consumer.
- [GaussianPolynomialStripBounds20261029.md](GaussianPolynomialStripBounds20261029.md):
  checked integrability and uniform inverse-moment majorants reused here.
- Mathlib at the repository's pinned revision
  [51e6992efd06126df61a496bebf8f49482a4e129](https://github.com/leanprover-community/mathlib4/tree/51e6992efd06126df61a496bebf8f49482a4e129):
  [Fourier inversion](https://github.com/leanprover-community/mathlib4/blob/51e6992efd06126df61a496bebf8f49482a4e129/Mathlib/Analysis/Fourier/Inversion.lean),
  [parameter integrals](https://github.com/leanprover-community/mathlib4/blob/51e6992efd06126df61a496bebf8f49482a4e129/Mathlib/Analysis/Calculus/ParametricIntegral.lean),
  and the
  [identity theorem](https://github.com/leanprover-community/mathlib4/blob/51e6992efd06126df61a496bebf8f49482a4e129/Mathlib/Analysis/Analytic/IsolatedZeros.lean)
  supply the proof infrastructure and analytic-continuation strategy.

These are classical analytic facts specialized and assembled for the stated
research program. No mathematical novelty or completed actual-zeta explicit
formula is asserted.

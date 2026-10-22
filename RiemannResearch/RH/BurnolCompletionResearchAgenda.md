# Burnol projection and BSY: verified progress and research agenda

Date: 2026-09-23. Project: RiemannResearch, Lean 4 / Mathlib.

## Status and exact targets

**The full Nyman–Beurling projection identification and BSY integral identity are not yet formalized.** This development supplies unconditional analytic and Hilbert-space prerequisites. No missing identification is inserted as an axiom, and no theorem assuming its own substantive conclusion is presented as completion.

Write NB for the actual closed span of the continuous generators

\[
\rho_\alpha(t)=\{\alpha/t\}-\alpha\{1/t\},\qquad 0<\alpha<1,
\]

in complex \(L^2((0,1),dt)\), and let \(P_{NB}\) be its orthogonal projection. The first requested target is

\[
\|P_{NB}1\|=B,\qquad
 B=\prod_{\Re\rho>1/2}\left|\frac{1-\rho}{\rho}\right|^{m_\rho}.
\]

The second target, including existence of the Lebesgue integral, is

\[
I:=\frac1{2\pi}\int_{\mathbb R}
\frac{\log|\zeta(1/2+it)|}{1/4+t^2}\,dt
=S:=\sum_{\Re\rho>1/2}m_\rho\log\left|\frac{\rho}{1-\rho}\right|.
\]

Both signs of the ordinate are included; multiplicity is essential. The already published scalar work proves absolute convergence of S, positivity of B, and \(B^2=e^{-2S}\). It does not identify either analytic left-hand side.

## Added Lean modules

All modules are under `RiemannResearch/RH/` and exported by `RiemannResearch.lean`.

| Module | Concrete content | Scope limit |
|---|---|---|
| `NymanContinuousSpace.lean` | Actual complex L² space, measurable bounded generators, closed span, norm-one constant, exact dilation identity and closed-span membership of dilated generators | No complete Mellin image identification |
| `NymanCommonZeros.lean` | The factors α−αˢ have common zero exactly at s=1; away from 0 and 1, common zeros of the symbolic Mellin family are precisely zeta zeros | No integral-transform formula or multiplicity transport asserted |
| `BurnolCriticalLine.lean` | Actual critical-line density; local logarithmic integrability including zeros; evenness; finite-cutoff splitting; finite bounded zero sets, countability and almost-everywhere nonvanishing | Global weighted integrability remains open |
| `BurnolCayleyJensen.lean` | Analytic pole removal; disk map and inverse; F(0)=1; exact Jensen formula for the actual F on every strict subdisk with Mathlib's divisor multiplicities | No r→1 integral passage asserted |
| `BurnolBoundaryCoordinates.lean` | Critical-line points map to the unit circle minus 1; boundary modulus of F equals critical-line zeta modulus | No measure change or integral convergence asserted |
| `BurnolRealAxis.lean` | ζ(σ)→1, regularized ratio→1, corresponding radial normalization, logarithmic modulus→0 | This alone does not exclude a singular factor without a factorization theorem |

Here the Cayley map is \(s=(1-z)^{-1}\), its inverse is \(z=(s-1)/s\), and
\(F(z)=z\zeta((1-z)^{-1})\) away from the removable center. The center value is proved through completed zeta and reciprocal Gamma, rather than using the totalized value of ζ at its pole. For every strict subdisk, the proved Jensen formula concerns this concrete function and its actual analytic divisor.

Lean's `Real.log 0 = 0` is a totalization convention. Zeta-zero ordinates form a null set, and local logarithmic integrability is proved explicitly. These facts justify local use of the totalized function; they do not justify the infinite boundary passage.

## Prioritized research agenda

### 1. Finish BSY independently of the projection theorem

This is the narrower next formalization target. Implement three explicit bridges:

1. **Divisor transport.** Prove the Cayley change preserves analytic zero orders and identify the divisor in `diskZeta_jensen` with the existing `RightZero` index and `zeroMult`. Exclude all other disk zeros using the existing zeta zero-free results. Transport the finite-radius zero sums and then their limit to `logarithmicZeroSum`.
2. **Boundary integration.** Establish the exact arc-length Jacobian \(1/(1/4+t^2)\), including the normalized circle-average measure. Prove global integrability of the actual weighted logarithm.
3. **Boundary limit.** Prove convergence of the logarithmic circle averages to the boundary integral. Record any exceptional contribution at z=1 and discharge it. Pointwise or almost-everywhere convergence alone is insufficient. The proved radial normalization is an input to this step, not a replacement for it.

Acceptance gate: a theorem `Integrable criticalLogDensity` and an unconditional equality between its normalized integral and `logarithmicZeroSum`, with no remaining boundary-convergence or factorization hypothesis.

A backup route is the slit-contour argument for the logarithm of pole-removed zeta. The existing rectangle log-derivative argument principle is useful infrastructure, but it does not by itself supply a branch of the logarithm, the slit contributions, or the limiting contour estimates.

### 2. Build an actual Hardy representation

Complete the currently open `WeightedMellin.GeneralHardyConverse`; construct the Hilbert space, Mellin isometry onto it, continuous evaluation, and reproducing kernel. Prove the Mellin integral formula for every real α in (0,1), not only the reciprocal-integer subfamily. Retain the removable value at s=1.

Acceptance gate: the image of `ContinuousNyman.closedSpace` is a concrete closed subspace of the represented Hardy space, obtained from actual transforms of its generators.

### 3. Identify the inner multiplier and the full Nyman space

Construct the holomorphic Blaschke product, its boundary isometry, and its evaluation at 1. Prove the required inner–outer / invariant-subspace theorem; identify the common inner divisor of the continuous family, including multiplicities and the absence of extra singular or exponential factors. Then apply the existing abstract multiplier-projection calculation.

Acceptance gate: the actual equality \(\mathcal M(NB)=BH^2\), followed by the projection norm theorem for the concrete norm-one constant. A theorem taking this equality as a hypothesis is only a conditional reduction.

### 4. Develop a constructive finite-product route

A smaller independent milestone is a Volterra realization. For Re(a)>0 define

\[
q_a(x)=\int_0^x e^{-\bar a(x-u)}f(u)\,du,
\qquad T_af=f-2\Re(a)q_a.
\]

First formalize, under sufficient regularity, the exact identity

\[
\int_0^R|T_af|^2
=\int_0^R|f|^2-2\Re(a)|q_a(R)|^2.
\]

Extend to L² and prove the boundary remainder tends to zero. The Laplace multiplier is \((z-a)/(z+\bar a)\), so composition gives finite Blaschke isometries. This is a proposed development, not a checked theorem in this change. It could reduce reliance on general Hardy machinery for intermediate projection results; completeness of the Nyman zero constraints would still need proof.

### 5. Connect continuous projection energy to Pareto without losing a remainder

Construct the intended isometric embedding of the discrete Pareto space and prove inclusion of its legal span K in NB. Preserve

\[
\|P_K1\|^2=\|P_{NB}1\|^2-\|P_{NB}1-P_K1\|^2.
\]

After the Burnol identification, this becomes \(\|P_K1\|^2=B^2-\Gamma\), where \(\Gamma\ge0\) is the actual projection gap. Connect finite Gram/Schur gains to this identity using the existing nested-projection and scalar-product telescopes. Do not infer Γ=0 merely from inclusion.

### 6. Separate formalization from new RH research

Once the classical identities are formalized, they yield \(I=S=-\log B\ge0\), and vanishing is equivalent to RH. They do not force vanishing. The arithmetic research target is an independent argument making S zero, or forcing the appropriate Pareto energy to saturate while controlling Γ. Investigate exact remainder formulas for finite Gram approximations and compare them with the analytic zero contributions. Any proposed saturation argument must be audited for an implicit RH-equivalent density assumption.

## Primary references and formal API

- Jean-François Burnol, *A note on Nyman's equivalent formulation of the Riemann Hypothesis*, [arXiv:math/9910055](https://arxiv.org/abs/math/9910055), Theorems 1.2–1.3, equations (2.1)–(2.3), Lemma 2.4. Source for the target identities and Hardy-factorization proof strategy.
- H. M. Bui, S. J. Lester, M. B. Milinovich, *On Balazard, Saias, and Yor's equivalence to the Riemann Hypothesis*, [arXiv:1306.0856](https://arxiv.org/abs/1306.0856), §4. Source for the alternative contour route. Its RH-conditional cutoff results must not be treated as unconditional completion.
- [Mathlib JensenFormula](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/JensenFormula.html): `AnalyticOnNhd.circleAverage_log_norm`.
- [Mathlib LogMeromorphic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Integrability/LogMeromorphic.html): local logarithmic integrability.
- [Mathlib LSeries Injectivity](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/Injectivity.html): `LSeries.tendsto_atTop`.

Validation uses the repository's pinned dependencies; live documentation can differ from that pin. The repository catalog records both established declarations and still-open obligations.

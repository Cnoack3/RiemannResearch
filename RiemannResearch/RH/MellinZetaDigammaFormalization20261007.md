# Mellin, zeta, and all-order digamma formalization in Lean

7 October 2026. Continuation of the interrupted Beurling/digamma work in the
RiemannResearch Lean 4/mathlib project, using Lean `v4.33.0-rc2`.

Thirteen new modules prove 124 public theorems, with 13 private proof helpers.
The results use the actual Bochner Mellin transform, Mathlib's analytic
`riemannZeta`, and `Complex.digamma` derived from Gamma. No desired analytic
identity is supplied as a hypothesis. Existing project providers are reused.

## Mellin transform and Beurling obstruction

For an integer conductor \(d>0\), the actual normalized step atom is
\[
g_d(j)=\frac{j\bmod d}{d},\qquad
\phi_d(t)=\{t/d\}-\{t\}/d=g_d(\lfloor t\rfloor),\quad t\ge0.
\]
Its complete physical norm uses the original Pareto weights:
\[
\|g\|_P^2=\sum_{j\ge1}\frac{|g(j)|^2}{j(j+1)}.
\]
The formalization proves absolute integrability and, for \(\Re s>0\), \(s\ne1\),
\[
\int_1^\infty\phi_d(t)t^{-s-1}\,dt
=\frac{\zeta(s)}s\bigl(d^{-1}-d^{-s}\bigr).
\]
The transform is holomorphic throughout \(\Re s>0\). Its regularized conductor
expression includes \(s=1\); both the actual integral there and the punctured
limit of the zeta expression are \(\log d/d\).

`ParetoAtomMellinSignature` proves these identities for the existing canonical
`normalizedResidueHilbert`, rather than introducing a replacement atom.
Important declarations are `corrected_fract_integral_eq_zeta`,
`corrected_fract_integral_one`, `tendsto_normalizedResidue_zeta_one`, and
`analyticAt_paretoMellin_normalizedResidue`.

The Mellin functional is continuous on the complete physical Hilbert space
when \(\sigma=\Re s>1/2\), with the proved estimate
\[
|\ell_s(g)|^2\le\frac{\|g\|_P^2}{2\sigma-1},\qquad \ell_s(1)=1/s.
\]
This is an upper bound on the functional norm. If \(s\ne1\) and
\(\zeta(s)=0\), every atom with \(d\ge2\), its real linear span, and its physical
norm closure are annihilated. Thus every \(f\) in that closure satisfies
\[
\ell_s(1-f)=1/s,\qquad
\frac{2\sigma-1}{|s|^2}\le\|1-f\|_P^2.
\]
The target is outside the closure, and target membership would imply that
zeta has no such zeros. These are actual functional and arithmetic results,
not consumers of a hypothetical Mellin provider. The principal theorem is
`ParetoBeurlingMellinObstruction.normalizedResidue_error_sq_lower_bound_of_zeta_zero`.
The approximation converse of the Nyman–Beurling criterion is not proved here.

## Actual zeta coefficients

The existing `positivePSeries k` is identified with actual zeta for every
natural \(k>1\):
\[
\left(\sum_{n\ge1}\frac1{n^k}:\mathbb C\right)=\zeta(k).
\]
This includes odd coefficients. Positivity, real-part identification, and
zero imaginary part are proved in `ParetoZetaSeries`. The canonical result is
`Pareto.positivePSeries_coe_eq_zeta`; no parallel coefficient definition is added.

## Convergent Laurent expansion and exact finite remainders

For \(z\ne0\), \(|z|<1\), the actual complex digamma satisfies the absolutely
convergent identity
\[
\psi(z)=-\gamma-\frac1z+
\sum_{k\ge0}(-1)^k\zeta(k+2)z^{k+1}.
\]
For every \(N\ge0\), the finite identity retains its full rational-series remainder:
\[
\psi(z)+\gamma+\frac1z
=\sum_{k=0}^{N-1}(-1)^k\zeta(k+2)z^{k+1}
+(-1)^N z^{N+1}R_N(z),\qquad
R_N(z)=\sum_{n\ge1}\frac1{n^{N+1}(n+z)}.
\]
The norm of the truncation error is bounded by
\[
|z|^{N+1}\frac{\zeta(2)}{1-|z|}.
\]
These are `DigammaComplexLaurent.digamma_laurent_truncation`,
`digamma_laurent_error_bound`, and `digamma_eq_zeta_laurent_tsum`, in namespace
`RiemannResearch.RH.Pareto.DigammaComplexLaurent`.

For positive real \(z\), the same exact finite formula holds for every \(z>0\),
with \(0<R_N(z)\le\zeta(N+2)\le\zeta(2)\). This finite formula does not require
\(z<1\). The infinite Laurent series requires \(0<z<1\).
`DigammaLaurentSeries` supplies both statements and their signed bounds.
`DigammaAsymptotic.digamma_ofReal_im_eq_zero` and `digamma_ofReal_eq_re` prove
that the real-part formulas are formulas for digamma itself at real arguments,
using the existing Gamma-derived conjugation theorem.

For literal complete CRT weights,
\[
\rho_Q(r)=\sum_{m\ge0}\frac1{(r+mQ)(r+mQ+1)},
\]
the existing actual digamma difference identity is used. For integer
\(0<r\), \(r+1<Q\), the newly proved convergent expansion is
\[
\rho_Q(r)=\frac1{r(r+1)}+
\sum_{k\ge0}\frac{(-1)^k\bigl((r+1)^{k+1}-r^{k+1}\bigr)\zeta(k+2)}{Q^{k+2}}.
\]
The first corrections are \(\zeta(2)/Q^2\),
\(-(2r+1)\zeta(3)/Q^3\), and \((3r^2+3r+1)\zeta(4)/Q^4\).
`progressionWeight_eq_zeta_laurent_tsum` proves the full identity; the
fourth-order module also retains the actual positive rational remainder.
The physical head and complete tail are preserved throughout.

## All-order positive-real Bernoulli asymptotics

Let \(B_k\) denote the Bernoulli numbers. Define the literal error
\[
E_N(x)=\psi(x)-\left(\log x-\frac1{2x}
-\sum_{k=1}^{N}\frac{B_{2k}}{2k\,x^{2k}}\right),\qquad x>0.
\]
For every \(N\in\mathbb N\), including \(N=0\), Lean proves
\[
\boxed{0<(-1)^{N+1}E_N(x)
<\frac{|B_{2N+2}|}{(2N+2)x^{2N+2}}.}
\]
Consequently the entire error has strictly smaller absolute value than the
first omitted term. In particular,
\[
\log x-\frac1{2x}-\frac1{12x^2}
<\psi(x)
<\log x-\frac1{2x}-\frac1{12x^2}+\frac1{120x^4}.
\]
The factorial/Gamma derivative identity \(\psi(n+1)=H_n-\gamma\) and the
corresponding harmonic-number Bernoulli enclosures are also formalized.
The all-order theorem is a finite Poincaré expansion with a proved remainder;
it does not assert convergence of an infinite Bernoulli series.

The proof avoids assuming Binet's formula. It starts with the actual digamma
partial-fraction series and the trapezoidal cell error
\[
\tau(x)=\tfrac12(x^{-1}+(x+1)^{-1})-
\bigl(\log(x+1)-\log x\bigr),\qquad
\sum_{n\ge0}\tau(n+x)=\log x-\frac1{2x}-\psi(x).
\]
The Bernoulli cells are actual interval integrals
\[
J_k(x)=\int_0^1\frac{B_k(u)}{(x+u)^{k+1}}\,du.
\]
Integration by parts gives the exact recurrence
\[
J_k(x)=-\frac{B_{k+1}}{k+1}
\bigl(x^{-k-1}-(x+1)^{-k-1}\bigr)+J_{k+1}(x).
\]
Every finite endpoint is retained. The complete exact remainder is
\[
E_N(x)=\sum_{n\ge0}\int_0^1
\frac{B_{2N+2}(u)-B_{2N+2}(0)}{(n+x+u)^{2N+3}}\,du.
\]
The Bernoulli Fourier series proves the signed endpoint defect is nonnegative
on \([0,1]\), and positive at \(u=1/2\). Continuity makes each actual signed
cell integral positive. The proved `HasSum` transfers strict positivity to
the full error. Finally the exact consecutive-error identity and the
opposite sign of \(E_{N+1}\) give the strict upper bound.

The key declarations, all in namespace
`RiemannResearch.RH.DigammaBernoulliSignedRemainder`, are
`hasSum_endpointDefectCell`, `evenDigammaError_eq_tsum_endpointDefect`,
`re_digamma_strict_signed_remainder`, and
`re_digamma_strict_absolute_remainder`.

```lean
import RiemannResearch.RH.DigammaBernoulliSignedRemainder

open RiemannResearch.RH.DigammaBernoulliCells
open RiemannResearch.RH.DigammaBernoulliSignedRemainder

example {x : ℝ} (hx : 0 < x) (N : ℕ) :
    0 < (-1 : ℝ) ^ (N + 1) * evenDigammaError N x ∧
      (-1 : ℝ) ^ (N + 1) * evenDigammaError N x <
        |bernoulliCoefficient (2 * N + 2)| / x ^ (2 * N + 2) :=
  re_digamma_strict_signed_remainder hx N
```

## Module inventory

Paths below are relative to `RiemannResearch/`. The theorem counts exclude
private helpers. Every module is exported by the project root.

| Module | Public theorems | Content |
|---|---:|---|
| `RH/ParetoZetaSeries.lean` | 4 | All actual positive-integer zeta coefficients |
| `RH/DigammaSmallArgument.lean` | 9 | Actual fourth-order digamma and CRT formulas |
| `RH/DigammaLaurentSeries.lean` | 21 | All finite real orders and full real/CRT series |
| `RH/ParetoAtomMellinSignature.lean` | 10 | Actual atom integrals, holomorphy, removable value |
| `RH/ParetoBeurlingMellinObstruction.lean` | 6 | Actual span/closure annihilation and physical distance |
| `RH/DigammaAsymptotic.lean` | 20 | Reality, complete cell sum, low-order/harmonic bounds |
| `RH/DigammaBernoulliCells.lean` | 5 | Bernoulli integration by parts and kernel FTC |
| `RH/DigammaComplexLaurent.lean` | 17 | Actual complex Laurent identity and finite error |
| `RH/DigammaBernoulliRemainder.lean` | 2 | Exact all-order finite cell expansion |
| `RH/DigammaBernoulliRemainderBounds.lean` | 4 | Complete exact digamma remainder series |
| `RH/DigammaBernoulliRemainderEstimates.lean` | 9 | Unconditional all-order decay, odd-term elimination |
| `Analysis/BernoulliEndpointDefect.lean` | 4 | Fourier endpoint sign and strict midpoint positivity |
| `RH/DigammaBernoulliSignedRemainder.lean` | 13 | Complete signed remainder and strict sharp bounds |

## Verification and corrected coverage

Targeted builds check the actual module dependency graph. The complex Laurent
and all-order remainder modules compiled in `job_1nfuQgkH8F6VYiMwe0RIj-4tYx3ibsaO`.
The consolidated signed module, including the real-axis reality theorems,
compiled through actual imports in `job_ZebgWhDgVDra5CHGgaozqAVDB9YD5nEG`
(exit code 0, 20.471 seconds). The coherent strict proof check
`job_Wx2wtp7CZzOC9HauOcjCzNmqjr5I-lMh` returned `verified: true`.
The final actual-import audit `job_aAtzrWY-Pr0i4DrDfJGFpfZfLv4OzD4M`
returned `verified: true`, exit code 0, in 4.112 seconds. Its source SHA-256 is
`5e59910a03c332fbe2901038b650054133ede2f363c98c685d343e6cc8495e2f`.
All 24 selected `#print axioms` reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. They cover the actual zeta coefficients,
Mellin integrability/identity/value/limit/holomorphy, Beurling distance and
zero-free consequence, real-axis digamma reality, real and complex finite and
infinite Laurent formulas, CRT series, complete trapezoidal cell sum,
harmonic bounds, Bernoulli recurrence, exact complete remainder, all-order
decay, midpoint positivity, and the exact and sharp strict signed remainder.

All thirteen source modules pass scans for proof holes, custom axioms,
`unsafe`, and unqualified `import Mathlib`. The root exports and theorem
catalog include the modules. Final project validation and publication use
one push-enabled checkpoint; its result is recorded in the delivered copy.

The earlier salvage note described Mellin/zeta and infinite CRT digamma
identifications as remaining analytic adapters. That description is superseded:
actual providers already existed, and this continuation assembles, extends,
and verifies them. The all-order positive-real digamma expansion and sharp
signed remainder are now formalized. The Binet integral representation itself
is not the Lean proof route and is not newly formalized.

Still open are the arithmetic cumulative gain estimate forcing the actual
residual errors to zero, the approximation converse/squarefree provider,
and the named continuum norm constant with its full correction-energy
assembly. This work proves no new RH theorem and does not formalize arbitrary
complex-sector all-order Bernoulli asymptotics.

## Classical references and formal providers

- [NIST DLMF 5.7.4](https://dlmf.nist.gov/5.7.E4): convergent Gamma/digamma series.
- [NIST DLMF 5.11.2](https://dlmf.nist.gov/5.11.E2): digamma asymptotic expansion.
- [NIST DLMF 24.8.1](https://dlmf.nist.gov/24.8.E1): Bernoulli Fourier series.
- Actual project providers: `Analysis/MellinNormalizedResidue`,
  `RH/ParetoMellinFunctional`, `RH/ParetoResidueMellinContinuation`,
  `RH/ZetaConductorRegularization`, `RH/ParetoProgressionDigamma`,
  `RH/ParetoProgressionTaylor`, and `RH/WeilExplicitFormula/GammaFacts`.
- Actual Mathlib providers include `hasSum_one_div_nat_pow_mul_cos`,
  `zeta_eq_tsum_one_div_nat_add_one_cpow`, and Gamma's natural-number derivative.

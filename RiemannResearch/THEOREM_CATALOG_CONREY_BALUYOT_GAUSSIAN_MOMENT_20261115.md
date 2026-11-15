# Conrey–Baluyot Gaussian moment continuation

Date: 15 November 2026. Starting published checkpoint:
`f1df51cb44c3b28bd0087864c316c8915271cef4`.
The restored workspace was clean and a managed sync found no newer main at the
start of this continuation. Publication must still validate any later integration.

## Status

The Gaussian smoothing step now has exact window/source-tail identities,
proved whole-line integrability for the actual finite mollifier, an explicit
Gaussian deficit, and a quantitative transfer to the central uncentered moment.
The initial reflected-product/vertical-contour representation is also formalized.

The quantitative central-moment result remains a **conditional research reduction**:
the actual whole-line smoothed-moment bound is a substantive premise.
Neither that bound, the full arithmetic decomposition and estimates, global
density, nor RH is proved here.

Source for the definitions and strategy: S. A. C. Baluyot,
[*On the Zeros of Riemann's Zeta-function* (2017)](https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320),
Section 3.3, equations (3.3.1)–(3.3.5), pp. 115–116, and the initial vertical
integral preceding (3.3.6). This is provenance, not a novelty claim.

## Exact accounting

Fix the actual polynomial with its exact cutoff
\(N=\lfloor y^{1+\varepsilon}\rfloor\), and write
\[
F(s)=\zeta(s)M_{\sigma,y,\varepsilon}(s),\qquad
f(t)=|F(\ell+it)|^2.
\]
The mollifier parameter \(\sigma\) and evaluation line \(\ell\) remain distinct.
For \(\Delta>0\), set
\[
K_\Delta(x)=\frac{e^{-(x/\Delta)^2}}{\Delta\sqrt\pi},\quad
A=T-H,\quad B=2T+H,
\]
\[
w(t)=\int_A^B K_\Delta(t-u)\,du,\quad
g_T(u)=\int_T^{2T}K_\Delta(t-u)f(t)\,dt,\quad
g(u)=\int_{\mathbb R}K_\Delta(t-u)f(t)\,dt.
\]
The kernel is represented in `Real.gaussianDensity` by the precision
\(a=\Delta^{-2}\); `Real.gaussianDensity_inv_sq` proves the exact scale conversion.

The primary exact identities retain both missing terms:
\[
w(t)+\int_{\mathbb R\setminus(A,B]}K_\Delta(t-u)\,du=1,
\]
\[
g(u)=g_T(u)+\int_{\mathbb R\setminus(T,2T]}K_\Delta(t-u)f(t)\,dt,
\]
\[
\mathcal M(T,2T)=\int_A^B g_T(u)\,du+R,\qquad
R=\int_T^{2T}(1-w(t))f(t)\,dt.
\]
Open/closed endpoint choices do not alter these Lebesgue integrals. Their exact
Lean versions use `Ioc` complements and oriented interval integrals.

For \(T,H\ge0\), the proved window estimate yields
\[
0\le R\le\delta\mathcal M(T,2T),\qquad
\delta=\sqrt2\,e^{-H^2/(2\Delta^2)}.
\]
The two-tail estimate follows by splitting the exponential into two equal
factors, bounding one factor outside the window, and integrating the remaining
Gaussian exactly. The factor \(\sqrt2\) includes both tails.

## Actual integrability and reflection

For every real \(\sigma,y,\varepsilon\), every \(\ell\ge1/4\) with
\(\ell\ne1\), and every \(\Delta>0,u\in\mathbb R\), the actual
Gaussian-weighted \(f\) is integrable. The proof combines the finite coefficient
sum, the existing linear zeta growth bound outside \([-1,1]\), and continuity
on the remaining compact interval. The resulting polynomial majorant depends
on the fixed parameters. It is used only for integrability; it is not a uniform
small moment estimate and is not claimed to remain bounded as \(\ell\to1\).

For \(y>0\), every positive-index coefficient is real, including when the
totalized normalizing denominator vanishes. The finite mollifier and its zeta
product commute with conjugation. Consequently, on \(s=\ell+it\),
\[
|F(s)|^2=F(s)F(2\ell-s).
\]
This gives the exact initial vertical integral
\[
g(u)=\frac1{\Delta\sqrt\pi}
\int_{\mathbb R}
e^{(s-\ell-iu)^2/\Delta^2}F(s)F(2\ell-s)\,dt,
\quad s=\ell+it.
\]
The equality is complex-valued: the entire right-hand side equals the real
Gaussian moment. Here the parameter is \(dt\); the factor \(i\) from \(ds\)
cancels the source's \(1/i\). This does **not** shift the contour, compute its
pole contribution, or establish an Estermann decomposition.

## Quantitative central moment

Assume \(\ell\ge1/4\), \(\ell\ne1\), \(T,H\ge0\), \(\Delta>0\),
\(\delta<1\), and the actual bound
\[
g(u)\le1+r\qquad\text{for every }u\in[T-H,2T+H].
\]
Then `mollifiedSecondMoment_le_of_gaussianMoment` proves
\[
\boxed{\mathcal M_{\sigma,y,\varepsilon}(\ell;T,2T)
\le T+\frac{2H+(T+2H)r+\delta T}{1-\delta}.}
\]
This uses finite Fubini, the exact source-tail identity and positivity of the
discarded source tail. Absorption of the relative window deficit avoids any
separate unproved estimate for the unsmoothed zeta second moment.

The excess `gaussianMomentExcess T H r δ` is nonnegative when \(r\ge0\).
It therefore supplies the `E` argument of
`exists_uniform_dyadic_count_of_prescribed_line_moment` without adding a
line-neighborhood or outward-endpoint hypothesis. On the coupled sigma strip,
\(\ell=\sigma\) automatically avoids 1; the other existing count hypotheses
must still be met.

For logarithmic padding \(H=\Delta\log T\), \(T>0\), \(\log T\ge2\),
`mollifiedSecondMoment_le_of_log_padded_gaussianMoment` removes the separate
small-deficit premise and uses
\[
\delta_T=\sqrt2\,e^{-(\log T)^2/2}<1.
\]
For any \(k\ge0\), `Real.exp_neg_log_sq_le_rpow` proves
\[
2k\le\log T\quad\Longrightarrow\quad
e^{-(\log T)^2/2}\le T^{-k}.
\]
These are explicit finite inequalities, not an asserted uniform arithmetic
asymptotic. A provider for \(r\) remains necessary.

## Declaration map

The application namespace is `RiemannResearch.Analysis.ConreyBaluyot`.

| File in `Analysis/` | Key declarations |
| --- | --- |
| `GaussianWindow.lean` | `Real.gaussianWindow_add_complement`, `Real.one_sub_gaussianWindow_le`, `Real.gaussianWindow_moment_identity`, `Real.gaussianWindow_remainder_bounds` |
| same | `Real.integrable_gaussianDensity_mul`, `Real.gaussianMoment_eq_truncated_add`, `Real.integral_le_of_gaussianMoment`, `Real.exp_neg_log_sq_le_rpow` |
| `ConreyBaluyotGaussianMoment.lean` | `exists_mollifiedZeta_vertical_quadratic_bound`, `integrable_mollifiedGaussianMoment`, `mollifiedGaussianMoment_eq_integral` |
| same | `mollifiedSecondMoment_gaussian_identity`, `mollifiedGaussianMoment_source_tail_identity`, `gaussianMomentExcess_nonneg` |
| same | `mollifiedSecondMoment_le_of_gaussianMoment`, `mollifiedSecondMoment_le_of_log_padded_gaussianMoment` |
| `ConreyBaluyotGaussianReflection.lean` | `conj_mollifierCoefficient`, `conj_nonstandardMollifier`, `conj_mollifiedZeta`, `mollifiedZeta_vertical_norm_sq_eq_reflected`, `mollifiedGaussianContourKernel_onLine`, `integrable_mollifiedGaussianContourKernel`, `mollifiedGaussianMoment_eq_vertical_integral` |

## Updated research agenda

| Priority | Obligation | Status and concrete acceptance |
| --- | --- | --- |
| Completed | Exact finite twisted expansion, outward endpoints, selectable line | Retain the previous checkpoint's results and all signed terms. |
| Completed | Gaussian smoothing and actual whole-line integrability | Explicit window deficit, source tails, central excess and logarithmic padding are proved. |
| Completed | Real coefficients and initial reflected vertical integral | Proved for the actual finite mollifier; contour shifting remains separate. |
| 1 | Actual smoothed moment | **Open.** Supply `mollifiedGaussianMoment σ y ε σ Δ u ≤ 1+r` uniformly on the padded center interval and coupled sigma strip, with quantified nonnegative r. The new transfer then supplies the central excess. |
| 2 | Shift the actual Gaussian contour | **Open.** Starting from the proved vertical integral, move to the required abscissa, retain the signed residue at s=1 and both horizontal contributions, and prove their limiting bounds. Do not replace this with a premise restating the shifted identity. |
| 3 | Full signed arithmetic decomposition | **Open.** Connect the actual shifted product to the established damped Estermann/Mellin objects and prove the full `g = M₁ + M₂ + D₁ + D₂ + E` decomposition. Its gcd main terms include off-diagonal mollifier pairs. |
| 4 | Complete and multilinear Kloosterman estimates | **Open.** Prove checked providers with the actual moduli, coefficient family and uniform parameter ranges. Exact finite completion alone is insufficient. |
| 5 | Parameter/error assembly and global counting | **Open.** Only after analytic error providers, spend the theta < 4/7 budget; keep cutoff and loss parameters distinct. Match analytic multiplicities and closed dyadic boundaries to global counters. |
| 6 | RH-level forcing | **Open.** Fixed density improvements and small smoothing error do not eliminate every zero or remove the signed right/horizontal boundary budgets. |

The existing `ConreyBaluyotEstermannMellin.lean` proves the initial complex
Mellin representation of the actual damped series, with inversion and exchange
providers discharged. This is available infrastructure, not the missing map
from the Gaussian mollified product to the full arithmetic decomposition.

## Verification evidence

The core combined candidate passed Bazel/BuildBuddy in 24.221 seconds of server
verification: `job_0S-P6puJqtU4kAbTnYgzck9Lrp8BnB23`,
[invocation](https://app.buildbuddy.io/invocation/e2e59519-f2de-4e0d-980c-14e51cc7f2b2).
The saved Gaussian window and actual moment modules, including logarithmic
padding, passed a focused import check in 47.342 seconds:
`job_NMdArWkX6zxs8bBmhtGkbMftxkKy-g3Y`,
[invocation](https://app.buildbuddy.io/invocation/4ce61c52-0210-4c3e-a244-2d226761f8f9).
The reflection candidate and eleven standard-axiom guards passed in 45.902 seconds:
`job_zbRstewSnRAxGkOtO2Lc4197U6Dkrh5y`,
[invocation](https://app.buildbuddy.io/invocation/8b39cf32-9630-4bd2-9e83-c7b054bea514).
All three final saved modules and fifteen standard-axiom guards passed in
48.772 seconds of server verification: `job_ufvlXGtchtk5CRYQ0jgPjTz0WHj-UcQ2`,
[invocation](https://app.buildbuddy.io/invocation/07386054-ae14-4c91-9476-f0b8ca336935).
Each guarded theorem depends exactly on `propext`, `Classical.choice` and
`Quot.sound`; no additional axiom is accepted. The managed checkpoint performs
the full-project validation required before publication. These focused checks
alone do not certify the full repository. All durations here are server
verification times, distinct from transport, setup and polling delays.

Wolfram returned the Gaussian mass, truncated mass and two-tail comparison as
`1`, `Erf[H/Δ]` and `sqrt(2) exp(-H²/(2Δ²))`, and simplified the excess identity
to zero. Those exploratory calls emitted Wolfram warnings; no theorem depends
on their output. Lean proves the required identities independently. `Erf` is
not introduced or required by the formalization.

An axiom audit checks foundations, not the truth of local premises. In
particular the smoothed-moment bound remains open even if its transfer theorem
depends only on `propext`, `Classical.choice` and `Quot.sound`.

Retained workspace: `ws_lzLF4hiCiyQmu7R7jEWw2e6gFfOXxu-2`.
Project root:
`/home/cri_2025/lean-agent-workspaces/ws_lzLF4hiCiyQmu7R7jEWw2e6gFfOXxu-2/RiemannResearch`.
Resume that token, inspect jobs and current main, and preserve newer work.

# Hardy endpoint formalization and the remaining RH bound

## Verified outcome

The raw Möbius sums and the canonical boundary-corrected sums converge in the actual Hardy norm on Re(s)>1. The analytic identification and quantitative arithmetic rate are now included in Lean, closing the gaps in the earlier [research note](HardyEndpointCompactness20260924.md).

There is no unconditional proof of RH here. The new implication from a uniform moving Hardy bound to RH is fully formalized; its uniform bound remains an explicit open hypothesis.

This extends the range stated in Manzur–Noor–Quintero, [arXiv:2606.16097](https://arxiv.org/html/2606.16097v1), Theorem 3.1. No historical novelty claim is made. That paper's alpha is the half-plane boundary, whose RH endpoint is 1/2. In the moving-bound theorem below, alpha is the offset from 1/2.

## Actual functions and endpoint theorem

Write
\[
G_k(s)=\frac{(k^{-s}-k^{-1})\zeta(s)}s,\quad
S_N(s)=\sum_{k=1}^N\mu(k)G_k(s),\quad
m_N=\sum_{k=1}^N\frac{\mu(k)}k.
\]
The first generator vanishes. Lean defines the generators using the actual Mellin transform, supplying the removable value at s=1, and proves the zeta formula on Re(s)>0 away from s=1.

The corrected family is
\[
\widetilde S_N=S_N-(N+1)m_NG_{N+1}.
\]
Its step profile satisfies
\[
F_N(n)=\sum_{k\le N}\mu(k)\lfloor n/k\rfloor
 -(N+1)m_N\lfloor n/(N+1)\rfloor,\qquad
F_N(n)=1\quad(1\le n\le N).
\]

The principal unconditional declaration is **rawHardyMobiusSum_endpoint**, in namespace RiemannResearch.RH.Pareto, in [HardyMobiusEndpoint.lean](HardyMobiusEndpoint.lean). Its exact assertion is
\[
\forall\eta>0,\quad\forall^\infty N,\quad\forall\sigma>1,\qquad
\int_{\mathbb R}\left|\frac1{\sigma+2\pi it}
-S_N(\sigma+2\pi it)\right|^2dt<\eta.
\]
The corrected version is **correctedHardyMobiusSum_endpoint**. This normalization equals the conventional vertical-line integral divided by \(2\pi\).

The generic Mellin function is proved to belong to the Hardy space. Its squared norm is identified as the least upper bound of the actual line integrals:
\[
\sup_{\sigma>1}\int_{\mathbb R}
|\mathcal Mf(\sigma+2\pi it)|^2dt
=\sum_{n\ge1}\frac{2n+1}{2n^2(n+1)^2}|f(n)|^2.
\]
This is **paretoMellin_hardy_endpoint_isLUB** in [ParetoMellinHardyEndpoint.lean](ParetoMellinHardyEndpoint.lean). No analytic-identification premise remains in its type.

## Closing the arithmetic gap

The corrected endpoint uses the earlier formal qualitative PNT argument and the exact cell-weight comparison. Removing the correction needs quantitative decay: \(m_N\to0\) alone does not justify a growing harmonic factor.

The proof adapts the existing quantitative PNT development and derives a sufficient rate:
\[
|\psi(y)-y|\le\frac{Cy}{(1+\log y)^2}\quad(y\ge1),
\]
\[
\sum_{k\le x}|R(x/k)|\le3Cx,\qquad M(x)\log x=O(x),
\]
\[
|m_N|\le\frac1K+\frac1{NK}
+\frac{C(H_K+1)}{\log N}\qquad(K\ge1,\ N\text{ sufficiently large}).
\]
The last estimate holds simultaneously for every K. Taking \(K=\lfloor\log N\rfloor+1\) gives a bound of order \((1+\log\log N)/\log N\), hence
\[
m_N^2\log N\longrightarrow0,\qquad m_N^2(H_N+1)\longrightarrow0.
\]
Exact finite quotient reindexing retains the complete tail before estimation; a finite telescoping comparison controls the logarithmic kernel.

The unconditional provider is **mobiusReciprocalSum_sq_mul_harmonic_tendsto_zero** in [MobiusQuantitativeRate.lean](MobiusQuantitativeRate.lean). The entire correction energy satisfies
\[
\|(N+1)m_NG_{N+1}\|_1^2\le m_N^2(H_N+1).
\]
Combining this with corrected convergence proves the raw endpoint. No Ramaré estimate is assumed; the derived rate is weaker than his sharper explicit bound but sufficient here.

The quantitative PNT source is the pinned [PrimeNumberTheoremAnd development](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/a5154676af9aa3095150ee410cdda80555aa0642). Three compatibility modules preserve attribution and adapt namespaces, imports, and changed APIs. Their theorem Quantitative.MediumPNT is checked with its dependencies.

## The formal implication toward RH

[ExactHeadMovingHardyRH.lean](ExactHeadMovingHardyRH.lean) proves **canonicalMobius_riemannHypothesis_of_movingHardy_bound**. For the actual corrected family, its hypotheses are
\[
\alpha_N\ge0,\qquad\alpha_N\to0,
\]
and one constant C satisfying
\[
\boxed{\quad
\forall N,\ \forall\sigma>\tfrac12+\alpha_N,\qquad
\int_{\mathbb R}|\widetilde S_N(\sigma+2\pi it)|^2dt\le C.
\quad}
\]
These imply the actual project RiemannHypothesis proposition. Legality, exact initial coordinates, Mellin identification, vanishing at zeta zeros, and reflection are all discharged.

**Open:** construct such a schedule and prove its common bound. Standard-foundation-only axiom output does not discharge hypotheses in a theorem's type.

The proof uses a direct quantitative obstruction. A zero \(\rho=\beta+i\gamma\), \(\beta>1/2\), forces polynomial energy growth. For an exact-head vector with vanishing Mellin transform at rho, \(N\ge3\), and \(1\le u<2\beta\), Lean proves
\[
E_u(F_N)\ge
\frac{2\beta-u}{4|\rho|^2}(N+1)^{2\beta-u},
\qquad
E_u(F)=\int_1^\infty|F(\lfloor x\rfloor)|^2x^{-u-1}\,dx.
\]
A moving bound with \(u_N=1+2\alpha_N\to1\) gives a fixed bound at every chosen \(u>1\) eventually, contradicting this cost. Cantor diagonal selection and Banach–Alaoglu do not supply that bound.

## Further progress and its limit

[MobiusSignCrossingBridge.lean](MobiusSignCrossingBridge.lean) proves that a finite sign crossing \(m_Nm_{N+1}\le0\) implies
\[
|m_{N+1}|\le\frac1{N+1},\qquad
\|\text{boundary correction at }N+1\|_{\rm critical}^2
\le\frac{2(N+2)}{(N+1)^2}.
\]
The sign-crossing premise is explicit. Cofinality of such cutoffs is not formalized, and the full residual tail is not controlled by the correction estimate.

An analytic comparison explains why endpoint estimates cannot simply be iterated. For \(N\ge2\), put \(K_N=\lceil N\log N\rceil\) and
\[
r_N(x)=N\,\mathbf1_{[K_N,2K_N)}(x).
\]
It has a zero initial interval and critical energy \(N^2/(2K_N)=o(N)\), but
\[
E_\alpha(r_N)=
\frac{N^2(1-2^{-2\alpha})}{2\alpha K_N^{2\alpha}}.
\]
Its alpha=1 energy tends to zero, whereas every fixed \(0<\alpha<1\) gives divergence. This is an analytic comparison, not a Möbius counterexample or a new Lean theorem. Exact heads and the available growth estimates alone therefore cannot justify iteration to the critical line.

## Verification boundary

The complete combined source passed Lean with exit code 0. The unconditional endpoint, canonical moving-bound implication, and polynomial lower bound report only **propext, Classical.choice, Quot.sound**. No proof admissions or new project-local axioms are introduced.

The endpoint theorem has no substantive unproved premise. The RH implication retains its displayed common bound. Final publication additionally validates the separate modules and their project dependencies.

Earlier Wolfram checks and finite experiments remain in [HardyEndpointCompactness20260924.md](HardyEndpointCompactness20260924.md). They are not proof premises, and no RH conclusion is inferred from finite computation.

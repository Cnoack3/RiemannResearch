# Effective sampling audit — 24 October 2026

This audit separates already formalized actual-zero inputs, new Lean results, and ordinary mathematical consequences of published density bounds. The consolidated modules, including the conditional numerical strict-tail specialization, passed project-module compilation and a principal-theorem axiom audit. Final publication is gated by the repository checkpoint.

## Actual Landau input already available

`Analysis/ActualUniformRationalLandau.lean`, theorem `exists_uniform_rational_landau_rpow_bound`, already proves an unconditional estimate for the actual zeta zeros, with analytic multiplicities. For one positive constant C, every T≥9 and integers 1≤m<n≤X satisfy

\[
\left|\operatorname{LandauSum}\!\left(T,\log\frac nm\right)
   +T\operatorname{rationalLandauMain}(n,m)\right|
\le C\left(X^{5/2}+X^{3/2}\log^2(T+3)+X\log(T+3)\right).
\]

The rational main coefficient is also formally identified with the appropriate von Mangoldt coefficient. This result uses the imported contour, good-height, Gamma, series, and local-count theorems; it does not assume a Landau estimate, a density estimate, or RH.

For integer conductor q>1, define

\[
W_L(q)=2\pi\sqrt q\,(q^{5/2}+q^{3/2}+q).
\]

The checked consumer `exists_actual_landauSignal_bound` derives

\[
|\mathrm{landauSignal}(q,T)-\Lambda(q)|
\le W_L(q)\,C\frac{1+\log^2(T+3)}T.
\]

For the actual inverse Gram matrix A define

\[
R_L=\sqrt{\sum_{q,r}|A_{qr}|W_L(q)W_L(r)},\qquad
R_H=\sqrt{\sum_{q,r}|A_{qr}|W_H(q)W_H(r)},
\quad W_H(q)=4\pi(\sqrt q-1)^2.
\]

These retain every inverse-matrix entry. The checked consumer bound is

\[
\|\widehat b(T)-b\|_{H^{-1}}
\le R_H\frac{E(T)}T
 +C R_L\frac{1+\log^2(T+3)}T.
\]

The only remaining analytic input is a bound on the actual horizontal energy E(T). The existence of C is formalized, but this audit does not extract a numerical value for C.

## Explicit schedule and finite tolerance

Choose certified integer weights w_j≥max(R_{H,j},R_{L,j}). Set

\[
M_0=0,\qquad M_j=M_{j-1}+16+jw_j,\qquad T_j=e^{M_j}.
\]

For j>0 one has M_j≥16 and M_j≥jw_j. The elementary inequalities M³≤e^M and log(e^M+3)≤2M, valid for M≥16, imply

\[
\frac{1+\log^2(e^M+3)}{e^M}\le\frac5M.
\]

Consequently, a certified horizontal bound E(T_j)/T_j≤D/M_j implies

\[
\|\widehat b(T_j)-b\|_{H^{-1}}\le\frac{D+5C}{j}.
\]

Thus `(D+5*C) ≤ epsilon*j` is a finite absolute-tolerance certificate. For relative tolerance eta one instead requires `(D+5*C) ≤ eta*j*sqrt(packetCapacity)`. The schedule is explicit once finite weight certificates are supplied. A numerical first successful stage additionally requires an explicit numerical C and the density provider's validity threshold; neither is hidden by the existential theorem.

## Published density constants: ordinary mathematics only

Primary source: Aleksander Simonič, *Explicit zero density estimate for the Riemann zeta-function near the critical line*, Theorem 1 and its corollary, [arXiv:1910.08274v2](https://arxiv.org/html/1910.08274v2).

The source uses strict counts N(σ,T), β>σ. Its corollary, for T≥2H₀ with H₀=3.0610046·10¹⁰ and 1/2≤σ≤0.831, has coefficient 10395.21/(2^(1−(σ−1/2)/4)−1) and factor T^(1−(σ−1/2)/4) log(T/2).

Our elementary inference is the weaker uniform strict-tail bound

\[
N(1/2+t,T)\le24000\,T\log T\,e^{-(\log T)t/8}
\quad(0\le t\le1/2,\ T\ge2H_0).
\]

On t≤0.331 the denominator exceeds 1/2 and the exponent 1/4 is stronger than 1/8. Above 0.331, monotonicity of the count and 0.331/4≥(1/2)/8 suffice.

The project's proved tail-to-energy inequality then yields

\[
E(T)/T\le 12{,}288{,}000/\log T
\]

whenever log T≥16 and T≥2H₀. This uses the conservative factor 8C/a² with C=24000 and a=1/8. The publication-to-actual-count provider is not a Lean theorem here. The numerical implication is checked as `horizontalEnergy_ratio_of_simonic_tail_at_exp`, with the strict-tail estimate explicitly assumed.

A citation is not a kernel proof. The strict-count convention also must not silently be replaced by the project's inclusive-count definition.

## Sharper Landau variant and provenance

Primary source: S. M. Gonek, *A Formula of Landau and Mean Values of ζ(s)*, Theorem 1, [author-hosted PDF](https://www.sas.rochester.edu/mth/people/faculty/gonek-steve/assets/pdf/8-landau-form.pdf).

The published uniform estimate can reduce the conductor weight substantially. Its displayed error terms use big-O constants; the statement does not furnish a numerical constant K. The larger weight above deliberately uses the existing unconditional Lean theorem, so the explicit schedule no longer depends on a newly postulated sharp Landau provider. Formalizing sharper constants is an optimization, while formalizing an actual density provider remains necessary for an unconditional sampled-signal rate in Lean.

## What this does not finish

Sampling accuracy does not prove a uniform bound on the full Pareto/Hilbert energy of the exact-head arithmetic approximants. That separate bound is the main unresolved arithmetic/RH step. Neither a finite experiment nor the present sampling estimate supplies it.

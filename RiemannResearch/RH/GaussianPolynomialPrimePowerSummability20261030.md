# Absolute prime-power summability for Gaussian-polynomial tests

30 October 2026.

## Scope

Let R > 0, tau be real, and B be any real polynomial, including zero.
Use exactly the existing test and integral-defined normalized transform:
`h_B(z) = B(z-tau) exp(-R(z-tau)^2)` and
`g_B(u) = (2*pi)^(-1) integral_R exp(-i*u*t) h_B(t) dt`.

This development proves absolute convergence of the full von Mangoldt
prime-power contribution. It also supplies a genuine sum-integral interchange
on every vertical line Re(s) = sigma > 1 for the actual -zeta'/zeta and the
Gaussian-polynomial test. No RH, zero-location, positivity, symmetry,
nonvanishing or polynomial-degree hypothesis is used.

## Exact identity before the estimate

Write K = frequencyConstant R B >= 0 and
M = (frequencyPolynomial R B).natDegree, as in the existing growth module.
For every real c,t and R>0 the exact identity is

\[
ct-\frac{t^2}{4R}=Rc^2-\frac{(t-2Rc)^2}{4R}.
\]

The last square is nonnegative. Together with
(1+t)^M <= exp(M*t) for t>=0, this gives, for every real a,

\[
(1+t)^M e^{-t^2/(4R)}
\le e^{R(M+a)^2}e^{-at}\qquad(t\ge0).
\]

Thus the proved Gaussian envelope for the actual transform implies

    |g_B(u)| <= K exp(R*(M+k)^2) exp(-k*|u|)

for each natural k and every real u. Set C_k = K exp(R*(M+k)^2).
For every integer n>=1, log n>=0 and exp(-k log n)=n^(-k), so

\[
|g_B(\log n)|\le \frac{C_k}{n^k},\qquad
|g_B(-\log n)|\le \frac{C_k}{n^k}.
\]

The comparison is global, not just eventual. C_k is independent of tau.
It depends on R,B,k; no uniformity in varying R or B is asserted.

## All integers and all prime powers

For n>=1, Mathlib's unconditional bound 0<=Lambda(n)<=log n and
sqrt(n)>=1 give Lambda(n)/sqrt(n)<=n. With k=3,

\[
0\le\frac{\Lambda(n)}{\sqrt n}
\bigl(|g_B(\log n)|+|g_B(-\log n)|\bigr)
\le \frac{2C_3}{n^2}.
\]

The natural-number index 0 contributes zero by Mathlib's conventions;
the index 1 also contributes zero because Lambda(1)=0.
Comparison with Mathlib's summable inverse-square series proves summability
over all natural numbers, hence also over n>=2.

The complex summand is retained exactly:

\[
A_n=\frac{\Lambda(n)}{\sqrt n}
\bigl(g_B(\log n)+g_B(-\log n)\bigr).
\]

Its norm is dominated by the displayed nonnegative summable sequence.
Consequently sum A_n is absolutely convergent. No real-part replacement,
positive-part truncation, prime-only replacement, or removal of higher
prime powers is performed. The support lemma gives A_n=0 whenever
n is not a prime power; it makes no converse assertion.
At n=p^k, p prime and k>=1, the coefficient is
exactly log(p)/sqrt(p^k).

## The justified vertical-line interchange

Fix sigma>1 and any complex-valued f in L1(R). Put

    D_n(t) = LSeries.term (Lambda complexified) (sigma+i*t) n.

For n>0 this is Lambda(n)/n^(sigma+i*t), and D_0=0.
The exact equality of norms

    |D_n(t)| = |D_n(0)|

is independent of t. Mathlib supplies summability of |D_n(0)| at sigma>1.
Each f*D_n is measurable and integrable, and

\[
\sum_{n=0}^{\infty}\int_{\mathbb R}|f(t)D_n(t)|\,dt
=\left(\sum_{n=0}^{\infty}|D_n(0)|\right)
 \int_{\mathbb R}|f(t)|\,dt<\infty.
\]

Applying Mathlib's Bochner series-integral theorem therefore gives

\[
\int_{\mathbb R}f(t)\sum_{n=0}^{\infty}D_n(t)\,dt
=\sum_{n=0}^{\infty}\int_{\mathbb R}f(t)D_n(t)\,dt.
\]

Mathlib's actual von Mangoldt Dirichlet-series theorem identifies
sum_n D_n(t) with -zeta'(sigma+i*t)/zeta(sigma+i*t).
This identity is used by the checked interchange, rather than introduced
as an unproved zeta hypothesis.

For the Gaussian application take

    f_sigma(t) = h_B(t+i*(1/2-sigma))
               = h_B((sigma+i*t-1/2)/i).

The previously checked integrable_horizontal supplies f_sigma in L1.
The specialized interchange consequently has only R>0 and sigma>1 as
inequality hypotheses, besides real tau and real polynomial B.

The usual normalization factor 1/(2*pi) can be multiplied into both sides.
There is no missing contour Jacobian: the displayed theorem is in the real
parameter t; on an upward line ds=i dt.

## What this does not yet interchange

Absolute summability of the evaluated values g_B(+-log n) does not itself
justify moving the n-sum inside the unshifted real Fourier integral.
The theorem above deliberately requires sigma>1.

The termwise shifted-transform evaluation

\[
\frac1{2\pi}\int_{\mathbb R}f_\sigma(t)D_n(t)\,dt
=\frac{\Lambda(n)}{\sqrt n}g_B(\log n).
\]

is a separate step. It follows on paper from the appropriate shifted
Fourier-transform identity (equivalently exponential tilting plus Fourier
inversion), but is not asserted as a checked declaration in this development.

For clarity, its paper proof needs no new zeta assertion. Set
\(q_\sigma(u)=e^{(\sigma-1/2)u}g_B(u)\). The existing Gaussian bounds
make \(q_\sigma\) continuous and integrable; the checked complex inversion
identity expresses \(f_\sigma(t)\) as its inverse Fourier integral.
The horizontal-strip theorem gives \(f_\sigma\in L^1\).
Ordinary Fourier inversion therefore recovers \(q_\sigma\) as the
normalized Fourier transform of \(f_\sigma\). Evaluating at \(\log n\)
and multiplying by \(\Lambda(n)n^{-\sigma}\) gives the displayed identity.
This is a paper proof of that additional assembly step, not a newly
kernel-checked theorem.

The left-side contribution and its sign/orientation must likewise be
assembled separately. The absolutely convergent final two-sided
prime-power series is already available in full.

Still open in the actual explicit-formula program:

1. The shifted-transform evaluation and contour assembly as needed.
2. The actual gamma logarithmic-derivative contribution.
3. Multiplicity-weighted zero-sum convergence and unconditional counting data.
4. Good heights, horizontal-edge bounds, residues and legitimate contour shifts.
5. The complete explicit formula with both pole terms.
6. The independent universal signed lower bound required by the RH consumer.

## Sources

The statement and comparison strategy come from the user's 30 October 2026
request and the earlier inversion memorandum:
[GaussianPolynomialFourierInversion20261029.md](GaussianPolynomialFourierInversion20261029.md).
The explicit completed-square constant is an elementary specialization of
that strategy, not a claim of novelty.

The implementation reuses Mathlib at revision
51e6992efd06126df61a496bebf8f49482a4e129, particularly
Analysis/PSeries.lean, NumberTheory/ArithmeticFunction/VonMangoldt.lean,
NumberTheory/LSeries/Dirichlet.lean, and
MeasureTheory/Integral/DominatedConvergence.lean.

## Lean declarations and verification

The reusable comparison is in Analysis/GaussianLogDecay.lean; the general
actual von Mangoldt interchange is in Analysis/VonMangoldtVerticalIntegral.lean;
the specialized results are in Analysis/GaussianPolynomialPrimePower.lean.
All three are exported from RiemannResearch.lean. The catalog supplement lists
the declarations and exact assumptions.

The complete coherent candidate passed Lean server job
job_9W3whlCgioRpSpn9ri2kGm1Yrzy_fAN_: exit code 0, verified true,
reported server duration 247.507 seconds. Four inspected main declarations
reported only propext, Classical.choice and Quot.sound, with no proof placeholders
or project-local axioms. This result certifies the candidate, not by itself
the saved-module build or the final checkpoint.

Workspace-opening request time and client polling delay were not separately
instrumented. The reported server duration is not a measurement of kernel-only
time, and no cache, network or disk cause is inferred from it.

The saved-module import/axiom request job_GJ_wxvkFPNjEhYl7nwIs0ojgI-WkUEEV
reached its 600.074-second wall limit (verified false). Its log explicitly records
successful builds of all three new modules: GaussianLogDecay (161 seconds),
VonMangoldtVerticalIntegral (302 seconds), and GaussianPolynomialPrimePower
(226 seconds). These per-module Lake timings are not additive wall-clock times.
The enclosing request did not finish and is not reported as a successful
import/axiom verification. Final publication remains gated by the separate
checkpoint's audit and required project validation.

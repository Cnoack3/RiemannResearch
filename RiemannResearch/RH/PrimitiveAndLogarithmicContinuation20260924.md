# Primitive criteria and the unconditional logarithmic Möbius mean

24 September 2026. This continues the repository's RH markdown agenda.
The results below concern the actual project vectors. RH is not proved.
The logarithmic Möbius mean is classical; no mathematical novelty is claimed.

## The arithmetic obligation now discharged

Put

\[
m_N=\sum_{n=1}^N\frac{\mu(n)}n,\quad
L_N=\sum_{n=1}^N\frac{\mu(n)\log n}n,\quad
B_N=\sum_{n=1}^N\frac{\Lambda(n)-1}n.
\]

`PrimeNumberTheorem.logarithmicMobiusMean_tendsto_neg_one` proves
\(L_N\to-1\) without additional arithmetic hypotheses. Its proof chain is:

1. The established `Quantitative.MediumPNT` gives
   \(|\psi(x)-x|\le Cx/(1+\log x)^4\) for every \(x\ge1\), after a
   finite-range adjustment. This is `R_inverseLogFourth_bound`.
2. Finite Abel summation retains the endpoint exactly. A telescoping
   logarithmic majorant then yields actual constants \(\beta,D\), with
   \(D\ge0\), such that
   \[
   |B_q-\beta|\le\frac D{(1+\log(q+1))^3}\qquad(q\ge1).
   \]
   This is `mangoldtHarmonicDefect_inverse_log_cube_bound`.
3. The finite divisor convolution is exact:
   \[
   L_N+1=-\beta m_N-
   \sum_{d=1}^N\frac{\mu(d)}d(B_{\lfloor N/d\rfloor}-\beta).
   \]
4. For any fixed positive integer \(K\), the contribution from
   \(d\le N/K\) has absolute value at most \(3D/(1+\log K)\).
   The remaining sum is exactly a finite sum of quotient windows:
   \[
   \sum_{q=1}^{K-1}(B_q-\beta)
   \left(m_{\lfloor N/q\rfloor}-m_{\lfloor N/(q+1)\rfloor}\right).
   \]
   Each window tends to zero by the existing proved reciprocal Möbius limit.
   Taking the limits in the order \(N\to\infty\), then \(K\to\infty\),
   proves the result. No unsquared estimate \(m_N\log N\to0\) is assumed.

The statement is NIST DLMF 27.11.15:
https://dlmf.nist.gov/27.11.E15 . The quantitative input is the project's
compatibility port of PNT+ at commit
`a5154676af9aa3095150ee410cdda80555aa0642`; the elementary convolution and
telescoping arguments here give the intervening formal proof.

## The full fixed Gram sources

Let \(U_N=\mathbf1-\mathrm{rawMobiusHilbert}(N)\) and let \(g_m\) be an
actual normalized residue generator. `NaturalMobiusSourceLimits` proves

\[
\langle U_N,\mathbf1\rangle_P=1+L_N\longrightarrow0,
\qquad \langle U_N,g_m\rangle_P\longrightarrow0
\quad\text{for each fixed }m\ge1.
\]

The second limit combines the proved constant source with the separately
proved centered periodic source. These are the full Pareto inner products,
including the infinite physical tail. This discharges the constant-mode
formalization obligation in Sections 7–8 of
`ReciprocalCharge_DilationAndPeriodicSource_20260924.md`.

## A stronger residual criterion

For a physical test \(f\), define \(H_f(K)=\sum_{k=1}^K f(k)\). The new
general Abel argument proves pairing decay whenever

\[
\sum_{K\ge0}|H_f(K)|
\frac{3+\tau(K+1)}{(K+1)(K+2)}<\infty.
\]

The boundary term follows from the actual cutoff bound; it is not a new
arithmetic premise. The real-exponent divisor series proves this condition
whenever \(|H_f(K)|\le C(K+1)^\alpha\) for one fixed \(\alpha<1\).

For the actual orthogonal residual \(r\), the exact pairing is
\(\langle U_N,r\rangle_P=E=\|r\|_P^2\) for every \(N\).
Consequently `limitResidual_zero_iff_summable_primitive` is an established
equivalence between residual vanishing and the displayed summability.
`riemannHypothesis_of_residual_primitive_rpow_bound` is a **conditional
research reduction**: its actual-residual power bound remains **Open**.
The axiom audit does not discharge that local hypothesis.

## What the new exact dilation identity supplies

For \(c_m=\langle r,D_mr\rangle_P\), the new checked identity is

\[
H_r(N)=2\sum_{m=1}^N c_m-Nc_{N+1}.
\]

The unconditional bound \(|c_m|\le\sqrt m\,E\) gives

\[
|H_r(N)|\le E\left(2\sum_{m=1}^N\sqrt m+N\sqrt{N+1}\right).
\]

This does not supply a sublinear power bound. The companion
`Residual_Abel_Obstruction_20260924.md` records additional paper estimates and
an exact iterated-limit obstruction, with their separate unformalized status.

**Open:** control the actual growing inverse Gram matrix on its arithmetic
source, or prove a sufficient actual-residual primitive estimate. Fixed source
coordinates tending to zero do not supply either conclusion.

## Verification and recovery ledger

The retained workspace resumed from published commit
`707c5adb443adaa4df6a0148159759786d6a581b`.
The earlier queued job `job_oL1fJw4GBIBFdiYr5j8PvVX9f610I-_a` and the separate
continuation's checkpoint `job_LDz1d9a0dXCYlC8orHJS342W9PBjuNTp` were both
reported terminal interrupted after their owners exited. Neither interruption
was treated as successful verification or publication.

The 14-module intermediate check `job_8Zuf2FZ5TW-fq62SbBilnO5JTGg3qoPy`
succeeded in 24.21 seconds, including the conditional mean assembly.
The final 16-module coherent check `job_MRYX9KShwGKCY8LFBcQV0RrndaHpoE7z`
succeeded (`verified: true`, exit 0, 6.466 seconds), code SHA-256
`69ba1fe754ce8cf70d2201819cb6085120d6d090d64dcaafed90a58dac37e05b`.
Its 12 principal axiom reports contain only `propext`, `Classical.choice`,
and `Quot.sound`. Publication separately requires the repository checkpoint's
module build, source audit, commit, and push.

Wolfram independently simplified the exact finite convolution identity to
zero at each cutoff 1 through 12. This was corroboration only; the Lean
arithmetic theorem proves the identity for every positive cutoff.

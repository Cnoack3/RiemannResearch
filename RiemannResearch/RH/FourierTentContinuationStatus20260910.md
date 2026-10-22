# Fourier tent reconstruction: Lean continuation

September 10, 2026. Continuation of `FourierBridgeLeanVerification20260910(1).md`.

## Result

This continuation adds **60 public theorems across five new modules**, plus one private calculus helper. It completes the actual logarithmic-tent Fourier reconstruction and its identification with **every positive-integer boundary step**, and proves an exact Fourier expansion for arbitrary finite signed packets.

The complete infinite signed arithmetic Fourier bridge and the uniform full boundary-energy estimate remain open. This development does not prove RH.

## Actual Fourier reconstruction

For the existing root tent, set
\[
g_i(t)=\tau_{2(i+1)}(\exp((\log2)t)),\qquad
\Phi_i(t)=\sum_{k\in\mathbb Z}g_i(t+k).
\]
Lean proves compact support, integrability, locally uniform absolute convergence of the translates, continuity and period one of the actual periodization, and
\[
\widehat g_i(h)=c_i(h),\qquad
\Phi_i(t)=\sum_{h\in\mathbb Z}c_i(h)e^{2\pi iht}.
\]
Here `c_i(h)` is the previously defined `dyadicTentMellinCoefficient`, not a newly substituted coefficient sequence. The real Fourier transform is identified with its actual Mellin integral by the substitution `t = log x / log 2`, including frequency zero. The reconstruction is a `HasSum` theorem using the existing absolute coefficient-row summability.

The physical periodization is
\[
P_i(x)=\sum_{k\in\mathbb Z}\tau_{2(i+1)}(x/2^k).
\]
The scale sum is genuinely summable and has at most one nonzero term. Its identification with the existing boundary coordinate is proved for **every** positive integer `m`, including rising sectors, falling sectors, zero gaps, and the small-integer region where negative-depth atomic terms vanish:
\[
\Phi_i(\log m/\log2)=P_i(m)
=\operatorname{dyadicBoundaryCoordinate}
  (\operatorname{dyadicProjectedStep}(m))(i).
\]

The principal endpoints are:

- `dyadicLogTent_fourier_eq_mellin`
- `dyadicLogTentPeriodization_hasSum_fourier`
- `dyadicTentPeriodization_integer`
- `dyadicBoundaryCoordinate_step_hasSum_fourier`
- `dyadicBoundaryCoordinate_finite_signed_packet_hasSum_fourier`

The finite-packet theorem allows arbitrary real signed weights and any finite subset of indices `m`, using positive dilations `m+1`. It moves the finite signed packet through the entire Fourier series by an exact identity. No absolute-value replacement or frequency diagonalization is used. The limit in the arithmetic cutoff is not part of this theorem.

The exact phase-zero cancellation is also proved:
`hasSum_dyadicTentMellinCoefficient_zero` gives `HasSum (dyadicTentMellinCoefficient i) 0`.

## Spatial and arithmetic control

For every frequency, including zero,
\[
|c_i(h)|\le\frac1{(i+1)\log2},\qquad
\sum_{i\ge0}|c_i(h)|^2
\le\frac1{(\log2)^2}\sum_{i\ge0}\frac1{(i+1)^2}.
\]
These are bounds for each frequency column. They do **not** bound the energy after the signed arithmetic Fourier frequencies are summed.

The actual signed discrepancy now has the exact integer-conductor reduction. With `K = floor x`, `Z = regularizationZetaSeries ε`, actual normalization `Nε`, residue `κε`, and actual floor-convolution prefix `Pε(K)`,
\[
D_\epsilon(x)=N_\epsilon\left(P_\epsilon(K)-K/Z\right)
+\kappa_\epsilon(K-x+1)-1.
\]
The atom at one and the compensator beginning at one are both retained. Lean proves `0 ≤ κε ≤ ε` and
\[
-1\le\kappa_\epsilon(K-x+1)-1\le\epsilon-1.
\]
Consequently the discrepancy differs from the normalized centered integer prefix by at most **1**, for `0 < ε ≤ 1` and `x ≥ 1`.

Finite Abel summation expresses the genuine damped Möbius prefix in ordinary Mertens prefixes. The exact kernel mass is proved, and decreasing nonnegative weights give
\[
\left|\sum_{n=1}^{N}\mu(n)n^{-\epsilon}\right|\le B
\quad\text{if}\quad
|M(n)|\le B\ \text{for all }n\le N,\quad\epsilon\ge0.
\]
This damping-uniform transfer contains no `1/ε` loss. Its premise is explicit: it does not prove the quantitative Mertens theorem.

## Module map

| Module | Public theorems | Scope |
| --- | ---: | --- |
| `Analysis/PositiveArithmeticPrefix` | 5 | Exact finite Abel identity, mass, and prefix contraction |
| `RH/DyadicArithmeticAbelReduction` | 12 | Actual Möbius prefixes, signed discrepancy, retained endpoint, and transfer bound |
| `RH/DyadicTentCoordinateEnergy` | 4 | Actual spatial majorant and coordinate-column square summability |
| `RH/DyadicTentFourierReconstruction` | 19 | Compact log tent, continuous periodization, Fourier–Mellin equality, reconstruction, zero cancellation |
| `RH/DyadicTentFourierSamples` | 20 | Full physical periodization, all integer samples, and finite signed packets |

All five modules are exported from `RiemannResearch.lean`. No project-local axiom, `sorry`, `admit`, or unsafe declaration is introduced.

## Remaining obligations toward RH

1. Formalize the quantitative ordinary Mertens provider and its reciprocal-tail and hyperbola consequences. The new finite Abel and endpoint identities supply concrete pieces of this step.
2. Identify the signed residue/zeta-ratio multipliers and prove cutoff bounds strong enough to pass from the exact finite signed packets to the actual infinite arithmetic remainder. `DyadicSignedFourierBridge` remains open.
3. Bound the complete signed boundary energy uniformly as damping vanishes, retaining all mixed terms and compensator corrections. `DyadicUniformSignedFourierEnergyBound` and `DyadicNormalizationRemainderUniformEnergyBound` remain open.
4. Supply the actual arithmetic coordinate limits and the complementary physical-energy/legal two-seed recovery needed for the final RH argument.

The next bounded target is to instantiate the existing scalar Fourier-limit theorem with the newly verified finite-packet identity, while proving the actual arithmetic kernel limit and a summable cutoff majorant. The finite identity alone does not authorize exchanging the remaining limits.

## Resumption

Workspace token: `ws__eykLs_HJEUiekupiRigb5Ft5hXoDngi`.

Project root: `/home/cri_2025/lean-agent-workspaces/ws__eykLs_HJEUiekupiRigb5Ft5hXoDngi/RiemannResearch`.

Starting commit: `2a8bad3eb0a4d3201cb0991c3c5a788ab530561e`.

Mathematical development was parallel; all Lean verification submissions were serialized. The generated verification handoff carries the publication commit and final checkpoint evidence.

## Combined source and axiom check

Job `job_SvdS2ytQI38joeQFEdNbGLs6HeLzx9UC` compiled all 60 public declarations together, succeeded with `verified: true`, exit 0, and runtime 4.323 seconds. The ten inspected endpoints use only `propext`, `Classical.choice`, and `Quot.sound`. Their mathematical hypotheses remain those displayed in their theorem types. The shared actual-import project checkpoint is the publication gate.

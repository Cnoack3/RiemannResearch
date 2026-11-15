# Conrey--Baluyot recovery and continuation, 15 November 2026

> Later continuation: normalized branch compatibility and outward dyadic
> coverage are now established, with a sharper conditional vertical moment
> conversion. See [the current catalog](THEOREM_CATALOG_CONREY_BALUYOT_NORMALIZED_20261115.md)
> for exact statements and remaining obligations. The record below is historical.

## Recovery result

The inaccessible chat's source work was already preserved in published main.
Its displayed final phase-existence idea was implemented before this recovery:

| Published commit | Saved result |
| --- | --- |
| [1b0e5c1](https://github.com/Cnoack3/RiemannResearch/commit/1b0e5c116ab549613256a0cf6cfa7f851fee590f) | Uniform linear actual-mollifier growth |
| [ae7d01b](https://github.com/Cnoack3/RiemannResearch/commit/ae7d01bfeaaee2054de713b3c53e726ffbd9b738) | Actual mollified-zeta Jensen divisor bound |
| [0425b1b](https://github.com/Cnoack3/RiemannResearch/commit/0425b1b96f8ec3b4d03f9384d7c188c0a3b650ef) | Uniform horizontal real-part zero count |
| [1405d5c](https://github.com/Cnoack3/RiemannResearch/commit/1405d5cb4bb83eb55bc4e82264f895057f6ff52b) | Continuous-phase displacement from finite crossings |
| [f026eb9](https://github.com/Cnoack3/RiemannResearch/commit/f026eb9a57ebcbda4a83d7ab7a0bbcec358dd90c) | Constructed normalized phase on a zero-free segment |
| [147ea71](https://github.com/Cnoack3/RiemannResearch/commit/147ea71266d86c0123445202061f9dd63ac54605) | Nearby zero-free heights |
| [2789c26](https://github.com/Cnoack3/RiemannResearch/commit/2789c2610d2ab28fa92f4fcea1281481fde4b073) | Uniform logarithmic good-height horizontal bounds |
| [24a6ca7](https://github.com/Cnoack3/RiemannResearch/commit/24a6ca7215fe61ec8e154ced41537da7de40fe97) | One fixed mollifier across a dyadic window |
| [8977394](https://github.com/Cnoack3/RiemannResearch/commit/89773947d9bb66b3fddb64f09173c172f95d1bc9) | Weighted product-zero contour identity |
| [9056048](https://github.com/Cnoack3/RiemannResearch/commit/9056048835a604bad47871585b4ca921f2dacab1) | Zeta-zero count bounded by the product contour |
| [68792a1](https://github.com/Cnoack3/RiemannResearch/commit/68792a12560740c667499c44ede5ffa54217abb9) | Zero-free vertical sides and rectangle borders |
| [0352937](https://github.com/Cnoack3/RiemannResearch/commit/035293716a82df7806fc46fc8fed6a6e56b658c6) | Actual dyadic zero-free rectangles |

The last commit above is the recovery base. No prior research source was removed.

## New exact identity

Modules:
- `Analysis/ComplexLittlewoodZeros.lean`
- `Analysis/ConreyBaluyotLittlewood.lean`
- `Analysis/ConreyBaluyotDyadicLittlewood.lean`

Let F = zeta M, with M the actual nonstandard mollifier at fixed parameters.
On a positive-height rectangle [a,b] + i[H,T] with zero-free product border,
Lean constructs its finite product-zero set Z and compatible continuous
complex logarithm lifts B and U on the bottom and top. Write

$$
\begin{aligned}
\mathcal L={}&\int_H^T\log|F(a+it)|\,dt
-\int_H^T\log|F(b+it)|\,dt\\
&+\int_a^b\operatorname{Im}U(x)\,dx
-\int_a^b\operatorname{Im}B(x)\,dx,\\
Z_\zeta={}&\sum_{\rho\in Z}\operatorname{ord}_\rho(\zeta)(\operatorname{Re}\rho-a),\\
Z_M={}&\sum_{\rho\in Z}\operatorname{ord}_\rho(M)(\operatorname{Re}\rho-a).
\end{aligned}
$$

The checked identity is exactly `L = 2*pi*(Z_zeta + Z_M)`, with `Z_M >= 0`.
For every alpha > a, the same lifts satisfy

$$
\sum_{\substack{\rho\in Z\\\operatorname{Re}\rho\geq\alpha}}
\operatorname{ord}_\rho(\zeta)
\leq \frac{\mathcal L/(2\pi)-Z_M}{\alpha-a}.
$$

All zeta zeros in the rectangle are product zeros, and a nonzero analytic
function value has zero analytic order. Thus the sum retains the actual
zeta-zero multiplicities, including shared zeros. This correction improves
the earlier discarded-mollifier bound whenever Z_M is positive.

## Exact declarations

1. `Complex.exists_logRectangleBoundary_eq_weighted_zeros`.
2. `RiemannResearch.Analysis.ConreyBaluyot.exists_mollifiedZeta_littlewood_identity_with_remainder`.
3. `RiemannResearch.Analysis.ConreyBaluyot.exists_mollifiedZeta_littlewood_count_bound`.
4. `RiemannResearch.Analysis.ConreyBaluyot.exists_uniform_dyadic_littlewood_identity`.

The last theorem constructs both border and lifts: for epsilon >= 0 and
theta > 0 it gives uniform eta, b and H, and for large T and
1/2 + 1/log(T^theta) <= sigma <= 1/2 + eta, the exact identity on rectangles
with heights arbitrarily close to T and 2T. The mollifier length remains
T^theta at both edges.

## Verification and retained workspace

Workspace: `ws_OqwfYAAM5jgtGfmsdC7jF1YBtJxA6f09`.
Project root:
`/home/cri_2025/lean-agent-workspaces/ws_OqwfYAAM5jgtGfmsdC7jF1YBtJxA6f09/RiemannResearch`.

The saved exact-identity/count module passed focused Bazel/BuildBuddy job
`job_FTE5_s1YqJAntqyq9KEG8e0BqupqBWcS` (67.085 seconds of server verification):
[focused build](https://app.buildbuddy.io/invocation/6b6d2eb6-e3cd-4c4f-977b-6a8908a363c3).

The four new declarations also passed a Bazel axiom-guard check:
`job_1jmGNWXJwmHgDOxYp1QR01dQ8P2T2Yvo`, 36.728 seconds of server
verification, [build evidence](https://app.buildbuddy.io/invocation/cded10c2-fb6e-4e90-b9e5-02ce7a7d2261).
Each guard admits exactly `propext`, `Classical.choice`, and `Quot.sound`.
This does not remove the explicit hypotheses in the theorem types.

Final publication must pass the managed full-project checkpoint
`//:RiemannResearch`; the commit containing this note identifies the
published source. No direct-push bypass is authorized by this note.

## Next critical check

The supplied horizontal O(log T) bounds normalize each phase independently
at b. The lifts in the Littlewood identity instead match along the rectangle's
right side. Those conditions must be reconciled before using the normalized
phase bounds in L. Do not silently discard a multiple of 2*pi times the
horizontal width.

A concrete route is to keep the right side on the established positive-real
anchor line, use its continuous principal logarithm, construct both
horizontal lifts from its endpoint values, and prove their identification
with the normalized phases. The repository already contains
`Complex.exists_logLift_at_right` and differentiable affine log-lift
construction in `ComplexIntegralLogLift.lean`, which may support this step.

After branch compatibility, bound the vertical terms and complete the
necessary limiting boundary argument. The actual mollified second moment,
complete and multilinear Kloosterman estimates, and unconditional density
provider remain open. None of the recovered or new results proves RH.

## Publication integration recovery

The first checkpoint retained local commit
`412625329bb4167686d4e01fba56a823e7a67fcf` after validation, but publication
integration conflicted with newer main commit
`928d4bb84010012b47ba1e75eef7ab9446da4fb2` in the root imports and catalog.
The original workspace and commit were preserved.

The final integration workspace is `ws_lzLF4hiCiyQmu7R7jEWw2e6gFfOXxu-2`,
root
`/home/cri_2025/lean-agent-workspaces/ws_lzLF4hiCiyQmu7R7jEWw2e6gFfOXxu-2/RiemannResearch`.
It starts from 928d4bb and carries forward the same verified Lean modules,
with imports and catalog additions placed away from the concurrently edited
section. The newer dyadic zeta contour-count theorem is retained. Final
acceptance requires validation of this combined source before publication.

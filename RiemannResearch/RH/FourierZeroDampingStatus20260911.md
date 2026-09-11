# Fourier zero-damping continuation: verified scope

September 11, 2026. Continuation of `FourierSignedBridgeVerification20260911(2).md`.

## Result

This continuation adds **27 public theorems across five modules**. The principal new unconditional estimates are:

1. The actual normalization tends to one as positive damping vanishes.
2. Every fixed nonzero signed zeta factor, complete Fourier multiplier, actual Fourier term, finite frequency packet, and finite boundary/frequency energy tends to zero.
3. For each fixed boundary coordinate, the actual tent coefficients admit a summable half-order frequency moment.

The infinite coordinate limits are **conditional** on an explicitly stated uniform frequency-growth bound. The exact signed frequency-tail and boundary-energy criteria are verified reformulations, not proofs of the required tail estimates.

**Neither original uniform-energy target, the required physical/legal recovery, nor RH is proved.**

## 1. Unconditional fixed-frequency cancellation

Retain the actual quantities from the previous bridge:
\[
\omega_h=\frac{2\pi h}{\log 2},\qquad q_\varepsilon=3^{-\varepsilon},
\qquad z_h=e^{i\omega_h\log3},
\]
\[
A_\varepsilon(h)=
N_\varepsilon\frac{\zeta(1-i\omega_h)}
{\zeta(1+\varepsilon-i\omega_h)}-1,\qquad
M_\varepsilon(h)=A_\varepsilon(h)\frac{1-z_h}{1-q_\varepsilon z_h},
\]
and \(f_{\varepsilon,i}(h)=c_i(h)M_\varepsilon(h)\).

Lean proves, as \(\varepsilon\to0^+\),
\[
N_\varepsilon\to1,\qquad
A_\varepsilon(h)\to0,\qquad
M_\varepsilon(h)\to0,\qquad
f_{\varepsilon,i}(h)\to0
\quad(h\ne0).
\]

The normalization proof uses the existing elementary bounds
\(1-\varepsilon\log3\le N_\varepsilon\le1+\varepsilon\).
The zeta proof uses Mathlib's unconditional nonvanishing on real part one and continuity away from the pole. For nonzero \(h\), \(1-i\omega_h\ne1\).

The complete Abel factor remains intact:
\[
|M_\varepsilon(h)|\le 2|A_\varepsilon(h)|.
\]
This avoids needing to divide by \(1-z_h\) at zero damping or to introduce a Diophantine nonresonance hypothesis.

For any fixed finite frequency set \(t\) and boundary set \(s\),
\[
\sum_{h\in t}f_{\varepsilon,i}(h)\to0,\qquad
\sum_{i\in s}\frac14
\left|\sum_{h\in t}f_{\varepsilon,i}(h)\right|^2\to0.
\]
All cross terms inside each squared modulus remain present. The cutoffs are fixed before taking the damping limit.

Main providers: `dyadicRegularizationNormalization_tendsto_one`,
`dyadicSignedZetaRatio_tendsto_zero`,
`dyadicSignedFourierMultiplier_tendsto_zero`,
`dyadicSignedFourierTerm_tendsto_zero`, and
`dyadicSignedFourierFiniteEnergy_tendsto_zero`.

## 2. An unconditional frequency moment and a conditional coordinate limit

For every fixed \(i\), Lean proves
\[
\boxed{\sum_{h\in\mathbb Z}|c_i(h)|\,|h|^{1/2}<\infty.}
\]
This follows from the existing actual inverse-square coefficient estimate and the convergent integer \(3/2\)-series. The estimate also holds on the nonzero-frequency subtype. Its constant depends on \(i\), so it supplies no summable bound over all boundary coordinates.

The new open specification is
\[
\boxed{\exists B\ge0\quad
|M_\varepsilon(h)|\le B|h|^{1/2}
\quad(0<\varepsilon\le1/2,\ h\ne0).}
\]
Its Lean name is `DyadicUniformSignedFourierMultiplierSqrtBound`.
**No provider for this specification was proved in this continuation.**

Under precisely that hypothesis, the moment gives an eventually valid summable majorant. Mathlib's dominated convergence theorem for sums then proves
\[
\sum_{h\ne0}f_{\varepsilon,i}(h)\to0.
\]
The previously proved full arithmetic bridge identifies this sum with the **actual**
`dyadicNormalizationBoundaryCoefficient ε i`.
Thus the real actual coordinate tends to zero under the displayed growth hypothesis.

Providers:
`summable_norm_dyadicTentMellinCoefficient_mul_half_rpow`,
`dyadicSignedFourierRow_tendsto_zero_of_sqrt_bound`, and
`dyadicNormalizationBoundaryCoefficient_tendsto_zero_of_sqrt_bound`.

## 3. The exact signed frequency-tail criterion

Define the complete signed tail after a finite packet:
\[
T_{\varepsilon,i,t}
=\sum_{h\ne0}f_{\varepsilon,i}(h)
-\sum_{h\in t}f_{\varepsilon,i}(h).
\]
At positive damping this is exactly the actual arithmetic coordinate minus the finite packet.

Lean proves
\[
\sum_{h\ne0}f_{\varepsilon,i}(h)\to0
\iff
\forall\eta>0\ \exists t\text{ finite},\
|T_{\varepsilon,i,t}|<\eta
\text{ eventually as }\varepsilon\to0^+.
\]
This criterion retains cancellation in the complete complex tail. The finite cutoff may depend on the tolerance, but is chosen before the damping limit. It is weaker than imposing an absolute majorant and is not itself a proof of small tails.

Provider: `dyadicSignedFourierRow_tendsto_zero_iff_signed_tails`.

## 4. Exact boundary-tail decomposition and the remaining energy obstruction

Set
\[
E_\varepsilon(i)=\frac14
\left|\sum_{h\ne0}f_{\varepsilon,i}(h)\right|^2,\qquad
Q_\varepsilon(s)=\sum_{i\notin s}E_\varepsilon(i).
\]
For positive damping, these are genuine summable energies of the actual remainder \(R_\varepsilon\), and Lean proves
\[
\boxed{\|R_\varepsilon\|^2
=\sum_{i\in s}E_\varepsilon(i)+Q_\varepsilon(s).}
\]

Given actual coordinate convergence to zero, Lean proves
\[
\|R_\varepsilon\|^2\to0
\iff
\forall\eta>0\ \exists s\text{ finite},\
Q_\varepsilon(s)<\eta
\text{ eventually}.
\]
The general theorem permits any parameter path with eventually positive damping. A specialization replaces its coordinate-limit hypothesis with the open square-root multiplier bound from Section 2.

A further checked consequence makes possible escape of energy explicit. If the actual coordinates vanish and \(\|R_\varepsilon\|^2\ge c>0\) eventually, then for **every fixed finite boundary set** \(s\),
\[
Q_\varepsilon(s)\ge c/2\quad\text{eventually}.
\]
This is a conditional implication, not a claim that energy escape actually occurs.

Providers:
`dyadicNormalizationRemainder_norm_sq_eq_head_add_signed_tail`,
`dyadicNormalizationRemainder_energy_tendsto_zero_iff_tail_tight`,
`dyadicNormalizationRemainder_energy_tendsto_zero_iff_tail_tight_of_sqrt_bound`, and
`dyadicSignedFourierBoundaryTail_eventually_ge_of_energy_lower`.

Tail tightness together with coordinate decay gives the **stronger zero-energy limit**. It must not be inferred from a uniform energy bound. No boundary or frequency mixed term is discarded.

## 5. Next bounded proof targets

1. **Discharge the uniform frequency-growth provider.** A plausible classical route is horizontal modulus monotonicity of completed \(\xi\) in the zero-free right half-plane, followed by a uniform gamma-ratio estimate. Sondow–Dumitrescu prove the relevant monotonicity statement in [their paper](https://arxiv.org/abs/1005.1104). The proposed application to this multiplier is an inference and remains unformalized here. It would use the unconditional region \(\Re s>1\); assuming zero-freeness for \(\Re s>1/2\) would be circular.
2. **Prove actual boundary-energy control.** Even after the coordinate limits are supplied, their dependence on \(i\) does not establish either original uniform norm bound or asymptotic tightness.
3. **Retain the physical/legal recovery obligation.** The present norm belongs to the existing projected arithmetic remainder. Convergence statements here do not automatically construct full legal two-seed approximants to the constant.

## 6. Modules and verification

| Module | Public theorems | Scope |
| --- | ---: | --- |
| `RH/DyadicFourierZeroDamping` | 7 | Unconditional scalar, mode, packet, and finite-energy limits |
| `RH/DyadicFourierFrequencyDomination` | 6 | Half-order moment; conditional actual coordinate limits and energy criterion |
| `RH/DyadicSignedFrequencyTailCriterion` | 2 | Actual signed-tail identity and exact row-limit criterion |
| `Analysis/NonnegativeSeriesTightness` | 4 | General finite-head/tail convergence and escape implications |
| `RH/DyadicSignedBoundaryTightness` | 8 | Exact actual signed-energy decomposition and conditional tail criteria |

All five modules are exported and the theorem catalog is updated.

Combined source and endpoint audit:
`job_QPckJSj0WfhikKRxXCZ1buAWC9V4LI43`;
**succeeded, verified true, exit 0, 3.340 seconds**.
All 27 theorem sources compiled together. The printed endpoint types retain the stated open hypotheses. All seven audited endpoints depend only on `propext`, `Classical.choice`, and `Quot.sound`.
No placeholder, additional axiom, or unsafe declaration was introduced.
The audit output was untruncated.

Audit source SHA-256:
`75b916a109f0211152414cb48ccb598726fb793dd9f73c0fcd32a4d9c62ce8d2`.

The one transient HTTP 504 was followed by job-list recovery: no corresponding job had been accepted. The later submission completed normally. All verification submissions were serialized.

Workspace token: `ws__eykLs_HJEUiekupiRigb5Ft5hXoDngi`.

Project root:
`/home/cri_2025/lean-agent-workspaces/ws__eykLs_HJEUiekupiRigb5Ft5hXoDngi/RiemannResearch`.

Starting published commit: `794c2a8e8297005269c847862f08f23a78925d27`.
The final affected-module checkpoint and published commit are recorded in the delivered handoff.

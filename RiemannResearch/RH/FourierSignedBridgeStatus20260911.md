# Full signed arithmetic Fourier bridge: Lean continuation

September 11, 2026. Continuation of `FourierResidueBridgeVerification20260911(1).md`.

## Result

**The full `DyadicSignedFourierBridge` is proved for every positive damping.**
This continuation adds **40 public theorems across six new modules**. It also
proves the proposed logarithmic conductor bound and an inverse-cutoff error estimate.

The complete signed energy is now identified unconditionally with the actual
normalization-remainder norm. A bound uniform as damping tends to zero, the
remaining physical/legal recovery, and RH are **not proved**.

## 1. The actual arithmetic bridge

Write
\[
\omega_h=\frac{2\pi h}{\log2},\quad q_\varepsilon=3^{-\varepsilon},\quad
z_h=e^{i\omega_h\log3},\quad
N_\varepsilon=
\operatorname{regularizationZetaSeries}(\varepsilon)
\frac{1-q_\varepsilon}{\log3}.
\]
The normalization is the project's existing real Dirichlet-series normalization.
For every \(\varepsilon>0\) and every boundary coordinate \(i\), Lean proves the genuine `HasSum`
\[
\boxed{
\sum_{h\in\mathbb Z\setminus\{0\}}c_i(h)
\left(
N_\varepsilon\frac{\zeta(1-i\omega_h)}
{\zeta(1+\varepsilon-i\omega_h)}-1
\right)\frac{1-z_h}{1-q_\varepsilon z_h}
=
\operatorname{dyadicNormalizationBoundaryCoefficient}(\varepsilon,i).
}
\]

Provider:
`RiemannResearch.RH.Pareto.dyadicSignedFourierBridge_proved`.

Its exact type is `DyadicSignedFourierBridge`. There is no RH, Mertens,
unproved Fourier-bridge, or uniform-energy premise. The actual boundary
coefficient belongs to `dyadicNormalizationRemainder ε`, by the project's
existing checked identification. This is not a replacement scalar model.

## 2. The decisive cancellation

For the complete residue symbol, including frequency zero,
\[
\boxed{S_{ab}(h)-S_a(h)=\operatorname{phase}_h(a)S_b(h).}
\]
Consequently
\[
|S_{ab}(h)-S_a(h)|=|S_b(h)|.
\]
Providers: `dyadicResidueFourierSymbol_mul_sub` and
`norm_dyadicResidueFourierSymbol_mul_sub`.

The physical identity is the existing exact Hilbert cocycle
\(T_a r_b=r_{ab}-r_a\). Combining it with the fixed-conductor Fourier
expansions supplies the genuine Fourier expansion of every dilated residue.

For the actual arithmetic columns, \(a=n3^j\) and \(b=3\).
After signed subtraction their Fourier size is exactly that of the fixed
residue \(3\), independently of both \(n\) and \(j\).
Thus the actual family's Fourier interchange uses the already absolutely
convergent residue-3 Fourier row and the absolutely summable actual coefficients.
This improves on estimating the two growing conductors separately.

The full proof uses the already established convergence of the **projected**
Hilbert-valued arithmetic family for every positive damping. It does not assert
absolute convergence of an unprojected infinite Hilbert series.

## 3. Exact arithmetic kernel and normalization

The genuine double-index phase series satisfies
\[
\sum_{n\ge1}\sum_{j\ge0}
\frac{\mu(n)}{n^{1+\varepsilon}}q_\varepsilon^j
e^{i\omega_h\log(n3^j)}
=
\frac{\zeta(1+\varepsilon-i\omega_h)^{-1}}
{1-q_\varepsilon z_h}.
\]
This is proved as a product-index `HasSum`, with absolute summability supplied.
Provider: `dyadicRegularizationPhaseKernel_hasSum`.

Mathlib's Möbius Dirichlet inversion in the half-plane of absolute convergence
supplies the arithmetic factor; the unit-circle phase and positive damping supply
the geometric factor. The positive phase sign gives precisely the displayed
negative imaginary shift in the zeta denominator.

At zero frequency, the original real normalization yields exactly
\[
N_\varepsilon
\left(\sum_{n,j}\frac{\mu(n)}{n^{1+\varepsilon}}q_\varepsilon^j\right)
\log3=1.
\]
Provider: `dyadicRegularizationPhaseKernel_zero_normalization`.

The normalized arithmetic family therefore contributes exactly \(c_i(0)\)
at frequency zero. Removing it and using the previously proved comparison
expansion gives the complete signed multiplier, including its subtraction of one
and its full Abel numerator.

The auxiliary nonzero residue-symbol summation is also checked:
\[
\sum_{n\ge1}\frac{\mu(n)}{n^{1+\varepsilon}}S_n(h)
=
\left(\zeta(1+\varepsilon)^{-1}
-\zeta(1+\varepsilon-i\omega_h)^{-1}\right)\zeta(1-i\omega_h).
\]

## 4. The proposed conductor improvement is proved

For every positive integer \(a\), physical cutoff \(K\), and frequency \(h\),
\[
\boxed{|D_a(K,h)|\le5+2\log a+2\log(1+|\omega_h|).}
\]
Provider: `norm_dyadicResidueFourierKernel_le_log_conductor`.

The proof keeps the exact reset reindexing
\[
\sum_{n\le K,\ a\mid n}\frac an=H_{\lfloor K/a\rfloor},
\]
bounds the physical head by \(H_K+H_{\lfloor K/a\rfloor}\), and bounds the
remaining signed modular Abel tail with both terminal corrections included.
A split at \(\lfloor a(1+|\omega_h|)\rfloor\) gives the claimed bound.
The logarithmic order in \(a\) is necessary because the zero-mode limit is \(\log a\).

The limiting symbol obeys the same bound. Furthermore,
\[
\boxed{
|D_a(K,h)-S_a(h)|
\le\frac{a(3+|\omega_h|)}{K+1}.
}
\]
Provider: `norm_dyadicResidueFourierKernel_sub_symbol_le`.
This improves the previous fixed-conductor norm error of order \(K^{-1/2}\)
to order \(K^{-1}\).

The logarithmically weighted Möbius conductor coefficients are absolutely
summable for every \(\varepsilon>0\). The generic conductor/frequency product
summability and the actual damped residue Fourier `HasSum` are proved separately.
They retain signed coefficients and include frequency zero.

## 5. Exact complete energy and the remaining RH boundary

Lean now proves, without a Fourier-bridge hypothesis,
\[
\boxed{
\|\operatorname{dyadicNormalizationRemainder}(\varepsilon)\|^2
=
\sum_{i\ge0}\frac14
\left|\sum_{h\ne0}
\operatorname{dyadicSignedFourierTerm}(\varepsilon,i,h)\right|^2.
}
\]
Provider: `dyadicNormalizationRemainder_norm_sq_eq_signed_fourier`.

Every frequency cross term remains inside the squared modulus.
No diagonal-frequency estimate replaces this complete signed norm.

The two uniform-energy specifications are now unconditionally equivalent:
`dyadicUniformSignedFourierEnergyBound_iff_actual_remainder`.
This proves their equivalence, **not either uniform bound**.

Still open:

- `DyadicUniformSignedFourierEnergyBound`.
- `DyadicNormalizationRemainderUniformEnergyBound`.
- Actual arithmetic coordinate limits as damping vanishes and the necessary
  control of the frequency tails.
- The complementary physical-energy and legal two-seed recovery steps.
- The quantitative Mertens provider and its hyperbola/reciprocal-tail consequences
  on that separate proposed route.
- RH.

The new Fourier bridge does **not** require the Mertens provider.
Fixed-positive-damping absolute bounds are insufficient to pass to zero damping
or to prevent energy from escaping to large boundary indices.

## 6. Next proof targets

The highest-leverage target is a single constant \(C\) controlling every finite
boundary set and all \(0<\varepsilon\le1/2\):
\[
\sum_{i\in s}\frac14
\left|\sum_{h\ne0}\operatorname{dyadicSignedFourierTerm}(\varepsilon,i,h)\right|^2
\le C.
\]
This is now a bound on a proved representation of the actual remainder, rather
than a bound coupled to an unproved Fourier identification.

A smaller bounded target is the actual coordinate limit as damping tends to zero,
with a justified frequency-tail passage. Such coordinate limits alone do not
supply the uniform energy bound. Any approach must preserve the signed zeta ratio,
the Abel numerator, and all frequency and boundary mixed terms.

## 7. Module map

| Module | Public theorems | Role |
| --- | ---: | --- |
| `RH/DyadicResidueConductorBounds` | 7 | Exact reset head, signed tail, logarithmic conductor control, symbol and cutoff error |
| `RH/DyadicDampedConductorFourier` | 6 | Log-weighted actual Möbius summability and justified conductor/Fourier interchange |
| `RH/DyadicResidueFourierCocycle` | 10 | Exact multiplicative cocycle, phase norms, actual dilations and infinite signed packets |
| `RH/DampedMobiusFourierSymbol` | 6 | Möbius Dirichlet inversion and exact complex phase/zeta identification |
| `RH/DyadicRegularizationPhaseKernel` | 6 | Actual double-index kernel, absolute coefficients and exact zero normalization |
| `RH/DyadicArithmeticFourierBridge` | 5 | Actual full bridge, unconditional signed-energy identity and uniform-target equivalence |

All six modules are exported. The analytic-target and comparison module
documentation is updated to identify the bridge as proved. Generic Möbius
Dirichlet providers use the `ArithmeticFunction` namespace.

## 8. Verification and resumption

The combined source and dependency audit succeeded:
`job_pnSeysp7VlLEYOhSOwH_HWrUzSSrYMly`, **verified true, exit 0, 5.509 seconds**.
All 40 new declarations compiled together. The main bridge, arithmetic kernel,
signed-energy identity and other displayed audited endpoints use only
`propext`, `Classical.choice` and `Quot.sound`.
Compact exact-type and endpoint-axiom audit:
`job_4OeJWpAExsB-pyCeSSLE2yGX0XeHqZml`,
**verified true, exit 0, 5.151 seconds**, with untruncated output.
Its printed types confirm no unresolved substantive hypothesis in the bridge.
Audit source SHA-256:
`a70f08c6543add69e33673e2d633fe6e3800690e6cb361b62cb5363714889640`.

No proof placeholder, project-local axiom, or unsafe declaration was introduced.
Mathematical development was parallel; all Lean submissions were serialized.

Workspace token: `ws__eykLs_HJEUiekupiRigb5Ft5hXoDngi`.

Project root:
`/home/cri_2025/lean-agent-workspaces/ws__eykLs_HJEUiekupiRigb5Ft5hXoDngi/RiemannResearch`.

Starting published commit: `1a637b91c0c85c0b635a7ad52b6e383be52a1649`.
The final checkpoint commit and publication result are recorded in the delivered
handoff. Resume this workspace and inspect current status before further changes.

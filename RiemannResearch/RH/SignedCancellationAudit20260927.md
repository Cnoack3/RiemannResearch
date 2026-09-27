# Signed cancellation below the Burnol half endpoint

Base audited: `Cnoack3/RiemannResearch`, commit
`d4e06595e09075250bc2c2c49399dcd0b3cd6767`.

Verification: the combined new Lean source passed the kernel check with
`exit_code = 0`, `verified = true`, and no warnings. Job:
`job_o5Oh4Z0gcdz5tVfm9jrIHVwpFaqbrhuO`.
The six principal dependency reports contain only `propext`,
`Classical.choice`, and `Quot.sound`; no `sorryAx` or domain-specific axiom.
Module-level integration is validated by the publication checkpoint.
The already completed half endpoint is reused, not re-proved.

## 1. What the pointwise obstruction actually says

Write

\[
A_\varepsilon(n)=\sum_{d\le n}\mu(d)d^{-\varepsilon}\lfloor n/d\rfloor,
\qquad c_\varepsilon=\operatorname{Re}\frac1{\zeta(1+\varepsilon)},
\qquad g_\varepsilon(n)=A_\varepsilon(n)-nc_\varepsilon.
\]

For every real fixed logarithmic exponent \(q\), and every
\(\varepsilon<1/2\), the candidate majorant

\[
\sum_{n\ge2}\frac{n^{-2\varepsilon}}{(\log n)^{2q}}
\]

diverges. The exact Pareto-weight calculation is

\[
\frac1{n(n+1)}
 \left(\frac{n^{1-\varepsilon}}{(\log n)^q}\right)^2
=\frac n{n+1}\frac{n^{-2\varepsilon}}{(\log n)^{2q}}.
\]

Thus retaining the exact weight does not remove the obstruction. At
\(\varepsilon=1/2\), the corresponding logarithmic majorant is summable
exactly when \(q>1/2\). These are assertions about a proposed **upper
majorant**; they do not prove divergence of the actual arithmetic energy.

Verified declarations in `Analysis/PowerLogSquareObstruction.lean`:

- `not_summable_power_log_of_lt_one` and
  `not_summable_shifted_power_log_of_lt_one`;
- `not_summable_subcritical_square_majorant`;
- `pareto_power_log_square_eq` and
  `not_summable_subcritical_exact_pareto_majorant`;
- `summable_log_power_majorant_iff` and
  `summable_half_square_log_majorant_iff`.

## 2. Existing cancellation statements and their limits

| Existing module / declaration | Actual content | Missing arithmetic input |
|---|---|---|
| `CanonicalMobiusSignedAverages.signedMobiusAverage_tail_energy` | Exact signed covariance expansion of the complete infinite physical tail. All mixed terms survive. | A cofinal uniform bound in `riemannHypothesis_of_frequently_bounded_signed_covariance` already implies RH. |
| `CanonicalMobiusCovarianceMinimum.covariance_isLeast` and `optimizedAverage_tail_energy` | The signed affine optimizer exists even for singular Gram matrices; its tail energy is inverse capacity. | Finite-stage positive capacity supplies no uniform lower bound for growing heads. |
| `CanonicalMobiusFixedHeadLimit.density_iff_single_windowCapacity_diverges` | Divergence of capacity at even one fixed positive head is equivalent to full legal density. | `riemannHypothesis_of_single_windowGain_divergence` makes the unproved divergence RH-strength. |
| `RawMobiusSignedGramEnergy.rawMobius_norm_sq_eq_diagonal_offDiagonal` | Exact raw energy splits into the logarithmic mean, diagonal, and signed off-diagonal. The diagonal is at most twice the harmonic sum. | `frequently_power_rawMobiusBudget_iff_offDiagonal` transfers power estimates; all-exponent subpower estimates imply RH. |
| `CRTExactSignedEnergy.growing_zeroMean_subpolynomial_iff` | The certified special-function enclosure has the same subpolynomial obligation as the true energy, uniformly in periods. | Increasing enclosure order does not provide growing-conductor cancellation. |
| `CanonicalMobiusWindowCancellation` | Exact finite floor-tail regrouping into differences of Möbius partial sums; explicit fixed-window estimates. | Its limit theorem takes ordinary and reciprocal Möbius cancellation as explicit inputs. Even after their PNT providers, fixed-window control does not bound the complete signed energy. |
| `DampedMobiusOrderedPairing.dampedPhysical_joint_ordered_pairing_tendsto` | Ordered scalar pairings converge along simultaneous cutoff and damping limits. | Summability of the primitive-side majorant and a sublinear boundary limit remain hypotheses. It does not assert Hilbert membership or justify a missing double-series interchange. |
| `DampedMobiusEnergyClosure.pareto_square_summable_of_coordinate_limit` | Finite-head Fatou transfers one common eventual head bound to the coordinate limit. | Coordinate convergence alone does not provide the common bound. |
| `ArithmeticCumulativeEnergy.energyPrefix_signed_identity` | Exact triangular identity with the signed terms `2*f(n)*cumulative(f,n-1)` and the terminal boundary. | The combined signed partial sums still require a bound; replacing cross terms by absolute values loses the useful structure. |
| `DampedMobiusCoefficientEnergy.normalizedSignedCoefficient_weighted_energy` | Unconditional weighted square bound for the arithmetic coefficients, with explicit scalar normalization assumptions. | This controls coefficients, not their cumulative centered prefixes; it is not the missing Pareto energy provider. |

No inspected theorem supplies an unconditional uniform signed-energy bound
at a fixed \(0<\varepsilon<1/2\).

## 3. The new unconditional diagonal estimate

Let

\[
u_{\varepsilon,d}=\frac{\mu(d)}{d^{1+\varepsilon}}
 \operatorname{hilbertResidue}(d),\qquad
F_{\varepsilon,M}=-\sum_{1\le d\le M}u_{\varepsilon,d}.
\]

The actual complete residue norms satisfy, for **every** positive damping,

\[
\|u_{\varepsilon,d}\|^2\le 2d^{-1-2\varepsilon},\qquad
D_\varepsilon:=2\sum_{d\ge1}d^{-1-2\varepsilon}<\infty.
\]

This is the substantive unconditional estimate added by
`DampedMobiusSignedGram`: the diagonal is uniformly bounded throughout
\(\varepsilon>0\), including below one half. It does not say that the
vector series converges: square-summability of its terms alone is insufficient.

The exact finite identity is

\[
\|F_{\varepsilon,M}\|^2
=\sum_{d\le M}\|u_{\varepsilon,d}\|^2
 +\sum_{\substack{d,e\le M\\d\ne e}}
     \langle u_{\varepsilon,d},u_{\varepsilon,e}\rangle.
\]

Verified declarations:

- `dampedMobiusResidue_norm_sq_le`;
- `dampedMobiusDiagonalMajorant_summable` and
  `dampedMobiusResidue_norm_sq_summable`;
- `dampedMobiusGramDiagonal_le`;
- `dampedMobius_partial_norm_sq_eq_signed`;
- `dampedMobius_frequently_bounded_norm_iff_offDiagonal`;
- `arithmeticFloorHilbertPartial_sequence_of_le`.

The last identity, once \(M\ge n\), gives exactly

\[
F_{\varepsilon,M}(n)
=A_\varepsilon(n)-n\sum_{d\le M}\frac{\mu(d)}{d^{1+\varepsilon}}.
\]

The existing scalar Möbius Dirichlet-series theorem therefore gives
coordinate convergence to \(g_\varepsilon\) for every \(\varepsilon>0\).
This uses absolute scalar convergence at \(1+\varepsilon>1\), without
assuming absolute convergence of the Hilbert-valued series.

The unconditional theorem `arithmeticFloorPartial_head_error` also proves,
for any real weights `w`, any center `C`, and `M >= H`,

\[
\sum_{n<H}w_n\left(F_M(n)-[A_w(n)-nC]\right)^2
=\left(C-\sum_{d\le M}\frac{w(d)}d\right)^2
  \sum_{n<H}w_n n^2,
\qquad w_n=\frac1{n(n+1)}.
\]

Thus the entire signed omitted residue tail is combined into a single
density error before it is squared. This is an exact finite-head bridge,
not an estimate obtained by squaring individual omitted terms. It does
not supply a bound uniform over growing heads.

## 4. The exact finite-head signed bridge

For a physical head \(H\), define

\[
K_H(u,v)=\sum_{0\le n<H}\frac{u(n)v(n)}{n(n+1)},
\]

where the repository's positive weight is zero at \(n=0\). Define the
signed distinct-pair sum

\[
O_\varepsilon(H,M)
=\sum_{\substack{d,e\le M\\d\ne e}}K_H(u_{\varepsilon,d},u_{\varepsilon,e}).
\]

Both pair orientations are included. No absolute values are inserted.
The finite-head diagonal is nonnegative and bounded by \(D_\varepsilon\),
independently of both cutoffs. The verified equivalence is

\[
\boxed{
\sum_{n\ge1}\frac{|g_\varepsilon(n)|^2}{n(n+1)}<\infty
\quad\Longleftrightarrow\quad
\exists B\in\mathbb R\;\forall H\;\forall^{\mathrm{eventual}}M,
  O_\varepsilon(H,M)\le B.
}
\]

The eventual threshold may depend on \(H\), but \(B\) may not. The
forward direction uses finite-head convergence and the nonnegative
diagonal: if the limiting energy is \(E\), take \(B=E+1\). The reverse
direction uses the exact signed expansion, the uniform diagonal bound,
and finite-head Fatou. Its energy bound is \(D_\varepsilon+B\).

Verified declarations in `DampedMobiusSignedHeadClosure`:

- `dampedMobius_partial_head_eq_signed`;
- `dampedMobius_density_hasSum`;
- `dampedMobius_partial_coordinate_tendsto` and
  `dampedMobius_partial_head_tendsto`;
- `arithmeticFloorPartial_head_error`;
- `centered_damped_energy_of_signed_head_bound`;
- `centered_damped_energy_iff_signed_head_bound`.

The implication and equivalence are proved without assuming RH. They
isolate the missing estimate; they do not establish that estimate. A
uniform bound on the complete cutoff off-diagonal is a stronger sufficient
condition. It must not be described as equivalent to finite energy of the
coordinate limit without a separate converse argument.

## 5. Fixed damping versus RH strength

For one fixed \(0<\varepsilon_0<1/2\), the boxed signed-head hypothesis is
exactly finite energy at that damping. The Mellin identity forces

\[
\zeta(\rho)=0,\quad \operatorname{Re}\rho>\tfrac12+\varepsilon_0
\quad\Longrightarrow\quad \zeta(\rho-\varepsilon_0)=0.
\]

Common numerator and denominator zeros cannot simply be discarded.
One fixed damping is not proved RH-equivalent by these results; neither
is a strict logical weakness proved. In contrast, finite energy at
arbitrarily small positive dampings is RH-strength, even if the finite
energy constants grow without bound as damping tends to zero.

The verified `BurnolFixedDampingObstruction` makes the converse obstruction
explicit: an off-line zero produces \(\delta>0\) such that every
\(0<\varepsilon<\delta\) fails finite energy, for every real centering.
Declarations:

- `centered_damped_square_summable_zero_propagation`;
- `right_half_zero_eventually_not_centered_damped_square_summable`.

Primary source: J.-F. Burnol, *On an analytic estimate in the theory of the
Riemann zeta function and a theorem of Báez-Duarte*, Section 4, especially
Corollary 4.1 and Theorem 4.2,
<https://arxiv.org/abs/math/0202166>.

The exact unresolved task is consequently to prove one common upper bound
for the **actual signed head off-diagonals** at a chosen fixed sub-half
damping. No inspected result supplies that bound, and no descent below the
completed endpoint is claimed here.

# Published Selberg range and real-order mollifier arithmetic

Updated 14 November 2026. Base repository revision:
`f3380fd6b8e228d87757e1c08ced9eda210b3a05`.

## Result and precise boundary

**The requested unconditional Lean density provider is not completed.**
The published near-critical-line estimate has the full range
`0 < a < 8/7` in

$
N^+(\sigma,T)\le C_a T^{1-a(\sigma-1/2)}\log T,
\qquad 1/2\le\sigma\le1,\quad T\ge T_a.
$

The exponent `8/7` itself is excluded. Neither `C_a` nor `T_a` is
uniform as a approaches the endpoint. This is the strongest published
range located for this uniform, single-logarithm near-line form; fixed-sigma
zero-density estimates are a different comparison.

Primary source: S. A. C. Baluyot, *On the Zeros of Riemann's Zeta-function*
(University of Rochester, 2017), Theorem 1.2.1 and Chapter 3, pp. 93–143:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320 .
The paper's parameter is theta=a/2. The author's CNTA XV statement:
https://maine-quebec.mat.ulaval.ca/CNTA_XV_website/docs/baluyot.pdf .

The conventional strict count and the repository's inclusive count are now
proved equivalent as uniform density statements. The endpoint sigma=1/2
uses the already unconditional Riemann–von Mangoldt upper bound; threshold
copies are not thrown away.

## New proved components

All declarations below are in `RiemannResearch.Analysis`.

| Module | New theorems | Scope |
| --- | ---: | --- |
| `ActualSelbergDensityConventions` | 6 | Strict-to-inclusive bounds, endpoint assembly, uniform equivalence, exact factor-of-two source parameter conversion. These interfaces do not prove a density provider. |
| `ActualConreyBaluyotConsequences` | 5 | General frequency width, every fixed b<8/7, moving-frequency convergence, and fixed-mode convergence for any positive density exponent. The analytic density input remains explicit. |
| `SelbergRealJordanMollifier` | 15 | Unconditional real-order Jordan divisor identity, Euler product, positivity, exact gcd-power energy, nonzero cutoff mass, residual completion and an attained supported optimum. Also defines `realPower` and `realJordan`. |

The full names are:

- `RiemannResearch.Analysis.ActualZeroOrdinate.rightInclusiveCount_le_rightStrictTail_of_lt`
- `RiemannResearch.Analysis.ActualZeroOrdinate.rightInclusiveCount_le_of_continuous_strict_majorant`
- `RiemannResearch.Analysis.ActualZeroOrdinate.rightInclusiveCount_le_of_strict_selberg`
- `RiemannResearch.Analysis.ActualZeroOrdinate.selbergDensityBound_of_strict_and_count`
- `RiemannResearch.Analysis.ActualZeroOrdinate.uniformSelbergDensity_iff_strict`
- `RiemannResearch.Analysis.ActualZeroOrdinate.conreyBaluyotDensity_iff_strict_source`
- `RiemannResearch.Analysis.ActualZeroOrdinate.normalized_ordinate_landau_error_of_density_width`
- `RiemannResearch.Analysis.ActualZeroOrdinate.eventually_ordinate_landau_error_of_uniform_density_width`
- `RiemannResearch.Analysis.ActualZeroOrdinate.ConreyBaluyotDensityHypothesis.frequency_band`
- `RiemannResearch.Analysis.ActualZeroOrdinate.tendsto_ordinate_landau_error_of_moving_density_band`
- `RiemannResearch.Analysis.ActualZeroOrdinate.tendsto_ordinate_landau_error_of_positive_density`
- `RiemannResearch.Analysis.SelbergMollifier.realPower_apply`
- `RiemannResearch.Analysis.SelbergMollifier.realPower_one`
- `RiemannResearch.Analysis.SelbergMollifier.realPower_mul`
- `RiemannResearch.Analysis.SelbergMollifier.realPower_isMultiplicative`
- `RiemannResearch.Analysis.SelbergMollifier.realJordan_one`
- `RiemannResearch.Analysis.SelbergMollifier.sum_realJordan_divisors`
- `RiemannResearch.Analysis.SelbergMollifier.realJordan_moebius_sum`
- `RiemannResearch.Analysis.SelbergMollifier.product_one_sub_eq_moebius_sum`
- `RiemannResearch.Analysis.SelbergMollifier.realJordan_eq_product`
- `RiemannResearch.Analysis.SelbergMollifier.realJordan_pos`
- `RiemannResearch.Analysis.SelbergMollifier.gcd_rpow_energy_eq`
- `RiemannResearch.Analysis.SelbergMollifier.one_le_cutoffMass_realJordan`
- `RiemannResearch.Analysis.SelbergMollifier.cutoffMass_realJordan_pos`
- `RiemannResearch.Analysis.SelbergMollifier.gcd_rpow_cutoff_completion`
- `RiemannResearch.Analysis.SelbergMollifier.exists_realJordan_cutoff_optimizer`

The finite arithmetic follows the optimization in Simonic,
*Explicit zero density estimate for the Riemann zeta-function near the critical line*,
Section 4.1, https://arxiv.org/abs/1910.08274 .
It supplies a genuine missing component of the classical Selberg route,
not the Kloosterman estimates needed for the full Conrey--Baluyot exponent.

The general Euler–Mobius helper adapts the upstream mathlib generalization
of `IsMultiplicative.prodPrimeFactors_one_sub` (dated 2026-09-14) to the
pinned dependency, which only has the squarefree case:
https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/NumberTheory/ArithmeticFunction/Moebius.lean .
The fetched source blob was `5763ab4c4a8e7869cffbeb2c108cdf151647b41e`.
No dependency or toolchain upgrade was made.

## Quantitative improvement available from the published input

For 0 <= b < a, |u| <= b log T, the verified bound is

$
\left\|\frac{Z_T(u)-L_T(u)}{T}\right\|
\le \frac{2C_a}{a^2-b^2}\frac{u^2}{\log T}.
$

Choosing a=(b+8/7)/2 gives every fixed b<8/7 from the published range.
Moving u(T) is allowed if u(T)^2/log T tends to zero and the stated band
condition holds eventually. The fixed-mode result only needs some a>0.
These are conditional on the density estimate, not unconditional FMZ providers.

For every real a>0 and n>=1 the finite arithmetic proves

$
J_a(n)=n^a\prod_{p\mid n}(1-p^{-a})>0,
\qquad \sum_{d\mid n}J_a(d)=n^a.
$

It retains the complete squared residual in the cutoff energy and constructs
coefficients supported on n<=X attaining the reciprocal finite capacity.
The factorial realization includes no additional nonzero coefficients.

## Remaining analytic proof

The Conrey--Baluyot provider is still
`ConreyBaluyotDensityHypothesis`, a proposition, not an axiom.

1. Formalize the actual nonstandard mollifier, its Mellin/Gamma weight bounds,
   and the Estermann functional equation used in Baluyot Chapter 3.
2. Prove the required Weil and Deshouillers–Iwaniec Kloosterman estimates.
3. Prove the uniform twisted/mollified zeta second moment, retaining both
   signed main terms and every remainder, with uniformity in sigma.
4. Complete the direct-mollifier contour/argument estimates, combine the
   near-line estimate with the away-line Ingham input, and sum dyadic heights.
5. Supply that actual analytic theorem to the now-proved strict/inclusive
   interface.

For the shorter classical Selberg route, generalized Jordan reciprocal-mass
asymptotics and the uniform approximate functional equation/twisted second
moment also remain open. A finite Dirichlet-polynomial mean square does not
replace a zeta moment, and a critical-line proportion does not imply this
exponential density estimate.

No step establishes RH. The arithmetic RH-level obligations from the
Mertens, CRT and projection programs are unchanged.

## Verification

- The coherent 15-theorem Jordan candidate passed Bazel/BuildBuddy:
  `job_bSh_JVxr1maAfVSazIsiTqKEuaugAO_O`,
  https://app.buildbuddy.io/invocation/e9d020fe-c6c9-484f-8c14-13c6def80b79 .
- All three persisted modules and all 26 new theorem declarations compiled:
  `job_tG3nuopa_ipN7PRRBzmjAOAtWO-eFVIg`,
  https://app.buildbuddy.io/invocation/fbfa21bf-251a-4dbf-85c2-c2634bfa7b5d .
- Nine exact axiom guards passed, accepting only propext, Classical.choice
  and Quot.sound: `job_r_7bHjDYbBTsWq9uxBa_Bn5fWPjaCyck`,
  https://app.buildbuddy.io/invocation/48d94383-8081-4e2c-9091-f9862dd795e7 .
- The final full-project publication checkpoint is recorded with the published
  commit in the research sites. An axiom audit does not discharge hypotheses
  occurring in a theorem's type.

## Mellin-weight continuation (14 November 2026)

Prepared on base `2a6eda9affacbb01d3bd5d8de280a1d859d1b38d`.
The user approved committing and pushing this continuation on 14 November 2026,
subject to the server publication checkpoint. The density provider remains open.

### Actual construction and completed analytic step

`ConreyBaluyotMellinWeight.lean` defines the integrand in (1.2.7),
the positive-line integral `weightOnLine sigma xi r`, its fixed-line
specialization `weight sigma xi := weightOnLine sigma xi 1`, and the
finite mollifier in (1.2.6), with the exact cutoff
`n in Finset.Icc 1 (floor (y^(1+epsilon)))`.
The intended application has `y>1`, `epsilon>0`, and `y=T^theta`; the thesis convention is used without silently
identifying its epsilon with the slides' epsilon.

For every `sigma>1/2`, `xi>0`, `r>0`, the actual integrand is continuous
and absolutely integrable. With `z=r+it`, the proved pointwise bound is

```text
|Gamma(z+1) * (zeta(2 sigma+z)/zeta(2 sigma)) * zeta(1+z) * xi^z|
  <= Gamma(r+3) * (1+1/r) * xi^r / (1+t^2).
```

Consequently,

```text
|weightOnLine sigma xi r| <= Gamma(r+3) * (1+1/r) * xi^r / 2.
|weight sigma xi| <= 6 * xi.
```

These constants are independent of sigma throughout sigma>1/2.
They are explicit in r; no uniform bound as r approaches zero is asserted.
No density, contour-shifting, or mollified-moment hypothesis occurs in these
theorem types. Sigma=1/2 and r=0 are excluded.

The complete proof uses the Euler Gamma integral, the exact identity
`Gamma(z+3)=(z+2)(z+1)Gamma(z+1)`, an integrable Cauchy-kernel majorant,
absolute convergence of the zeta Dirichlet series, and the integral
`integral (1+t^2)^(-1) dt = pi`.
The normalized zeta comparison is proved, including a nonzero denominator;
it is not assumed as an analytic interface.

| File | Public new theorems | Scope |
| --- | ---: | --- |
| `Analysis/GammaMellinBounds.lean` | 3 | Euler-integral norm bound, exact recurrence, uniform vertical bound |
| `Analysis/ZetaAbsoluteConvergenceBounds.lean` | 5 | Real-series identity, exact absolute mass, lower bound, half-plane comparison, normalized quotient bound |
| `Analysis/ConreyBaluyotMellinWeight.lean` | 6 | Five analytic results above; coefficient-one identity with the explicit hypothesis W(y) != 0 |

The public declarations are:

- `Complex.gamma_norm_le_real_part`
- `Complex.gamma_add_three_eq`
- `Complex.gamma_vertical_cauchy_bound`
- `riemannZeta_real_eq_tsum_norm`
- `norm_riemannZeta_real_eq_tsum_norm`
- `one_le_norm_riemannZeta_real`
- `norm_riemannZeta_le_real_of_re_le`
- `norm_riemannZeta_div_real_le_one`
- `RiemannResearch.Analysis.ConreyBaluyot.norm_mellinIntegrand_le`
- `RiemannResearch.Analysis.ConreyBaluyot.continuous_mellinIntegrand`
- `RiemannResearch.Analysis.ConreyBaluyot.integrable_mellinIntegrand`
- `RiemannResearch.Analysis.ConreyBaluyot.norm_weightOnLine_le`
- `RiemannResearch.Analysis.ConreyBaluyot.mollifierCoefficient_one`
- `RiemannResearch.Analysis.ConreyBaluyot.norm_weight_le`

The five definitions in the last file include the actual mollifier.
The coefficient-one identity does not prove that W(y) is nonzero.

### Comparison with the Jordan arithmetic

The real-order Jordan results optimize a finite gcd-power quadratic form.
They neither identify Baluyot's coefficients with that optimizer nor prove
a zeta moment for those coefficients. The parameter called a in the Jordan
module is an arbitrary positive Jordan order; it is not automatically the
density exponent a=2 theta. The two constructions are therefore kept in
separate modules. The existing Jordan identities and squared residuals
are unchanged.

The existing `ActualZeroOrdinate.conreyBaluyotDensity_iff_strict_source`
in `ActualSelbergDensityConventions.lean` still requires a density
provider for each fixed theta<4/7. The new weight lemmas do not supply it.
The separate Ingham-detector pipeline in
`ActualMollifierSignedBoundaryBudget.lean` retains
`SignedRectangleBudget`: a signed left logarithmic integral plus the
top-minus-bottom argument integrals. No estimate for that budget, or
identification of its `zetaDetector X` with this mollifier, is asserted here.

### Exact remaining targets

This is a proved part of the analytic groundwork for Lemma 3.1.1, not a
formalization of that entire lemma. Still open:

1. Independence of the defining integral from the positive contour.
2. The signed expansion (3.1.3), retaining
   `A(sigma)=Gamma(2-2 sigma) zeta(2-2 sigma)/zeta(2 sigma)`:
   `W(xi)=1+A(sigma) xi^(1-2 sigma)+R(sigma,xi)`,
   with a remainder bound uniform in the prescribed sigma strip.
3. Lemma 3.1.1's uniform positive lower bound for W(y), global boundedness,
   and exponential tail; the current bound `6 xi` proves none of these.
4. Estermann's functional equation, the Weil incomplete Kloosterman bound
   and the Deshouillers--Iwaniec multilinear estimate.
5. The twisted/mollified second moment with both signed main terms and all
   error terms, followed by the contour/argument estimates and dyadic sum.

The published near-line restrictions remain
`1/2 + 1/log y <= sigma <= 1/2 + epsilon0`, with
`0<epsilon0<1/4` suitably small, and `0<theta<4/7`.
The new elementary Mellin bound holds on the larger domain sigma>1/2,
but does not enlarge that density range.

The exponent barrier in the source's second-moment error terms includes
`T^(-1/2+7 delta/2+epsilon) y^(7/8)` and
`T^(-1+7 delta/2+epsilon) y^(7/4)`.
Recovering the published density range requires their full uniform proof.
Going beyond it would require improved analytic error estimates, not just
finite Jordan optimization or the present weight bound.
No endpoint a=8/7 or uniform endpoint constants are claimed.

### Verification of this continuation

- Saved-file Bazel/BuildBuddy check:
  `job_9p0Qjat6Eddpn-F7mn-OvBIUfxzacll8`, successful, 70.021 seconds
  server job elapsed; target `//RiemannResearch/Analysis:ConreyBaluyotMellinWeight`
  and its transitive imports:
  https://app.buildbuddy.io/invocation/c0f45d13-518e-476c-91b8-dea21e0ea590 .
- All 14 public theorem axiom guards passed in
  `job_ZsI3vRTCfiBJHNnsk_asf_PcNLHbTWQM` (29.938 seconds server job elapsed):
  https://app.buildbuddy.io/invocation/cecf885b-e09d-45ed-86c5-7b054c465928 .
  Each guard accepts exactly propext, Classical.choice and Quot.sound.
  This does not discharge the explicit W(y)!=0 hypothesis.
- Standalone full-project Bazel/BuildBuddy build:
  `job_pdSbHlUqoi8ixA0IPghOpHF6aIZ47NoL`, successful, scope `full`,
  target `//:RiemannResearch`, 193.345 seconds server job elapsed:
  https://app.buildbuddy.io/invocation/42d0c84b-a779-48bd-b1b4-c678d7f6719b .
  The saved-file check recorded SHA-256
  `5150a0b9cfa33b1f98325496c4491d45b02b35976074a08793d66d16860d8845`
  for `ConreyBaluyotMellinWeight.lean`; the reviewed copy matches.
- The source and evidence above were reviewed before publication approval.
  The publication checkpoint supplies the final commit and any required
  integrated-source verification record.
- Wolfram confirmed the two-step Gamma identity and the Cauchy-kernel integral.
  Those computations were exploratory; the acceptance evidence is Lean/Bazel.

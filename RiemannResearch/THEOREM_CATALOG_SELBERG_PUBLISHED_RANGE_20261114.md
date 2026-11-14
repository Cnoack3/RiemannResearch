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

### Remaining targets at the first Mellin-weight checkpoint

At that checkpoint this was a proved part of the analytic groundwork for
Lemma 3.1.1, not a formalization of that entire lemma. The following list
records the obligations then open; the next continuation below updates them:

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

## Positive-contour, exponential-tail and residue continuation (14 November 2026)

Prepared on base `57d0785fbea35e5539f0e5f174cde10348c75457`.
The user approved committing and pushing this continuation on 14 November 2026,
subject to the server's source audit and full-project publication checkpoint.

### Exact analytic results and hypotheses

There are 19 new public theorems in four focused modules, with two new
definitions, `mellinKernel` and `secondaryResidueCoefficient`.
The actual weight, cutoff and mollifier definitions are unchanged.

| File in Analysis | Public theorems | Content |
| --- | ---: | --- |
| `VerticalContourShift.lean` | 1 | Rectangle Cauchy theorem plus an inverse-square strip majorant implies equality of absolutely convergent vertical integrals |
| `ConreyBaluyotMellinContour.lean` | 10 | Actual kernel holomorphy, compact-strip bound, positive-contour independence, factorial bounds and reality |
| `ConreyBaluyotMellinDecay.lean` | 3 | Explicit uniform small-argument exponential bound and its tail specialization |
| `ConreyBaluyotMellinResidues.lean` | 5 | The two actual local residues, real secondary coefficient, and rectangle-residue API identities |

The main new statements are:

1. `weightOnLine_eq`: for sigma>1/2, xi>0 and a,b>0,
   `weightOnLine sigma xi a = weightOnLine sigma xi b`.
   Holomorphy, integrability and horizontal decay are proved from the actual
   Gamma/zeta kernel, not left as analytic provider hypotheses.
2. `norm_weight_le_of_posLine`: for sigma>1/2, xi>0 and r>0,
   `norm(weight sigma xi) <= Gamma(r+3) (1+1/r) xi^r / 2`.
   `norm_weight_le_factorial` specializes this to
   `norm(weight sigma xi) <= (n+2)! xi^n` for integers n>=1.
3. `weight_im_eq_zero`: for xi>0, the weight is real.
   The sigma restriction is unnecessary for this conjugation identity.
4. `norm_weight_le_exp`: for sigma>1/2 and 0<xi<=1,
   `norm(weight sigma xi) <= 72 exp(-1/(2 xi))`.
   The constant 72 is absolute and independent of sigma.
   `norm_weight_ratio_le_exp` gives
   `norm(weight sigma (y/h)) <= 72 exp(-h/(2 y))` for h>=y>0.
5. `mellinKernel_residue_zero`: for sigma>1/2 and xi>0,
   the punctured-neighborhood limit of `z * mellinKernel sigma xi z`
   at zero equals 1. The nonzero zeta denominator is proved.
6. `mellinKernel_residue_secondary`: for 1/2<sigma<1 and xi>0,
   the limit of `(z-(1-2 sigma)) * mellinKernel sigma xi z`
   at `1-2 sigma` equals `A(sigma) xi^(1-2 sigma)`, where
   `A(sigma)=Gamma(2-2 sigma) zeta(2-2 sigma)/zeta(2 sigma)`.
   This is a signed complex identity; `secondaryResidueCoefficient_im_eq_zero`
   proves the coefficient is real. No positivity or negativity claim is
   substituted for the coefficient.
7. `residue_mellinKernel_zero` and `residue_mellinKernel_secondary`
   express the same coefficients in the existing rectangle-residue API.

All kernel arguments and powers in the actual residue statements are complex,
with real parameters coerced explicitly. The exact theorem types are in the
named source modules.

The public declarations, with namespace
`RiemannResearch.Analysis.ConreyBaluyot` except for the first, are:

- `Complex.integral_vertical_eq_of_cauchy_bound`
- `mellinKernel_onLine`
- `differentiableAt_mellinKernel`
- `exists_mellinKernel_strip_bound`
- `weightOnLine_eq`
- `norm_weight_le_of_posLine`
- `norm_weight_le_factorial`
- `mellinKernel_conj`
- `conj_mellinIntegrand`
- `conj_weightOnLine`
- `weight_im_eq_zero`
- `norm_weight_le_factorial_all`
- `norm_weight_le_exp`
- `norm_weight_ratio_le_exp`
- `mellinKernel_residue_zero`
- `secondaryResidueCoefficient_im_eq_zero`
- `mellinKernel_residue_secondary`
- `residue_mellinKernel_zero`
- `residue_mellinKernel_secondary`

### Proof and source comparison

The source is Baluyot (2017), Lemma 3.1.1, equations (3.1.3)--(3.1.4),
pp. 94--95, at the primary thesis URL above. The positive-contour argument
uses finite Cauchy rectangles, a compact-strip majorant and convergence of
the two absolutely integrable vertical sides. The exponential estimate
sums the integer-contour factorial bounds against the exponential series;
it does not assume Stirling's formula. This yields the thesis's tail
shape with an explicit constant on the larger domain sigma>1/2, 0<xi<=1.
The residue proofs use Mathlib's proved zeta residue at 1.

Wolfram checks of elementary inverse-Mellin and generating-series identities
were exploratory only. The final exponential argument and both actual
residues are proved in Lean.

### Updated obligation ledger

| ID | Current status | Remaining work |
| --- | --- | --- |
| CB-01 | Proved | None: the actual positive-contour theorem has only numerical domain hypotheses |
| CB-02 | Partly proved | Both local residues are computed; prove the negative-contour identity and its uniform remainder estimate |
| CB-03 | Partly proved | Reality and exponential decay are proved; the uniform positive lower bound for W(y) and global boundedness remain open |
| CB-04 | Open | Estermann continuation and functional equation; justified exchanges |
| CB-05 | Open | Weil incomplete Kloosterman and Deshouillers--Iwaniec bounds |
| CB-06 | Open | Actual uniform mollified zeta moment, both signed main terms and every remainder |
| CB-07 | Open | Full logarithmic/argument, near/away-line and dyadic density assembly |
| CB-08 | Open | A theorem inhabiting `ConreyBaluyotDensityHypothesis` with no unresolved analytic provider |

The next concrete target is
`W(xi)=1+A(sigma) xi^(1-2 sigma)+R(sigma,xi)`, with R the actual
integral on Re z=-3/4, and a bound `|R| <= C xi^(-3/4)` uniform on
the source's narrow sigma strip. Existing proved infrastructure includes
`Zeta23.RvM.riemannZeta_linear_growth` in
`RH/WeilExplicitFormula/RvM/ZetaGrowth.lean` and
`RectangleIntegral'_eq_sumResiduesIn` in
`RH/WeilExplicitFormula/FromPNTPlus/ResidueCalcOnRectangles.lean`.
Still needed are the actual kernel's meromorphy and pole-set bookkeeping,
negative-line absolute convergence, a uniform remainder bound, and the
horizontal limits across the two poles. The newly computed residues alone
do not imply a contour identity.

Neither W(y)!=0 nor the density proposition follows from the results above.
The published target remains each fixed 0<a<8/7; no endpoint a=8/7,
uniform endpoint constant, or RH result is claimed.

### Verification of the new continuation

- The coherent contour/decay/residue candidate passed Bazel/BuildBuddy:
  `job_yFfeJ12v2kl0nAX7bzThJxYB4ac3A7YQ`, 20.44 seconds server elapsed,
  https://app.buildbuddy.io/invocation/76b9865c-7406-4a00-972f-c4c9616bd44b .
- All four saved modules and exact axiom guards for all 19 public theorems
  passed Bazel/BuildBuddy in `job_M8sDDR3Kh2JlGZtAq2i1a8xCzJ7rISOo`,
  19.251 seconds server elapsed:
  https://app.buildbuddy.io/invocation/3412268b-281e-45a1-a31e-fb70526ff5fc .
  Every guard accepts exactly propext, Classical.choice and Quot.sound.
  The audit imports the saved modules, rather than copying their proofs.
- Standalone full-project Bazel/BuildBuddy acceptance succeeded:
  `job_GO89KPezfENscuegyrwBcH1VynzGkz9W`, scope `full`,
  target `//:RiemannResearch`, 190.229 seconds server job elapsed:
  https://app.buildbuddy.io/invocation/2bc2a059-f3e1-48e7-99b4-4b49eb402bf8 .
  No Lean source changed after this acceptance; only this verification
  record and the publication approval were recorded. The publication checkpoint
  supplies the final commit and any required integrated-source validation.

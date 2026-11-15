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

## Negative-contour and normalization closure (14 November 2026)

Development base: f26bc44f85c68c42b36a53eb9418af9fb1f623c1.
This continuation was initially retained for review without publication.
It follows Conrey_Baluyot_Density_Closure_Plan(1).md. Fresh publication approval
was granted after recovery and the integrated checks recorded below.

### Thirty new public theorems

All names below except the Gamma bound are in
`RiemannResearch.Analysis.ConreyBaluyot`.

| Owning Analysis module | New public declarations |
| --- | --- |
| GammaMellinBounds | `Complex.gamma_vertical_quartic_bound` |
| ConreyBaluyotMellinNegativeContour | `differentiableAt_mellinKernel_off_poles`, `norm_mellinIntegrand_negative_le`, `integrable_mellinIntegrand_negative`, `norm_weightOnLine_negative_le` |
| ConreyBaluyotMellinShift | `analyticAt_mellinKernel_off_poles`, `meromorphicAt_mellinKernel`, `hasSimplePolesOn_mellinKernel`, `rectangleIntegral_mellinKernel`, `norm_mellinKernel_strip_tail_le`, `exists_mellinKernel_closed_strip_tail_bound`, `weight_eq_residues_add_negative`, `weight_eq_residues_add_negative_real` |
| ConreyBaluyotMellinNormalization | `tendsto_secondaryResidueCoefficient`, `exists_secondaryResidueCoefficient_bound`, `negativeRemainderConstant_pos`, `norm_weight_sub_one_le`, `weight_re_lower_bound`, `rpow_le_exp_neg_two_of_coupled_strip`, `norm_weight_le_global_of_coefficient_bound`, `exists_uniform_weight_normalization`, `weight_ne_zero_of_re_lower_bound`, `norm_weight_inv_le_of_re_lower_bound`, `exists_uniform_mollifier_coefficient_bounds` |
| ConreyBaluyotMollifierTruncation | `norm_mollifierCoefficient_le_exp`, `mollifier_tail_geometric_bound`, `mollifier_floor_tail_geometric_bound`, `exists_stretched_tail_bound`, `exists_uniform_mollifier_truncation` |
| ConreyBaluyotParameterBudget | `exists_strict_error_budget` |

The one new definition is `negativeRemainderConstant = 1024 Gamma(17/4)`.
The existing two-step Gamma recurrence is generalized from Re(s)>=0
to Re(s)>-1. All five new modules are exported by RiemannResearch.lean,
with the existing Analysis BUILD.bazel. Existing weight, coefficient,
finite cutoff and density definitions are unchanged.

### Exact hypotheses and conclusions

For 1/2<sigma<=3/4 and xi>0, the actual integrand on Re(z)=-3/4
is absolutely integrable, and the signed identity is

`W_sigma(xi) = 1 + A(sigma) xi^(1-2sigma) + R_sigma(xi)`,

where R is the existing weightOnLine at -3/4. Its uniform bound is

`|R_sigma(xi)| <= C_- xi^(-3/4), C_- = 1024 Gamma(17/4)>0`.

No holomorphy, meromorphy, simple-pole, convergence, or horizontal-decay
provider remains in the concrete contour theorem. The proof uses the actual
rectangle residue theorem with both signed residues, then passes to the
absolutely convergent vertical integrals. Both complex- and real-power
versions are provided.

The coefficient A(sigma) tends to -1 as sigma decreases to 1/2.
There exist 0<epsilon0<1/4 and Y0>1 with exp(1/epsilon0)<=Y0 such that:
- for 1/2<sigma<=1/2+epsilon0 and xi>0, |W_sigma(xi)|<=K, where
  K=max(72,3+C_-);
- on y>=Y0 and 1/2+1/log(y)<=sigma<=1/2+epsilon0, Re(W_sigma(y))>=1/4;
- on that coupled strip, W_sigma(y)!=0, |W_sigma(y)^(-1)|<=4,
  b_sigma,y(1)=1, |b_sigma,y(n)|<=4K for n>=1, and
  |b_sigma,y(n)|<=288 exp(-n/(2y)) for n>=y.

Reality was already proved. The coupled restriction and quantifier order
are retained; no positive lower bound for every sigma>1/2 is asserted.

For y<=N+1 and Re(s)>=0, the normalized coefficient tail beginning at
N+1 is absolutely summable and summable, with norm at most
`288 exp(-(N+1)/(2y))/(1-exp(-1/(2y)))`.
The exact floor N=floor(y^(1+epsilon)) is used. For each fixed epsilon>0,
a sufficiently large threshold gives the uniform bound
`864 exp(-y^epsilon/4)` on the coupled strip. The proof controls the
geometric denominator first, then absorbs the factor y via log(y)=o(y^epsilon).
The final uniform truncation theorem has no analytic-provider premise.

For 0<theta<4/7 and eta>0, the proposed choices
g=1-7theta/4, delta=g/28 and epsilon_err=g/16 admit a positive
epsilon0<=min(eta/2,1/8,delta/(8theta)). Lean verifies
E1=-5g/16, E2=-13g/16, 2theta epsilon0<=g/112 and
4theta epsilon0<delta, and the strict comparison with theta(1-2sigma).
This checks parameter algebra only. It does not prove the analytic error
estimates or identify the independent cutoff and error-loss parameters.

### Historical Mellin-stage ledger (CB-04 is advanced below)

| ID | Status | Remaining work |
| --- | --- | --- |
| CB-01 | Previously proved | None |
| CB-02 | Proved in retained changes | Actual signed shift and uniform remainder now discharged |
| CB-03 | Proved in retained changes | Uniform normalization, global/coefficients bounds, absolute convergence and exact-floor/exponential truncation now discharged |
| CB-04 | Open: first unmet stage | Estermann series/Hurwitz bridge, continuation, functional equation and justified exchanges |
| CB-05 | Open | Incomplete and multilinear Kloosterman estimates |
| CB-06 | Open | Actual zeta-mollifier moment, signed main terms and all errors; elementary parameter budget is now proved |
| CB-07 | Open | Signed counting, boundaries, full sigma coverage, away-line input and dyadic assembly |
| CB-08 | Open | Unconditional provider of the exact ConreyBaluyotDensityHypothesis |

The next target at this stage was the actual absolutely convergent double series
D(s,alpha,beta,H/K) for Re(s+alpha)>1 and Re(s+beta)>1, with K>0 and
coprime integers H,K, and its finite Hurwitz-zeta identity (3.1.7):

D = K^(-2s-alpha-beta) sum_{a=1}^K sum_{b=1}^K
exp(2 pi i abH/K) zeta(s+alpha,a/K) zeta(s+beta,b/K).

This was initially a specification. The Estermann continuation below now proves
absolute convergence, residue-class reindexing, meromorphic continuation and
the functional equation. The transformed contour identity remains open.
At this earlier stage, bounded declaration and filename searches had found no
Estermann or Kloosterman implementation in the inspected project.

No `conreyBaluyotDensity` declaration is added. The exact density proposition,
actual multiplicities, single logarithm, full sigma interval and strict
a<8/7 range remain unchanged. No endpoint a=8/7 or RH result is claimed.

### Acceptance evidence

- Saved-module acceptance and exact axiom guards for all 33 public declarations
  (30 new plus three existing Gamma helpers) passed in
  `job_MQVqzorl1o3U1r84p1xK5_fDVmWHY-EV`, backend Bazel, verified=true, exit code 0,
  91.842 seconds server elapsed:
  https://app.buildbuddy.io/invocation/9bac2235-9a89-4be9-9f08-6d3d134355d4 .
  Every guard requires exactly propext, Classical.choice and Quot.sound.
- Standalone full-project validation passed in `job_2Uf28pCVOAMAiw-ppLxrlPcEdXjswWCS`,
  scope `full`, target `//:RiemannResearch`, backend Bazel/BuildBuddy,
  218.573 seconds server elapsed:
  https://app.buildbuddy.io/invocation/14dca3f6-cfd9-4ec6-9dda-040b3c6d5aa6 .
  All saved Lean source and root exports were included. No Lean source
  changed after this acceptance; only the catalog/review evidence was recorded.
- Wolfram checks were exploratory; the acceptance evidence is Lean/Bazel.
  Source scans of the six proof modules found no placeholders, new axioms,
  or unsafe declarations.

During development, published main advanced to
`24c7355cf07d2f756cf7103b01232977c4cc8300`
(Mobius D-lift convergence and unit-ball lift equivalence).
Its inspected diff adds unrelated RH modules and root imports without
editing the Mellin modules. The retained workspace remains based on f26bc44;
the standalone build above does not claim integration of 24c7355.
After fresh publication approval, the server checkpoint must integrate
newer main and validate the integrated full project before any push.

### Recovery on current main

The recovered Lean changes were applied to a separate retained workspace based on
`95b5aeb20ecd8bc18a8fdfc2bae7ce13cf6eef22`. The integrated full-project
Bazel/BuildBuddy build passed in `job_TtAqS8tF81amvy0oV9CqPRgH_dqMEJsP`
(197.217 seconds server elapsed):
https://app.buildbuddy.io/invocation/8781f5db-6b8e-45d1-922d-2bb0714d4f50 .

## Estermann continuation

The recovered negative-contour, normalization and truncation theorems
are the completed inputs for this continuation. Both new Analysis modules
are exported by RiemannResearch.lean.

| Module | Public theorems | Verified scope |
| --- | ---: | --- |
| ConreyBaluyotEstermann | 15 | Actual exponential phase, absolute convergence, product-to-iterated summation, finite Hurwitz-zeta formula, meromorphic continuation, exact shifted residues, diagonal leading coefficient and the reflected functional equation |
| ConreyBaluyotEstermannDampedSeries | 2 | Absolute convergence and iterated summation of the actual damped series for arbitrary complex shifts and Im(w)>0 |

The two exponents in the first module are u and v. Baluyot's notation is
$D(s,\alpha,\beta,H/K)=D_h(s+\alpha,s+\beta)$, with h the class of H.
The underlying series converges absolutely when Re(u)>1 and Re(v)>1.
`estermannSeries_eq_estermann` and `estermann_eq_sum_hurwitzZeta` give
the exact finite Hurwitz-zeta formula (3.1.7). It uses ZMod K with K>0.
The zero class represents the fraction 1 in the Hurwitz sum. The phase
bridge for the integer numerator is `estermannTerm_intCast`.

The meromorphic continuation in s has possible poles at $1-\alpha$
and $1-\beta$. For distinct shifts and a unit h, the left residue is
$K^{-(1-\alpha+\beta)}\zeta(1-\alpha+\beta)$. The right residue
exchanges the shifts. On the diagonal $D_h(u,u)$, the leading
double-pole coefficient at $u=1$ is $1/K$.
The owning declarations include `meromorphic_estermann_shifted`,
`analyticAt_estermann_shifted`, `estermann_shifted_residue_left`,
`estermann_shifted_residue_right`, and `estermann_diagonal_doublePole_limit`.

`estermann_one_sub` proves the exact reflection for h a unit,
with $u,v\notin\{1,0,-1,-2,\ldots\}$.
$$
D_h(1-u,1-v)=2K^{u+v-1}(2\pi)^{-u-v}\Gamma(u)\Gamma(v)
\left[
\cos\left(\frac{\pi(u-v)}2\right)D_{h^{-1}}(u,v)
+\cos\left(\frac{\pi(u+v)}2\right)D_{-h^{-1}}(u,v)
\right].
$$
This is the two-exponent form of the functional equation in the proof of
Baluyot's Lemma 3.1.3. The $h^{-1}$ reindexing uses multiplication by a
unit modulo K. The separate damped series `estermannDampedSeries` is
the $S$ of equation (3.1.6). `summable_norm_estermannDampedTerm`
and `estermannDampedSeries_eq_iterated_tsum` discharge its absolute
convergence and the double-series exchange on the upper half-plane.

Source: S. A. C. Baluyot, *On the Zeros of Riemann's Zeta-function* (2017),
pp. 95–97, equations (3.1.5)–(3.1.7) and the proof of Lemma 3.1.3.
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320

### Complex Mellin representation and local residues

The continuation from base `8c2a2616e1b94d3d3481cb3b9bdbe33be1aa0eaa`
adds **26 public theorems in five modules**, exported from `RiemannResearch.lean`.

| Module under `RiemannResearch/Analysis/` | Public theorems | Established scope |
| --- | ---: | --- |
| `ComplexLaplaceGamma.lean` | 2 | Absolute convergence and the complex Laplace–Gamma identity |
| `ComplexMellinExponential.lean` | 6 | Exact recurrence, quantitative majorants, vertical integrability, exponential inversion |
| `ConreyBaluyotEstermannMellinKernel.lean` | 9 | Exact term norms, common-shift factorization, integral–series exchange and general kernel assembly |
| `ConreyBaluyotEstermannMellin.lean` | 3 | Actual kernel integrability, explicit majorant and unconditional initial Mellin representation |
| `ConreyBaluyotEstermannMellinResidues.lean` | 6 | Three actual local residue limits and their values in the rectangle-residue API |

For every positive modulus K, **every** residue h modulo K, arbitrary complex
shifts alpha and beta, Im(w)>0, and

$$
c>\max\{0,1-\Re\alpha,1-\Re\beta\},\qquad \lambda=-2\pi i w,
$$

`estermannDampedSeries_eq_mellinIntegral` proves the identity of the actual series
and the actual continued function:

$$
S(w,\alpha,\beta,h)=\frac1{2\pi}
\int_{\mathbb R}\Gamma(c+it)\lambda^{-(c+it)}
D_h(c+it+\alpha,c+it+\beta)\,dt.
$$

`integrable_estermannMellinKernel_vertical` separately proves absolute
integrability. The theorem assumes neither an inversion provider nor a
summation-exchange provider. This initial formula does not need a unit h, an
upper bound on c, or strip restrictions on the shifts beyond absolute
convergence of the shifted undamped series. These are improvements in the
scope of the formalized initial step, not an improved zero-density exponent.

The scalar proof first establishes, for Re(a)>0 and Re(lambda)>0,

$$
\int_0^\infty x^{a-1}e^{-\lambda x}\,dx=\lambda^{-a}\Gamma(a).
$$

Dominated differentiation and analytic continuation from positive real lambda
supply this equality. The exact two-step recurrence then gives the explicit bound

$$
|\Gamma(c+it)\lambda^{-c-it}|
\le
\frac{|\lambda|^2(\Re\lambda)^{-c-2}\Gamma(c+2)}{c^2+t^2}.
$$

`gamma_mul_cpow_neg_vertical_bound_uniform` makes the numerator uniform when
Re(lambda)>=delta>0 and |lambda|<=M, replacing it by
M^2 delta^(-c-2) Gamma(c+2). Thus the genuinely complex damping is controlled
without a separate Stirling estimate. All complex powers are principal powers.

The actual kernel is
`estermannMellinKernel h alpha beta lambda s` =
Gamma(s) lambda^(-s) D_h(s+alpha,s+beta).
Its zero residue is D_h(alpha,beta), assuming alpha,beta are not 1 and lambda
is nonzero; h need not be a unit. For a unit h and distinct shifts, the left
residue is

$$
\Gamma(1-\alpha)\lambda^{\alpha-1}
K^{-(1-\alpha+\beta)}\zeta(1-\alpha+\beta),
$$

under Re(alpha)<1 and lambda nonzero. The right residue exchanges alpha and
beta and assumes Re(beta)<1. Both punctured-neighborhood limits and the
repository's `residue` identities are proved. This covers the intended
alpha=2 sigma-1, beta=0 regime for 1/2<sigma<1. It does not yet cover the
source's full shifted range or collisions among the candidate poles.

Source: Baluyot (2017), equation (3.1.8) and the proof of Lemma 3.1.3,
printed pp. 96–97. The source supplies the statements and Mellin strategy;
the kernel bounds and integral exchanges are checked proofs.

### Remaining part of CB-04

The initial complex Mellin representation and its integral–series exchange
are now proved. Still open:

- The global shift to Re(s)=1-c: finite rectangle bookkeeping, horizontal
  limits, and convergence on the shifted line, retaining every signed residue.
- Pole collisions and the full shifted parameter range of Lemma 3.1.3.
- Assembly of that justified shift with the already proved functional equation,
  retaining the inverse residue and both cosine terms.
- The uniform bound of Lemma 3.1.2, |D_h(2 sigma-1,0)| <= 2 K^2.

CB-05 through CB-08 remain open, including the Kloosterman bounds, the uniform
mollified moment, and an unconditional provider of the exact repository
`ConreyBaluyotDensityHypothesis` for 0<a<8/7. RH is not proved by this continuation.

### Acceptance evidence for the complex Mellin continuation

Saved-module compilation and **26 exact axiom guards** succeeded in
`job_mbtPuj6rTltpAVNB2lJtwgFbtXiX8-LT` using Bazel/BuildBuddy
(89.066 seconds server verification time).
The audit imports the five saved modules through the actual Mellin theorem and
residue module. Every public theorem in this continuation accepts exactly
`propext`, `Classical.choice`, and `Quot.sound`.
https://app.buildbuddy.io/invocation/69532c70-d3f7-4bd1-9240-f7c51c8a888a

This is focused saved-module evidence. Publication additionally uses the server
checkpoint's full incremental `//:RiemannResearch` build; its terminal result and
published commit are reported with the checkpoint.

### Acceptance evidence on base 95b5aeb

- Saved-module compilation and 50 axiom guards succeeded in `job_bMuEK1z6OgpoeI6TXuzWfbsN0XEW2csL`
  (39.060 seconds server elapsed).
  The guards cover 30 recovered theorems, three existing Gamma helpers and
  17 new Estermann theorems. Each uses exactly the axioms `propext`,
  `Classical.choice` and `Quot.sound`.
  https://app.buildbuddy.io/invocation/00971277-6c98-42a3-8716-6540860fa6b9
- Full Bazel/BuildBuddy verification of `//:RiemannResearch` succeeded in `job_Ogmxl15-soyhs1Xn0qAdnuEpHoT50Cdm`
  (168.634 seconds server elapsed). It covered both Estermann
  modules and their exports along with the recovered Mellin changes.
  https://app.buildbuddy.io/invocation/7601e8dd-55a4-4665-b885-1dde8451bc4c

## Uniform dyadic assembly beyond one quarter (15 November 2026)

The new modules `Analysis/DyadicPowerLogBound.lean` and
`Analysis/ActualSelbergDyadicAssembly.lean` close the **conditional height-window
assembly**, including the finite initial count and the narrow logarithmic band.
The unconditional Conrey--Baluyot density provider is still **Open**.

The general assembly works for `0 <= a < 2`; this is the validity range of a
conditional implication, not a new published density range. It includes every
requested `1/4 < a < 8/7`. The analytic source excludes the endpoint `8/7`.

### Exact identity and uniform constant

For every nonnegative H and natural n, actual inclusive counts satisfy

```text
N+(sigma, H*2^n)
  = N+(sigma,H)
    + sum_{k<n} N+(sigma; H*2^k < gamma <= H*2^(k+1)).
```

Analytic multiplicities and all boundary conventions remain unchanged.
If every window (T/2,T] is at most
`D*T^(1-a*(sigma-1/2))*log T` for T >= 2H, with the same D,H for every
sigma in [1/2,1], the proof constructs

```text
r = 2^(-(1-a/2)) < 1,
A = N(0,2H) / log H,
K = (A+D)/(1-r).
```

Then K works for every T >= H and every sigma in the whole strip.
The complete finite initial count is absorbed into A, never declared zero.
The dyadic formulation is equivalent to `UniformSelbergDensity a` on this
range, and hence characterizes the complete open Conrey--Baluyot range.

### Near-line and away-line gluing

`uniformSelbergDensity_of_near_excess_and_far_windows` assumes:

1. One near-line weighted-excess bound
   `rightLogExcessWindow (T/2) T alpha <=
     D*T*exp(-(a*log T)*(alpha-1/2))`,
   uniformly for alpha in [1/2,1/2+eta] and sufficiently large T.
2. One away-line actual-window density bound with the same exponent a,
   uniformly for sigma in [1/2+eta,1] and sufficiently large T.

The two providers may have different constants and thresholds.
The proof combines them, handles `(sigma-1/2)*log T <= 1/a` by the
unconditional total-count theorem, and otherwise uses the exact shifted
weighted-excess identity at `alpha=sigma-1/(a*log T)`. The exponent is preserved.

Both providers remain Open. In particular, the actual uniform mollified zeta
second moment, the necessary Kloosterman estimates, and the analytic away-line
input have not been proved by these implications. An axiom guard does not
discharge those local hypotheses. No RH conclusion is asserted.

Source for the final assembly strategy: Baluyot (2017), section 3.6,
equations (3.6.12)--(3.6.13), printed pp. 142--143, at the primary-source URL
already cited above. The dyadic induction and inclusive-count specialization
are formal proofs rather than assumptions imported from that source.

### Declarations

- `RiemannResearch.Analysis.bound_of_dyadic_power_log`
- `RiemannResearch.Analysis.ActualZeroOrdinate.rightInclusiveCount_monotone_height`
- `RiemannResearch.Analysis.ActualZeroOrdinate.rightInclusiveCount_dyadic_exact`
- `RiemannResearch.Analysis.ActualZeroOrdinate.uniformSelbergDensity_of_dyadic_windows`
- `RiemannResearch.Analysis.ActualZeroOrdinate.uniformSelbergDensity_iff_dyadic_windows`
- `RiemannResearch.Analysis.ActualZeroOrdinate.conreyBaluyotDensity_iff_dyadic_windows`
- `RiemannResearch.Analysis.ActualZeroOrdinate.uniformSelbergDensity_of_near_excess_and_far_windows`

### Focused verification

Saved modules and all seven exact axiom guards passed Bazel/BuildBuddy in
`job_kAn8OxeSd8GiCesI8YP5PCieVsJL6lbQ` (38.726 seconds server verification).
Only `propext`, `Classical.choice`, and `Quot.sound` are accepted by the guards.
https://app.buildbuddy.io/invocation/f78582d6-e538-4a7d-8b3e-2914c0aab8f5

Publication additionally requires the full incremental `//:RiemannResearch`
checkpoint. The Compact Orbit Site records that terminal receipt and commit.

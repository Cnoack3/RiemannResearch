# Published Selberg range and real-order mollifier arithmetic

## Outward Gaussian ray rotation (15 November 2026)

The modules `Analysis/GaussianHorizontalShift.lean` and
`Analysis/GaussianRayRotation.lean` establish the exact logarithmic kernel
norm, a uniform Gaussian majorant, absolute ray integrability, the principal
logarithm on the rays, and the positive exponential Jacobian. Cauchy's
rectangle identity is passed to the whole line with both vertical sides
proved to vanish.

For arbitrary real l,u, positive Delta, nonnegative frequency omega,
tau in {1,-1}, and any two angles in [0,pi), the outward ray integrals
`Complex.gaussianRayIntegral l Delta u (tau*omega) (tau*theta)`
are equal. This strengthens the requested sector [0,pi/2] and includes
the oscillatory endpoint theta=0. The corresponding logarithmic-coordinate
integrals are invariant on the full closed half-sector [0,pi].
The negative principal-log cut is explicitly excluded for the ray theorem.

Key declarations:
- `Complex.integral_horizontal_eq_of_gaussian_bound`;
- `Complex.norm_gaussianRayLogKernel`;
- `Complex.norm_gaussianRayLogKernel_le`;
- `Complex.gaussianRayLogKernel_integral_angle_independent`;
- `Complex.gaussianRayIntegrand_exp`;
- `Complex.gaussianRayIntegrand_integrable`;
- `Complex.gaussianRayIntegral_angle_independent`.

This checkpoint proves rotation of the explicitly defined ray integrals.
The exact identification with the existing actual Euler branches, including
omega^(1-2*l), is the next step. Then prove joint series/ray absolute
convergence and the rational-phase Estermann identity. The uniform
long-mollifier moment provider and the independent Ingham provider remain
open formalization obligations. No density or RH conclusion is asserted.

## Gamma–Euler evaluation and exact moment series (15 November 2026)

**Priority 1 of the Gaussian arithmetic continuation is established.**
The new modules are `Analysis/GaussianGammaTransform.lean` and
`Analysis/ConreyBaluyotGaussianEuler.lean`. Product-space absolute
integrability, Euler insertion, Fubini, and the two phases of the actual
Gamma-weighted scalar transform are proved, with no analytic provider
hypothesis.

For arbitrary complex $a,z$, real $c,l,u$, $\Delta>0$, and
$\operatorname{Re}a+c>0$, the general result is
$$
\int_{\mathbb R} e^{(c+it-l-iu)^2/\Delta^2}
 \Gamma(a+c+it)e^{(c+it)z}\,dt
=\Delta\sqrt\pi\int_0^\infty e^{-x}x^{a-1}
 \exp\!\left((l+iu)(z+\log x)
 -\frac{\Delta^2}{4}(z+\log x)^2\right)\,dx.
$$
The Euler integral is absolutely convergent for every complex $a,z$.
The vertical integral is independent of $c$ throughout
$\operatorname{Re}a+c>0$. The key norm identity factors the joint norm
into the real Gamma weight $e^{-x}x^{\operatorname{Re}a+c-1}$ and the
norm of the complex-frequency Gaussian, proving genuine product-space
integrability before applying Fubini.

For the actual arithmetic transform put $a=1-2l$ and
$L_\omega(x)=\log x-\log(2\pi)-\log\omega$. Define
$$
E_v(\omega)=e^{a(-\log(2\pi)+iv)}
 \int_0^\infty e^{-x}x^{a-1}
 \exp\!\left((l+iu)(L_\omega(x)+iv)
 -\frac{\Delta^2}{4}(L_\omega(x)+iv)^2\right)\,dx.
$$
Then, for **every $c>2l-1$**, arbitrary real $l,u$, and
$\Delta,\omega>0$,
$$
J_c(\omega)=\Delta\sqrt\pi
 \bigl(E_{\pi/2}(\omega)+E_{-\pi/2}(\omega)\bigr).
$$
This proves abscissa independence for the actual scalar transform,
with neither $c>1$ nor $c<2$ required. The original arithmetic-series
interchange still uses $c>\max(1,2l)$.

Set $E(\omega)=E_{\pi/2}(\omega)+E_{-\pi/2}(\omega)$ for
positive frequency and $E(0)=0$. With the original finite coefficients
$a_h=\mathrm{mollifierCoefficient}(\sigma,y,h)$ and
$N=\lfloor y^{1+\varepsilon}\rfloor$, define
$$
E_{m,n}=\sum_{1\le h,k\le N}
 \frac{a_h a_k n^{2l-1}}{k^{2l}} E(mnh/k).
$$
The exact normalized actual-moment identity is
$$
\boxed{g_l(u)=\sum_{m,n\ge1}E_{m,n}
 -\frac{2\sqrt\pi}{\Delta}R_1.}
$$
The Lean sum includes zero natural indices with vanishing Euler values.
The paired series is absolutely convergent. Its convergence theorem
allows all fixed real $\sigma,y,\varepsilon,l,u$ and $\Delta>0$.
The actual-moment identity requires only $y,\Delta>0$, $0<l<1$;
$\sigma,\varepsilon,u$ are arbitrary real parameters. No abscissa
appears in this final theorem.

| Declaration | Established content |
| --- | --- |
| `Complex.gaussianGammaEulerKernel_integrable` | Joint absolute integrability |
| `Complex.gaussian_gamma_vertical_laplace_integral` | General exact Gamma-weighted transform |
| `Complex.gaussian_gamma_euler_integrable` | Euler convergence for every complex shift and frequency |
| `gaussianArithmeticTransform_eq_euler` | Actual scalar evaluation at the two phases |
| `gaussianArithmeticTransform_abscissa_independent` | Every pair of lines with $c,d>2l-1$ |
| `gaussianArithmeticTransform_eq_eulerValue` | Also the zero-frequency convention when $c>0$ |
| `integral_mollifiedGaussianArithmeticTerm_eq_eulerTerm` | Actual finite coefficients pass into the Euler representation |
| `summable_norm_mollifiedGaussianEulerTerm` | Absolute convergence of the paired outer series |
| `mollifiedGaussianMoment_eq_euler_series` | Complete normalized identity with the signed residue |

**Remaining research obligations.** The next task is to turn these
positive-axis Euler integrals into the oscillatory and rotated-ray
integrals of Baluyot's Lemma 3.1.7 and Section 3.3. Prove the contour
rotations, endpoint/arc limits, principal-log branches, and positive
damping, then identify the actual rational-phase
`estermannDampedSeries` after gcd reduction of $h/k$.
The Euler evaluation does not establish those rotations.

The global signed Estermann Mellin decomposition, complete and
multilinear Kloosterman estimates, cofinal
`UniformGaussianMollifiedMoment` provider, and independent
`ActualZeroOrdinate.InghamDensityBound` remain open formalization
obligations. Fixed-parameter convergence here is not a uniform
growing-height moment bound and does not prove RH.

## Gaussian-to-arithmetic bridge (15 November 2026)

**Established identities.** `Analysis/ConreyBaluyotGaussianArithmetic.lean`
proves `mollifiedGaussianMoment_eq_arithmetic_series` and
`mollifiedGaussianMoment_eq_expanded_arithmetic_series` for the actual
mollifier, with no unresolved moment, summability, or integral-exchange
hypothesis. Let $a_j$ be `mollifierCoefficient sigma y j` and
$N=\lfloor y^{1+\varepsilon}\rfloor$. With $s=c+it$, define
$$
A_{l,\Delta,u}(s)=
 e^{(s-l-iu)^2/\Delta^2}
 2(2\pi)^{-(1-2l+s)}\Gamma(1-2l+s)
 \cos\!\left(\frac{\pi(1-2l+s)}2\right),
\qquad
J_c(\omega)=\int_{\mathbb R}A_{l,\Delta,u}(c+it)\omega^{-c-it}\,dt.
$$
The exact result is
$$
g_l(u)=\frac1{\Delta\sqrt\pi}
\left[
 \sum_{m,n\ge1}\sum_{1\le h,k\le N}
 \frac{a_h a_k n^{2l-1}}{k^{2l}} J_c(mnh/k)
 -2\pi R_1
\right].
$$
The Lean equality is in `Complex`; the left side is the cast of the real
moment. Natural-index sums include zero indices, whose terms are proved to
vanish on `c > 0`. The exact signed pole coefficient `R_1`, floor cutoff,
and normalization are retained.

**Stronger parameter range than the proposed bridge.** The final theorem
requires only `0 < l < 1`, `y > 0`, `Delta > 0`, `1 < c`, and
`2*l < c`. There is no `c < 2` requirement; `sigma`, `epsilon`, and
`u` are arbitrary real numbers, and `sigma` is independent of `l`.
The Gaussian–Gamma kernel itself is integrable as soon as
`0 < 1 - 2*l + c` and `Delta > 0`, without any ordering between `l`
and `c`.

Supporting declarations prove:

- `mollifiedGaussianContourKernel_eq_arithmetic`: actual functional
  equation and the untwisted Estermann product.
- `integrable_mollifiedGaussianArithmeticTerm`: genuine termwise
  integrability.
- `summable_integral_norm_mollifiedGaussianArithmeticTerm` and
  `summable_norm_integral_mollifiedGaussianArithmeticTerm`: the absolute
  convergence needed for Fubini and for the integrated double series.
- `mollifiedGaussianArithmeticTerm_eq_finite_sum_of_re_pos` and
  `integral_mollifiedGaussianArithmeticTerm_eq_finite_sum`: the explicit
  coefficient expansion, including complex-power branches and zero terms.
- `integrable_gaussianArithmeticTransform`: absolute convergence of
  the scalar transform at every positive frequency.

The reusable lemma `estermann_mod_one_eq_zeta_product` is in
`Analysis/ConreyBaluyotEstermann.lean` and holds for all complex arguments,
including continued values. Three previously private bounds in
`ConreyBaluyotGaussianShift.lean` are exported for reuse.

**Next analytic obligations.**

1. Evaluate `gaussianArithmeticTransform` as the two oscillatory
   integrals in Baluyot's Lemma 3.1.7; then justify rotation to the rays
   with arguments plus/minus lambda, `0 < lambda < pi/2`.
2. Identify the resulting rational-phase sums with the existing actual
   `estermannDampedSeries`, preserving its positive-damping condition.
   The modulus-one identification above is not that rotated/damped formula.
3. Prove the global Estermann contour shifts and the signed main/error
   decomposition, then supply the complete and multilinear Kloosterman
   bounds with their full parameter quantifiers.
4. Obtain the cofinal family of `UniformGaussianMollifiedMoment`
   providers. The independent `ActualZeroOrdinate.InghamDensityBound`
   provider also remains open.

The fixed-parameter Gaussian domination proved here is not a uniform
growing-height small-moment estimate. No full density or RH conclusion is
claimed. Source for the expansion strategy:
[Baluyot's thesis](https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320),
Section 3.3, pp. 116–117, between (3.3.6) and (3.3.7).


**Additional exact Gaussian input.** `Analysis/GaussianVerticalLaplace.lean`
proves `Complex.gaussian_vertical_laplace_integrable` and
`Complex.gaussian_vertical_laplace_integral`. For every real `c,l,u`,
every `Delta > 0`, and every complex `z`,

$$
\int_{\mathbb R}
 e^{(c+it-l-iu)^2/\Delta^2} e^{(c+it)z}\,dt
 = \Delta\sqrt\pi\,
   e^{(l+iu)z-\Delta^2z^2/4}.
$$

This strengthens the inner Gaussian calculation to arbitrary complex
frequency and proves independence from `c`. One concrete route toward
obligation 1 is now to insert the Euler integral for Gamma, split the
cosine into two exponentials, and use this theorem on the inner integral.
The joint absolute-integrability/Fubini proof and the rotated-ray
identification remain obligations; the Gaussian identity alone does not
establish the full Gamma-weighted transform.

## Actual Gaussian contour and uniform-density transfer

Baluyot's [thesis](https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320),
Theorem 1.2.1 and Sections 3.2–3.6, proves the estimate unconditionally in
the literature for every fixed `0 < a < 8/7`. The Lean result below is a
conditional research reduction with two analytic hypotheses.

- `Analysis/ConreyBaluyotMomentExcess.lean`
  proves `exists_uniform_dyadic_logExcess_of_prescribed_line_moment`.
  For the actual mollifier of length `T^theta`, a moment at most `T + E`
  on the prescribed line gives
  `rightLogExcessWindow T (2*T) sigma <= E/(4*pi) + B*log T`.
  The threshold and all boundary constants are uniform in sigma and T.
  The inequality permits signed E. The proof chooses outward good heights
  and a zero-free left side below sigma with arbitrarily small added cost.
  It uses the exact Littlewood identity with both signed boundary terms
  and all mollifier-zero multiplicities.
- `Analysis/ActualConreyBaluyotDensity.lean`
  proves `uniformDyadicMollifiedMoment_of_gaussian` with the exact
  logarithmic padding `Delta*log T`, the Gaussian deficit, and the same
  exponent as the source moment. It proves
  `uniformSelbergDensity_of_dyadicMollifiedMoment_and_ingham` and
  `conreyBaluyotDensity_of_cofinal_gaussianMollifiedMoments`.
  For each target exponent a it suffices to supply a Gaussian bound
  for one theta with `a <= 2*theta` and `theta < 4/7`.
  The counting theorem includes multiplicities and finite initial heights.
  `UniformSelbergDensity.all_heights_ge_two` absorbs the initial interval
  into the constant for every `T >= 2` and every `sigma >= 1/2`.
- `Analysis/ConreyBaluyotGaussianShift.lean`
  proves the exact normalized rightward shift
  `mollifiedGaussianMoment_eq_right_shift`, including the source range
  `2*l < c < 2`. In the dt parameterization it subtracts `2*pi` times
  the coefficient at s = 1 from the new vertical integral before
  normalizing. Both horizontal integrals vanish and the shifted integral
  is absolutely convergent. `exists_uniform_mollifiedGaussianPoleCoeff_bound`
  bounds the coefficient by `C*y^2*exp(-(u/Delta)^2)` on the coupled strip
  when `Delta >= 1`.

**Open in Lean.** The uniform upper Gaussian moment still requires the
signed arithmetic decomposition and estimates, including the full
Kloosterman inputs. The away-line Ingham estimate is an independent
unproved Lean provider. The signed contour shift and the normalized
Littlewood boundary work are already proved. The literature theorem
allows a-dependent constants and excludes the endpoint `a = 8/7`.

Updated 14 November 2026. Base repository revision:
`f3380fd6b8e228d87757e1c08ced9eda210b3a05`.

## Unconditional dyadic rectangle count in terms of the contour (15 November 2026)

**ConreyBaluyotDyadicCount.lean** combines the actual zero-free rectangle
construction, its two horizontal phase bounds, and the zeta-zero count bound.
The theorem **exists_uniform_dyadic_zeta_rectangle_count_bound** holds for
fixed epsilon >= 0 and theta > 0, all sufficiently large T, and sigma in the
established coupled strip. It chooses t1 near T and t2 near 2T, and vertical
sides l < alpha < beta < r within [1/2,b], with a zero-free border for one
fixed mollifier of length T^theta. Its finite set Z is exactly the zeta zeros
in the selected closed rectangle, and it proves

  (alpha - l) sum_{rho in Z, Re rho >= alpha} ord_rho(zeta)
    <= Re[(1/(2 pi i)) integral_boundary (s - l) F'(s)/F(s) ds].

Both horizontal normalized phase integrals retain their D log T bound.
An exact seven-declaration axiom guard (BuildBuddy invocation
0a7ef826-72d2-47b3-a1b5-5829eed46c2c) checked the dyadic horizontal theorem,
weighted rectangle identity, zeta weighted-zero and margin bounds, general
zero-free border, dyadic rectangle construction, and this count theorem;
only propext, Classical.choice, and Quot.sound occur.

The count bound retains the actual contour integral; it is not yet an
unconditional numerical zero-density estimate. Conversion to logarithmic
and phase integrals, bounds on vertical sides and boundary limits, the
mollified second moment, Kloosterman inputs, and Ingham remain separate.

## Dyadic zero-free rectangles for one actual mollifier (15 November 2026)

**ConreyBaluyotDyadicRectangle.lean** combines the fixed-mollifier dyadic
good-height result with the zero-free side construction. For each epsilon >= 0
and theta > 0, the theorem
**exists_uniform_dyadic_mollifiedZeta_zero_free_rectangle** chooses uniform
eta, b, D and H. For T >= H and sigma in the established coupled strip, and
for each sufficiently small positive delta, it chooses t1 and t2 arbitrarily
near T and 2T, respectively, and vertical sides l and r in arbitrary prescribed
separated interior intervals.

The actual product with its one fixed mollifier of length T^theta is nonzero
on the entire chosen rectangle border. On each horizontal edge a continuous
phase is normalized at b and all integrals from a in [1/2,b] to b are bounded
in absolute value by D log T. The phases apply to the larger horizontal
segment ending at b, while the selected right side r is strictly less than b.

The boundary-existence part is now unconditional on the recorded strip; the
conversion of the weighted contour integral into logarithmic and phase terms,
the necessary vertical-side estimates and limiting argument, the mollified
moment, Kloosterman bounds and Ingham density provider remain open.

## Zero-free vertical lines and rectangle borders (15 November 2026)

**ConreyBaluyotZeroFreeRectangle.lean** proves that if an analytic function on
a rectangle is nonzero at a point, the real parts of its zeros form a finite
set. Consequently every nonempty open subinterval of the horizontal range
contains a zero-free vertical segment.

If the original rectangle's lower and upper edges are zero-free, then
**exists_zero_free_rectangle_border_between** chooses both vertical sides in
arbitrary prescribed separated interior intervals. The resulting smaller
rectangle has no boundary zeros. This general lemma does not by itself bound
the contour integral, establish the moment, or pass to a limiting boundary.

## Actual zeta-zero count under a mollified rectangle boundary (15 November 2026)

**ConreyBaluyotZetaRectangle.lean** strengthens the product-zero identity.
Under the same explicit zero-free product-boundary condition, the rectangle
has a finite set A of exactly the actual zeta zeros, and their weighted
analytic-multiplicity sum is at most the real part of the normalized weighted
log-derivative contour integral of the mollified product. The proof uses
additivity of analytic orders for the product and proves both orders finite.

For alpha >= Re z, **exists_zeta_rectangle_count_margin_bound** proves

  (alpha - Re z) sum_{rho in A, Re rho >= alpha} ord_rho(zeta)
    <= Re[(1/(2 pi i)) integral_boundary (s - Re z) F'(s)/F(s) ds].

Both sides retain actual analytic multiplicity. A positive margin is needed
to divide by it. The zero-free boundary, the log-modulus/phase form of the
contour integral, boundary limits, and the mollified moment remain separate
obligations; this is not yet the unconditional density estimate.

## Weighted rectangle identity for the actual mollified product (15 November 2026)

**ConreyBaluyotWeightedRectangle.lean** applies the previously proved weighted
argument principle to the actual analytic product F = zeta M. For a rectangle
of positive imaginary part on whose entire border F is nonzero, the theorem
**mollifiedZeta_rectangle_weighted_zero_identity** constructs its finite
zero set Z and proves

  Re[(1/(2 pi i)) integral_boundary (s - Re z) F'(s)/F(s) ds]
    = sum_{rho in Z} ord_rho(F) (Re rho - Re z).

The analytic multiplicity is retained and zeros of the mollifier are included.
The border nonvanishing hypothesis remains explicit. This is the weighted-zero
side of the contour argument: the conversion into log-modulus and continuous
phase integrals, the choice of both vertical boundaries and boundary-limit
passage, and the upper mollified moment remain separate obligations. No
unconditional density theorem is asserted here.

## One mollifier at both dyadic boundaries (15 November 2026)

**ConreyBaluyotDyadicHorizontalArgument.lean** strengthens the preceding
good-height result to every nominal height U in [T,2T], with one fixed actual
mollifier of length T^theta.

For every fixed epsilon >= 0 and theta > 0,
**exists_uniform_mollifiedZeta_dyadic_good_horizontal_argument** chooses
eta, b >= 2, D > 0 and H uniformly. For each T >= H and each sigma in the
coupled strip 1/2 + 1/log(T^theta) <= sigma <= 1/2 + eta, every U in
[T,2T] and every 0 < delta <= 1/4 admit t with |t-U| < delta. On the
segment [1/2,b]+it the actual product F is zero-free and has a continuous
polar phase normalized by phi(b) = arg F(b+it), with

  |integral_alpha^b phi(x) dx| <= D log T

for all alpha in [1/2,b]. In particular the result applies near both T and
2T without changing sigma, epsilon or the mollifier length T^theta.

This is an unconditional Lean proof of the good-height horizontal bound.
The Littlewood zero-count contour identity and its boundary-limit passage
remain open, as do the mollified moment, the complete and multilinear
Kloosterman estimates, and the Ingham density provider.

## Uniform horizontal argument on nearby good heights (15 November 2026)

**ConreyBaluyotGoodHorizontalArgument.lean** assembles the normalized phase
and nearby zero-free heights for one fixed mollifier. The theorem
**exists_uniform_mollifiedZeta_good_horizontal_argument** gives arbitrarily
close good heights and the explicit logarithmic integral bound for the
coupled sigma,y strip.

The stronger specialization
**exists_uniform_mollifiedZeta_power_good_horizontal_argument** fixes any
epsilon >= 0 and theta > 0. It chooses eta, b >= 2, D > 0 and H uniformly.
For every T >= H, every sigma with

  1/2 + 1/log(T^theta) <= sigma <= 1/2 + eta,

and every 0 < delta <= 1/4, there is t with |t-T| < delta such that
F(s) = zeta(s) M_{sigma,T^theta,epsilon}(s) is zero-free on [1/2,b]+it.
A continuous polar phase phi, normalized by phi(b) = arg F(b+it), satisfies

  |integral_alpha^b phi(x) dx| <= D log T

for all alpha in [1/2,b]. The mollifier length T^theta and all its
parameters stay fixed as t approaches T. The horizontal estimate itself
does not require theta < 4/7; the mollified moment does.

This establishes the good-height horizontal input with explicit quantifiers,
but does not pass to the limiting Littlewood boundary or prove the moment,
the complete or multilinear Kloosterman estimates, or Ingham's density
estimate in Lean.

## Nearby zero-free heights for a fixed mollifier (15 November 2026)

**ConreyBaluyotMollifierGoodHeights.lean** proves that an analytic function
nonzero at the center of a suitable compact disk has zero-free horizontal
segments at arbitrarily close heights. Its proof places all relevant zeros in
the finite support of the disk divisor and avoids their finite set of
ordinates.

For each fixed epsilon >= 0,
**exists_uniform_mollifiedZeta_zero_free_heights** chooses eta, Y, b >= 2
uniformly. For y >= Y and sigma in the coupled strip, every L >= b,
T >= L + 1, and 0 < delta <= 1/4 admit t with |t-T| < delta such that
the actual mollified zeta has no zeros on [1/2,L] + it.

The mollifier parameters sigma, y and epsilon are held fixed while t varies.
This statement does not identify a limit with the Littlewood contour
argument or prove the mollified moment, complete or multilinear Kloosterman
estimates, or Ingham's density theorem in Lean.

## Normalized horizontal argument on zero-free segments (15 November 2026)

**ConreyBaluyotHorizontalArgument.lean** constructs a continuous polar phase
for every continuous nonvanishing complex function on a compact real interval.
It uses a continuous logarithm on an open, simply connected interval and
normalizes the phase to the principal argument at the right endpoint.

For each fixed epsilon >= 0, the theorem
**exists_uniform_mollifiedZeta_normalized_horizontal_argument** chooses
uniform eta, Y, b >= 2 and C. Whenever y >= Y, sigma lies in the coupled
strip, T >= b + 1, and the actual mollified zeta F has no zeros on
[1/2,b] + iT, it constructs a continuous phase phi with

  F(x+iT) = |F(x+iT)| exp(i phi(x)),
  phi(b) = arg F(b+iT),
  |phi(x) - phi(b)| <= pi (J(T,y) + 2),
  |phi(x)| <= pi (J(T,y) + 3),

where J(T,y) is the explicit logarithmic count in the following sections.
It also bounds the norm of the horizontal integral from alpha to b by
pi (J(T,y) + 3) |b-alpha| for every alpha in [1/2,b].

The zero-free segment is an explicit hypothesis. The preceding good-heights
module supplies arbitrarily nearby zero-free heights for each fixed mollifier.
Passage through the Littlewood boundary limits remains to be formalized.
The mollified moment, complete and multilinear
Kloosterman estimates, and Ingham provider also remain open in Lean.

## Horizontal phase displacement from the real-zero count (15 November 2026)

**ConreyBaluyotHorizontalPhase.lean** proves a general finite-crossing
principle: if a continuous phase on [A,B] has all cosine zeros covered by a
finite set S, then every phase displacement from B is bounded by
pi (|S| + 2). This controls displacement, not total variation.

**exists_uniform_mollifiedZeta_horizontalPhase_bound** combines the
crossing principle with the actual real-part zero count. For every fixed
epsilon >= 0 it chooses uniform strip parameters eta, Y, b and C. For
admissible y, sigma and T, any continuous phi satisfying the polar
representation

  zeta(x+iT) M(x+iT) = |zeta(x+iT) M(x+iT)| exp(i phi(x))

on [1/2,b] obeys |phi(x) - phi(b)| <= pi (J(T,y) + 2), where J is
the explicit logarithmic real-zero bound in the next section.

The theorem assumes the continuous polar phase rather than constructing it.
The subsequent horizontal-argument module constructs and normalizes a phase
on a zero-free segment, and the good-heights module supplies nearby heights.
The Littlewood boundary-limit passage, mollified second moment, complete and multilinear
Kloosterman estimates, and Ingham's density estimate remain open in Lean.

## Uniform count of horizontal real-part zeros (15 November 2026)

**ConreyBaluyotHorizontalRealZeros.lean** proves that every distinct zero of
a nontrivial analytic function in a closed disk contributes a positive
integer to its divisor. It then bounds the cardinality of a finite set of
such zeros by the divisor sum and applies the Jensen estimate to real-part
zeros on a horizontal segment.

For each fixed epsilon >= 0, the theorem
**exists_uniform_mollifiedZeta_horizontalRealZeros_bound** supplies eta, Y,
b >= 2 and C uniformly. For y >= Y, 1/2 + 1/log y <= sigma <= 1/2 + eta
and T >= b + 1, the set of x in [1/2,b] where

  Re(zeta(x+iT) M_{sigma,y,epsilon}(x+iT)) = 0

is finite. Its cardinality is at most

  log(2 (1 + C (T + b - 1/4) y)) /
    log((b - 1/4) / (b - 1/2)).

This proves the real-part zero-count step, including finiteness, uniformly on
the coupled strip. It does not construct a continuous argument or bound its
variation, control boundary limits, prove the mollified second moment, supply
the complete or multilinear Kloosterman estimates, or prove Ingham's density
estimate.

## Jensen divisor bound for the actual mollified zeta (15 November 2026)

**ConreyBaluyotMollifiedJensen.lean** constructs the holomorphic
symmetrization g_T(z) = (F(z+iT) + conjugate(F(conjugate(z)+iT)))/2,
where F is the actual mollified zeta. On the real axis g_T(x) = Re F(x+iT).

The proved generic Jensen estimate bounds the divisor sum inside an inner disk
from a uniform outer-circle bound and a positive right-hand anchor. The
specialization **exists_uniform_mollifiedZeta_jensen_bound** discharges those
hypotheses unconditionally using the linear growth and right-line lower
bound. For fixed epsilon >= 0 it chooses eta, Y, b, C uniformly in y, sigma,
and T. With r = b - 1/2 and R = b - 1/4, it proves the divisor sum in
the closed disk centered at b of radius r is at most

  log(2 (1 + C (T + R) y)) / log(R / r).

The actual theorem assumes y >= Y, 1/2 + 1/log y <= sigma <= 1/2 + eta,
and T >= b + 1. Its output is the finite Jensen divisor sum, not a formalized
cardinality or argument-variation estimate. The separate horizontal-real-zero
module subsequently proves the cardinality bound. The passage to
the horizontal argument term, including zero-free segment and limiting
conditions, remains open. The mollified moment, complete and multilinear
Kloosterman estimates, and Ingham provider also remain open in Lean.

## Linear uniform mollifier growth (15 November 2026)

**ConreyBaluyotMollifierLinearGrowth.lean** improves the bound below to
|M(s)| <= C y throughout Re(s) >= 0, uniformly on the proved coupled
sigma,y strip and simultaneously for every real cutoff exponent. It combines
the existing global coefficient bound with the exponential tail bound to
obtain one geometric majorant for all positive indices. This majorant sums
to O(y), independent of the truncation length.

**exists_uniform_mollifiedZeta_linear_growth** consequently proves
|zeta(s) M(s)| <= C |Im(s)| y when Re(s) >= 1/4 and |Im(s)| >= 1,
uniformly in the same parameters and every real cutoff exponent. These
pointwise estimates do not prove the horizontal argument bound, mollified
second moment, complete or multilinear Kloosterman estimates, or Ingham's
density estimate in Lean.

## Uniform growth of the actual mollifier (15 November 2026)

**ConreyBaluyotMollifierGrowth.lean** proves, for every fixed epsilon >= 0,
the bound |M(s)| <= C y^(1+epsilon) throughout Re(s) >= 0. The constants
are uniform for the actual coupled sigma,y strip in the coefficient theorem.
The proof bounds the actual finite polynomial, using the established uniform
coefficient bound; it does not assume a mollified-moment estimate.

**exists_uniform_mollifiedZeta_growth** combines this with the existing
unconditional zeta bound to obtain |zeta(s) M(s)| <= C |Im(s)| y^(1+epsilon)
for Re(s) >= 1/4 and |Im(s)| >= 1. This is polynomial growth needed for
boundary arguments; it does not itself supply the horizontal boundary
integral, the second moment, Kloosterman cancellation, or Ingham's estimate.

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

## Away-line reduction to Ingham (15 November 2026)

The actual inclusive zero-count version of Ingham's classical estimate is
recorded as the proposition **InghamDensityBound**. The unconditional
classical bound is stated, with inclusive cutoff and positive heights, in
Chourasiya and Simonič, https://arxiv.org/abs/2507.15184. Its application
here is the away-line step in Baluyot, §3.6, p. 142.

For a fixed away-line width eta > 0 and a < 4/3, let
d = (4/3 - a) eta. The exact exponent identity is

$
\frac{3(1-\sigma)}{2-\sigma}
=1-\frac{2}{2-\sigma}(\sigma-\tfrac12).
$

For sigma in [1/2 + eta, 1], adding d still leaves the Ingham exponent
below or equal to the Selberg exponent 1 - a(sigma - 1/2). The elementary
bound (log T)^4 <= (4/d)^4 T^d for T >= 1 absorbs all four excess
logarithms. The positive dyadic window (T/2, T] is bounded by the positive
global count at the same T, preserving the inclusive cutoff and multiplicity.

The declarations in **ActualSelbergIngham.lean**, namespace
**RiemannResearch.Analysis.ActualZeroOrdinate**, are:

- **ingham_exponent_add_gap_le** proves the uniform exponent comparison.
- **exists_selberg_far_windows_of_ingham** supplies the exact far-window
  input of the existing assembly, with explicit multiplier (4/d)^4.
- **uniformSelbergDensity_of_near_excess_and_ingham** assembles the bound
  from near-line weighted excess and the classical Ingham input.

This is a checked reduction. A Lean proof of **InghamDensityBound** remains
open, as do the actual near-line moment and its Kloosterman estimates.
The mathematical theorem for 0 < a < 8/7 is proved unconditionally in Baluyot,
Theorem 1.2.1 and §3.6. The derived away-line comparison through a < 4/3
does not extend that theorem's near-line exponent range.

## Near-line assembly on Baluyot's truncated strip (15 November 2026)

**ActualSelbergTruncatedNearLine.lean** proves
**uniformSelbergDensity_of_truncated_near_excess_and_ingham** in the
**RiemannResearch.Analysis.ActualZeroOrdinate** namespace. It accepts the
actual weighted excess estimate on the strip

$
1/2 + A / \log T \le \alpha \le 1/2 + \eta
$

at window (T/2, T], with the additional boundary cost E log T from
Baluyot's Lemma 3.2.1. The output is **UniformSelbergDensity a** for
0 < a < 4/3 and a eta < 1, given the explicit near estimate and Ingham
providers. For the source's window (U, 2U] and y = U^theta, the cutoff is
1/log y <= 2/(theta log T) at T = 2U >= 4, so A = 2/theta suffices.

The exact existing shifted-window identity is applied at
alpha = sigma - 1/(a log T). If (sigma - 1/2) log T <= A + 1/a,
unconditional total counting gives the required uniform bound. Otherwise
the shifted alpha lies in the analytic strip. The additional a E (log T)^2
is bounded by (a E / (1 - a eta)) times the target power-log kernel, and the
loss from the shift itself is exactly the factor e. The away-line part uses
**exists_selberg_far_windows_of_ingham**. This matches the one-sided source
moment's usable domain, without requiring an estimate at the critical line.

The actual uniform weighted excess estimate, its moment and Kloosterman
inputs, and a kernel proof of **InghamDensityBound** remain open.

## Finite Fourier completion of the inverse sums (15 November 2026)

**KloostermanCompletion.lean** defines the complete classical sum
S(k,m;q) with phase kx + m/x, using the standard additive character on
ZMod q and retaining only invertible x. Every modulus q > 0 is allowed.

For the weight w that counts residues in an interval of length L starting
at b, **interval_inverseSum_eq_complete** proves the signed identity

$
\sum_{j=0}^{L-1} e_q\bigl(m/(b+j)\bigr)\,1_{(b+j,q)=1}
 = q^{-1} \sum_{k\bmod q} \widehat w(k) S(k,m;q),
$

where the indicator notation on the left means the phase is evaluated only
on units, and the forward transform uses the negative character. There is
no restriction L <= q in the identity: repetitions are counted with their
full multiplicities. **dft_intervalWeight** and
**dft_intervalWeight_mul_complement** keep the translated phase and the
complete geometric numerator, including the zero frequency.
**norm_dft_intervalWeight_le** gives the explicit nonzero-frequency
majorant 2 / |1 - e_q(-k)|.

**norm_interval_inverseSum_le_of_complete** transfers an upper bound B
for every complete sum at fixed (m,q) to the normalized full Fourier mass.
The follow-up below proves a harmonic bound and isolates the zero mode.

## Harmonic Fourier mass for the incomplete sum (15 November 2026)

**KloostermanIntervalBound.lean** proves that for every q > 0, b mod q,
and interval length L, the nonzero Fourier mass is at most q H_(q-1).
It uses the exact unit-circle chord identity, Jordan's sine inequality,
the representatives 1 through q-1, and reciprocal pairing. The proof
includes q = 1 and arbitrarily many complete periods.

For B >= 0 bounding every complete S(k,m;q) at k != 0, Lean verifies

$
\left|\sum_{j<L} e_q(m/(b+j))1_{(b+j,q)=1}
-\frac Lq S(0,m;q)\right|
\le B H_{q-1}\le B(1+\log q).
$

The signed zero-frequency term and all repetitions remain in the exact
identity preceding the bound. The result needs no complete-sum estimate
at k = 0, which is a sharper interface than a uniform bound for all k.
The complete Weil bound, Deshouillers–Iwaniec multilinear estimate,
and the uniform zeta-mollifier moment remain open in Lean.

## Direct mollified-zeta vertical bounds (15 November 2026)

**ConreyBaluyotMollifiedBoundary.lean** uses the actual fixed-parameter
product F(s) = zeta(s) M(s) from Baluyot (1.2.6). The analytic parameter
sigma in the coefficients is separate from the complex integration point.
The mollifier is entire with its exact floor cutoff, and subtraction of
the normalized n = 1 term leaves the original finite tail.

The new theorems **exists_uniform_mollifiedZeta_right_decay** and
**exists_uniform_mollifiedZeta_right_real_lower** prove the normalization
used in (3.2.1). There is one D, independent of the height, y and sigma
on the specified coupled strip, such that for Re s >= 2,

$
|F(s)-1|\le D\,2^{2-\operatorname{Re}s}.
$

A single fixed right line has Re F >= 1/2 on and to its right, uniformly
in the ordinate and parameters. This supplies a nonzero right side for
the Littlewood contour and a positive center value for the horizontal
Jensen argument. Its proof uses the convergent real p=2 majorant, not an
estimate on zeta near the critical line.

**integral_log_mollifiedZeta_le_of_moment** proves the one-sided
left-boundary transfer on any zero-free vertical segment at positive
heights H <= T. An upper uncentered second moment at most T-H+E yields
a logarithmic integral at most E/2. The interval integrability of both
functions follows from analyticity and the domain condition. The
uniform moment estimate, the quantitative horizontal term with
boundary-limit treatment, the full Kloosterman estimates and the
classical Ingham provider remain open in Lean.

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

## Recovered continuation: exact Littlewood identity (15 November 2026)

The inaccessible chat's results were recovered from published main through
`035293716a82df7806fc46fc8fed6a6e56b658c6`. In particular, its proposed
continuous-logarithm improvement was already published in
`f026eb9a57ebcbda4a83d7ab7a0bbcec358dd90c`:
**exists_uniform_mollifiedZeta_normalized_horizontal_argument** constructs
the phase from nonvanishing, and later commits supply nearby good heights
and zero-free dyadic rectangles. These results were preserved.

The new continuation adds:

- **Complex.exists_logRectangleBoundary_eq_weighted_zeros**,
  in namespace `Complex`: the full signed Littlewood boundary equals
  (2 pi) times the weighted analytic zero mass, for compatible logarithm
  lifts of any analytic function with zero-free rectangle border.
- **exists_mollifiedZeta_littlewood_identity_with_remainder**: for the actual
  Baluyot product (F=zeta M), this is exactly
  `L = 2*pi*(Z_zeta + Z_M)`, where each weighted mass sums the analytic
  multiplicity times `Re(rho)-a`. The theorem also proves `Z_M >= 0`.
- **exists_mollifiedZeta_littlewood_count_bound**: the same compatible lifts
  work simultaneously for every `alpha > a`, giving
  `N_Z(alpha) <= (L/(2*pi) - Z_M)/(alpha-a)`.
  Here Z is exactly the product-zero set in the rectangle and N_Z sums zeta's
  analytic multiplicities on its points with `Re(rho) >= alpha`. All zeta
  zeros in the rectangle belong to Z; a nonzero value of zeta has order zero.
  The entire nonnegative mollifier correction is retained.
- **exists_uniform_dyadic_littlewood_identity**: the exact identity on
  rectangles with heights arbitrarily close to T and 2T, with one fixed
  mollifier of length `T^theta`. For each `epsilon >= 0` and `theta > 0`,
  the strip constants and height threshold are uniform. The theorem constructs
  both the zero-free boundary and the compatible lifts.

**Current proof boundary.** The exact compatible-lift Littlewood identity is
now proved, including its dyadic existence specialization. Older checkpoint
paragraphs above that list this conversion as open describe earlier states.
The O(log T) bounds already proved for phases independently normalized at b
do not automatically apply to these compatible lifts. Relating the two,
including any right-edge winding/endpoint correction, remains open.
Vertical quantitative estimates, limiting boundary passages, the actual
mollified moment, complete/multilinear Kloosterman estimates, and the full
density provider remain separate obligations. No proof of RH is claimed.

Verification uses the managed Bazel/BuildBuddy checkpoint for all new modules.
The recovery note
`CONREY_BALUYOT_RECOVERY_20261115.md` records the source history and next check.

The publication integration also preserves the newer dyadic contour-count
commit `928d4bb84010012b47ba1e75eef7ab9446da4fb2`.

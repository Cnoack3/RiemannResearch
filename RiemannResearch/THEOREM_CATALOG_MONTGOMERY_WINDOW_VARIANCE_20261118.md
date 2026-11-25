# Fixed-width Montgomery variance

## Signed prime-probe width averages

For the convention \(2/R\) on initial widths, the averaged prime statistic has
limit \(1+\alpha D_\Lambda\) whenever \(R\to\infty\) and
\(R/(\log T)^2\to\alpha<\infty\). At supercritical widths its ratio to
\(R/(\log T)^2\) tends to \(D_\Lambda\). Both statements are unconditional
arithmetic theorems in [MontgomeryPrimeProbeCesaro](Analysis/MontgomeryPrimeProbeCesaro.lean).

[MontgomerySignedCesaroTrace](Analysis/MontgomerySignedCesaroTrace.lean) preserves
every equal-ordinate pair in the collision mass and keeps the signed smooth drift.
Its fixed positive-rational width-average criterion is equivalent to ordinary
positive-gap PCC. Its compact-width transfer holds uniformly down to zero.
At all growing submacroscopic widths, after subtracting the exact clipping
parabola, the trace–gap difference divided by \(R/\log T\) tends to
\(2(1+\log(2\pi))\). The critical dyadic contrast follows from the
compensated sampled-argument input at both widths.

The [companion proof](RIEMANN_SIGNED_PRIME_PROBE_CESARO_20261125.md) derives the
growing-width actual-zero input from the oriented triangle decomposition and
published argument-function bounds. Those analytic estimates remain external
to the signed Cesàro Lean transfer. Fixed positive-gap PCC remains open.

## Kernel-checked reductions

- `MontgomeryWindowVarianceCriterion.lean` proves
  `positiveGapPCC_of_rationalSineWindowVariance` for the actual list of
  ordinate occurrences with analytic multiplicity. The target is
  `sineWindowEnergy R - R^2`, and `sineWindowEnergy_eq` expresses it
  as the fixed-width sinc-square integral after subtracting the squared mean.
- `positiveGapPCC_of_rationalTriangleWidthAverages` in the same module
  needs convergence to zero of the signed triangle-moment error integrated
  on each fixed interval with positive rational endpoints. Monotonicity
  bounds the triangle moment at a width between its adjacent interval
  averages. Continuity of the sine model recovers its value there.
  Establishing these signed averages for the actual zeros remains open.
- `ActualZeroWindowDiscrepancy.lean` identifies the finite cutoff count
  almost everywhere with `Ncount t (min T (t+h))`, including its analytic
  multiplicities. The count is the clipped discrepancy increment plus
  the exact gamma drift. The signed difference from the full-window
  centered second moment is supported on `(T-h,T]`. The local count
  bounds its absolute value by `h * (A * log(T+3) + |lam|)^2` for
  `0 <= h <= min 1 T`.
- In `MontgomeryWindowFourierVariance.lean`,
  `raw_central_window_test_sub_mean_sq_tendsto_zero` uses the
  `BGSTBPositiveCutoffEstimate` premise to identify the central sinc-square
  test integral with the limiting squared mean.
- `MontgomeryFejerPower.lean` bounds every translated triangular test of
  the ordinate form factor by its centered value. This is a finite
  inequality from the nonnegative pair coefficients.

- `ActualZeroWindowDiscrepancy.lean` gives the uniform microscopic clipping
  rate in `eventually_normalizedWindowClipError_le`, its fixed-width limit
  in `normalizedWindowClipError_tendsto`, and its signed interval limit
  in `integral_normalizedWindowClipError_tendsto`.
- `ActualZeroWindowCrossTerm.lean` bounds the unnormalized mixed increment
  uniformly in height. `MicroscopicGammaDrift.lean` bounds the normalized
  mean-square drift by $C_B/(\log T)^2$.
- `MontgomeryArgumentWindowVariance.lean` retains the finite normalization
  and clipping in `eventually_window_sub_argument_eq` and the two signed
  gamma contributions in `fullArgumentWidthMoment_sub_pure`.
  `integral_triangle_sub_pureArgument_tendsto` identifies the signed
  interval tests asymptotically. `positiveGapPCC_of_pureArgumentHalfWidthContrasts`
  has the single open input `RationalPureArgumentHalfWidthContrasts`.
- `MontgomeryDyadicWidthCriterion.lean` proves the half-width implication
  directly for triangle moments, using finite triangular overlap and dyadic
  telescoping. `MontgomeryDyadicWidthFourier.lean` computes the exact
  multiplier, proves its inverse-cubic bound, and evaluates it at $3/2$.
  Its spectral tail estimate retains the unit-interval mass hypothesis.

## Analytic reduction and open estimate

Write `L = log T`, `lambda = L / (2 pi)`, and `F_T` for the raw
ordinate form factor with Cauchy weight. Let `K_R(alpha) =
R^2 sinc(pi R alpha)^2`. Its Fourier transform is the physical overlap
`(R - |x|)_+`. The whole-line pairing against `F_T` is exactly the
Cauchy-weighted triangle moment. The unweighted moment differs by at most
`(R/lambda)^2 / 4` times the unweighted moment, since only gaps of
magnitude at most `R` enter.

The width-one triangle moment is bounded by Goldston, Lee, Schettler
and Suriajaya, [Propositions 1–2](https://doi.org/10.1112/mtk.70127).
A translated `K_1` test is bounded by that same moment by Fourier
pairing and the cosine bound. Since `K_1 >= 4/pi^2` within half a
unit of its center, the mass of `F_T` on every unit frequency
interval is bounded uniformly in the center and large `T`.
Summing `K_R(alpha) <= 1/(pi alpha)^2` gives an `O(A^-1)` bound
for the tail beyond frequency `A`.

The same tail bound follows directly from the translated frequency
triangle proved in Lean. Choose a fixed radius `w>0` in the range
of the central-peak estimate. The centered triangle test is bounded
by `w^{-1}` times the mass on `[-w,w]`. The translated test bounds
the mass within distance `w/2` of its center, where its triangle
is at least `1/(2w`). A unit interval is covered by finitely many
such intervals with a number depending only on `w`.

For any fixed small `a > 0`, the averaged central-peak estimate
from Theorem 2 of the repository's *Montgomery pair correlation without RH* note (November 18, 2026) gives, under its positive-cutoff estimate,
`int_[−a,a] F_T = 1 + O(a^2) + o_T(1)`. The central contribution
to the `K_R` pairing is therefore `R^2 + O_R(a^2) + o_T(1)` under the stated central-peak input.
Putting these together, the variance error and the signed integral
of `K_R(alpha) * (F_T(alpha) - min(|alpha|,1))` on
`a <= |alpha| <= A` differ by at most
`O_R(a^2 + A^-1) + o_T(1)`.

The fixed-width sine variance at every positive rational width
remains open. It suffices to bound the limsup of the absolute signed
integral by a quantity tending to zero as `a` decreases to zero
and `A` increases to infinity after the height limit.

## Signed argument increments on half-sized width intervals

Let $L_T=\log T/(2\pi)$, $h=r/L_T$ and $D(t)=N(0,t)-\int_0^t\mu(u)\,du$.
Put $G_T(r)=T^{-1}\int_0^T(D(t+h)-D(t))^2\,dt$ and
$V(r)=r-2\int_0^r(r-u)\operatorname{sinc}^2(\pi u)\,du$.
Here $\operatorname{sinc}(x)=\sin(x)/x$ with its continuous value at zero.
The actual count includes analytic multiplicity. The increment agrees with
the continued-argument increment at good heights above one.

For $I=[a,b]$ with positive rational endpoints, write
$A_T(I)=|I|^{-1}\int_I(G_T(r)-V(r))\,dr$.
The remaining analytic obligation is
$A_T(I)-A_T(I/2)\to0$ for every such $I$. A proof would imply ordinary
positive-gap ordinate pair correlation without an RH premise.
The shrinkage inequality $E_T(sr)\le s E_T(r)$ for the actual triangle
($0\le s\le1$) explains why no constant is lost. The first difference
bounds the original interval moment. Telescoping a fixed number of
differences leaves a remainder bounded by a constant times $2^{-n}$,
after which $n$ tends to infinity.

### GLSS comparison

Goldston, Lee, Schettler and Suriajaya, Proposition 2, (2.6), approximate
the uncentered full count second moment by $Tr^2+T G_T(r)$, with error
$O(Th^2 L_T+L_T^2)$. Normalizing makes this $O_B(1/\log T+(\log T)^2/T)$
for $0\le r\le B$. Their (2.7) gives
$G_T(r)=\pi^{-2}\log(2+r)+O(\sqrt{\log(2+r)})$ for positive microscopic
widths. The latter estimate permits an order-one signed error on each
fixed interval. The half-width condition tests the actual bias relative
to $V(r)$. [GLSS, Propositions 1 and 2](https://arxiv.org/html/2503.15449v2)

For the **centered** full count, write
$d(t)=\int_t^{t+h}\mu(u)\,du-r$.
The difference of its normalized second moment and $G_T(r)$ equals
$T^{-1}(2\int_0^T\Delta_hD(t)d(t)\,dt+\int_0^T d(t)^2\,dt)$.
Translation places the difference on the monotone gamma weight and the
two end intervals. The all-height Backlund envelope gives a uniform
$O_B(1)$ bound for the unnormalized signed cross term. Stirling's
gamma estimate gives $T^{-1}\int d^2=O_B((\log T)^{-2})$.
The clipped triangle comparison keeps a separate term
$2r^2(n_T-1)$, with $n_T=N(0,T)/(T L_T)$, and clipping of
$O_B(\log T/T)$. This separates the improved centered comparison from
the first-moment correction in the uncentered GLSS formula.

### Frequencies tested by the half-width condition

Write $K_I(\alpha)=|I|^{-1}\int_I r^2\operatorname{sinc}^2(\pi r\alpha)\,dr$.
For $\alpha\ne0$ the contrast $W_I=K_I-K_{I/2}$ is
$$
W_I(\alpha)=
\frac{2[\sin(\pi b\alpha)-\sin(\pi a\alpha)]
      -[\sin(2\pi b\alpha)-\sin(2\pi a\alpha)]}
     {4\pi^3(b-a)\alpha^3}.
$$
The Fourier multiplier has $W_I(0)=(a^2+ab+b^2)/4$, the difference of
the averaged squared means. At nonzero frequencies
$|W_I(\alpha)|\le3/(2\pi^3(b-a)|\alpha|^3)$. A uniform unit-interval
mass bound gives $O_I(M^{-2})$ for the absolute spectral tail beyond
$M$, compared with $O_I(M^{-1})$ for an individual width average.

The compact-frequency signed pairing still needs arithmetic input. For
example $W_{[1,2]}(3/2)=4/(27\pi^3)$. Adding equal positive masses at
$\pm3/2$ to a model measure preserves its restriction to $[-1,1]$ and
bounded unit-interval mass but changes this test. This example only
concerns the information contained in the spectral estimates. In Lean,
the central test in `MontgomeryWindowFourierVariance.lean` takes
`BGSTBPositiveCutoffEstimate` as a premise.

The moving FMZ estimate `eventually_fejer_ordinate_remainder_le` controls
a linear combination of ordinate sums from signed horizontal prefixes
and an explicit complex Landau remainder in its power band. The squared
increment above contains correlations of pairs at height-dependent
frequencies. A transfer to its signed quadratic statistic is open.
[Ford, Meng and Zaharescu](https://arxiv.org/abs/1511.06814)

## The FMZ projection law with all integer cutoffs

Specialize the frequency sequence in `ZeroOrdinateInfiniteDPP.lean`
to `q(k) = log(k+1)`. Consecutive integer cutoffs restrict a feature to
one unit height interval. On such an interval,
the numbers `exp(i * log(2) * gamma)` for the distinct ordinates are
distinct. The harmonics `j * log(2)` occur at the powers of two.
Real parts of Lagrange interpolation polynomials in these numbers
therefore express the indicator of each equal-ordinate class in the
real feature span.

Every feature is constant on each such class. Since finite linear
combinations of the class indicators are dense in the class-constant
subspace, this is exactly the closed feature space. Its orthogonal
projection has an all-`1/m` block on each class of `m` occurrences and
zero between classes. The DPP selects at most one from each block by
the two-point determinant and has expected count one there by the
diagonal. Countability then gives exactly one selected occurrence
per distinct ordinate almost surely. The sine variance of these
distinct ordinates still requires a spacing estimate.

## Factorial window tests on the pure-prime DPP

In `ZeroDPPFactorialWidthContrast.lean`, the normalized translation integral
of $N(N-1)$ counts ordered pairs of different occurrence labels, including
distinct labels at a common ordinate. The finite-height triangle equals this
factorial moment plus the exact window mean. For width $s=2^{-j}r$, its
signed triangle error integrated over $[a,b]$ equals the factorial error
against $\mathrm{sineWindowEnergy}(s)-s$ plus
$(\mathrm{unfoldedWindowMean}(T,1)-1)\int_a^b 2^{-j}r\,dr$.
The displayed correction tends to zero for every fixed interval and scale.

`positiveGapPCC_of_factorialHalfWidthContrasts` takes the one open input
that the difference of those signed factorial errors at scales $1$ and
$1/2$ tends to zero on every positive rational interval.
`factorialHalfWidthContrasts_iff_prime_sampled` identifies this condition
with the corresponding almost-sure condition for the multiplicity-weighted
translated counts of the pure-prime DPP. The sampling identity holds at
all finite heights and widths on one common full-measure event.

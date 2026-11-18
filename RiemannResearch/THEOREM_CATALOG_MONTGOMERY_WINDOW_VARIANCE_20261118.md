# Fixed-width Montgomery variance

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
in Theorem 2 of *Montgomery pair correlation without RH* (November 18, 2026) gives
`int_[−a,a] F_T = 1 + O(a^2) + o_T(1)`. The central contribution
to the `K_R` pairing is therefore `R^2 + O_R(a^2) + o_T(1)`.
Putting these together, the variance error and the signed integral
of `K_R(alpha) * (F_T(alpha) - min(|alpha|,1))` on
`a <= |alpha| <= A` differ by at most
`O_R(a^2 + A^-1) + o_T(1)`.

The fixed-width sine variance at every positive rational width
remains open. It suffices to bound the limsup of the absolute signed
integral by a quantity tending to zero as `a` decreases to zero
and `A` increases to infinity after the height limit.

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

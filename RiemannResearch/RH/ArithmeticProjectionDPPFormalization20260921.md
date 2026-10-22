# Arithmetic projection DPP draft: Lean coverage and RH tests

Source: `ArithmeticProjectionDPPDraft20260921.md`, archived beside this
file. That source is the full ordinary-mathematics draft of 21 September
2026. Archiving it does not make every assertion in it a Lean theorem.

## Checked construction and tests

The `CoordinateMellin` namespace uses physical coordinate cutoffs of the
completed residue projection. It is distinct from the existing finite
arithmetic-rank `MellinFrequency.kernel` and `mellinLaw`.

- `coordinateFeature_eq_mellin` identifies the explicit cell formula with
  the actual Pareto Mellin integral, including the critical line.
- `intensity_decomposition` and `diagonalDefect_eq_intensity_difference`
  retain the full orthogonal defect and every mixed term. The real and
  imaginary coordinate heads implement complexification of the existing
  real Hilbert space.
- `windowDeficit` is a nonnegative Lebesgue integral in `ENNReal`, with
  reference measure `dt/(2*pi)`. A divergent sequence cannot become zero
  through a totalized real-valued liminf or undefined Bochner integral.
- `windowDeficit_one` is the exact factorization
  `d_1(I) = ofReal(limitingVacancy) * firstModeMass(I)`.
- `first_window_zero_iff_density` proves that, on every positive-measure
  window, `d_1(I) = 0` if and only if the actual residue closure is the whole
  Hilbert space.
- `riemannHypothesis_of_first_window_zero` consequently proves actual
  Mathlib `RiemannHypothesis` from that zero-deficit premise. It has no
  additional analytic provider premise. The premise itself is not proved.
- `windowTest_iff_cofinallySmall` gives an exact epsilon/cofinal formulation
  of the asymptotic `liminf d_M(I) = 0` test.

## Zero-profile lower bound

The finite profile and its infinite-series candidate are explicit sums of
the actual cell transforms. The checked Cauchy argument gives, for a
hypothetical zero `rho` with `Re rho > 1/2`,

\[
\frac{2\Re\rho-1}{2}|F_{\rho,M}(t)|^2\le E_M(t,t).
\]

This is a deliberately weaker lower bound than the sharp normalized
rank-one bound `|F|^2/c_rho` in the manuscript. Its advantage is that it
follows directly from the already checked Mellin distance obstruction in
the real Hilbert realization. No profile-domination provider is needed.

`Analysis.NonnegativeDeficit.integral_le_liminf_of_dominated_profile`
is the general Fatou step. The application `zeroWindowMass_le_liminf`
turns convergence of the explicit profiles into a lower bound for the
actual unscaled deficit. Positivity of the limiting profile mass then
excludes a vanishing liminf.

## Exact status of the asymptotic RH equivalence

`riemannHypothesis_iff_windowTest` is a **conditional research reduction**.
Its unresolved formalization dependencies are visible in its type:

1. **Open formalization:** convergence of the explicit partial zero profiles
   to their series, for every `Re rho > 1/2`.
2. **Open formalization:** positive window mass of that profile on the chosen
   bounded positive-measure window. The manuscript proves this through
   analyticity and nonvanishing; that analytic provider is not yet supplied
   in the project.
3. **Open formalization:** the classical implication from Mathlib RH to
   density of this residue span. The existing project proves density
   implies RH; the converse is not supplied by this addition. It is a
   known mathematical theorem in the Bagchi/Nyman--Beurling framework,
   not a new conjecture.

The first two dependencies are the explicit fields of
`ZeroModeWindowProvider`. They are analytic statements for all points in
the half-plane, not only for zeta zeros. The actual zero hypothesis enters
the independently proved Cauchy domination theorem.

**Open mathematical problem:** prove the unscaled deficit vanishes (or its
cofinal small-value condition) without assuming RH. Neither the criterion
nor a kernel check proves that premise. The equivalent signed-capacity
divergence also remains unproved.

## Scaling results and limits of coverage

`firstCoordinateCorrection_tendsto_zero` proves that removing the first
coordinate contributes a correction tending to zero after division by
`log(M+1)`. `compensated_firstCoordinateCorrection_tendsto` proves that
multiplying it back by `log(M+1)` recovers a nonzero limiting profile.
`same_limit_iff_missing_first` proves equality of any existing leading
kernel limits for the filled comparison and its proper subprojection.
These statements do not assume the arithmetic projection is that comparison
subprojection.

`CoordinateSineLimitTarget` and `CoordinateSecondOrderTarget` record the
precise remaining coordinate-cutoff asymptotics as propositions. They are
formalization targets, not theorems. The full local process/Fredholm
convergence, the smooth covariance remainder estimates, the meromorphic
zero-profile continuation, the higher-order exceptional-center bound, and
the uncut local trace-class obstruction remain ordinary proofs in the
archived manuscript. No Montgomery or Hilbert--Polya identification is
claimed.

## Existing modules reused

The new work builds on `IntegerDPPAllSiteObstruction`,
`IntegerDPPMellinObstruction`, `IntegerDPPClosure`, `IntegerDPPKernel`,
`MellinFrequencyMeasure`, `ParetoBoundedMellinLinearity`, and the existing
Mellin/DPP constructions. The earlier signed Schur, capacity, integer
existence, and class-lifting modules are not duplicated.

Kernel axiom audits must be read together with theorem types: absence of
`sorryAx` or project-local axioms does not discharge a theorem's explicit
analytic or zero-deficit hypotheses.

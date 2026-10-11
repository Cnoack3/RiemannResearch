# Chebyshev handoff: exact arithmetic energy and Lean status

Source: user-provided `V_Zeta_Zeros_Fourier_Chebyshev_Handoff_2026-09-16 (1).md`.
This is a partial formalization of that full handoff, with strengthened finite
energy and endpoint-obstruction results. It does not prove RH.

## Established unconditional results

- `Analysis/SequenceMidpoint.lean`: algebraic midpoint bijection, adjacent
  differences, finite squared telescope and weighted Abel identity, including
  terminal endpoint; harmonic specialization.
- `NumberTheory/PrimePowerTwist.lean`: prime-power support projection; completely
  multiplicative twist convolution endomorphism, polynomial equivariance,
  kernel and injectivity. Infinite convolution exp/log is not supplied.
- `NumberTheory/PrimePowerLocalCoordinates.lean`: inverse local exp/log
  coordinates and twist equivariance through degree three only.
- `RH/ChebyshevMidpoint.lean`: actual Mathlib von Mangoldt and Chebyshev
  specialization. With R_n = psi(n)-n, exactly
  2 sum_{n=1}^N (Lambda(n)-1)(psi_0(n)-n+1/2)/n
  = R_N^2/(N+1) + sum_{n=1}^N R_n^2/[n(n+1)].
- `Analysis/ChebyshevCellEnergy.lean`: actual interval integral, completed
  square, minimizing center b(a)=a(a+1)log((a+1)/a), and
  0 <= d(a)=1-a(a+1)log((a+1)/a)^2 <= 1/(12a^2).
- `RH/ChebyshevParetoEnergy.lean`: actual continuous energy is exactly the
  shifted Pareto energy plus the deterministic correction. The correction
  is <=1/6; I_N <=2 D_N+13/6 and D_N <=2 I_N+2.
- `RH/ChebyshevEnergyCriterion.lean`: analytic continuation of the actual
  convergent Mellin integral as punctured germs; both strict and endpoint
  off-line-zero energy obstructions. In particular
  `offLineZeroDampedEnergyDivergence` discharges the formerly open
  `OffLineZeroDampedEnergyDivergenceTarget` from ChebyshevZeroObstruction.

## Conditional research reduction

`riemannHypothesis_of_all_chebyshev_damping` proves Mathlib's
RiemannHypothesis from the actual integrability conditions
`forall epsilon > 0, ErrorFiniteEnergy (1+epsilon)`.

Open substantive obligation: prove these actual arithmetic energy conditions
without RH. The finite prime-power identities and the nonnegative signed sum
do not provide the required upper bounds. Preserve the R_N^2/(N+1) endpoint.

The complete coefficientwise exp/log isomorphism, actual zero B2 expansion,
RH-to-energy analytic provider and full determinant continuation have not all
been formalized by this task. Their paper statements and assumptions remain
in the companion report. The conditional B2 input is supported by
Akbary--Ng--Shahabi (arXiv:1306.1657), Theorem 1.2 and Corollary 1.15(i).

## Verification evidence

The final seven-module import and ten selected transitive axiom checks passed
Lean server job `job_uK7mcrCfduM7ynT0dmh3asLdW-k8794f`, exit code 0.
Every selected report lists only `propext`, `Classical.choice`, `Quot.sound`.
No placeholders or project-local axioms are introduced. This targeted check
is not a claim of a full repository rebuild. Final acceptance/publication is
through the required server checkpoint.

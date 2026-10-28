# Selberg density formalization: theorem catalog supplement

28 October 2026. See [proof route and remaining obligations](RH/SelbergDensityFormalization20261028.md).

**Status:** the full positive-exponent Selberg density provider is
**Open (intentionally deferred)**. At the user's request, the known analytic
theorem is retained as an explicit hypothesis to save formalization time.
The FMZ theorems keep `UniformSelbergDensity (1 / 4)`, which may be all the
eventual application needs. No new axiom or unconditional density provider
is introduced.

## Analysis/ActualZeroSelbergDensity.lean

- `ConreyBaluyotDensityHypothesis`: the explicit proposition
  `∀ a : ℝ, 0 < a → a < 8 / 7 → UniformSelbergDensity a`, citing Baluyot's
  proof of the theorem announced by Conrey. The endpoint is excluded and
  constants may depend on a.
- `ConreyBaluyotDensityHypothesis.classical`: checked extraction of the
  classical `UniformSelbergDensity (1 / 4)` premise.
- `ConreyBaluyotDensityHypothesis.one`: checked extraction of exponent 1.

The selectors and downstream ordinate deductions are **conditional research
reductions**. The domain-specific density input is Open in Lean and
deliberately deferred, although it is an unconditional theorem in the
literature. The classical consumers are not strengthened to require the
whole range: pass `hDensity.classical` only when the stronger hypothesis
is available. No proof of the density hypothesis itself is claimed.

## Analysis/ActualSelbergDensityAssembly.lean

Established unconditional endpoint and transfer lemmas:

- `selbergDensityBound_mono_exponent`
- `uniformSelbergDensity_mono`
- `uniformSelbergDensity_zero`
- `exists_selberg_form_on_logarithmic_strip`
- `rightInclusiveCount_antitone`
- `selbergDensityBound_of_partial`
- `uniformSelbergDensity_quarter_of_five_sixteenths`
- `selberg_shift_count_exact`
- `densityWindow_le_of_shifted_logExcess`
- `selberg_shift_optimal`

The partial-strip and shifted-log-excess consumers are **conditional research
reductions** when invoked as Selberg estimates: their displayed analytic
source estimates are open. The zero-exponent provider is unconditional but
gives no sigma-dependent power saving. The narrow-strip estimate has the
essential restriction (sigma-1/2)log T <= A.

## NumberTheory/DivisorIncidence.lean

- `moebius_right_inverse`: the finite divisor incidence right inverse,
  deduced from the established left inverse and finite matrix algebra.

## Analysis/SelbergMollifierOptimization.lean

- `diagonalMass`
- `diagonal_completion`
- `diagonal_lower_bound`
- `diagonal_optimizer_normalized`
- `divisorCoordinate`
- `divisorCoordinate_moebius_normalization`
- `divisorEnergy`
- `divisorEnergy_completion`
- `sum_gcd_divisors_eq`
- `gcdKernel_energy_eq`
- `divisorInverse`
- `divisorCoordinate_inverse`
- `cutoffSet`
- `cutoffMass`
- `cutoffTarget`
- `cutoffOptimizer`
- `cutoffOptimizer_eq_zero_above`
- `cutoffOptimizer_one`
- `divisorCoordinate_eq_zero_above`
- `cutoffEnergy_completion`
- `cutoffEnergy_lower_bound`
- `cutoffEnergy_optimizer`
- `cutoffSet_factorial`
- `cutoffMass_factorial`
- `gcd_energy_eq_totient`
- `one_le_totient_cutoffMass`
- `totient_cutoff_optimizer`

Finite exact identities and minimization statements, with their displayed
nonzero/positive-weight hypotheses. The totient specialization discharges
these weight premises for the ordinary gcd kernel. The cutoff is genuinely
n<=X, not a larger divisor lattice. No zeta-integral estimate is assumed or
concluded.

## Analysis/ComplexLogSecondMoment.lean

- `logSecondMomentDefect`
- `integral_log_norm_second_moment_exact`
- `log_norm_le_half_sq_sub_one`
- `logSecondMomentDefect_nonneg`
- `integral_log_norm_le_half_second_moment_excess`
- `integral_log_norm_le_of_second_moment`

Exact integrated residual and direct uncentered second-moment transfer.
Nonvanishing and interval integrability are explicit; the actual analytic
moment upper bound remains open.

## Open (intentionally deferred analytic proof)

Uniform generalized-Jordan arithmetic estimates; approximate functional
equation and twisted zeta second moment; optimized-mollifier moment;
compatible horizontal argument bounds for the direct mollifier; final
height-window and inclusive-count assembly. The research note distinguishes
the direct Selberg mollifier from the existing Mobius quadratic detector.

The final server checkpoint controls source verification and publication.

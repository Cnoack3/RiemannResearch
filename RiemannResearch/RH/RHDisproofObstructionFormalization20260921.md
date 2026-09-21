# RH disproof obstruction: formalization coverage

21 September 2026.

Source: the ordinary argument archived in
`RHDisproofObstructionDraft20260921.md`, corresponding to the user's
`RH_Obstruction_Compact_Frequency_Rigidity_2026-09-21.md`.

This update does not prove or disprove RH. It adds checked gap and convergence
criteria, a complete Jensen sampling theorem, a complete individual critical-mode
energy obstruction, and explicit statements and conditional reductions for the
remaining mixture arguments.

## Conventions

The capacity development uses the project's actual real `ThresholdHilbert`.
Stage `n` contains moduli 2 through `n+1`; the gap infimum uses stages `n+1`
to omit the empty dictionary. Coercivity is formalized for every real signed
coefficient family, retaining the entire Hilbert tail and all mixed terms.
The complex-coefficient formulation in the ordinary draft follows by
complexification; that identification is not an additional theorem of this update.

The spectral development uses complex-valued coordinate sequences. Array index
`n` means physical integer `n+1`, so `paretoWeight n` is
`1/((n+1)(n+2))`. A finite complex measure is represented by an integrable complex
density against a finite positive measure. A general polar-decomposition
conversion theorem is not asserted here.

## Established declarations

### FirstCoordinateTailGap

`firstCoordinateTailGap` is the infimum of the actual constrained finite tail
minima. The following statements have complete proofs:

- `firstCoordinateTailGap_nonneg` and `firstCoordinateTailGap_le`.
- `firstCoordinateTailGap_pos_iff_capacity_bounded`.
- `uniformTailCoercivity_iff_capacity_bounded`.
- `firstCoordinateTailGap_pos_iff_coercivity` and
  `firstCoordinateTailGap_pos_iff_certificate`.
- `firstCoordinateTailGap_controls_all` and `uniform_tail_constant_le_gap`:
  the gap is exactly the largest constant controlling all finite signed trials.
- `firstCoordinateTailGap_le_normalized_trial`.
- `not_RH_firstCoordinateTailGap_pos` and
  `riemannHypothesis_of_firstCoordinateTailGap_zero`.

The last two use actual Mathlib RH with no RH-to-density hypothesis.

### TailMinimumConvergence

The existing `tailMinimum_increment` and `tailMinimum_tendsto_canonical` are
reused instead of duplicated. New complete proofs give:

- `tailCapacity_le_strong_limit_energy`.
- `tailMinimum_converges_iff_capacity_bounded`.
- `tailMinimum_strong_limit_eq_canonical`.
- `tailMinimum_uniform_capacity_conclusion`: a supplied uniform capacity bound
  yields the actual canonical certificate, strong convergence, and the exact
  error identity and bound
  `norm(z* - z_n)^2 = norm(z*)^2 - C_n <= B - C_n`.

These are exact equivalences and consequences; no uniform arithmetic capacity
bound is supplied.

### LogIntegerSamplingUniqueness

`logIntegerSamplingUniqueness_proved` completely proves the general sampling
input: an entire function of exponential type that vanishes at every
`log d`, for integer `d>=2`, is identically zero.

The proof uses Mathlib's `AnalyticOnNhd.sum_divisor_le`. It places `n^2`
distinct logarithmic zeros inside a ball of radius `2n + O(1)`, then obtains a
contradictory quadratic-versus-linear inequality from Jensen's estimate.
There is no open analytic provider in this theorem.

### CriticalMellinMixtureEnergy

The following have complete proofs, without the countable energy provider:

- `criticalPoint_norm_lower`.
- `coefficient_norm_summable`, `coefficient_square_summable`, and
  `coefficientEnergy_pos`.
- `criticalMode_norm_le` and `criticalMixture_coordinate_summable`:
  the stated absolute first-moment assumption gives genuine coordinatewise
  summability, even for unbounded ordinates.
- `summable_logEnergy_tendsto_zero` and
  `not_summable_of_positive_logEnergy_limit`, for arbitrary complex sequences.
- `criticalMode_energy_ge_sqrt_gap`, `criticalMode_energy_lower`, and
  `criticalMode_not_summable`. In particular, every individual critical-line
  mode satisfies the unconditional harmonic lower bound
  `paretoWeight n * norm(mode n)^2 >= 1/(4*(n+2))`, hence has infinite energy.

### CompactFrequencyMellinRigidity

The actual modes, coordinate mixtures, absolutely-convergent-pairing identity
target, zeta-weighted Fourier transform, mass, and sampling defect are defined.
Complete helper proofs include `densityFourier_norm_le`,
`bounded_exponential_coefficient_eq_zero`,
`samplingDefect_zero_implies_mass_zero`,
`weightedDensity_zero_iff_supported_on_zeros`, and
`continuumMixture_eq_zero_of_density_zero`.

## Conditional reductions and open formalization obligations

| Declaration | Explicit dependency still required |
|---|---|
| `not_RH_iff_firstCoordinateTailGap_pos` and `riemannHypothesis_iff_firstCoordinateTailGap_zero` | `hDensity : RiemannHypothesis -> closedSpace = top`. This is the classical RH-to-density theorem, still missing as a checked provider in this project. |
| `compactFrequencyRigidity_of_analyticProvider` | `CompactMixtureAnalyticProvider`: the actual Mellin/Fubini pairing identity (including convergence), entire exponential-type control of the actual sampling defect, and Fourier uniqueness for the actual weighted density. Jensen sampling uniqueness is now discharged. |
| `nonzero_criticalMixture_not_summable_of_provider` | `CriticalPurePointEnergyProvider`: the actual logarithmic-energy limit for distinct ordinates with absolute first-moment coefficient control. Coordinate convergence and positive coefficient energy are already proved separately. |

`CompactCriticalMixtureTrivialityTarget` records the complete bounded-frequency
critical-line statement with actual quantities. It remains an open formalization
target: the finite zero-support decomposition and mixture energy argument have
not been completed in Lean. It is a proposition definition, not an axiom.

The ordinary proofs of these analytic statements are in the companion draft.
Their Open status here denotes missing formalization, not a claim that those
analytic statements are new unsolved mathematical conjectures.

The separate mathematical problem is deciding the gap: proving strict
positivity would disprove RH, and proving it vanishes would prove RH.
Neither endpoint is established.

## Verification evidence

The combined candidates passed the isolated Lean check
`job_Ap3qxyBblw90Qrk6aErQQzd2T3xlJiT_` with exit code 0. A redundant unreachable
tactic was subsequently removed before the project checkpoint.

Axiom audits of the positive-gap/capacity equivalence, optimal coercivity
constant, uniform-capacity convergence conclusion, Jensen sampling theorem,
individual-mode nonsummability, and conditional countable-mixture conclusion
reported only `propext`, `Classical.choice`, and `Quot.sound`.

Local theorem hypotheses remain visible and are listed above; an axiom audit
does not discharge them. No `sorry`, `admit`, project-local axiom, or unsafe
declaration is introduced. The changed modules and root exports are subject to
the final publication checkpoint's affected-module validation.

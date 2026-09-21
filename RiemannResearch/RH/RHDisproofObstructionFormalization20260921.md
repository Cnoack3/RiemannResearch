# RH disproof obstruction: formalization coverage

21 September 2026.

Source: the ordinary argument archived in
`RHDisproofObstructionDraft20260921.md`, corresponding to the user's
`RH_Obstruction_Compact_Frequency_Rigidity_2026-09-21.md`.

This continuation does not prove or disprove RH. It removes the analytic
provider assumptions from compact-frequency continuum rigidity. The earlier
gap, capacity, Jensen-sampling, and individual-mode results remain established.
The complex coercivity extension and complete countable critical-mixture
energy law are now verified, including nonsummability theorems without analytic
provider hypotheses. The finite-mixture specialization and complete compact critical-triviality
assembly are also verified.

The classical implication from RH to density of the actual residue span
remains a separate, explicit missing formalization. It is not hidden inside
an equivalence and is not supplied by the mixture rigidity theorems.

## Conventions

The capacity development uses the project's actual real `ThresholdHilbert`.
Stage `n` contains moduli 2 through `n+1`; the gap infimum uses stages `n+1`
to omit the empty dictionary. Coercivity is formalized for every real signed
coefficient family, retaining the entire Hilbert tail and all mixed terms.
`ComplexTailCoercivity` gives a verified explicit complexification, including
equality of the real and complex coercivity constants and the actual weighted
coordinate norm identities.

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

### Continuum rigidity with the analytic inputs discharged

`compactFrequencyRigidity_proved` in the `CompactFrequencyRigidity` module
is the assembly theorem (its Lean namespace is `SpectralObstruction`). Its only inputs are
the actual `CompactFrequencyData`: `1/2 <= sigma < 1`, a nonnegative frequency
bound, a finite positive measure, an integrable complex density, and
almost-everywhere frequency support inside the stated bound. It proves

    every normalized residue pairing vanishes
      iff zeta(verticalPoint sigma t) * a(t) = 0 almost everywhere.

The formerly required analytic inputs are supplied by:

| Module | Checked mathematical content |
|---|---|
| `MellinModeResiduePairing` | Exact single-mode arithmetic pairing and genuine absolute convergence on the positive half-plane, away from the pole. |
| `CompactMixtureResidueIdentity` | The actual mixture's summation/integration interchange and residue identity, including absolute convergence. |
| `CompactFrequencyMellinEntire` | Integrability of the zeta-weighted density, entire dependence on the Fourier variable, and exponential growth of the actual sampling defect. |
| `WeightedDensityFourierUniqueness` | An integrable complex density whose Fourier transform vanishes on the real axis is zero almost everywhere. No positivity of the density or compact-support hypothesis is required for this uniqueness theorem. |
| `LogIntegerSamplingUniqueness` | Jensen logarithmic-sampling uniqueness, already established in the previous publication. |
| `CompactFrequencyRigidity` | `compactMixtureAnalyticProvider_proved` and `compactFrequencyRigidity_proved`, with no remaining provider arguments. |

The earlier `_of_provider` assembly lemmas retain their general hypothesis
forms; those hypotheses are now instantiated by actual checked declarations
for compact-frequency data. They no longer represent a missing analytic step
in the specialized continuum rigidity theorem.

### Critical-mixture and complex-coercivity developments

The complete combined proof batch verified every module below. The source
audit and module validation are performed by the publication checkpoint.

| Module | Intended fully specialized conclusion | Verification status |
|---|---|---|
| `ComplexTailCoercivity` | The same sharp tail gap controls every finite complex coefficient family; `complex_tail_bound_iff_real` identifies all real and complex coercivity constants. The norm is that of the genuine complex Pareto Hilbert space. | Verified |
| `CriticalMellinCellAsymptotics` | `cellSlope_tendsto` for every complex parameter; exact Mellin-mode first-difference factorization and the positive-real-part slope norm bound. | Verified |
| `HarmonicToeplitz` | Harmonic normalization tends to one, and harmonic weighted means of every complex sequence tending to zero also tend to zero. | Verified |
| `LogarithmicPowerMeans` | `harmonic_phase_tendsto`: the normalized sum of `(n+1)^(-1-i*t)` tends to `1` when `t=0`, and to `0` otherwise. | Verified |
| `CriticalMellinGramLimits` | Exact complex mixed-energy decomposition, diagonal/off-diagonal limits, and a uniform frequency-factorized Gram bound. | Verified |
| `FiniteCriticalMellinMixtureEnergy` | The full logarithmic-energy law for finite distinct critical modes, retaining every cross term; finite energy forces every coefficient to vanish. | Verified |
| `CriticalMellinCountableEnergy` | `criticalPurePointEnergyProvider_proved`: the actual countable logarithmic-energy law for injective ordinates and summable absolute first moments. No bound on the ordinates is assumed. | Verified |
| `CompactCriticalMixtureAtoms` | Finitely many zeros in a compact critical-line band; exact atomic decomposition of an annihilating compact-frequency density. | Verified |
| `CompactCriticalMixtureTriviality` | `compactCriticalMixtureTriviality_proved`: finite-energy compact-frequency critical-line annihilators have zero density almost everywhere and identically zero coordinate mixture. | Verified |

For the power means, the proof uses the exact telescope

    q_n - q_(n+1) = (n+1)^(-1-i*t) * cellSlope(i*t,n),
    q_n = (n+1)^(-i*t),  |q_n| = 1,

together with `cellSlope(i*t,n) -> i*t` and harmonic Toeplitz convergence.
Thus an assumed asymptotic estimate for the oscillatory partial sums is
unnecessary. Countable-energy convergence uses the actual mixed Gram series
and the summable first-moment majorant.

## Remaining formalization obligation and mathematical scope

| Declaration | Explicit dependency still required |
|---|---|
| `not_RH_iff_firstCoordinateTailGap_pos` and `riemannHypothesis_iff_firstCoordinateTailGap_zero` | `hDensity : RiemannHypothesis -> closedSpace = top`. This is the classical RH-to-density theorem, still missing as a checked provider in this project. |

`CriticalMellinCountableEnergy` also proves the directly usable specialized APIs
`criticalMixture_not_summable` and `nonzero_criticalMixture_not_summable`. They
assume only injective ordinates, summability of the absolute first-moment
coefficients, and respectively positive coefficient energy or a nonzero
coefficient. No analytic provider, zeta-zero, or RH hypothesis remains.

`compactCriticalMixtureTriviality_proved` proves the complete
`CompactCriticalMixtureTrivialityTarget` proposition: finite-energy compact
critical-line mixtures annihilating every residue have density zero almost
everywhere, and their coordinate mixture is identically zero. No additional
analytic provider or RH hypothesis remains.

The RH-to-density dependency is a missing formalization of a known classical
theorem, not an unsolved theorem of ordinary mathematics. The detailed audit
is `RHToDensityDependencyAudit20260921.md`. It identifies the exact remaining
provider and Bagchi's classical route: finite damped Möbius residue sums,
Littlewood's RH-dependent ordered Dirichlet convergence and uniform bounds,
zeta growth and shifted-quotient estimates, and two boundary L2 limits.
No checked project provider for those RH-dependent analytic inputs was found.

Crucially, Littlewood's series convergence must use ordered finite partial
sums. Mathlib's `LSeriesSummable_moebius_iff` identifies absolute summability
with `Re(s)>1`; writing `Summable` in the larger RH half-plane would be an
incorrect formalization of conditional convergence.

The separate mathematical problem is deciding the gap. Using the classical
RH-to-density converse, strict positivity would disprove RH; that reverse
implication still carries `hDensity` in Lean. Vanishing of the gap implies
RH by an already established Lean theorem. Neither endpoint is established.

## Verification evidence

The previous publication's combined candidates passed the isolated Lean check
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

**Continuation verification:** the complete fifteen-module combined batch
passed as `job_KIcJpWoBI14ZXz8ybgjvQu6GCm66OD_c`. This includes all the
actual compact-frequency, complex-coercivity, finite/countable energy, and
compact critical-triviality results described above.

The final batch axiom audits of `compactCriticalMixtureTriviality_proved`,
`criticalPurePointEnergyProvider_proved`, `compactFrequencyRigidity_proved`,
and `firstCoordinateTailGap_controls_complex` report only `propext`,
`Classical.choice`, and `Quot.sound`. The finite-mixture energy theorem is
also covered by the downstream compact-critical-triviality audit.

The source audit and module validation are performed by the publication
checkpoint. No additional checks were submitted by the documentation/audit
agent. Mathematical development was parallel and all Lean verification
submissions were serialized by the root coordinator.

These axiom audits accompany the exact theorem types. They do not remove
the explicit RH-to-density hypothesis in the separate RH equivalences.
That classical converse is the only remaining formalization obligation
identified in this coverage report.

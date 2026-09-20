# Orthonormal, DPP, Fredholm, Mellin, and spectral chat: Lean coverage

Source: Christian's supplied conversation, incorporated on 20 September 2026.
Base commit inspected: ca5af511ff2cfb490eb46f47358f63401a6943c1.

This inventory distinguishes an actual arithmetic theorem from a general
lemma, a conditional implication, and an outstanding formalization. No
project-local axiom or admitted theorem is used to stand for a missing result.
A successful proof of an implication does not supply its hypothesis.

The original additions comprise 30 focused Lean modules; the subsequent
finite-rank Mellin DPP construction adds 11 more, followed by two modules for
exact finite and dual vacancy certificates. Every new module is exported
from `RiemannResearch.lean`; the checkpoint validates the individual modules
and their affected dependents. The status below refers to each theorem's exact
Lean statement, including any explicitly listed hypotheses.

## Index convention

The chat uses physical sites n≥1 and conductors d≥2. Lean's integer coordinate
k means physical site k+1; mode j means conductor j+2. The Hilbert realization
absorbs sqrt(1/((k+1)(k+2))) into ordinary square-summable coordinates. Thus
`integerKernel` is Q, including the Pareto weights; it is not the unweighted
kernel K in the chat. The first physical site's counting index is zero.

## Existing results reused

| Chat statement | Existing formal location and scope |
|---|---|
| Independence of g_d; Gram–Schmidt never loses a vector | `residueAtom_linearIndependent`, `residueMode_orthonormal`, finite/full span identities in `RH/ResidueOrthonormalCoordinates` |
| alpha coefficients, finite projection, c_N and c_infinity | `projection_eq_mode_sum`, `modeAlpha_eq_log_sum`, `coefficient_eq_mode_sum`, `mode_coefficient_series_norm_summable`, `limitCoefficient_eq_mode_tail` |
| Möbius coefficient functional and defect | `RH/MobiusCoefficientStabilization` and `RH/ResidueOrthonormalCoordinates`; absolute convergence is unconditional, Möbius target values are not |
| Completeness, constant projection, Parseval, first point, capacity | Existing closure/orthonormal/tail-capacity equivalences; criterion-to-RH is proved; RH-to-density remains a separate formalization gap |
| Genuine finite and limiting integer DPP laws | `RH/IntegerDPPExistence`: all finite correlation determinants, with positivity proved for the actual projections |
| Exactly N points | `integerLaw_cardinality` in `RH/IntegerDPPCardinality` |
| Two-point covariance, expectation, variance | `Probability/DeterminantalEntry`, `Probability/DeterminantalMoments`; these are actual probabilities/integrals |
| Arithmetic exclusion and conditional independent lifts | `RH/IntegerDPPArithmeticExclusion`, `RH/IntegerDPPLiftFactorization`, `RH/IntegerDPPConditionalLifts` |
| Finite-window gap determinants and generating functions | `RH/IntegerDPPWindow`, `RH/IntegerDPPWindowGenerating`, `RH/IntegerDPPGramDeterminant` |
| First-site odds, Schur capacity, determinant ratio | `RH/IntegerDPPSchur`, `RH/IntegerDPPHazards`, `RH/IntegerDPPGramDeterminant` |
| First-site coupling and conditional full spatial coupling | `RH/IntegerDPPCoupling`, `RH/IntegerDPPSpatialCoupling`; the latter still needs `SpatialWindowFeasible` |
| Mellin residue formula | `normalizedResidue_mellin_zeta` in `Analysis/MellinNormalizedResidue`, with actual convergent Mellin integrals |

## Additions in this work

| Topic | New modules and exact scope |
|---|---|
| Exact Gram cofactors | `RH/ResidueGramCofactors`: inverse-Gram projection coefficients, positive normalization, determinant quotient for its square, signed minors, positive leading coefficient |
| Finite G/K bridges | `RH/ResidueGramModeIdentities`: logarithmic and first-point inverse-Gram forms equal the actual mode sums |
| Finite digamma evaluation | `RH/ResidueGramDigamma`: full infinite-tail Gram evaluated through a finite residue sum; first mode and its normalization evaluated exactly |
| Small exact Gram constants | `RH/ResidueSmallGram`: reflection identity and the G23/G33 logarithm/pi/sqrt3 formulas |
| Independent Bernoulli counts | `Probability/DeterminantalSpectralCount`, `Probability/DeterminantalBernoulliCount`: compression eigenvalues in [0,1], product PGF, actual count-law equality, mutual independence in the auxiliary eigenvalue-indexed model |
| Multivariate determinant | `RH/IntegerDPPMultiplicativeGram`: separate site weights and actual expectations, preserving the full Gram matrix; full-Gram polynomial (1−z)^N |
| Maximum distribution | `RH/IntegerDPPMaximum`: actual probability that all points lie in a finite prefix equals the prefix/full Gram determinant ratio; infinite-tail event handled by continuity from above |
| Symmetric finite damping | `RH/IntegerDPPFiniteDamping`: sqrt-weight compressed determinants equal the actual multiplicative expectations, also for the limiting law |
| Exact scalar benchmark | `RH/ParetoProductBenchmark`: positive Pareto product limit sin(π(√5−1)/2)/π, by exact finite identity and Euler's product |
| Damped saturation | `Probability/MultiplicativeOccupancy`, `Probability/MultiplicativeOccupancyLower`, `RH/IntegerDPPDampedMinimum`, `RH/IntegerDPPDampedLimit`: finite minimum rigidity and infinite-prefix benchmark convergence equivalent to zero limiting vacancy; hence a sufficient condition for RH |
| Decisive vacancy certificates | `RH/IntegerDPPVacancyCertificates`, `RH/IntegerDPPVacancyDuality`: exact finite-trial criterion using all signed Gram terms; sharp certificate lower bound and unique canonical equality case; the arithmetic provider remains open |
| Rank-growth counterexample | `Probability/DeterminantalRankGrowth`: a genuinely nested DPP family with exactly N occupied sites and a permanent first-site hole |
| Actual Mellin kernel | `Analysis/ComplexKernelPairCorrelation`, `RH/MellinFrequencyKernel`: exact zeta-envelope factorization of the actual inverse-Gram kernel, Hermitian symmetry, zero rows at critical-line zeros, cancellation from normalized pair correlation |
| Finite-rank Mellin DPP construction | `RH/MellinProjectionDPP` with six analytic/kernel support modules and four `Probability/ContinuousProjection*` modules: actual Mellin cross-Plancherel, angular-measure orthonormality, inverse-Gram/mode identity, normalized probability law, permutation invariance, exactly n distinct points, full n-point determinant density, reproducing kernel and trace n |
| Cutoff matrices | `Analysis/FrequencyCutoffMatrix`, `RH/MellinFrequencyRegularization`: actual compact-frequency integrals of residue modes, integrability/continuity, Hermitian matrices, real spectrum |
| Positive spectral factors | `Analysis/PositiveSpectralPolynomial`, `Analysis/PositiveSpectralProduct`: finite factors and actual convergent canonical products with summable nonnegative weights have only real zeros; `RH/HilbertPolyaPositiveProduct` proves actual Mathlib RH from an explicit, unproved completed-zeta product identity on the critical strip |
| Step-profile obstruction | `Analysis/MellinLogStepContinuity`, `RH/ParetoMellinLogDomain`: even a continuous a.e. representative forces the actual profile to vanish |
| Frequency-domain obstruction | `Analysis/FourierFirstMomentContinuity`, `Analysis/MellinLogFrequencyDomain`, `RH/ParetoMellinLogFourierDomain`: Fourier first-moment continuity and the actual Hilbert-space domain obstruction, with ordinary Fourier normalization (a harmless 2π frequency factor) |
| Sine scaling | `Analysis/ComplexKernelScaling`, `RH/MellinFrequencyScalingTargets`: precise scaling targets and the conditional implication from kernel convergence to the normalized sine pair profile; no existence claim; `RH/IntegerDPPEdgeScalingTargets` specifies the actual-law upper-edge CDF target |

Independence of the auxiliary Bernoulli variables does not assert independence
of occupations at spatial sites. Likewise, a Hermitian kernel formula is not
by itself a formalized continuum point-process existence theorem.

## What is still not proved or formalized

The following distinctions must remain visible in any later RH claim.

1. **Bagchi converse: formalization gap.** The classical result relating RH
   to density is a cited mathematical theorem. This repository does not yet
   provide the direction RH → closed residue span = the full Hilbert space.
   It does prove the converse direction needed by its sufficient criteria.
   The entire chat's chain must not be described as an unconditional
   kernel-checked RH iff chain until this direction is supplied.
2. **Full negative association and spatial coupling: formalization gaps.**
   Pairwise covariance and count moments are checked. Negative association
   for arbitrary increasing functions of disjoint occupation sets, and the
   finite supported-transport provider for `SpatialWindowFeasible`, are not.
   These are known general DPP theorems, not proposed new RH assumptions.
3. **Finite-rank continuum Mellin law: completed; further identities remain.**
   `RH/MellinProjectionDPP` constructs the actual law for every rank n from
   the actual Mellin modes, with no RH or normalization-provider hypothesis.
   The logarithmic isometry, Fourier/Mellin identification, cross-Gram
   identities, full n-point determinant density, probability normalization,
   permutation invariance, distinctness, and cardinality are proved.
   Separate lower-order factorial marginal formulas have not yet been
   formalized. This construction does not assert an infinite-rank locally
   finite law or a pointwise map from sampled integer configurations to
   frequency configurations.
4. **Infinite local-trace obstruction: formalization gap.** The chat's weakly
   null scaled residue sequence and local noncompactness argument have not
   yet been fully instantiated as a theorem about the continuum projection.
   Its consequence that unscaled positive-length frequency gaps vanish
   independently of RH is not claimed as a checked theorem here.
5. **Operator Fredholm identification: formalization gap.** Finite matrix
   determinants, probability expectations, the exact product benchmark, and
   the infinite-prefix convergence criterion are checked separately. The
   trace-class operator W^(1/2)Q_infinity W^(1/2), its operator Fredholm
   determinant, and the trace-norm identification with those finite
   compressions still need a formal operator-theoretic implementation.
6. **Cutoff spectral bound: formalization gap.** Real spectrum is proved.
   The precise interval bound [−R,R] uses transformed orthonormality and has
   not been silently inferred from Hermitian symmetry alone.
7. **Arithmetic endpoint: open research.** Zero limiting vacancy, constant
   membership, tail-capacity divergence, and attainment of the damped
   benchmark remain unproved. The exact new criterion requires finite trials
   with arbitrarily large source-squared-to-full-energy ratio; equivalently,
   every genuine Hilbert tail certificate must be excluded. Both formulations
   remain open. No new theorem assumes these without showing them explicitly
   in its type.
8. **Montgomery, Airy, KPZ, and Hilbert–Pólya identification: open research.**
   The new algebra and conditional limits do not establish a sine/Airy
   scaling limit, identify sampled frequencies with zeta-zero ordinates,
   specify and prove a KPZ space-time limit, or identify a spectral
   determinant with the completed zeta function. Positive spectral factors
   imply real zeros only after such an arithmetic identity is supplied.

The displayed decimal coefficients for modes 3–5 are numerical illustrations.
Their exact cofactor definitions are formalized; no certified rounding-error
bound is asserted for the decimal strings.

## References and provenance

The supplied chat is the immediate source of the requested statements.
Module docstrings specify this provenance and the underlying mathematical
sources where relevant: Bagchi, arXiv:math/0607733; Hough–Krishnapur–Peres–Virag,
arXiv:math/0503110; Lyons, arXiv:math/0204325. Euler's sine product, matrix spectral
theory, Fourier inversion, and measure convergence use checked Mathlib
results. These citations support terminology/statements or proof strategy;
they do not replace missing Lean proof terms.

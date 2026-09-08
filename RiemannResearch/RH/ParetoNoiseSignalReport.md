# Lean translation of Noise, signal, and arithmetic repair

Source: RH_Noise_Signal_Arithmetic_Repair_2026-09-07.pdf, prepared 7 September 2026.

PDF SHA-256: `812ac328c9bda0c248d78f487661f116c96269759594f58ec5de42e97f035584`.
Canonical Markdown source SHA-256:
`a5c39c964e2d161b837d7642b562a2157dea67c0836705a21eb41deb06eaed4f`.

This is a formalization in the existing RiemannResearch Lean 4/mathlib project.
The files use that project's actual residue functions, genuine Möbius function,
and complete infinite Pareto sums. They are not standalone Mathlib-only files.
The project toolchain is Lean 4.33.0-rc2.

## Coverage

| Report claim | Formalization | Scope |
|---|---|---|
| §2: overall scale optimization and NSR conversion | NoiseSignalQuadratic; ParetoNoiseSignal | Actual Pareto variance, nonzero mean, and bounded sequence hypotheses |
| §2: geometric mixture and total-error decomposition | Existing ParetoGeometricMixture, ParetoGeometricEnergy, ParetoGeometricTransform | Reused bounded-sequence results; the sharp Hankel spectral theorem remains an open translation obligation |
| §3.1: Möbius defect and residue/packet incidence | Existing ParetoResidueDuality | Genuine arithmetic, including composite indices |
| §3.1: norm convergence forces defect convergence | ParetoDefectContinuity | Each approximant bounded separately; anchoring at zero explicit |
| §3.2: prime-power obstruction | Existing ParetoFiniteCertificates and ParetoSequenceCertificates; new ParetoNoiseSignal | Existing stronger full error bound implies the report's NSR floor 1/91 |
| §3.3: coprime increment and pair completion | NoiseSignalQuadratic; ParetoCoprimeObstruction | Finite exact remainder identity and full infinite error/NSR floors with the actual reciprocal-square mass |
| §4: exact Pareto dilation | Existing ParetoDilation | Complete infinite means and inner products for bounded anchored sequences |
| §§4–5: four-residue repairs, head preservation, defects | ParetoArithmeticRepair | Explicit indices; all conductor collision assumptions visible |
| §5: mixed-packet representation | ParetoArithmeticRepair.mixedPrimeLift_eq_residues | Actual divisor sum; prime multiplier coprime to old scale |
| §§4–5, 8.1: repair mean, variance and covariance | ParetoRepairCovariance | Complete four-term covariance, exact diagonal cost, and explicit nonnegative-profile bound |
| §5: fixed base plus smooth35 repairs is insufficient | ParetoRepairObstruction | Automatic arithmetic invariant and no pointwise convergence, including varying coefficients |
| §6: hidden-noise family | ParetoHiddenNoise | Actual residue/dilation family, zero mean, head values, parity amplitudes, exact interval masses and energies |
| §8.2: common optimizer mismatch | Existing TwoBlockCommonOptimizer | Generic two-form completion reused; literal matrix inverse display not separately re-proved |
| §3.3: exact finite Euler product | ParetoEulerProduct | Full reciprocal-square mass for every nonzero even modulus; exact two-prime constants |
| §3.1: prime defect dual norm | ParetoPrimeDualNorm | Actual finite-support representer, full squared dual norm 2(p²+1) for p≥3, and packet coefficient error bound |
| §4: residue moments | ParetoResidueMoments; DigammaQuarter | Complete sums: G44=6 log 2−π/2 and binary residue mean/norm=log 2 |
| §6: full hidden-noise moments | ParetoHiddenNoiseMoments; ParetoHiddenNoiseAsymptotics | Explicit error at most 18 from 2 log n, for every n≥3; all tails retained |
| §6: conditioned limit | ParetoHiddenConditioning; ParetoHiddenConditioningLimit; ParetoHiddenConditioningSubstitution; ParetoHiddenConditioningConstant; ParetoHiddenConditioningVerified; FermiIntegral | Complete actual limit (π²−6)/9, for all natural indices tending to infinity |
| §5: repair modulus and prime summation | ParetoRepairModulus; PrimeLogSummability; ParetoRepairSummability | Actual discrete variance bound and unconditional prime-weight convergence |
| §5: exact existence target from the gap theorem | Smooth35RepairCompletion | Conditional reduction: the quantitative smooth-number gap is the only remaining hypothesis |
| §8.3: gain-product criterion | Analysis.ResidualGainProduct; Analysis.ResidualGainTermination | Exact recurrence/product and complete exhaustion criterion, including a gain equal to one |
| §8: proposed normalized Bessel estimate | ParetoBesselClusters; Analysis.SmoothScaleReciprocal; ParetoBesselSmoothObstruction; Smooth35Choice; PrimeReciprocalTail | Refuted for the actual least-smooth scale assignment; no quantitative gap input |
| Named analytic targets | ParetoNoiseResearchTargets and the providers above | Four positive targets proved, the proposed Bessel route refuted for the report's choice, and one arithmetic input unformalized |

## New conclusions

For the actual hidden-noise family and every n≥3, both
`|paretoInner(Fn,Fn) − 2 log n| ≤ 18` and
`|n·paretoMean(|Fn|) − 2 log n| ≤ 18` are proved. The conditioned
energy satisfies `n·∫_0^1 (CFn)^2 → (π²−6)/9`. Its proof includes
the exact transform, exponential substitution, integrable majorant, dominated
convergence, and the exact Fermi integral π²/12.

For 0<h≤n, the actual binary repair satisfies
`variance ≤ 8(h/n²)(1+log(n/h)) ≤ 16 sqrt(h/n)/n`.
An eventual bound `h/p ≤ C/(log p)^η`, η>0, therefore implies both
the actual scale-ratio limit and summability of the actual repair variances.
The theorem `summablePrimeRepairs_of_leastSmooth35_log_gap` has exactly
the original `ResearchTargets.SummablePrimeRepairs` as its conclusion.

The speculative normalized all-coefficient Bessel estimate fails for
`leastSmooth35Above`. A Bessel constant would bound each common-scale
cluster cardinality by a constant times sqrt(E). Since p<E≤2p, its prime
reciprocal mass would then be bounded by a constant times 1/sqrt(E).
Summing over E=3^a5^b gives a convergent double geometric series, contradicting
Euler's divergence of prime reciprocals. The least-scale construction and
its bound E≤2p are proved elementarily; this negative result uses no
unformalized gap theorem. It resolves a suggestion explicitly left open in
the PDF, and is compatible with summability of individual squared norms.

For fixed even prime support P, the complete reciprocal-square mass equals
`(π²/6) · ∏_{p∣P}(1−p⁻²)`. For P=6 this gives actual error and NSR
floors `(π²−9)/(2π²)` and `(π²−9)/(π²+9)`.

## Remaining proof obligations

The quantitative spacing theorem for consecutive 3^a5^b numbers remains
unformalized. It is the explicit missing arithmetic input to the original
`SummablePrimeRepairs` target. The new conditional proof does not
silently assume a variance bound, a ratio limit, or summability.

Other report statements outside the six named targets still need formalization:
the fixed-old-space gain asymptotic, full Hilbert-space infimum/closure
conversions, and the cited spectral and RH-criterion literature inputs,
including the sharp pi/4 Hankel contraction and Bagchi/Burnol/Bettin–Conrey–Farmer
results. Numerical tables are not promoted to interval certificates.

RH and convergence of a sufficient repair system remain unresolved. No
project axiom, `sorry`, `admit`, or `unsafe` declaration is used in
these proofs. Normal Lean foundations and explicit theorem hypotheses are
distinguished from unproved arithmetic inputs.

## Use

Place these modules in the corresponding directories of RiemannResearch and
use the repository's pinned toolchain and dependencies. Import only the
subject modules needed by the proof. The main project exports the new modules.

Verification and publication status is recorded in the accompanying task
delivery and the published commit.

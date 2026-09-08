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
| §§4–6 and 8: remaining key analytic statements | ParetoNoiseResearchTargets | Proposition definitions only; these are not theorems or assumptions imported by established results |

## Remaining proof obligations

The PDF is not fully verified by this translation. In particular:

1. The published quantitative gaps between 3^a5^b numbers, the square-wave
   integral modulus estimate, and the resulting summability of individual
   prime-repair variances need Lean proofs.
2. The fixed-support infinite reciprocal-square mass is defined and used
   directly. Its zeta/Euler-product evaluation, and hence the displayed
   pi-squared numerical constants, are not yet proved here.
3. The hidden-noise logarithmic asymptotics, conditional-variance limit
   (pi^2-6)/9, and fixed-space gain estimate need the remaining analytic steps.
   Exact finite interval formulas are available as proved ingredients.
4. The residue-four moment evaluation, prime dual norm formula, full
   Hilbert-space infimum conversion, and the infinite product/gain criterion
   have not all been separately translated.
5. Literature inputs such as the Bagchi criterion and squarefree sufficiency,
   weighted Hankel diagonalization, Burnol rate barrier, and conditional
   Bettin–Conrey–Farmer benchmark are not asserted as new Lean theorems.
6. Numerical tables remain numerical evidence, not interval certificates.

The suggested all-coefficient Bessel/covariance bound is unproved in the PDF
itself. RH and global convergence of a sufficient repair system remain open
mathematical research problems, not merely omitted Lean proof scripts.

No project axiom, `sorry`, `admit`, or `unsafe` declaration is part of the
intended translation. Normal Lean foundations are distinguished from all
substantive hypotheses appearing in theorem statements.

## Use

Place these modules in the corresponding directories of RiemannResearch and
use the repository's pinned toolchain and dependencies. Import only the
subject modules needed by the proof. The main project exports the new modules.

Verification and publication status is recorded in the accompanying task
delivery and the published commit.

# FMZ, circle Poisson, and Pareto Lean recovery (2026-10-11)

The recovered development adds eight modules and extends the existing
`ActualZeroCoshMass` module. It reuses the existing actual-zero energy,
normalized-residue closure, inverse-Gram optimizer, bounded Mellin linearity,
and contour zero-sum results.

## Verification

- Lean: `4.33.0-rc2`, pinned project dependencies.
- Core import and selected transitive axiom report:
  `job_RqSthxV7Nj1b-rp1pVbL-jtLcx7TMa-d` (succeeded).
- Combined nine-module import and thirteen selected transitive axiom reports:
  `job_sOL1L-tn_natEbX91GhBXduzZZD9XHAh` (succeeded).
- Publication uses the server checkpoint's audit and affected-module validation
  of the integrated delta. No full-project build is claimed here.

The original saved archive was recovered with all eight original Lean-source
SHA256 checks matching. Compiler failures were repaired in an isolated
workspace; failed attempts were not published. The original separate
`ActualZeroHorizontalCoshEnergy` draft was replaced by sharp estimates in the
already existing `ActualZeroCoshMass`, avoiding a duplicate energy definition.

## Exact mathematical scope

| Module | Result and hypotheses |
|---|---|
| `Analysis/ActualZeroFMZComparison` | Actual ordinate/Landau comparison from the explicitly displayed Selberg right-tail bound; retains both frequency signs, the finite exponential endpoint terms, the rational majorant, and the constant `128 C / 3` on `abs u <= log T / 8`. |
| `Analysis/PoissonHaarSpecialization` | Actual continuous circle Poisson kernel for `0 <= a < 1`; Fourier coefficient `a ^ abs k`, real rational density, strict positivity, Haar mass one, centered coefficients, and even-power multipliers. |
| `Analysis/ArithmeticWeightedFourierRemainder` | Exact signed series remainder and quantitative bound for arbitrary index types, under explicit modewise and summability hypotheses. |
| `RH/ParetoHorizontalZeroBridge` | Actual legal signed finite candidates and normalized-residue closure; horizontal fourth energy bounded by the complete physical residual norm, including the actual canonical projection and captured-energy deficit. |
| `Analysis/ActualZeroReciprocalConstant` | Unconditional multiplicity-weighted all-sign reciprocal sum, its explicit positive constant, and the resulting actual optimizer bound. |
| `RH/ParetoResidualBoundaryEnergy` | Exact boundary Mellin/Plancherel energy for the literal finite residual, retaining the full cross term and complete candidate norm square. |
| `RH/ParetoFiniteMellinHalfPlane` | Exact signed finite Mellin formula for `Re s > 0`, `s != 1`; explicit critical-line zeta energy with denominator `1/4 + t^2`, without an extra provider premise. |
| `Analysis/ActualZeroCoshMass` (extended) | Sharp bounds for the existing convergent regularized cosh mass; no second energy is introduced. |
| `Analysis/ActualZeroParetoCoshBridge` | Existing regularized cosh mass controlled by the actual physical Pareto error. |

Writing

\[C_0=2+\gamma-\log(4\pi),\qquad
S_2=\sum_{\rho}\frac{m_\rho}{1+(\Im\rho)^2},\qquad
e=\lVert 1-f\rVert^2,\]

all actual nontrivial zeros occur, both ordinate signs are retained, and
`zeroMult` supplies analytic multiplicity. The verified conclusions include

\[\sum_\rho\frac{m_\rho}{\rho(1-\rho)}=C_0>0,\qquad
S_2\le C_0,\qquad E_4\le\frac{eS_2}{4},\qquad
e\ge\frac{4E_4}{C_0}.\]

For the repository's actual inverse-Gram optimizer, the captured energy obeys

\[Q_n\le 1-\frac{4E_4}{C_0}.\]

The existing regularized mass satisfies

\[\frac{u^2}{2}E_4\le M(u)
\le4\bigl(\cosh(|u|/2)-1\bigr)E_4
\le\bigl(\cosh(|u|/2)-1\bigr)eS_2.\]

No RH assumption, zero simplicity, desired residual convergence, or assumed
Hadamard product is introduced. All thirteen selected transitive axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`.

## Open obligations

The classical Selberg zero-density theorem is unconditional on paper; its Lean
provider is still unfinished. Subsequent work derives the actual rational
Landau limits and completes the finite-prime arithmetic, mixed-mode,
product-Haar/Poisson, Fourier-decay and reconstruction assembly conditional
only on that Selberg provider. This supersedes the earlier finite-prime
assembly gap; see RH/FinitePrimeFMZAssembly20261011.md and
Analysis/ActualPrimeTorusFMZContinuous. The precise density input is in
Analysis/ActualZeroSelbergDensity. No infinite-prime torus law is claimed.
Pareto residual convergence and vanishing of the detecting cosh mass remain
open; these bridges do not prove RH.

Source provenance is retained in the Lean module docstrings, including the
Ford--Zaharescu and Ford--Meng--Zaharescu comparison references.

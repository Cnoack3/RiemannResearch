# Layer-cake and fixed-width RH program: Lean coverage

Source: the user-provided handoff and its continuation through sections 1–40,
`RH_Layer_Cake_Sublevel_Program_and_Next_Attack_2026-09-16_Continued.md`.
The complete mathematical record is preserved in
`LayerCakeSublevelProgram20260918.md`. Two Markdown trailing-space line breaks
were removed to satisfy the repository whitespace policy; mathematical text
and formulas are preserved.

Original source SHA-256:
`e80c9f8c0464c68f1766dcd2061dc7a5705a5ee4ae8894d96e4c4ae6818c4b3f`.

The source is an ordinary mathematical research record, not a Lean proof file.
This addition does **not** certify every analytic assertion in that record and
does **not** prove RH. It records all sections and adds the formal results and
explicit remaining interfaces described below. A named proposition without a
provider is a statement to prove, not an axiom or an established theorem.

## Formal modules

Paths in this table are relative to `RiemannResearch/`.

| Module | Exact scope |
| --- | --- |
| `Analysis/CofinalQuadraticPositivity` | A fixed value is nonnegative under vanishing lower errors; cofinal domains and eventually consistent forms; nested exhaustion; correct relative-form error addition; antitone divergence from arbitrarily low witnesses. No arithmetic lower bound or Weil converse is supplied. |
| `Analysis/DyadicHatRefinement` | Actual rescaled `rootTent` functions; bounds, symmetry, continuity, support, and exact three-term dyadic refinement with mask `1/2,1,1/2`. |
| `Analysis/HatIntegrability` | Compact support and actual integrability, all `MemLp` exponents, translated hats, squared hats, autocorrelation integrands, and real exponential moments, for positive width. |
| `Analysis/HatMassIntegral` | Direct integration of the affine pieces: total mass `h` and squared mass `2*h/3`. The target integral formulas are proved, not assumed. |
| `Analysis/FiniteKernelRefinement` | Exact finite atomic convolution and double-mask reconstruction; exponential centering; absolute reconstruction bound with squared mask mass. Kernel/moment identities are explicit inputs to the centered-discrepancy application. |
| `LinearAlgebra/SparseQuadraticEnergy` | Complex finite quadratic entry bounds, effective coefficient count, sparse coercivity from explicit entry and mass estimates, exact normalized remainder identities, and collective-cancellation obstructions. The actual uniform prime/archimedean estimate is not provided. |
| `LinearAlgebra/SignedSchurResidual` | Exact signed trial completion, coercive residual estimate, actual inverse correction, two-sided Schur bounds, positivity certificate, and induction from an arbitrary starting level. It treats real inner-product spaces; Hermitian applications require the corresponding real quadratic realization. |
| `LinearAlgebra/IncreasingEnergyTolerance` | Exact refinement of shifted energies; inherited positive buffer; polynomial increments for every natural degree at least one. The new-block residual domination remains a hypothesis. |
| `RH/WeilPositiveDiagonal` | RH implies positivity of the actual completed arithmetic Weil form on `SmoothSuperexponentialDecay` tests, using the existing proved arithmetic/zero-side adapter and actual zeta zeros. It does not apply the smooth theorem directly to nonsmooth hats. |
| `RH/FixedWidthWeilDiscrepancy` | Actual hats, correlation integrals, polar moments, locally finite prime discrepancies using von Mangoldt weights, decaying archimedean remainder, and completed Weil form. Proves support/cutoff facts and signs. Names the two-hat and Landau analytic provider propositions without asserting them. |
| `RH/PolynomialWeilCriterion` | Actual Mathlib RH from a one-sided polynomial discrepancy bound plus the explicit Landau provider; from a two-hat polynomial lower bound plus both analytic providers; and the reference-energy version with its explicit bounded-energy premise. |
| `RH/SplineWeilMatrixTargets` | Actual mesh `log 2 / 2^j`, `Fin (2*j*2^j-1)` indices, complex spline tests, literal signed Weil matrix entries, mass and difference energy. Defines actual polynomial targets and analytic representation/admissibility obligations; proves mass-to-energy and approximation-error transfer. The index cardinality does not establish basis independence or density. |
| `RH/PolynomialSplineRH` | Actual Mathlib RH from the polynomial spline energy or mass target and explicit quantitative interpolation, two-hat, and Landau providers. The literal matrix version additionally requires the nonsmooth quadratic representation. |

## Complete section-by-section coverage map

“Recorded” below means preserved in the full source, with no new claim of
kernel verification. “Provider open” means its formal proof remains to be
implemented; this does not imply the underlying classical theorem is an open
mathematical problem.

| Source sections | Formal coverage and remaining work |
| --- | --- |
| 1–2 | Source/provenance and localized multiplier setup recorded. The concrete arithmetic form reuses existing `SignedWeilCorrelation`, `WeilEnergyNormalization`, and `WeilSpectralPairing`; the full compressed multiplier realization is not supplied here. |
| 3–5 | Bohr moments, covariance asymptotics, Gaussian/Chernoff statements and qualitative torus transfer recorded. Their proofs are not newly formalized. The proposed huge quantitative transfer scale remains an unproved heuristic, not a Lean theorem. |
| 6–8 | Positive smoothing, layer-cake operator inequality, prolate concentration and density obstruction recorded. The corrected positive-density nonreproduction claim is not given a new Lean proof. |
| 9–12 | Boundary-overlap and logarithmic boundary-energy estimates recorded. The disjoint-strip restriction is retained; no boundary estimate lacking it is added. |
| 13–19 | Original obligations and next calculations recorded, together with the subsequent corrections. Unavailable companion interval certificates are not invented or imported. |
| 20–22 | Corrected normalization, both pole terms, disjoint strips, relative-form errors, smoothing obstruction and prolate scale recorded. Relative-form error addition is checked; the existing exact arithmetic normalization is reused. |
| 23–24 | Exact archimedean energy/boundary potential and larger removable layer recorded. The new code defines the positive difference energy and proves its sign; the full Fourier identity, boundary decomposition and asymptotic bounds still need providers. |
| 25 | General cofinal vanishing-error and locally consistent form arguments checked. Specialization to all admissible Weil tests still needs the domain/exhaustion and Weil-converse providers. |
| 26–27 | Exact `log 5` Fourier entries and nonvanishing signed cross-block coupling recorded. No interval certificate, all-frequency matrix identity or Cesaro coupling computation is claimed newly verified. |
| 28 | Trial Schur algebra and coercive/inverse residual bounds checked. Compactness of the actual energy-normalized operator and its spectral identification still need analytic providers. |
| 29 | Actual hats, integrability, masses and dyadic refinement checked; actual finite spline tests/matrices defined. Cubic autocorrelation formula, off-diagonal cancellation, finite-dimensional spanning, nesting injections and density are not all discharged. |
| 30–31 | Necessary two-point bounds and status record preserved. No two-point condition is promoted to full matrix positivity. |
| 32–33 | Uniform `O(h_j)` entry remainder argument recorded. The prime-power/sieve and archimedean scaling providers remain to be formalized. |
| 34–35 | Sparse coercivity and collective-cancellation algebra checked with their precise mass/entry/refinement premises. No unconditional actual-matrix theorem is claimed before those premises have providers. |
| 36–37 | Actual fixed-width discrepancy, cutoff equality and sign/support facts checked. The exact transformed discrepancy, entire-factor zero set, noncancellation and the nonnegative-Laplace Landau argument remain formalization obligations. |
| 38 | Polynomial criteria assembled as explicitly conditional RH theorems. Quantitative interpolation is a quantified error/energy interface, not a hidden appeal to a fixed-vector limit. Full equivalences and the actual spectral dichotomy require the outstanding analytic providers. |
| 39 | Finite signed reconstruction, exponential centering, mask-mass loss and coarse effective-count algebra checked. General coarse-mask moment sums and the actual discrepancy reconstruction need their providers. No required signed cancellation bound is asserted. |
| 40 | Increasing-tolerance buffer and full signed Schur certificate/induction checked. Uniform control of the actual new Schur blocks, and a concrete finite starting certificate, remain unproved. |

## Conditional RH declarations and their assumptions

The most direct fixed-width theorem is:

`RiemannResearch.RH.FixedWidthWeilDiscrepancy.riemannHypothesis_of_twoHat_polynomial_lower`.

Its substantive premises are:

1. `TwoHatWeilIdentity h`: equation (38.3) for the actual completed arithmetic
   form and actual integral-defined hats, for separations greater than `2*h`.
2. `FixedWidthLandauDetection h`: every hypothetical right-half-strip zero
   forces the actual discrepancy above every polynomial arbitrarily far out.
   The intended proof uses `0 < h` and `2*h < log 2`; the chosen
   `fixedHatWidth = log 2 / 4` satisfies these inequalities by checked proofs.
3. A lower bound `Q(twoHatTest h x) >= -C*(1+x)^A` beyond a fixed threshold,
   with one nonnegative finite real `C` and one natural degree `A`.

The finite matrix theorem is:

`RiemannResearch.RH.SplineWeilMatrixTargets.riemannHypothesis_of_polynomial_spline_matrix`.

In addition to the first two providers, it requires:

- `QuantitativeTwoHatSplineApproximation h`: actual spline approximants at
  sufficiently large levels, bounded energy, polynomial comparison of level
  and separation weights, and a bound on the complete signed form error.
- `SplineQuadraticRepresentation`: the literal complex matrix quadratic
  equals the completed arithmetic form on the actual nonsmooth spline tests.
- `PolynomialSplineMatrixEnergyLowerBound`: one polynomial lower bound on
  all sufficiently large literal signed spline matrices.

These are **conditional research reductions**. The conclusions concern the
actual `riemannZeta` and Mathlib `RiemannHypothesis`; RH is not redefined as
positivity of an abstract matrix. The natural-degree polynomial version is
the formalized sufficient condition; the source's full real-exponent
equivalence is not separately claimed.

## Open research estimate versus unfinished formalization

The uniform polynomial lower bound and the sufficient uniform signed
new-block Schur certificate are still the mathematical RH-strength targets.
They have no proof in the source or in this addition.

Many other missing providers concern ordinary arguments already given in
the source or established classical analysis: the fixed-width Laplace
calculation, Landau's boundary-singularity lemma, the uniform entry estimate,
and quantitative spline approximation. They are unfinished formalization,
not new assumptions that have been shown true merely by writing their types.

Further formal work should discharge those providers on the concrete
definitions above, then address the actual polynomial or Schur bound. The
unconditional sparse estimate alone does not control the increasingly
collective directions required by the fixed-width argument.

## Verification and provenance

The source of the new mathematical statements is the user-provided argument.
Existing Mathlib and project results are reused with focused imports.
The analytic Weil identity already in `WeilSpectralPairing` is an actual
proved theorem, not an explicit-formula axiom added by this change.

Development uses serialized Lean jobs and a final checkpoint validating the
changed modules and their reverse dependencies. The final publication, its
exact theorem count and axiom audit are reported with the checkpoint result.
No `sorry`, `admit`, project-local `axiom`, or `unsafe` declaration is added.

Standalone verification passed for all 13 modules with their declared import
closures: 110 theorem declarations (109 public and one private helper).
Representative axiom audits, including the actual matrix-to-RH theorem,
report only `propext`, `Classical.choice`, and `Quot.sound`. Domain-specific
premises remain visible in the declaration types and in the ledger above.

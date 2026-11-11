# Screened CRT coordinate assembly

11 November 2026. Source: the coordinate derivation in
`CanonicalPrimePowerUpdatesResearch20261107.md`, Section 3, and ledger item
`PAPER-004` in the Riemann Research Proof Ledger.

## Scope and definitions

For positive nested cutoffs `2 ≤ L`, `2 ≤ M`, `L ∣ M`, the old index set is
`L.divisors.erase 1`; the new index set is
`(M.divisors.erase 1) \ (L.divisors.erase 1)`.
The old and new columns are the actual `qResidue` atoms. This includes
prime powers, and every inner product uses the complete physical Q space.
No numerical truncation or external computation is used.

Let `U` and `V` be their finite synthesis maps. The new columns are screened
as `W = V − U G⁻¹ B`, where `G = U*U` and `B = U*V`. The implementation uses
the existing actual inverse-Gram map `inverseCoeff`. Distinct-conductor
independence is discharged by `QCovarianceInvertibility.qResidue_linearIndependent`.

The difference-test matrix has entries `A_ij = ⟨φ_j, D φ_i⟩`, for
`φ = (U,W)` and the actual anchored physical `differenceCLM`. It is not
assumed symmetric. The known source is `h_M − F_L`, rather than an unknown
pairing with the new canonical vector. The old, full, and Schur inverses
are constructed from physical difference accretivity and finite dimension.

## Declaration map

All application declarations below are in
`RiemannResearch.RH.QCRTScreenedCoordinates`.

| Mathematical obligation | Declaration |
| --- | --- |
| Actual old/new families and independence | `oldFamily`, `newFamily`, `old_independent`, `raw_joined_independent` |
| Screened columns and their independence | `screenedFamily`, `screened_independent`, `joined_independent` |
| Complete old/new orthogonality | `old_screened_orthogonal` |
| Complete physical Gram invertibility | `physical_gram_det_pos` |
| Exact signed Gram Schur entries | `screened_gram_exact` |
| Screened coordinates span the actual new trial space | `joined_span` |
| Physical difference accretivity | `difference_strict` |
| Actual old, full, and Schur inverses | `oldCollocationInverse`, `collocationInverse`, `schurInverse` |
| All four difference-test blocks | `A00`, `A01`, `A10`, `A11` |
| Exact screened test source | `beta1_exact` |
| Two block equations and their Schur solution | `coordinate_equations`, `schur_coordinates` |
| Inverse-system synthesis equals `F_M − F_L` | `canonical_assembly` |
| Physical Gram response identity | `physical_response_exact` |
| Signed canonical coordinate energy | `canonical_energy_exact` |

Reusable analysis lives in `Analysis/FiniteScreenedCollocation.lean`.
The finite-dimensional algebraic Schur inverse extends the existing
`LinearAlgebra/ObliqueBlockElimination.lean`; the existing elimination theorem
is preserved. The application imports existing CRT canonical lifts without
changing their definition.

## Exact identities and the remaining obligation

Writing `F_L = Uc` and `F_M − F_L = Ux + Wy`, the resulting identities are

\[
K=A_{11}-A_{10}A_{00}^{-1}A_{01},\qquad
\sigma=\beta_1-A_{10}A_{00}^{-1}\beta_0,
\]
\[
y=K^{-1}\sigma,\qquad x=A_{00}^{-1}(\beta_0-A_{01}y),
\]
\[
\|F_M\|_Q^2-\|F_L\|_Q^2
=2c^\mathsf{T}Gx+x^\mathsf{T}Gx+y^\mathsf{T}Hy.
\]

The signed cross term `2 cᵀGx` is retained. The physical equation is
`Hy = (⟨W_j,F_M−F_L⟩)_j`. Its right-hand side is a response pairing,
and is not replaced by the oblique test source `σ`.

The assembly supplies finite solvability and exact identities. It supplies
no uniform inverse norm, summable canonical growth bound, cofinal finite-head
energy bound, or reciprocal repair/residual-tail decay. Those remain separate
proof obligations. In particular this does not establish RH.

## Verification evidence

The saved modules compiled with Bazel/BuildBuddy, exit code 0, in server job
`job_kpjYj4JfDGu73WA1ztzZhsJuBdq3gIxf` (89.848 s):
[scoped source build](https://app.buildbuddy.io/invocation/e011fdc1-b4e1-4076-898c-14d7d02e415d).

A separate fail-closed audit compiled successfully in job
`job_UhSV6O8YGiyJNg-1Zg5TlsLgC74SObFn` (63.315 s, exit code 0):
[strict axiom audit](https://app.buildbuddy.io/invocation/52f3b722-7e0c-48ae-9def-0b56aac6ada8).
It enumerated all 59 added declarations, rejected missing names, collected
each declaration's transitive axioms with `Lean.collectAxioms`, and rejected
every axiom outside `{propext, Classical.choice, Quot.sound}`. Thus no
`sorryAx` or project-local axiom is accepted in these declarations.

These development checks used the source additions over repository base
`d69d459c7a6250961959204bdf28966047dab9a5`. The commit containing this note
identifies the integrated sources. The publication checkpoint supplies the
full-project build record, which is also linked from ledger item `PAPER-004`.
The source and axiom checks establish the stated finite identities; they
do not discharge the remaining quantitative growth and tail obligations.

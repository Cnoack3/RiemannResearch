# Infinite affine comparison attempt — 8 September 2026

## Status

**No new mathematical theorem is verified in this attempt. RH remains unproved.**
The project was inspected at published base `dcb61e8462bb9fc173c1bc9931ff8ebacdf8dee1`.
The previously verified phase bounds, weighted projection, and adjoint results
remain valid. Their open operator-identification and legal-covariance obligations
are not marked closed by these drafts.

The files linked below are **unverified Lean proof candidates**, deliberately
stored as fenced Lean code in Markdown outside the compiled import graph. They contain full proof
attempts rather than placeholders, but an unaccepted proof attempt is not a proof.
The Markdown format marks their unverified status, not a way to bypass verification:
these files must be repaired, accepted by Lean, installed as actual modules,
exported, audited, and checkpoint-validated before any declaration is promoted.

## Intended substantive results

All constructions use the existing complete real Hilbert space
`ThresholdHilbert = lp (fun _ : Nat => Real) 2`, which realizes the original
positive-coordinate weight `w(k)=1/[k(k+1)]`.

1. Construct the actual uniform affine isometry `L_m`. Its column at raw source
   index `j` is `1/sqrt(m)` on raw coordinates `m*(j+1)+r-1`, `0<=r<m`, and zero
   elsewhere. Disjoint unit columns give a complete-space linear isometry.
   Construct `U_m=L_m L_m*` and prove its self-adjointness, idempotence and exact
   Pythagoras. The finite exceptional head is explicit.
2. Identify the actual existing weighted projection `P_m=(1/m)T_m T_m*` against
   `U_m`. The intended signed within-block matrix entry is

   `((P_m-U_m)e_(j,t))_(j,r) = c_(m,r,j+1)*c_(m,t,j+1) - 1/m`.

   Distinct positive blocks have zero entries, and the exceptional initial
   basis vectors are annihilated. Derive the overlap from actual columns,
   then prove full standard-basis square summability before regrouping:

   `sum_n ||(P_m-U_m)e_n||^2 = affineProjectionEnergyTail m 0`.

   This would close the missing identification of the arithmetic energy with
   the actual infinite operator. Only after this identity is verified can
   the existing `0 <= 2s-E_m <= 2/(3m^2)` estimate be reported for that operator.
3. Construct actual finite legal spaces

   `V_M = span {T_a residue_2, T_a residue_3 : a in M}`,

   for finite sets `M` of arbitrary positive integer scales. Construct their
   genuine orthogonal projections `Q_M`; identify `sup_M V_M` with the existing
   algebraic two-seed legal subspace; derive strong convergence of `Q_M` to the
   projection `Q_legal` onto its closure. **The limit is not assumed to be the
   identity.** Derive exact nested innovation energy and mixed covariance.
4. For actual dilation-block compression `C_(m,M)=P_m Q_M P_m`, derive the
   bilinear form, positivity, exact covariance increments and strong limit
   `P_m Q_legal P_m`. This is a dilation-block construction, not the paper's
   still-separate finite residue-quotient covariance or spectral synthesis.
5. Identify the already certified period-36 witness as an actual Hilbert vector
   in `V_M` for `M={1,2,3,6,9,18}`. The intended transfer gives actual projection
   error `<53/1000` and captured energy `>947/1000`, including the closed legal
   projection. The arithmetic witness estimate was proved earlier; this draft
   supplies its projection interpretation, not a new numerical certificate.
6. Retain the exact signed comparison of the two actual compressed covariances.
   Writing `D_m=P_m-U_m`, the intended scalar identity is

   `<C_(m,M)f,f> = ||Q_M U_m f||^2 + ||Q_M D_m f||^2
                  + 2 <Q_M U_m f, Q_M D_m f>`.

   The mixed term is not discarded or asserted nonnegative.

## Candidate source index

Paths are relative to this report's directory.

| Candidate file | Main intended endpoints |
|---|---|
| [ThresholdUniformAffineOperatorCandidate.md](ThresholdUniformAffineOperatorCandidate.md) | `hilbertUniformAffine`, `hilbertUniformBlockProjection_idempotent`, `hilbertUniformBlockProjection_pythagoras` |
| [ThresholdAffineOperatorComparisonCandidate.md](ThresholdAffineOperatorComparisonCandidate.md) | `hilbertAffineDiscrepancy_matrix_branch`, `hilbertAffineDiscrepancy_basis_summable`, `hilbertAffineDiscrepancy_basis_energy`, `hilbertAffineDiscrepancy_phase_gap_rate` |
| [ThresholdHilbertFiniteLegalCandidate.md](ThresholdHilbertFiniteLegalCandidate.md) | `iSup_finiteTwoSeedSpan`, `finiteTwoSeedProjection_innovation_covariance`, `finiteTwoSeedProjection_tendsto`, `twoSeedBlockCovariance_tendsto` |
| [ThresholdHilbertLegalCertificateCandidate.md](ThresholdHilbertLegalCertificateCandidate.md) | `finiteTwoSeedProjection_period36_error_lt`, `twoSeedLegalProjection_period36_energy_gt` |
| [ThresholdTwoSeedAffineCovarianceCandidate.md](ThresholdTwoSeedAffineCovarianceCandidate.md) | `twoSeedBlockCovariance_uniform_comparison`, `twoSeedBlockCovariance_uniform_energy` |

Names in the table have prefix `RiemannResearch.RH.Pareto`.
Intended assumptions are positive integer `m`, actual vectors in the real H,
finite positive-integer scale sets, `M subset N` for nested gains, and branch
residue bounds where relevant. There is no RH, legal-density, or unproved
matrix-realization premise. These are intended types, not accepted declarations.

## Verification evidence and limitation

Submissions were serialized; each timeout was recovered and awaited to a
terminal state before the next submission. The exact receipts are recorded in
[ThresholdOperatorComparisonAttemptVerification.json](ThresholdOperatorComparisonAttemptVerification.json).

- Research-import API check: `job_g10Mtw6vz9NebiAU91M2AJ3QD2VeBUae`, terminal
  wall timeout after 180 seconds, exit `-9`, no output.
- Minimal core-Lean runtime probe: `job_sPAlne0L0Y2nh0Kdn4y2ZZqq6Ehv5R5e`,
  succeeded in 17.623 seconds. This only checks basic natural-number computation;
  it is not mathematical progress toward the target.
- Actual-coordinate plus uniform-operator candidate:
  `job_SgnlCJoRPpJjj625rlf3KiGWdGwQ7cn9`, terminal wall timeout after 600 seconds,
  exit `-9`, no output.
- Uniform-operator candidate using Mathlib imports and the exact Hilbert-space
  definition directly: `job_p2yuCCNUr9abnU7_mDCaN0wE9VauMw-5`, terminal wall
  timeout after 240 seconds, exit `-9`, no output.
- Saved-source verification: `job_dKIhDMIbSI_RksSXSaeBCADRxG_Wvt2L`, terminal
  wall timeout after 180 seconds, exit `-9`, no output.

These failures do not refute the mathematics. They also do not verify any
candidate. The available output is insufficient to determine the timeout cause.
No new candidate has a successful axiom audit or a successful saved-module check.

## Resume target

First restore a research-capable Lean verification path and check
`ThresholdUniformAffineOperatorCandidate.md` against the exact project dependency
version. Then check the actual-coordinate and standard-basis energy assembly,
followed by the independent finite legal construction and its certificate.
Promote only accepted sources to `.lean` modules and update exports and ledgers
at their successful publication checkpoint.

An integrity-checked snapshot of the 31 exact existing project dependencies was
prepared locally for fallback inlining; those sources are already persisted in
the base commit and need not be duplicated in the published project. Their
[recorded dependency manifest](ThresholdOperatorDependencySnapshot.json) can be used to reproduce the check input.

After operator identification is actually accepted, the promising mathematical
next step is the residue-quotient legal covariance and its concrete spectral
synthesis/repair estimates. Legal density, the criterion bridge to genuine RH,
and RH itself remain open. No conditional reduction is promoted here.

A declaration-free documentation module named `ThresholdUniformAffineOperator.lean`
is retained because the workspace patch tool disallows file deletion. Its
original candidate body is preserved in `ThresholdUniformAffineOperatorCandidate.md`.
Importing that documentation module supplies no operator or theorem, and
compiling it is not verification of the candidate. No unverified declaration
is exported.

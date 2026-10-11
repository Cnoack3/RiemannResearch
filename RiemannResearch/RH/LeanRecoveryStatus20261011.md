# Lean recovery record — 11 October 2026

Recovery validation: all twenty source modules passed a combined import check
on the project server in job `job_qLV5LgK5vCeCoU--RBHGL-2xcKlhEXoH`
(terminal success, exit code 0, verified true). The transitive axiom reports for
`regularizedCoshMass_eq_zero_iff_RH`, `exists_polynomial_compact_control`,
and `reciprocal_product_error_explicit` contained only `propext`,
`Classical.choice`, and `Quot.sound`. Publication remains gated by the
final integrated-project checkpoint; its terminal result identifies the
published commit and validation scope.

Recovery repairs preserved theorem statements: explicit addition monotonicity,
the current Mathlib push-tactic import, direct complex conjugate/norm-square
and real-cast proofs, and finite collision arithmetic normalization.
The package history below records the verification state at recovery intake.

The integration workspace is `ws_hpqrnJbaPc0ZNyhBW2ywJ9K2VPm0t9rb`, based on
`415a2c777f274bec07b7a19fadf089640c31f703`. The user's server must verify the
exact integrated source before publication. GitHub Actions is not the verifier.

## Recovered prime-phase development

Four modules were recovered: `LagPhase`, `PrimePhaseTorus`,
`ActualPhaseGramExpansion`, and `ActualZeroCoshMass`. Their original combined
check and the persisted project build succeeded; the latter is server job
`job_DYBz4hksIY8ksgRTUEv9nnCJ2ge0rHoa`.

The later publication checkpoint `job_f7aL0T5v6TrOx_x-esU5iMOl4cHFsFv8`
created unpublished commit `66a6e9908147803efade13e93be914137439748f` but
failed while integrating newer `main`, with conflicts in the aggregate import
file and theorem catalog. The original module verification is retained as
historical evidence; integration into the present base requires fresh checking.

## Recovered harmonic and collision drafts

Six modules were recovered intact from
`ZetaZeroHarmonic_LeanDrafts_20261011.zip`: `FrequencySpreadInterval`,
`BalancedPowerTransfer`, `BalancedTuplePhase`, `ActualZeroBalancedTuplePhase`,
`FiniteCollisionCertificates`, and `ActualOrdinateCollisionCertificates`.
All archived file sizes and SHA-256 hashes matched before the recovery edits.

The original workspace was `ws_8vfQzVumlkttVHnRPjYhe62a7Qvn3pCQ`, based on
`c173f559e39c149116d0a56c5a6e230b069b668c`. Initial snippet job
`job_Yts5GqrQN8pd_vOlrU6c3mRGXajDyhLX` is terminal with a compiler error in
the addition-monotonicity argument. The recovered proof candidate has been
repaired. The complete six-module development has not yet obtained final
integrated certification. The archived combined candidate was not submitted
in the interrupted session.

These results concern exact finite algebra, explicit error-transfer hypotheses,
and collision-certificate implications. Existence of the cofinal arithmetic
certificates is still open. Distinct-zero certificates do not require simplicity;
multiplicity-copy certificates have the stronger criticality-and-simplicity
conclusion. Neither kind of implication by itself establishes RH.

## Recovered analytic reciprocal development

`Analytic_Reciprocal_Lean_Proofs_20261011.zip` preserved nine locally compiled
modules: `AnalyticCircleSquareBounds`, `EmpiricalCompactCircleControl`,
`EmpiricalReciprocalTransfer`, `TruncatedMobiusConvolution`,
`ProductFrequencyDispersion`, `ReciprocalRateBalance`,
`AbsoluteReciprocalCompatibility`, `AnalyticDirichletPolynomial`, and
`AnalyticAbsoluteReciprocal`. The saved hashes for all nine matched the recovered
sources before edits. The local compiler was Lean 4.33.0-rc2; exact equivalence
with the repository's pinned dependencies was not certified by those checks.

`ActualAnalyticPolynomialControl` is an additional integration draft, making
ten source modules in this package. It was not included among the nine local
successful compiler checks.

The original server job `job_y1I4AWlbop2VtNRAD7QdBHTe9bdk4Os1` is terminal
with a compiler error in an early analytic-circle candidate, not a completed
validation of the final package. Its workspace was
`ws_oWKg9SfdAD036d82LIbf7ZMrdoIps-CN`; the archive records repository base
`b56e06ee6bbeecb11d56166b8c5adabb4a9124a1`. No original final-project
checkpoint or publication was recorded for this package.

The unconditional absolute-convergence result concerns real part greater than
one. The complete critical-strip application still needs the explicit actual
ordinate FMZ estimates, zero-count normalization, and weighted tail estimates.
These provider obligations must remain visible in theorem hypotheses and the
catalog; they are not new axioms and have not been proved merely by recovering
or compiling the deterministic transfer lemmas.

## Final certification boundary

The final checkpoint must cover the current module contents, aggregate exports,
and catalog against the integration base above. Earlier failed jobs are terminal
and no longer described as unknown queued work. Earlier successful builds apply
only to the snapshots they checked. A later successful checkpoint record should
identify its exact commit and job before this integration is described as
verified or published.

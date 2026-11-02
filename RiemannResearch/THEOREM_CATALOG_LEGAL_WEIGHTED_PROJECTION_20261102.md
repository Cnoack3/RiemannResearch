# Legal weighted projection continuation — 2 November 2026

This continues the weighted-CRT program without republishing its ten completed
principal results. The arithmetic cofinal growth provider remains **Open**.

## General weighted finite projection

Owning module: `Analysis/FiniteWeightedLegalProjection.lean`.

- `weightEquiv`: multiplies each coordinate by sqrt(w), with an explicit inverse,
  for any strictly positive real weights on a finite index type.
- `weightEquiv_norm_sq`: the transported Euclidean norm square is exactly the
  actual finite weighted energy.
- `weightedProjection`: constructs the weighted orthogonal projection onto any
  finite-dimensional submodule, with no rank or conditioning assumption.
- `weightedProjection_mem`, `weightedProjection_completion`, and
  `weightedProjection_minimizes`: membership and the complete norm-square
  remainder for every competitor.
- `constrainedProjection`: translates by an actual feasible reference and
  projects onto the intersection of the submodule and the observation kernel.
- `constrainedProjection_mem`, `constrainedProjection_observation`, and
  `constrainedProjection_completion`: admissibility, exact observations and
  the complete constrained error identity. Dependent observation rows are
  allowed. Feasibility is supplied by the reference vector, not inferred from
  a nonexistent universal interpolation theorem.

A coherent isolated check succeeded with exit code 0 and verified=true in
`job_IOFZ-Yh647L_Mq4CJMAVP4ZbMLYTUr7A`; reported check duration 21.501 seconds.
Axiom inspection of the weighted and constrained completion theorems returned
only `propext`, `Classical.choice`, and `Quot.sound`. No unresolved arithmetic
provider is an assumption of these finite projection theorems.

## Actual arithmetic application

Owning application module: `RH/WeightedLegalPrimitiveProjection.lean`. Its
standalone verification requests timed out; final source validation is required
at the publication checkpoint.

- `legalPrimitiveSpace` packages the existing literal zero-mean legality
  predicate as a submodule.
- `legalProjection` specializes the general construction to the positive
  `residueWeight` and that submodule.
- `legalProjection_legal`, `legalProjection_completion`.
- `primitiveHeadMap`: actual positive-index head evaluation, reduced modulo L.
- `constrainedLegalProjection` and its `_legal`, `_head`, `_completion` theorems.

The saved-module import/axiom request
`job_ihOj1OOlE1zmTGoG7wdS5lQtSjoOUgJV` ended in a 300.051-second wall
timeout, exit -9. It did report a successful build of the generic
`Analysis/FiniteWeightedLegalProjection.lean` module (22 seconds), but did not
finish the arithmetic application. A second attempt (`job_7WYs02ZlE23-9ria4CVFQgUysCZFpuhl`) also timed
out at 180.022 seconds. No axiom audit for the application is claimed. A bounded full-file check (`job_1WH-oeV562c29RQUFFtI5m9tpWYnRWxE`)
also reached its 180.152-second wall timeout without diagnostics.
The final publication checkpoint must validate this module and its aggregate
import. Publication is blocked unless that source validation succeeds.

## Paper results and external computations

Research note: `RH/LegalWeightedProjectionResearch20261102.md`.

- Exact finite basis, rational feasibility, Gram projection and inverse
  observation-Gram cost, including the entire signed cross term.
- Legal compressed CRT adjoints and their tower, using existing isometry,
  adjoint and legal-nesting theorems. These applications remain paper arguments.
- Complete period-6 legal space and the unavoidable head-preserving energy cost.
- Exact divisibility-refinement energy gain. No asymptotic rate is asserted.
- Explicit h_q=4g_(2q)-2g_q, with delayed zero head and period mean 1.
  Paper proof: complete Cesàro energy <=4/(zeta(2)(q-1)). Hence zero mean
  can be enforced at arbitrarily small complete-energy cost without changing
  a fixed head, allowing unrestricted squarefree periods.
- Equality of the fixed-head energy infima with and without zero mean, over
  all permitted periods. This is not an attained minimum at a fixed period.
- Exact rational external certificate: a period-30 H=2 legal trial has energy
  <0.6311726122, whereas the unique period-6 H=2 vector has energy
  >0.6364830283. Infinite tails and zeta(2) enclosures are retained. These
  numerical certificates are not Lean-certified.

Unverified delayed-repair candidates were retained separately. Three attempts
ended in wall timeouts (240.103, 600.182, 180.103 seconds); none supplies
verification or an axiom certificate. The timeouts do not refute the arguments.

## Open arithmetic provider

Construct a cofinal family of actual legal exact-head primitives whose
normalized complete energy has zero lower logarithmic growth. Finite existence,
projection contraction, the small-period certificates and cheap mean repair
do not prove this provider. The established conditional RH consumer remains
conditional; this continuation does not prove RH.

## Timing scope

The successful workspace-opening retry ran from 2026-11-02T10:43:41.117Z
to 2026-11-02T10:45:37.335Z (116.218 seconds); an earlier opening request
had a transport timeout. This is separate from Lean verification. The successful
isolated projection job entered the single-worker queue at position 1; its
reported check duration was 21.501 seconds. Other listed durations are wall
timeouts, not measurements of successful kernel checking.

## Publication gate

The final checkpoint must audit the saved sources, build the changed modules
and their required reverse dependents, and validate any integration before
push. The checkpoint receipt, rather than an isolated snippet, determines
publication status.

# Ordinate pair-correlation continuation: verification ledger

Date: 2026-10-11.

The coherent four-module candidate, including its actual-zero assembly and four
principal axiom reports, passed the Lean server in
`job_PR_vKXrffVXh4S7Sk0zbCHyXnY3GkstC`: exit code 0, verified true.
Every principal report lists only propext, Classical.choice and Quot.sound.
An isolated snippet does not certify final project integration; publication is
gated by the final checkpoint.

Modules:
- Analysis/OrdinateWindowVariance.lean: exact clipped interval overlap, first
  and second finite count moments, and triangle = squared mean + count variance.
- Analysis/OrdinateTriangleSecants.lean: finite hinge convexity, strict/inclusive
  secants, collision-atom bound, and quantitative three-energy-error transfer.
- Analysis/CosinePolynomialMeanSquare.lean: the complete signed double-sum mean
  square and zero/even cosine kernels.
- Analysis/ActualZeroWindowVariance.lean: actual multiplicity-copy assembly.
  Its geometric lower-support and exact-mean hypotheses are explicit.

The paper continuation is RH/OrdinatePairCorrelation20261011.md.
The prime asymptotic, Montgomery--Vaughan input, contour/canonical-product
deduction, Fujii input, vague compactness, and limiting PCC deduction are paper
results, not newly formalized providers.

Open: identification of the signed actual prime/residual quadratic limit
(5.7), or its cutoff-T form (5.8). The useful microscopic Selberg-type
approximation remains an analytic provider to establish.

The first checkpoint, job_lqnQ2xByEdLYhrWQHAYZoMsiHb0OBDhi, retained local
commit 6045ed240b7aa174d10e414ee81f5a32a0663145 but did not publish it:
integration conflicted only in the aggregate imports and the catalog.
The validated candidate is preserved in its original workspace.
The continuation applies the same four modules to newer published base
13d61f34d625af1e3a0c76ba9642e16fc9cfe38a, preserving its additions and
requiring a new final integrated server checkpoint before publication.

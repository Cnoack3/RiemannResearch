/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Init

/-!
# Source claim and status index

The combined-audit archive is indexed below by import disposition. The exact
progress PDF, TEX source, scripts, outputs, requirements, and README dated
3 September 2026 are now available and byte-identified in ProgressManifest.
progressReportClaims records the report's formally labelled items, while
progressReportStatuses records its finite, conditional, computational, and
open statuses through PDF page 8. A claim kind reproduces the report's label;
it does not state that a matching declaration is already established here.
The interval endpoint records remain candidate computations.
-/

namespace RiemannResearch.RH.CombinedAudited

set_option linter.style.longLine false

inductive ManuscriptClaimKind where
  | theorem | proposition | lemma | corollary | conjecture | criterion
  | definition | warning | auditWarning | openProblem | problem | researchTarget
  deriving Repr, DecidableEq

structure ManuscriptClaim where
  page : Nat
  kind : ManuscriptClaimKind
  label : String
  title : String
  extractedStatement : String
  deriving Repr, DecidableEq

/-- The combined-audit archive supplied no formal headings from
combined_audited_manuscript(4).pdf. The newly received progress report is
indexed separately in progressReportClaims. -/
def sourceClaims : Array ManuscriptClaim := #[
]

/-- Formally labelled items in the progress report dated 3 September 2026.
The kind field reproduces the report's own label and does not assert that a
matching declaration has already been established in this project. -/
def progressReportClaims : Array ManuscriptClaim := #[
  { page := 2
    kind := .auditWarning
    label := "Status warning 1.1"
    title := "Finite endpoint qualification"
    extractedStatement := "The interval result is a reproducible candidate computer-assisted result conditional on the displayed analytic reduction and the interval library; it is not external review, and a finite support endpoint does not imply RH." },
  { page := 2
    kind := .theorem
    label := "Theorem 2.1"
    title := "Prime-gap curvature Green formula"
    extractedStatement := "For strictly increasing nodes and positive diagonal weights, the adjacent curvature map has kernel equal to the affine profiles, its Green matrix is positive definite, and weighted affine residual energy equals the inverse-Green curvature quadratic form." },
  { page := 2
    kind := .corollary
    label := "Corollary 2.2"
    title := "Local factorization of the actual signal Hessian"
    extractedStatement := "The actual signal Hessian factors through adjacent curvature coordinates, and the actual-direction target is the inverse-Green curvature energy being little-o of inverse log x." },
  { page := 4
    kind := .theorem
    label := "Theorem 3.1"
    title := "Bandwidth-two curvature innovations"
    extractedStatement := "The bandwidth-two LDL-star factorization of the pentadiagonal Green matrix has positive pivots and gives the affine residual energy as the sum of squared scalar innovations divided by those pivots." },
  { page := 4
    kind := .theorem
    label := "Theorem 4.1"
    title := "Exact common-optimizer gluing formula"
    extractedStatement := "Block inversion splits the global inverse-Green energy into the sum of separately optimized block energies and a nonnegative Schur-complement boundary innovation." },
  { page := 5
    kind := .corollary
    label := "Corollary 4.2"
    title := "Exact diagnostic for blockwise arguments"
    extractedStatement := "A separate-block argument must also establish the target little-o bound for the boundary innovation omitted by independent block optimizers." },
  { page := 5
    kind := .researchTarget
    label := "Research target 5.1"
    title := "Revised N4/M1 target"
    extractedStatement := "For the actual common-optimizer endpoint moment, establish the explicit innovation-sum bound, retain the exact boundary term under blocking, and retain the signed return-energy decomposition." },
  { page := 6
    kind := .lemma
    label := "Lemma 6.1"
    title := "Exact rank-one high-mode elimination"
    extractedStatement := "If the high floor and its rank-one update denominator are positive, positivity of the displayed effective low Schur matrix suffices for positivity of the lower block model." },
  { page := 7
    kind := .auditWarning
    label := "Status warning 6.2"
    title := "Second interval implementation qualification"
    extractedStatement := "The log 3 interval calculation has a small even margin and remains candidate evidence pending external validated-numerics and form-core normalization review." }
]

inductive ReportLeanDisposition where
  | sourceRecordOnly
  | representedOpenTarget (declarationName : String)
  | checkpointVerified (declarationName : String)
  deriving Repr, DecidableEq

/-- Project disposition of each source-labelled report item. Source labels and
project verification are intentionally recorded in separate arrays. -/
def progressReportLeanDispositions :
    Array (String × ReportLeanDisposition) := #[
  ("Status warning 1.1", .sourceRecordOnly),
  ("Theorem 2.1", .sourceRecordOnly),
  ("Corollary 2.2", .sourceRecordOnly),
  ("Theorem 3.1", .sourceRecordOnly),
  ("Theorem 4.1", .sourceRecordOnly),
  ("Corollary 4.2", .sourceRecordOnly),
  ("Research target 5.1",
    .representedOpenTarget
      "RiemannResearch.RH.PrimeGapCurvature.RevisedN4M1Target"),
  ("Lemma 6.1", .sourceRecordOnly),
  ("Status warning 6.2", .sourceRecordOnly)
]

inductive ReportEvidenceStatus where
  | finiteIdentity
  | conditionalFiniteReduction
  | candidateComputation
  | openEstimate
  | openComputation
  | openConstruction
  deriving Repr, DecidableEq

structure ReportStatusRecord where
  page : Nat
  code : String
  status : ReportEvidenceStatus
  description : String
  deriving Repr, DecidableEq

/-- Page-level status ledger for the mathematical content on report pages 2-8.
In particular, interval output is recorded only as candidate computation.
These are source-report statuses, not project-verification dispositions. -/
def progressReportStatuses : Array ReportStatusRecord := #[
  { page := 2
    code := "curvature-green"
    status := .finiteIdentity
    description := "The adjacent-curvature Green factorization is an exact finite-dimensional identity." },
  { page := 3
    code := "all-triples-compression"
    status := .finiteIdentity
    description := "Every triple determinant is expressed through adjacent curvatures, and the all-triples sum is compressed to one Green quadratic form." },
  { page := 4
    code := "bandwidth-two-innovation"
    status := .finiteIdentity
    description := "The pentadiagonal Green energy has an exact scalar LDL-star innovation sum." },
  { page := 5
    code := "boundary-gluing"
    status := .finiteIdentity
    description := "The common-optimizer gluing penalty is the nonnegative boundary Schur innovation." },
  { page := 5
    code := "actual-moment-asymptotic"
    status := .openEstimate
    description := "The required little-o bound for the actual endpoint moment remains open." },
  { page := 6
    code := "rank-one-elimination"
    status := .conditionalFiniteReduction
    description := "The high-mode rank-one reduction is exact under its displayed positivity conditions." },
  { page := 7
    code := "log3-second-interval"
    status := .candidateComputation
    description := "The second implementation reports strict interval pivots at log 3, but external review and the analytic reduction remain prerequisites." },
  { page := 8
    code := "R1"
    status := .openEstimate
    description := "Bound the actual conditional innovations relative to the explicit pivots." },
  { page := 8
    code := "R2"
    status := .openComputation
    description := "Evaluate the exact gluing term on growing instances with one global coefficient vector." },
  { page := 8
    code := "R3"
    status := .openComputation
    description := "Extend the independent endpoint implementation to log 4 and log 5." },
  { page := 8
    code := "R4"
    status := .openConstruction
    description := "Construct the global Selberg-Connes comparison with archimedean and polar sectors and identify it with the completed Weil form." }
]

structure ResearchAgendaItem where
  code : String
  page : Nat
  description : String
  deriving Repr, DecidableEq

/-- Research-agenda items stated in the source manuscript. -/
def researchAgenda : Array ResearchAgendaItem := #[
  { code := "N1", page := 50, description := "Define from the Pareto/CRT model the activated-atom map, true tail Gram, return operator, and actual signed signal; prove all range conditions before pseudoinverses." },
  { code := "N2", page := 50, description := "Fix polynomial conductor restrictions; without them the target is already RH-equivalent by density." },
  { code := "N3", page := 50, description := "Compute the actual signal spectral measure after exact Schur elimination, not an all-directions eigenvalue surrogate." },
  { code := "N4", page := 50, description := "Prove or disprove the restricted O(x^2 log x) estimate with one global optimizer across all blocks and the signed prime-power response retained." },
  { code := "M1", page := 51, description := "Attack the explicit innovation sum using growing-prime interaction; fixed-prime asymptotic independence is insufficient." },
  { code := "M2", page := 51, description := "Test block spectral gaps only at the critical cover scale T^2." },
  { code := "M3", page := 51, description := "Seek a scale-dependent or non-product blocking law with elementary predictable mean and a non-rare coherent Moebius path." },
  { code := "C1", page := 51, description := "Attack the first prime window as a compact variational problem." },
  { code := "C2", page := 51, description := "Prove or disprove the two-polar-mode negative-index bound and compute the sign of the reduced matrix." },
  { code := "C3", page := 51, description := "Construct an analytic-realization functor from the F1 sheaf to the local Hilbert datum." },
  { code := "C4", page := 51, description := "Glue local complexes into a support-adaptive semilocal Hilbert complex." },
  { code := "C5", page := 51, description := "Construct a globally truncated adelic/Eisenstein complex and prove a common relative-Fredholm or Maass-Selberg trace formula." },
  { code := "C6", page := 51, description := "Add the archimedean gamma complex and polar terms with a common phase normalization." },
  { code := "C7", page := 51, description := "Construct the positive semilocal projection, prove trace class, and compute the trace geometrically without using zeros." },
  { code := "C8", page := 51, description := "Prove compatibility as the cutoff varies and density of the test algebra in the full Weil criterion class." }
]

inductive AgendaUpdateStatus where
  | materiallyReduced
  | reformulatedOpen
  | openWithCandidateEvidence
  | unchangedOpen
  deriving Repr, DecidableEq

structure AgendaSourceStatus where
  code : String
  reportPage : Option Nat
  status : AgendaUpdateStatus
  description : String
  deriving Repr, DecidableEq

/-- Source-qualified updates to all fifteen entries of researchAgenda.
A missing report page means that the new report does not separately reassess
that agenda item. These are report statuses, not project verification claims. -/
def revisedAgendaSourceStatuses : Array AgendaSourceStatus := #[
  { code := "N1", reportPage := some 7, status := .materiallyReduced
    description := "The activated-atom collapse and exact return energy are recorded as supplied; remaining range and asymptotic obligations are not closed." },
  { code := "N2", reportPage := none, status := .unchangedOpen
    description := "The polynomial conductor restriction issue is not resolved by this report." },
  { code := "N3", reportPage := some 7, status := .materiallyReduced
    description := "The actual-signal spectral formulation is recorded as supplied; an all-directions surrogate is still excluded." },
  { code := "N4", reportPage := some 5, status := .reformulatedOpen
    description := "Research target 5.1 and R1-R2 replace this by the actual innovation sum plus the boundary gluing term." },
  { code := "M1", reportPage := some 5, status := .reformulatedOpen
    description := "An explicit scalar growing-prime innovation object is supplied, while its arithmetic little-o estimate remains open." },
  { code := "M2", reportPage := none, status := .unchangedOpen
    description := "The critical-cover-scale spectral-gap task is not settled." },
  { code := "M3", reportPage := none, status := .unchangedOpen
    description := "No scale-dependent or non-product blocking law is established." },
  { code := "C1", reportPage := some 7, status := .openWithCandidateEvidence
    description := "The second log 3 interval implementation supplies candidate evidence only; the compact variational target remains open." },
  { code := "C2", reportPage := some 7, status := .openWithCandidateEvidence
    description := "Rank-one reduction and parity computations supply candidate evidence only; the general two-polar-mode index target remains open." },
  { code := "C3", reportPage := some 8, status := .unchangedOpen
    description := "The analytic-realization construction remains part of the global Selberg-Connes work." },
  { code := "C4", reportPage := some 8, status := .unchangedOpen
    description := "The support-adaptive semilocal gluing construction remains open." },
  { code := "C5", reportPage := some 8, status := .unchangedOpen
    description := "The global truncated complex and common trace formula remain open." },
  { code := "C6", reportPage := some 8, status := .unchangedOpen
    description := "The common archimedean and polar normalization remains open." },
  { code := "C7", reportPage := some 8, status := .unchangedOpen
    description := "The positive semilocal projection, trace-class result, and zero-independent geometric trace remain open." },
  { code := "C8", reportPage := none, status := .unchangedOpen
    description := "Cutoff compatibility and density in the full Weil criterion class remain open." }
]

inductive ArchiveImportDisposition where
  | canonical | mergedDuplicate | replacedAggregator | metadata
  deriving Repr, DecidableEq

structure ArchiveSource where
  path : String
  disposition : ArchiveImportDisposition
  canonicalModule : String
  deriving Repr, DecidableEq

/-- Complete disposition ledger for every Lean source supplied by the archive.
Duplicate candidates are represented by repaired canonical modules rather than
redeclared under colliding names. -/
def archiveSources : Array ArchiveSource := #[
  { path := "RiemannResearch/CombinedAudited/BooleanSigns.lean",
    disposition := .canonical,
    canonicalModule := "RiemannResearch.RH.CombinedAudited.BooleanSigns" },
  { path := "RiemannResearch/CombinedAudited/CriticalLine.lean",
    disposition := .canonical,
    canonicalModule := "RiemannResearch.RH.CombinedAudited.CriticalLine" },
  { path := "RiemannResearch/CombinedAudited/LimitsPositivity.lean",
    disposition := .canonical,
    canonicalModule := "RiemannResearch.RH.CombinedAudited.LimitsPositivity" },
  { path := "RiemannResearch/CombinedAudited/MorseIndex.lean",
    disposition := .canonical,
    canonicalModule := "RiemannResearch.RH.CombinedAudited.MorseIndex" },
  { path := "RiemannResearch/CombinedAudited/NormContraction.lean",
    disposition := .canonical,
    canonicalModule := "RiemannResearch.RH.CombinedAudited.NormContraction" },
  { path := "RiemannResearch/CombinedAudited/RawCountReciprocal.lean",
    disposition := .canonical,
    canonicalModule := "RiemannResearch.RH.CombinedAudited.RawCountReciprocal" },
  { path := "RiemannResearch/CombinedAudited/ScalarCounterterm.lean",
    disposition := .canonical,
    canonicalModule := "RiemannResearch.RH.CombinedAudited.ScalarCounterterm" },
  { path := "RiemannResearch/CombinedAudited/ScalarSchur.lean",
    disposition := .canonical,
    canonicalModule := "RiemannResearch.RH.CombinedAudited.ScalarSchur" },
  { path := "RiemannResearch/CombinedAudited/SourceClaimIndex.lean",
    disposition := .canonical,
    canonicalModule := "RiemannResearch.RH.CombinedAudited.SourceClaimIndex" },
  { path := "RiemannResearch/CombinedAudited/TwoPolarModes.lean",
    disposition := .canonical,
    canonicalModule := "RiemannResearch.RH.CombinedAudited.TwoPolarModes" },
  { path := "RiemannResearch/CombinedAudited/WeightedPythagoras.lean",
    disposition := .canonical,
    canonicalModule := "RiemannResearch.RH.CombinedAudited.WeightedPythagoras" },
  { path := "unverified_candidates/FiniteCore.lean",
    disposition := .mergedDuplicate,
    canonicalModule := "the nine corresponding split finite-core modules" },
  { path := "unverified_candidates/OpenTargets.lean",
    disposition := .canonical,
    canonicalModule := "RiemannResearch.RH.CombinedAudited.OpenTargets" },
  { path := "unverified_candidates/Conjectures.lean",
    disposition := .mergedDuplicate,
    canonicalModule := "RiemannResearch.RH.CombinedAudited.OpenTargets" },
  { path := "RiemannResearch/CombinedAudited.lean",
    disposition := .replacedAggregator,
    canonicalModule := "RiemannResearch.RH.CombinedAudited" },
  { path := "CombinedAuditedManuscript.lean",
    disposition := .replacedAggregator,
    canonicalModule := "RiemannResearch.RH.CombinedAudited" }
]

@[simp] theorem sourceClaims_size : sourceClaims.size = 0 := rfl

@[simp] theorem progressReportClaims_size :
    progressReportClaims.size = 9 := rfl

@[simp] theorem progressReportLeanDispositions_size :
    progressReportLeanDispositions.size = 9 := rfl

@[simp] theorem progressReportStatuses_size :
    progressReportStatuses.size = 11 := rfl

@[simp] theorem researchAgenda_size : researchAgenda.size = 15 := rfl

@[simp] theorem revisedAgendaSourceStatuses_size :
    revisedAgendaSourceStatuses.size = 15 := rfl

@[simp] theorem archiveSources_size : archiveSources.size = 16 := rfl

end RiemannResearch.RH.CombinedAudited

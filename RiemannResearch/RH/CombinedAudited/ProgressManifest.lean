/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Init

/-!
# RH progress-package SHA-256 manifest

This module faithfully records the user-supplied
`rh_irreducible_targets_progress_2026-09-03.sha256` file and the SHA-256
computed for the separately supplied Lean archive. The five manifest payloads
were absent from this continuation, so their contents are not claimed to have
been imported or checked.
-/

namespace RiemannResearch.RH.CombinedAudited

set_option linter.style.longLine false

structure DigestEntry where
  sha256 : String
  fileName : String
  deriving Repr, DecidableEq

/-- The five digest lines in the supplied progress manifest. -/
def expectedUpdatedArtifacts : Array DigestEntry := #[
  { sha256 := "b2fdd659dac83aa92aeda527c01a0df7cdc5df15ab51ba905d56b9bbabaf6b98",
    fileName := "rh_irreducible_targets_progress_2026-09-03.pdf" },
  { sha256 := "1e5512fb8cc97fea3925de3fec481cfd43f6d0ab782280c8d8758bbc99ebfa5b",
    fileName := "rh_irreducible_targets_progress_2026-09-03.tex" },
  { sha256 := "08fea7dba06b7836b67598a559d7382f4e2618280d0f0b2d37609d32a74b89cd",
    fileName := "prime_gap_curvature.py" },
  { sha256 := "6489005d4b2f4efc338a9cf14140c59cba7fb1a61961cb6ec32340c640791f77",
    fileName := "rh_log3_second_interval_verifier.py" },
  { sha256 := "443ec212dfb2d6e23ee3687c5ffddcbafb80b973e5a48dd4206635aab34188eb",
    fileName := "rh_irreducible_targets_progress_package_2026-09-03.zip" }
]

/-- Digest computed for the independently supplied source archive. It is not
one of the five entries in `expectedUpdatedArtifacts`. -/
def suppliedLeanArchive : DigestEntry :=
  { sha256 := "7921d9027562a661f6beaa5e73cef3295aa547d1069068e2fb4c054231f8dff5",
    fileName := "combined_audited_lean_sources.zip" }

/-- Status strings bundled with the Lean archive before the present repair. -/
def archiveReportedStatuses : Array (String × String) := #[
  ("build_status.txt", "NO_MATHLIB_PROJECT_FOUND"),
  ("extra_module_status.tsv", "MorseIndex: NO_PROJECT"),
  ("final_aggregator_status.txt", "NO_PROJECT"),
  ("git_integration_status.txt", "NO_LOCAL_GIT_REPOSITORY"),
  ("git_sync_status.txt", "NO_LOCAL_GIT_REPOSITORY"),
  ("module_status.tsv", "environment: NO_MATHLIB_PROJECT; MorseIndex: NO_PROJECT; SourceClaimIndex: NO_PROJECT"),
  ("open_targets_status.txt", "NO_PROJECT"),
  ("source_inventory_status.txt", "SOURCE_NOT_FOUND"),
  ("standalone_verify_status.tsv", "environment: UNAVAILABLE lean= mathlib=")
]

@[simp] theorem expectedUpdatedArtifacts_size :
    expectedUpdatedArtifacts.size = 5 := rfl

@[simp] theorem archiveReportedStatuses_size :
    archiveReportedStatuses.size = 9 := rfl

end RiemannResearch.RH.CombinedAudited

/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Init

/-!
# RH progress-package SHA-256 manifest

This module records the earlier five-entry manifest, the exact nine-member
progress package received on 3 September 2026, and the separately supplied
Lean archive. The package archive matches the digest named by the earlier
manifest. The PDF, TEX source, and two Python members also match their earlier
manifest digests; the remaining five member digests were computed directly
from the received archive. These records establish byte identity and receipt
only; they do not upgrade any mathematical or numerical statement.
-/

namespace RiemannResearch.RH.CombinedAudited

set_option linter.style.longLine false

structure DigestEntry where
  sha256 : String
  fileName : String
  deriving Repr, DecidableEq

/-- The five digest lines in the earlier progress manifest; all named payloads
are now received, and their verification is recorded below. -/
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

inductive ReceiptVerification where
  | receivedAndMatchedManifest
  | receivedAndHashed
  deriving Repr, DecidableEq

structure ArtifactReceipt where
  digest : DigestEntry
  verification : ReceiptVerification
  deriving Repr, DecidableEq

/-- The exact progress package received under the transport filename
rh_irreducible_targets_progress_package_2026-09-03(1).zip. Its bytes match
the canonical package digest recorded in the earlier manifest. -/
def receivedProgressPackage : ArtifactReceipt :=
  { digest :=
      { sha256 := "443ec212dfb2d6e23ee3687c5ffddcbafb80b973e5a48dd4206635aab34188eb"
        fileName := "rh_irreducible_targets_progress_package_2026-09-03.zip" }
    verification := .receivedAndMatchedManifest }

/-- SHA-256 receipts for all nine members of the received progress package.
receivedAndMatchedManifest means that the member digest agrees with the
earlier five-line manifest; receivedAndHashed means that the digest was
computed directly from a package member not named by that manifest. -/
def receivedProgressPackageContents : Array ArtifactReceipt := #[
  { digest :=
      { sha256 := "b2fdd659dac83aa92aeda527c01a0df7cdc5df15ab51ba905d56b9bbabaf6b98"
        fileName := "rh_irreducible_targets_progress_2026-09-03.pdf" }
    verification := .receivedAndMatchedManifest },
  { digest :=
      { sha256 := "1e5512fb8cc97fea3925de3fec481cfd43f6d0ab782280c8d8758bbc99ebfa5b"
        fileName := "rh_irreducible_targets_progress_2026-09-03.tex" }
    verification := .receivedAndMatchedManifest },
  { digest :=
      { sha256 := "08fea7dba06b7836b67598a559d7382f4e2618280d0f0b2d37609d32a74b89cd"
        fileName := "prime_gap_curvature.py" }
    verification := .receivedAndMatchedManifest },
  { digest :=
      { sha256 := "573fd7aa42940595d2899ee202bcf05ef69cd9fabf9b7122084054d8306c7f1f"
        fileName := "prime_gap_curvature_output.txt" }
    verification := .receivedAndHashed },
  { digest :=
      { sha256 := "6489005d4b2f4efc338a9cf14140c59cba7fb1a61961cb6ec32340c640791f77"
        fileName := "rh_log3_second_interval_verifier.py" }
    verification := .receivedAndMatchedManifest },
  { digest :=
      { sha256 := "69e7730ee4db75cf96cb798dd308db40cbdf2ebc56e8d93e3b48d5e623b97864"
        fileName := "rh_log3_second_interval_output.txt" }
    verification := .receivedAndHashed },
  { digest :=
      { sha256 := "9dcbd686892fdb6732231f54ec61f6c6d9a9acfdaaca3e588adc5fff4b99d95e"
        fileName := "rh_log3_second_interval_robustness_output.txt" }
    verification := .receivedAndHashed },
  { digest :=
      { sha256 := "31bc9dfa2c7e63d927796b5f2489bfa11a0de28aecb1920978202d2dc54810c2"
        fileName := "requirements_rh_log3_second_interval.txt" }
    verification := .receivedAndHashed },
  { digest :=
      { sha256 := "cf6649aeb99ec5801b479f45b6990421d118ef853c2ce66e2a8c03adeda23a92"
        fileName := "README_rh_irreducible_targets_progress_2026-09-03.md" }
    verification := .receivedAndHashed }
]

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

@[simp] theorem receivedProgressPackageContents_size :
    receivedProgressPackageContents.size = 9 := rfl

@[simp] theorem archiveReportedStatuses_size :
    archiveReportedStatuses.size = 9 := rfl

end RiemannResearch.RH.CombinedAudited

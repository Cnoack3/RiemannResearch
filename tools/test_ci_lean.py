"""Exercise CI classification with actual Git changes and unusual filenames."""

import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import ci_lean


class CIClassificationTests(unittest.TestCase):
    def test_unknown_and_mixed_inputs_require_lean(self):
        for paths in ([], ["README.md", "RiemannResearch/Test.lean"], ["lakefile.toml"], ["lean-toolchain"], ["unknown.pdf"], ["tools/readme.md"], [".github/README.md"], ["AGENTS.md"], ["RiemannResearch/RH/AGENTS.md"]):
            with self.subTest(paths=paths):
                self.assertFalse(ci_lean.documentation_only(paths))

    def test_unusual_prose_names_are_safe(self):
        self.assertTrue(ci_lean.documentation_only(["RiemannResearch/a\n b.md", "README.rst"]))

    def test_main_manual_and_invalid_base_do_not_skip(self):
        self.assertTrue(ci_lean.classify("push", "a" * 40)[0])
        self.assertTrue(ci_lean.classify("workflow_dispatch", "a" * 40)[0])
        self.assertTrue(ci_lean.classify("pull_request", "$(false)")[0])

    def test_actual_git_changes_deleted_lean_and_empty_diff(self):
        with tempfile.TemporaryDirectory() as directory:
            previous = Path.cwd()
            try:
                os.chdir(directory)
                def run(*args):
                    return subprocess.check_output(["git", *args], stderr=subprocess.DEVNULL, text=True).strip()
                run("init", "-q")
                run("config", "user.email", "ci-test@example.invalid")
                run("config", "user.name", "CI Test")
                Path("Proof.lean").write_text("example : True := True.intro\n")
                run("add", ".")
                run("commit", "-qm", "base")
                base = run("rev-parse", "HEAD")
                proof_hash = ci_lean.source_digest()
                self.assertTrue(ci_lean.classify("pull_request", base)[0])
                Path("a\n b.md").write_text("notes\n")
                run("add", ".")
                run("commit", "-qm", "notes")
                required, reason, paths = ci_lean.classify("pull_request", base)
                self.assertFalse(required)
                self.assertEqual(paths, ["a\n b.md"])
                self.assertEqual(reason, "documentation-only PR")
                self.assertEqual(ci_lean.source_digest(), proof_hash)
                Path("Proof.lean").rename("Proof.md")
                run("add", "-A")
                run("commit", "-qm", "rename proof to prose")
                required, _, paths = ci_lean.classify("pull_request", base)
                self.assertTrue(required)
                self.assertIn("Proof.lean", paths)
                self.assertNotEqual(ci_lean.source_digest(), proof_hash)
                Path("Proof.md").rename("Proof.lean")
                run("add", "-A")
                run("commit", "-qm", "restore proof path")
                Path("Proof.lean").unlink()
                run("add", "-u")
                run("commit", "-qm", "remove proof")
                self.assertTrue(ci_lean.classify("pull_request", base)[0])
            finally:
                os.chdir(previous)

    def test_failed_comparison_requires_lean(self):
        with patch("ci_lean.subprocess.check_output", side_effect=subprocess.CalledProcessError(1, "git")):
            self.assertTrue(ci_lean.classify("pull_request", "a" * 40)[0])

    def test_receipt_never_promotes_failed_skipped_or_cancelled(self):
        with tempfile.TemporaryDirectory() as directory:
            previous = Path.cwd()
            try:
                os.chdir(directory)
                Path("lean-toolchain").write_text("pinned\n")
                for required, outcome in ((required, outcome) for required in ("true", "false") for outcome in ("failure", "skipped", "cancelled", "success")):
                    with self.subTest(required=required, outcome=outcome), patch.dict(os.environ, {"RUNNER_TEMP": directory, "GITHUB_STEP_SUMMARY": str(Path(directory) / "summary"), "CI_LEAN_OUTCOME": outcome, "CI_LEAN_REQUIRED": required}, clear=True), patch("ci_lean.git", return_value="a" * 40), patch("builtins.print"):
                        ci_lean.receipt_step()
                        receipt = json.loads(Path("lean-ci-receipt.json").read_text())
                        self.assertEqual(receipt["lean_verified"], required == "true" and outcome == "success")
                        self.assertEqual(receipt["input_sha256"]["lean-toolchain"], ci_lean.hash_file("lean-toolchain"))
            finally:
                os.chdir(previous)

    def test_failed_classification_is_not_reported_as_docs_only(self):
        with tempfile.TemporaryDirectory() as directory:
            previous = Path.cwd()
            try:
                os.chdir(directory)
                Path("lean-toolchain").write_text("pinned\n")
                summary = Path(directory) / "summary"
                with patch.dict(os.environ, {"RUNNER_TEMP": directory, "GITHUB_STEP_SUMMARY": str(summary), "CI_CLASSIFICATION_OUTCOME": "failure", "CI_LEAN_OUTCOME": "skipped"}, clear=True), patch("ci_lean.git", return_value="a" * 40), patch("builtins.print"):
                    ci_lean.receipt_step()
                receipt = json.loads(Path("lean-ci-receipt.json").read_text())
                self.assertIsNone(receipt["lean_required"])
                self.assertFalse(receipt["lean_verified"])
                self.assertNotIn("Documentation-only", summary.read_text())
            finally:
                os.chdir(previous)


if __name__ == "__main__":
    unittest.main()

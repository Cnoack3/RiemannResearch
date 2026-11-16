# Reproducible RH part 2 research evidence

These files accompany `RH_PART2_REVIEW_20261116.md` and its paper ledger.

## Zero-phase diagnostics

Run `python phase_diagnostics.py` in an environment with NumPy. The script locates the saved ordinates beside itself and regenerates `phase_diagnostics.json`. The recorded run used Python 3.12.14, NumPy 2.3.5 and random seed 20261116. Rerunning in that environment matched every saved output value.

The 300 ordinates were supplied by Wolfram's `ZetaZero` at machine precision. A source regeneration expression is `ExportString[N[Im[Table[ZetaZero[k], {k, 300}]]], "RawJSON"]`. The ordinate data and subsequent diagnostics are not interval-certified. No asymptotic conclusion or RH proof follows from the finite samples. `wolfram_exact_checks.json` contains a separate exact rational head-tail example and the n=5 reciprocal-max inverse calculation.

## First-prime interval computation

Run `python test_interval_enclosures.py` for the exact-rational regression checks. Run `python prime_cover_c2_odd_endpoint_repaired.py` for the complete repaired computation; `odd_endpoint_repaired_output.txt` is its retained output. The script also writes `odd_endpoint_interval_witness.json` with full-precision endpoint strings suitable for subsequent exact-rational certificate work. The script uses only the Python standard library. Its four head modes are 1,3,5,7, with J=20 and K=2001.

The original Drive script is preserved at https://drive.google.com/file/d/1HDzIW9Znf9g-ZcE-HuGIB8LKPUphJXFh/view. It contains an interval-enclosure bug. This repaired copy uses exact Decimal sign/absolute-value operations, outward square-root neighbors, interval multiplication in the remaining tail estimate, and an exact-zero-only integral branch.

The numerical assertions are external evidence. The analytic series bounds, off-diagonal tail inequality, operator monotonicity and Schur reduction still require their own proof audit and Lean formalization. Rounded display endpoints in the printed table are not independent certificate inputs; the internal interval objects drive the assertions.

## Provenance and verification

`paper_review_ledger.json` lists all 89 original source items and their import decisions. Available text and TeX hashes identify the actual versions reviewed; normalized-text duplicate labels do not assert identical PDF bytes. `verification_manifest.json` records the final focused Lean check and hashes. The final publication checkpoint is a separate whole-project validation, reported with its terminal commit.

`axiom_guard_snippet.txt` is the exact successful axiom audit. It is retained as text, not as an additional exported Lean module. The main source additions contain 38 theorem declarations; the audit verifies ten principal statements have only the three expected foundational axioms.

Standalone sources and the full axiom audit are preserved in [reproduction_sources.md](reproduction_sources.md).

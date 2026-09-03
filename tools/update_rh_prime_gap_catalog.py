#!/usr/bin/env python3
"""Insert the PrimeGapCurvature declarations into THEOREM_CATALOG.md once."""

from pathlib import Path

CATALOG = Path("RiemannResearch/THEOREM_CATALOG.md")
MARKER = "RiemannResearch.RH.PrimeGapCurvature.adjacentCurvature_affine"
ANCHOR = (
    "| `RiemannResearch.RH.CombinedGain.jointProduct_forces_absoluteScale` | "
    "`RiemannResearch.RH.CombinedGain` | A joint product certificate with capture at most one "
    "still forces an absolute cross-flux lower bound | Kernel checked scale obstruction |"
)
ROWS = """\
| `RiemannResearch.RH.PrimeGapCurvature.adjacentCurvature_affine`, `adjacentCurvature_add_affine`, `curvature_eq_zero_iff_exists_affine_on_range` | `RiemannResearch.RH.PrimeGapCurvature` | Adjacent divided second differences annihilate affine signals, are invariant under affine translation, and have exactly the affine signals as their finite zero-curvature kernel when all adjacent gaps are nonzero | Kernel checked finite-dimensional reduction; the actual arithmetic signal estimate remains open |
| `RiemannResearch.RH.PrimeGapCurvature.tripleDet_eq_gap_mul_gap_mul_slopeDiff`, `consecutiveTripleDet_eq` | `RiemannResearch.RH.PrimeGapCurvature` | Three-point determinants factor through secant-slope differences, with consecutive determinants equal to the product of adjacent gaps and adjacent curvature | Kernel checked exact determinant identities |
| `RiemannResearch.RH.PrimeGapCurvature.bilinearEnergy_decomposition`, `bilinearEnergy_minimum` | `RiemannResearch.RH.PrimeGapCurvature` | A kernel-orthogonal lift has an exact Pythagorean energy decomposition and minimizes every nonnegative symmetric bilinear energy in its constraint fibre | Kernel checked abstract minimum-energy reduction |
| `RiemannResearch.RH.PrimeGapCurvature.twoBlock_schur_identity`, `twoBlock_value_at_mean`, `twoBlock_mean_minimizes` | `RiemannResearch.RH.PrimeGapCurvature` | The common weighted optimizer has the exact two-block Schur gluing penalty and minimizes the combined loss whenever the total weight is positive | Kernel checked exact scalar gluing identity |
| `RiemannResearch.RH.PrimeGapCurvature.bandwidthTwoInnovation_forward`, `bandwidthTwoEnergy_nonneg` | `RiemannResearch.RH.PrimeGapCurvature` | The two-subdiagonal forward recursion solves the innovation equations exactly, and positive pivots make the finite diagonal innovation energy nonnegative | Kernel checked finite recursion; no asymptotic innovation bound is asserted |
| `RiemannResearch.RH.PrimeGapCurvature.signedReturn_mul_rayleigh` | `RiemannResearch.RH.PrimeGapCurvature` | Retains the signed prime-power return decomposition through multiplication by the actual Rayleigh factor | Kernel checked algebraic bookkeeping only |
"""


def main() -> None:
    text = CATALOG.read_text(encoding="utf-8")
    if MARKER in text:
        return
    if ANCHOR not in text:
        raise RuntimeError("the expected CombinedGain catalog anchor was not found")
    CATALOG.write_text(text.replace(ANCHOR, ANCHOR + "\n" + ROWS, 1), encoding="utf-8")


if __name__ == "__main__":
    main()

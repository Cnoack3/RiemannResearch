import RiemannResearch.Analysis.WeightedMellinTopologyTargets
import RiemannResearch.RH.AnnularMellinPoleOrder

/-!
# A local full-zero pole obstructs weighted Mellin membership

Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

The local Mellin identity is explicitly assumed and not inferred from an
identity only in Re(s)>1. Establishing that analytic continuation for the
actual infinite arithmetic signal remains an independent obligation.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis.WeightedMellinTopology
open MeasureTheory.WeightedMellin
open RiemannResearch.RH.AnnularMellin

/-- An analytic Mellin transform agreeing locally with the annular
expression excludes an actual full zero there. -/
theorem zeta_ne_zero_of_Ha_and_local_annular_identity
    {f : ℝ → ℂ} {a : ℝ} {z : ℂ} (hf : Ha a f)
    (ha : a < z.re) (hz : 0 < z.re) (hz1 : z ≠ 1)
    (hidentity : transform f =ᶠ[𝓝 z] meromorphicExpression) :
    riemannZeta z ≠ 0 := by
  have hF : AnalyticAt ℂ (transform f) z :=
    transform_analyticAt hf (by linarith : (2 * a) / 2 < z.re)
  exact (analyticAt_expression_iff_zeta_ne_zero hz hz1).mp (hF.congr hidentity)

theorem not_Ha_of_local_annular_identity_at_zero
    {f : ℝ → ℂ} {a : ℝ} {z : ℂ}
    (ha : a < z.re) (hz : 0 < z.re) (hz1 : z ≠ 1)
    (hzero : riemannZeta z = 0)
    (hidentity : transform f =ᶠ[𝓝 z] meromorphicExpression) :
    ¬ Ha a f := by
  intro hf
  exact zeta_ne_zero_of_Ha_and_local_annular_identity hf ha hz hz1 hidentity hzero

end RiemannResearch.Analysis.WeightedMellinTopology

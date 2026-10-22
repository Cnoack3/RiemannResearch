import RiemannResearch.RH.CountableZetaDetector
import RiemannResearch.RH.SingleZetaDetectorCriterion

/-!
# Fixed zeta detector and conditional tail criteria

Source: RH_Candid_Assessment_Pareto_Green_CRT_2026-09-07.md, sections 1–2;
countable-tilt refinement developed during formalization of the associated chat.
The existing CountableZetaDetector module establishes a nonzero smooth compact
pole-annihilating detector for every actual nontrivial zeta zero. This module
makes one fixed choice and supplies its RH and quantitative zero-free criteria.

Detector existence is established. Tail L² membership, logarithmic remote
support, exact spectral cancellation, and the stated growth bounds remain
explicit conditional research hypotheses. No transform nonvanishing at every
point of the open strip is asserted.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace RiemannResearch.RH

/-- One fixed choice of the actual compact zeta detector. It is independent
of the truncation scale and the subsequently supplied tail family. -/
def fixedZetaDetector : ℝ → ℂ :=
  Classical.choose exists_smooth_compact_actual_zeta_detector

/-- All structural properties of the fixed detector are established. -/
theorem fixedZetaDetector_spec :
    ContDiff ℝ (↑(⊤ : ℕ∞)) fixedZetaDetector ∧
      HasCompactSupport fixedZetaDetector ∧ fixedZetaDetector ≠ 0 ∧
      BilateralLaplace.centeredTransform fixedZetaDetector 0 = 0 ∧
      BilateralLaplace.centeredTransform fixedZetaDetector 1 = 0 ∧
      ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
        BilateralLaplace.centeredTransform fixedZetaDetector s ≠ 0 :=
  by
    obtain ⟨hf, hfc, hfn, hf0, hf1, hd⟩ :=
      Classical.choose_spec exists_smooth_compact_actual_zeta_detector
    exact ⟨hf, hfc, hfn, hf0, hf1, fun s hz h0 h1 => hd s ⟨hz, h0, h1⟩⟩

/-- Conditional research reduction using the established fixed detector.
Open providers: actual tail L² membership, logarithmic remote support, exact
spectral cancellation against this detector, and subpower tail energy.
Detector existence and nonvanishing are no longer assumptions. -/
theorem riemannHypothesis_of_fixed_zeta_detector_subpower_tail
    {τ : ℕ → ℝ → ℂ} {a : ℝ}
    (hLp : ∀ M, MemLp (τ M) 2 volume)
    (hsupport : ∀ M y, y < a + Real.log (M + 1 : ℕ) → τ M y = 0)
    (hsignature : ∀ (M : ℕ) (s : ℂ), riemannZeta s = 0 →
      0 < s.re → s.re < 1 → BilateralLaplace.centeredTransform (τ M) s =
        -BilateralLaplace.centeredTransform fixedZetaDetector s)
    (hgrowth : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun M : ℕ => Real.exp (-ε * Real.log (M + 1 : ℕ)) *
        RemoteLaplaceTail.energy (τ M)) atTop (𝓝 0)) : RiemannHypothesis := by
  exact riemannHypothesis_of_single_zeta_detecting_subpower_tail_test
    hLp hsupport hsignature fixedZetaDetector_spec.2.2.2.2.2 hgrowth

/-- The quantitative zero-free consequence in section 1 of the candid
assessment, expressed as a bound on the actual squared L² norm. The fixed
test is supplied by the proved construction; the power bound remains an
explicit conditional research hypothesis. -/
theorem zeta_ne_zero_of_fixed_detector_power_energy_bound
    {τ : ℕ → ℝ → ℂ} {a θ C : ℝ} (hθ : 0 ≤ θ)
    (hLp : ∀ M, MemLp (τ M) 2 volume)
    (hsupport : ∀ M y, y < a + Real.log (M + 1 : ℕ) → τ M y = 0)
    (hsignature : ∀ (M : ℕ) (s : ℂ), riemannZeta s = 0 →
      0 < s.re → s.re < 1 → BilateralLaplace.centeredTransform (τ M) s =
        -BilateralLaplace.centeredTransform fixedZetaDetector s)
    (hupper : ∀ᶠ M : ℕ in atTop, RemoteLaplaceTail.energy (τ M) ≤
      C * Real.exp ((2 * θ) * Real.log (M + 1 : ℕ)))
    (s : ℂ) (hs1 : s.re < 1) (hsθ : 1 / 2 + θ < s.re) : riemannZeta s ≠ 0 := by
  intro hz
  have hs0 : 0 < s.re := by linarith
  apply fixedZetaDetector_spec.2.2.2.2.2 s hz hs0 hs1
  exact RemoteLaplaceTail.signature_eq_zero_of_supported_power_bound
    (by linarith) hLp hsupport (BilateralLaplace.centeredTransform fixedZetaDetector s)
    (fun M => hsignature M s hz hs0 hs1) (by linarith) hupper

end RiemannResearch.RH

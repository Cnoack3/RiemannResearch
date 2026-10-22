/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualMollifierDensityTransfer
import RiemannResearch.Analysis.ComplexLittlewoodBoundary
import RiemannResearch.Analysis.ActualMollifierRectangleContour
import RiemannResearch.Analysis.ActualMollifierRightBoundary
import RiemannResearch.Analysis.ActualMollifierBoundaryAvoidance
import RiemannResearch.Analysis.ComplexQuadraticDetectorMoments

/-!
# The remaining signed analytic budget and one-point harmonic transfer

Conditional research reduction along Chourasiya--Simonic, arXiv:2507.15184v2,
Theorem 1 and equation (32): https://arxiv.org/html/2507.15184v2.
Littlewood's identity, compatible lifts, detector orders, right-side estimate,
boundary avoidance, exact height-window expansion and asymptotic transfer
are proved. Only the quantitative signed left logarithmic integral plus the
compatible top-minus-bottom argument budget remains an explicit hypothesis.
The finite strict correction D(H,sigma)-J(T,sigma), full original N(T),
reflection, multiplicities and actual signed operators are unchanged.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.InghamMollifier

/-- The automatic right estimate leaves exactly the signed left logarithmic
integral and the signed top-minus-bottom argument integral to control. -/
theorem logRectangleBoundary_le_left_and_arguments {X : ℕ} (hX : 37 ≤ X)
    (B U : ℝ → ℂ) {α H T : ℝ} (hHT : H ≤ T) :
    Complex.logRectangleBoundary (zetaDetector X)
      (fun u => (B u).im) (fun u => (U u).im) α (3 / 2) H T ≤
      (∫ t in H..T, Real.log ‖zetaDetector X ((α : ℂ) + (t : ℂ) * Complex.I)‖) +
      (∫ u in α..(3 / 2), (U u).im) - (∫ u in α..(3 / 2), (B u).im) +
      (T - H) * (-Real.log (1 - 36 / (X : ℝ))) := by
  have hr := zetaDetector_right_signed_log_integral_le_sharp hX hHT
  unfold Complex.logRectangleBoundary
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at ⊢
  linarith

end RiemannResearch.Analysis.InghamMollifier

namespace RiemannResearch.Analysis.ActualZeroOrdinate
open InghamMollifier

/-- A normalized contour identity replaces the earlier Littlewood premise.
The only quantitative premise is the signed left-and-horizontal budget.
The identity itself is supplied by the proved analytic lift construction. -/
theorem densityDifference_le_of_normalizedContour_signedBudget
    {X : ℕ} (hX : 37 ≤ X) {H T α σ F : ℝ} (B U : ℝ → ℂ)
    (hαβ : α ≤ 3 / 2) (hH : 0 < H) (hHT : H ≤ T) (hασ : α < σ)
    (hborder : ∀ s ∈ RectangleBorder
      ((α : ℂ) + (H : ℂ) * Complex.I) (((3 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I),
      zetaDetector X s ≠ 0)
    (hnormalized :
      (RectangleIntegral'
        (fun s => (s - ((α : ℂ) + (H : ℂ) * Complex.I)) * logDeriv (zetaDetector X) s)
        ((α : ℂ) + (H : ℂ) * Complex.I) (((3 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I)).re =
      Complex.logRectangleBoundary (zetaDetector X)
        (fun u => (B u).im) (fun u => (U u).im) α (3 / 2) H T / (2 * Real.pi))
    (hbudget :
      (∫ t in H..T, Real.log ‖zetaDetector X ((α : ℂ) + (t : ℂ) * Complex.I)‖) +
      (∫ u in α..(3 / 2), (U u).im) - (∫ u in α..(3 / 2), (B u).im) ≤
      2 * Real.pi * (σ - α) * F - (T - H) * (-Real.log (1 - 36 / (X : ℝ)))) :
    rightInclusiveCount T σ - rightInclusiveCount H σ ≤ F := by
  apply densityDifference_le_of_detector (show 1 ≤ X by omega) hHT hασ
  have hcontour := detectorLogExcessOnZetaWindow_le_rectangleContour X hαβ
    (show (1 : ℝ) ≤ 3 / 2 by norm_num) hH hHT hborder
  have hboundary : Complex.logRectangleBoundary (zetaDetector X)
      (fun u => (B u).im) (fun u => (U u).im) α (3 / 2) H T ≤
      2 * Real.pi * (σ - α) * F := by
    have hb := logRectangleBoundary_le_left_and_arguments hX B U (α := α) hHT
    linarith
  calc detectorLogExcessOnZetaWindow X H T α ≤
      (RectangleIntegral'
        (fun s => (s - ((α : ℂ) + (H : ℂ) * Complex.I)) * logDeriv (zetaDetector X) s)
        ((α : ℂ) + (H : ℂ) * Complex.I) (((3 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I)).re := hcontour
    _ = Complex.logRectangleBoundary (zetaDetector X)
        (fun u => (B u).im) (fun u => (U u).im) α (3 / 2) H T / (2 * Real.pi) := hnormalized
    _ ≤ (σ - α) * F := (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr (by
      nlinarith [hboundary])

end RiemannResearch.Analysis.ActualZeroOrdinate

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate Zeta23 FiniteHyperbolicHarmonicCap InghamMollifier

/-- The finite-height count and current strict boundary correction remain
visible under the original full Ncount(0,T) normalizer. -/
theorem strictHarmonicBudget_le_of_normalizedContour_signedBudget
    {X : ℕ} (hX : 37 ≤ X) {H T α δ F : ℝ} (d : ℕ) (B U : ℝ → ℂ)
    (hαβ : α ≤ 3 / 2) (hH : 0 < H) (hHT : H ≤ T) (hδ : 0 ≤ δ)
    (hgap : α < 1 / 2 + δ)
    (hborder : ∀ s ∈ RectangleBorder
      ((α : ℂ) + (H : ℂ) * Complex.I) (((3 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I),
      zetaDetector X s ≠ 0)
    (hnormalized :
      (RectangleIntegral'
        (fun s => (s - ((α : ℂ) + (H : ℂ) * Complex.I)) * logDeriv (zetaDetector X) s)
        ((α : ℂ) + (H : ℂ) * Complex.I) (((3 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I)).re =
      Complex.logRectangleBoundary (zetaDetector X)
        (fun u => (B u).im) (fun u => (U u).im) α (3 / 2) H T / (2 * Real.pi))
    (hbudget :
      (∫ t in H..T, Real.log ‖zetaDetector X ((α : ℂ) + (t : ℂ) * Complex.I)‖) +
      (∫ u in α..(3 / 2), (U u).im) - (∫ u in α..(3 / 2), (B u).im) ≤
      2 * Real.pi * (1 / 2 + δ - α) * F - (T - H) * (-Real.log (1 - 36 / (X : ℝ)))) :
    (strictTail T δ / (Ncount 0 T : ℝ)) * harmonicHyperbolicCap d ≤
      (2 * (F + rightInclusiveCount H (1 / 2 + δ) - rightBoundaryCount T (1 / 2 + δ)) /
        (Ncount 0 T : ℝ)) * harmonicHyperbolicCap d :=
  strictHarmonicBudget_le_of_densityDifference T H δ F d hδ
    (densityDifference_le_of_normalizedContour_signedBudget hX B U
      hαβ hH hHT hgap hborder hnormalized hbudget)

end RiemannResearch.Analysis.ActualZeroPhaseMoments



namespace RiemannResearch.Analysis.ActualZeroOrdinate
open InghamMollifier Complex Set

/-- The quantitative obligation left after proving Littlewood and the right side.
It is required only for the signed horizontal integrals belonging to the
proved normalized contour identity. -/
def SignedRectangleBudget (X : ℕ) (α H T σ F : ℝ) : Prop :=
  ∀ B U : ℝ → ℂ, Continuous B → Continuous U →
    (RectangleIntegral'
      (fun s => (s - ((α : ℂ) + (H : ℂ) * I)) * logDeriv (zetaDetector X) s)
      ((α : ℂ) + (H : ℂ) * I) (((3 / 2 : ℝ) : ℂ) + (T : ℂ) * I)).re =
      logRectangleBoundary (zetaDetector X)
        (fun u => (B u).im) (fun u => (U u).im) α (3 / 2) H T / (2 * Real.pi) →
    (∫ t in H..T, Real.log ‖zetaDetector X ((α : ℂ) + (t : ℂ) * I)‖) +
      (∫ u in α..(3 / 2), (U u).im) - (∫ u in α..(3 / 2), (B u).im) ≤
      2 * Real.pi * (σ - α) * F - (T - H) * (-Real.log (1 - 36 / (X : ℝ)))

theorem densityDifference_le_of_signedRectangleBudget
    {X : ℕ} (hX : 37 ≤ X) {H T α σ F : ℝ}
    (hαβ : α ≤ 3 / 2) (hH : 0 < H) (hHT : H ≤ T) (hασ : α < σ)
    (hborder : ∀ s ∈ RectangleBorder
      ((α : ℂ) + (H : ℂ) * I) (((3 / 2 : ℝ) : ℂ) + (T : ℂ) * I), zetaDetector X s ≠ 0)
    (hbudget : SignedRectangleBudget X α H T σ F) :
    rightInclusiveCount T σ - rightInclusiveCount H σ ≤ F := by
  obtain ⟨B, U, hBc, hUc, _, _, hn⟩ :=
    Complex.exists_logRectangleBoundary_eq_contour hαβ hHT
      (zetaDetector_analyticOnNhd_rectangle X hαβ hH hHT) hborder
  exact densityDifference_le_of_normalizedContour_signedBudget hX B U
    hαβ hH hHT hασ hborder hn (hbudget B U hBc hUc hn)

/-- Expanded rectangles preserve the original H subtraction and closed top T. -/
def ExpandedSignedRectangleBudget (X : ℕ) (H T σ F : ℝ) : Prop :=
  ∃ α H' T' : ℝ, α ≤ 3 / 2 ∧ α < σ ∧ 0 < H' ∧ H' ≤ H ∧ T ≤ T' ∧
    (∀ s ∈ RectangleBorder
      ((α : ℂ) + (H' : ℂ) * I) (((3 / 2 : ℝ) : ℂ) + (T' : ℂ) * I), zetaDetector X s ≠ 0) ∧
    SignedRectangleBudget X α H' T' σ F

theorem densityDifference_le_of_expandedSignedRectangleBudget
    {X : ℕ} (hX : 37 ≤ X) {H T σ F : ℝ} (hHT : H ≤ T)
    (hbudget : ExpandedSignedRectangleBudget X H T σ F) :
    rightInclusiveCount T σ - rightInclusiveCount H σ ≤ F := by
  obtain ⟨α, H', T', hαβ, hασ, hH', hH'H, hTT', hborder, hb⟩ := hbudget
  have hHT' : H' ≤ T' := hH'H.trans (hHT.trans hTT')
  have hc := densityDifference_le_of_signedRectangleBudget hX hαβ hH' hHT' hασ hborder hb
  have he := rightInclusiveDifference_le_expandedWindow hH'H hHT hTT' σ
  rw [rightInclusiveWindow_eq_sub hHT'] at he
  exact he.trans hc

end RiemannResearch.Analysis.ActualZeroOrdinate



namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate Zeta23 ZeroDensityRate FiniteHyperbolicHarmonicCap
open Filter

theorem strictHarmonicBudget_le_of_expandedSignedRectangleBudget
    {X : ℕ} (hX : 37 ≤ X) {H T δ F : ℝ} (d : ℕ)
    (hHT : H ≤ T) (hδ : 0 ≤ δ)
    (hbudget : ExpandedSignedRectangleBudget X H T (1 / 2 + δ) F) :
    (strictTail T δ / (Ncount 0 T : ℝ)) * harmonicHyperbolicCap d ≤
      (2 * (F + rightInclusiveCount H (1 / 2 + δ) - rightBoundaryCount T (1 / 2 + δ)) /
        (Ncount 0 T : ℝ)) * harmonicHyperbolicCap d :=
  strictHarmonicBudget_le_of_densityDifference T H δ F d hδ
    (densityDifference_le_of_expandedSignedRectangleBudget hX hHT hbudget)

/-- Conditional research reduction. All branch, contour, right-boundary,
reflection and asymptotic transfers are proved. Only the one-point signed
left-and-horizontal quantitative budget remains a domain hypothesis. -/
theorem shrinking_harmonic_tail_of_expandedSignedRectangleBudget
    (d X : ℝ → ℕ) (ω : ℝ → ℝ) (C η H B₂ B₃ : ℝ)
    (hC : 0 < C) (hη : 0 < η) (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃)
    (hd : ∀ᶠ T : ℝ in atTop, 1 ≤ d T)
    (hsmall : Tendsto (fun T : ℝ => Real.log (d T : ℝ) / Real.log T) atTop (nhds 0))
    (hω : Tendsto ω atTop atTop)
    (hωsmall : Tendsto (fun T : ℝ => ω T / Real.log T) atTop (nhds 0))
    (hX : ∀ᶠ T : ℝ in atTop, 37 ≤ X T)
    (hbudget : ∀ᶠ T : ℝ in atTop,
      let L := Real.log T
      let δ := sourceAdmissibleCutoff T (d T) C (ω T) η
      ExpandedSignedRectangleBudget (X T) H T (1 / 2 + δ)
        ((C * T * L ^ 3) * Real.exp (-(L + Real.log L) * inghamRate δ) + B₂ * L ^ 2 + B₃ * L)) :
    let δ := fun T => sourceAdmissibleCutoff T (d T) C (ω T) η
    Tendsto δ atTop (nhds 0) ∧
      Tendsto (fun T => (strictTail T (δ T) / (Ncount 0 T : ℝ)) *
        harmonicHyperbolicCap (d T)) atTop (nhds 0) ∧
      Tendsto (fun T => actualSignedTailBudget T (d T) (δ T)) atTop (nhds 0) ∧
      Tendsto (fun T => ‖signedBadHyperbolic T (d T) (δ T)‖) atTop (nhds 0) := by
  apply shrinking_harmonic_tail_of_admissibleDifference d ω C η H B₂ B₃
    hC hη hB₂ hB₃ hd hsmall hω hωsmall
  filter_upwards [hX, hbudget, eventually_ge_atTop H] with T hx hb hHT
  exact densityDifference_le_of_expandedSignedRectangleBudget hx hHT hb

end RiemannResearch.Analysis.ActualZeroPhaseMoments


namespace RiemannResearch.Analysis.ActualZeroOrdinate
open InghamMollifier Complex Set

/-- Only the signed left logarithmic and compatible horizontal argument terms
are a quantitative hypothesis. The right side is proved separately. -/
def SignedLeftRectangleBudget (X : ℕ) (α H T σ F : ℝ) : Prop :=
  ∀ B U : ℝ → ℂ, Continuous B → Continuous U →
    (RectangleIntegral'
      (fun s => (s - ((α : ℂ) + (H : ℂ) * I)) * logDeriv (zetaDetector X) s)
      ((α : ℂ) + (H : ℂ) * I) (((3 / 2 : ℝ) : ℂ) + (T : ℂ) * I)).re =
      logRectangleBoundary (zetaDetector X)
        (fun u => (B u).im) (fun u => (U u).im) α (3 / 2) H T / (2 * Real.pi) →
    (∫ t in H..T, Real.log ‖zetaDetector X ((α : ℂ) + (t : ℂ) * I)‖) +
      (∫ u in α..(3 / 2), (U u).im) - (∫ u in α..(3 / 2), (B u).im) ≤
      2 * Real.pi * (σ - α) * F

def ExpandedLeftRectangleBudget (X : ℕ) (H T σ αmax F : ℝ) : Prop :=
  ∃ α H' T' : ℝ, α ≤ 3 / 2 ∧ α ≤ αmax ∧ 0 < H' ∧ H' ≤ H ∧ T ≤ T' ∧ T' ≤ T + 1 ∧
    (∀ s ∈ RectangleBorder
      ((α : ℂ) + (H' : ℂ) * I) (((3 / 2 : ℝ) : ℂ) + (T' : ℂ) * I), zetaDetector X s ≠ 0) ∧
    SignedLeftRectangleBudget X α H' T' σ F

theorem densityDifference_le_of_expandedLeftRectangleBudget
    {X : ℕ} (hX : 37 ≤ X) {H T σ F L η : ℝ}
    (hHT : H ≤ T) (hL : 0 < L) (hη : 0 < η) (hXT : T + 37 ≤ (X : ℝ))
    (hbudget : ExpandedLeftRectangleBudget X H T σ (σ - η / L) F) :
    rightInclusiveCount T σ - rightInclusiveCount H σ ≤ F + 18 * L / (Real.pi * η) := by
  obtain ⟨α, H', T', hαβ, hαmax, hH', hH'H, hTT', hT'T, hborder, hleft⟩ := hbudget
  have hHT' : H' ≤ T' := hH'H.trans (hHT.trans hTT')
  have hgap : η / L ≤ σ - α := by linarith [hαmax]
  have hασ : α < σ := by linarith [div_pos hη hL]
  let E : ℝ := 18 * L / (Real.pi * η)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have heq : 2 * Real.pi * (η / L) * E = 36 := by
    dsimp [E]
    field_simp [Real.pi_ne_zero, hL.ne', hη.ne']
    ring
  have h36 : 36 ≤ 2 * Real.pi * (σ - α) * E := by
    rw [← heq]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgap (by positivity)) hE
  obtain ⟨B, U, hBc, hUc, _, _, hn⟩ :=
    Complex.exists_logRectangleBoundary_eq_contour hαβ hHT'
      (zetaDetector_analyticOnNhd_rectangle X hαβ hH' hHT') hborder
  have hr := zetaDetector_right_signed_log_integral_le_constant hX hHT'
    (show T'-H' ≤ (X : ℝ) - 36 by linarith)
  have hl := hleft B U hBc hUc hn
  have hb : logRectangleBoundary (zetaDetector X)
      (fun u => (B u).im) (fun u => (U u).im) α (3 / 2) H' T' ≤
      2 * Real.pi * (σ - α) * (F + E) := by
    unfold logRectangleBoundary
    norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at ⊢
    nlinarith [hl, hr, h36]
  have hd : detectorLogExcessOnZetaWindow X H' T' α ≤ (σ - α) * (F + E) := by
    have hc := detectorLogExcessOnZetaWindow_le_rectangleContour X hαβ
      (show (1 : ℝ) ≤ 3 / 2 by norm_num) hH' hHT' hborder
    rw [hn] at hc
    exact hc.trans ((div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr (by nlinarith [hb]))
  have hc := densityDifference_le_of_detector (show 1 ≤ X by omega) hHT' hασ hd
  have hw := rightInclusiveDifference_le_expandedWindow hH'H hHT hTT' σ
  rw [rightInclusiveWindow_eq_sub hHT'] at hw
  exact hw.trans hc

end RiemannResearch.Analysis.ActualZeroOrdinate

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate Zeta23 ZeroDensityRate FiniteHyperbolicHarmonicCap Filter

/-- The right boundary is absorbed automatically into B3 log T. Only the
signed left-and-horizontal quantitative provider remains. -/
theorem shrinking_harmonic_tail_of_expandedLeftRectangleBudget
    (d X : ℝ → ℕ) (ω : ℝ → ℝ) (C η H B₂ B₃ : ℝ)
    (hC : 0 < C) (hη : 0 < η) (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃)
    (hd : ∀ᶠ T : ℝ in atTop, 1 ≤ d T)
    (hsmall : Tendsto (fun T : ℝ => Real.log (d T : ℝ) / Real.log T) atTop (nhds 0))
    (hω : Tendsto ω atTop atTop)
    (hωsmall : Tendsto (fun T : ℝ => ω T / Real.log T) atTop (nhds 0))
    (hX : ∀ᶠ T : ℝ in atTop, T + 37 ≤ (X T : ℝ))
    (hbudget : ∀ᶠ T : ℝ in atTop,
      let L := Real.log T
      let δ := sourceAdmissibleCutoff T (d T) C (ω T) η
      ExpandedLeftRectangleBudget (X T) H T (1 / 2 + δ) (1 / 2 + δ - η / L)
        ((C * T * L ^ 3) * Real.exp (-(L + Real.log L) * inghamRate δ) + B₂ * L ^ 2 + B₃ * L)) :
    let δ := fun T => sourceAdmissibleCutoff T (d T) C (ω T) η
    Tendsto δ atTop (nhds 0) ∧
      Tendsto (fun T => (strictTail T (δ T) / (Ncount 0 T : ℝ)) *
        harmonicHyperbolicCap (d T)) atTop (nhds 0) ∧
      Tendsto (fun T => actualSignedTailBudget T (d T) (δ T)) atTop (nhds 0) ∧
      Tendsto (fun T => ‖signedBadHyperbolic T (d T) (δ T)‖) atTop (nhds 0) := by
  apply shrinking_harmonic_tail_of_admissibleDifference d ω C η H B₂
    (B₃ + 18 / (Real.pi * η)) hC hη hB₂ (by positivity) hd hsmall hω hωsmall
  filter_upwards [hX, hbudget, eventually_ge_atTop H, eventually_ge_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_gt_atTop 0] with T hx hb hHT hT hL
  have hx37 : 37 ≤ X T := by
    exact_mod_cast (show (37 : ℝ) ≤ (X T : ℝ) by linarith)
  have hc := densityDifference_le_of_expandedLeftRectangleBudget hx37 hHT hL hη hx hb
  dsimp only at hc ⊢
  convert hc using 1
  ring

end RiemannResearch.Analysis.ActualZeroPhaseMoments

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate Zeta23 ZeroDensityRate FiniteHyperbolicHarmonicCap Filter InghamMollifier

/-- A concrete mollifier cutoff removes even the mollifier-growth premise. -/
theorem shrinking_harmonic_tail_of_leftRectangleBudget
    (d : ℝ → ℕ) (ω : ℝ → ℝ) (C η H B₂ B₃ : ℝ)
    (hC : 0 < C) (hη : 0 < η) (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃)
    (hd : ∀ᶠ T : ℝ in atTop, 1 ≤ d T)
    (hsmall : Tendsto (fun T : ℝ => Real.log (d T : ℝ) / Real.log T) atTop (nhds 0))
    (hω : Tendsto ω atTop atTop)
    (hωsmall : Tendsto (fun T : ℝ => ω T / Real.log T) atTop (nhds 0))
    (hbudget : ∀ᶠ T : ℝ in atTop,
      let L := Real.log T
      let δ := sourceAdmissibleCutoff T (d T) C (ω T) η
      ExpandedLeftRectangleBudget (growingMollifierCutoff T) H T (1 / 2 + δ) (1 / 2 + δ - η / L)
        ((C * T * L ^ 3) * Real.exp (-(L + Real.log L) * inghamRate δ) + B₂ * L ^ 2 + B₃ * L)) :
    let δ := fun T => sourceAdmissibleCutoff T (d T) C (ω T) η
    Tendsto δ atTop (nhds 0) ∧
      Tendsto (fun T => (strictTail T (δ T) / (Ncount 0 T : ℝ)) *
        harmonicHyperbolicCap (d T)) atTop (nhds 0) ∧
      Tendsto (fun T => actualSignedTailBudget T (d T) (δ T)) atTop (nhds 0) ∧
      Tendsto (fun T => ‖signedBadHyperbolic T (d T) (δ T)‖) atTop (nhds 0) :=
  shrinking_harmonic_tail_of_expandedLeftRectangleBudget d growingMollifierCutoff ω C η H B₂ B₃
    hC hη hB₂ hB₃ hd hsmall hω hωsmall
    (Eventually.of_forall growingMollifierCutoff_height) hbudget

end RiemannResearch.Analysis.ActualZeroPhaseMoments

namespace RiemannResearch.Analysis.InghamMollifier
open MeasureTheory

/-- The actual quadratic detector is dominated by every error moment of order
one through two. Interval integrability remains explicit. -/
theorem zetaDetector_left_log_integral_le_moment
    (X : ℕ) {α H T p : ℝ} (hHT : H ≤ T) (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (hlog : IntervalIntegrable (fun t =>
      Real.log ‖zetaDetector X ((α : ℂ) + (t : ℂ) * Complex.I)‖) volume H T)
    (hmoment : IntervalIntegrable (fun t =>
      ‖riemannZeta ((α : ℂ) + (t : ℂ) * Complex.I) *
        mollifier X ((α : ℂ) + (t : ℂ) * Complex.I) - 1‖ ^ p) volume H T) :
    (∫ t in H..T, Real.log ‖zetaDetector X ((α : ℂ) + (t : ℂ) * Complex.I)‖) ≤
      ∫ t in H..T, ‖riemannZeta ((α : ℂ) + (t : ℂ) * Complex.I) *
        mollifier X ((α : ℂ) + (t : ℂ) * Complex.I) - 1‖ ^ p := by
  simp_rw [zetaDetector_eq_one_sub_error_sq] at hlog ⊢
  exact Complex.integral_log_norm_one_sub_sq_le_rpow hHT hp1 hp2 hlog hmoment

end RiemannResearch.Analysis.InghamMollifier

namespace RiemannResearch.Analysis.ActualZeroOrdinate
open InghamMollifier Complex Set MeasureTheory

/-- A concrete norm-power moment and the compatible signed horizontal estimate
supply the remaining budget. This is a conditional research reduction:
the analytic moment and horizontal estimates are not inferred from it. -/
theorem signedLeftRectangleBudget_of_moment_and_horizontal
    (X : ℕ) {α H T σ F p M A : ℝ} (hHT : H ≤ T)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (hlog : IntervalIntegrable (fun t =>
      Real.log ‖zetaDetector X ((α : ℂ) + (t : ℂ) * I)‖) volume H T)
    (hmi : IntervalIntegrable (fun t =>
      ‖riemannZeta ((α : ℂ) + (t : ℂ) * I) *
        mollifier X ((α : ℂ) + (t : ℂ) * I) - 1‖ ^ p) volume H T)
    (hm : (∫ t in H..T, ‖riemannZeta ((α : ℂ) + (t : ℂ) * I) *
        mollifier X ((α : ℂ) + (t : ℂ) * I) - 1‖ ^ p) ≤ M)
    (hhorizontal : ∀ B U : ℝ → ℂ, Continuous B → Continuous U →
      (RectangleIntegral'
        (fun s => (s - ((α : ℂ) + (H : ℂ) * I)) * logDeriv (zetaDetector X) s)
        ((α : ℂ) + (H : ℂ) * I) (((3 / 2 : ℝ) : ℂ) + (T : ℂ) * I)).re =
        logRectangleBoundary (zetaDetector X)
          (fun u => (B u).im) (fun u => (U u).im) α (3 / 2) H T / (2 * Real.pi) →
      (∫ u in α..(3 / 2), (U u).im) - (∫ u in α..(3 / 2), (B u).im) ≤ A)
    (hMA : M + A ≤ 2 * Real.pi * (σ - α) * F) :
    SignedLeftRectangleBudget X α H T σ F := by
  intro B U hBc hUc hn
  have hl := (zetaDetector_left_log_integral_le_moment X hHT hp1 hp2 hlog hmi).trans hm
  have hh := hhorizontal B U hBc hUc hn
  linarith

/-- Exact logarithmic right-side cost for any X>=37, with the original
closed top T and finite-height subtraction. No X>=T+37 premise is needed. -/
theorem densityDifference_le_of_expandedLeftRectangleBudget_sharpRight
    {X : ℕ} (hX : 37 ≤ X) {H T σ F L η : ℝ}
    (hHT : H ≤ T) (hL : 0 < L) (hη : 0 < η)
    (hbudget : ExpandedLeftRectangleBudget X H T σ (σ - η / L) F) :
    rightInclusiveCount T σ - rightInclusiveCount H σ ≤
      F + (T + 1) * (-Real.log (1 - 36 / (X : ℝ))) * L / (2 * Real.pi * η) := by
  obtain ⟨α, H', T', hαβ, hαmax, hH', hH'H, hTT', hT'T, hborder, hleft⟩ := hbudget
  have hHT' : H' ≤ T' := hH'H.trans (hHT.trans hTT')
  have hgap : η / L ≤ σ - α := by linarith
  have hασ : α < σ := by linarith [div_pos hη hL]
  have hXp : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hx36 : (36 : ℝ) < (X : ℝ) := by exact_mod_cast (show 36 < X by omega)
  have hbase : 0 < 1 - 36 / (X : ℝ) := by
    have hh := (div_lt_one hXp).mpr hx36
    linarith
  let q : ℝ := -Real.log (1 - 36 / (X : ℝ))
  have hq : 0 ≤ q := by
    dsimp [q]
    apply neg_nonneg.mpr
    have hh := Real.log_le_log hbase (show 1 - 36 / (X : ℝ) ≤ 1 by
      linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 36) hXp.le])
    simpa using hh
  have hT1 : 0 ≤ T + 1 := by linarith
  let E : ℝ := (T + 1) * q * L / (2 * Real.pi * η)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have heq : 2 * Real.pi * (η / L) * E = (T + 1) * q := by
    dsimp [E]
    field_simp [Real.pi_ne_zero, hL.ne', hη.ne']
  have hcost : (T' - H') * q ≤ 2 * Real.pi * (σ - α) * E := by
    calc
      (T' - H') * q ≤ (T + 1) * q :=
        mul_le_mul_of_nonneg_right (by linarith) hq
      _ = 2 * Real.pi * (η / L) * E := heq.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hgap (by positivity)) hE
  obtain ⟨B, U, hBc, hUc, _, _, hn⟩ :=
    Complex.exists_logRectangleBoundary_eq_contour hαβ hHT'
      (zetaDetector_analyticOnNhd_rectangle X hαβ hH' hHT') hborder
  have hl := hleft B U hBc hUc hn
  have hb :
      (∫ t in H'..T', Real.log ‖zetaDetector X ((α : ℂ) + (t : ℂ) * I)‖) +
      (∫ u in α..(3 / 2), (U u).im) - (∫ u in α..(3 / 2), (B u).im) ≤
      2 * Real.pi * (σ - α) * (F + E) -
        (T' - H') * (-Real.log (1 - 36 / (X : ℝ))) := by
    change _ ≤ 2 * Real.pi * (σ - α) * (F + E) - (T' - H') * q
    nlinarith [hl, hcost]
  have hc := densityDifference_le_of_normalizedContour_signedBudget hX B U
    hαβ hH' hHT' hασ hborder hn hb
  have hw := rightInclusiveDifference_le_expandedWindow hH'H hHT hTT' σ
  rw [rightInclusiveWindow_eq_sub hHT'] at hw
  exact hw.trans hc

end RiemannResearch.Analysis.ActualZeroOrdinate

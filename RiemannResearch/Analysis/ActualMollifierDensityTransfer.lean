/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroDensityLogExcess
import RiemannResearch.Analysis.ComplexLogRectangleBoundary
import RiemannResearch.Analysis.ActualHyperbolicShrinkingTail

/-!
# Actual mollifier density transfer to the complete signed harmonic budget

These are conditional research reductions along Chourasiya--Simonic,
arXiv:2507.15184v2, Theorem 1 and equation (32):
https://arxiv.org/html/2507.15184v2.
The exact finite weighted identities, orders, reflection, strict-mask
boundary correction, original full N(T), fixed-height remainder decay and
harmonic transfer are proved. The one-point detector estimate remains an
explicit analytic premise. The rectangle consumers further expose both the
Littlewood and full signed boundary estimates; compatible argument lifts,
boundary-zero treatment and moment estimates have not been imported as axioms.
The admissible consumer uses a proved left line strictly above 1/2.
All signed hyperbolic channels and composite interactions survive through the
unchanged actual operators.
-/

noncomputable section
open Filter
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualZeroOrdinate
open InghamMollifier
theorem rightInclusiveWindow_le_of_detector {X : ℕ} (hX : 1 ≤ X)
    {H T α σ F : ℝ} (hασ : α < σ)
    (hdet : detectorLogExcessOnZetaWindow X H T α ≤ (σ-α)*F) :
    rightInclusiveWindow H T σ ≤ F :=
  rightInclusiveWindow_le_of_logExcess hασ
    ((rightLogExcessWindow_le_detector X hX H T α).trans hdet)

theorem densityDifference_le_of_detector {X : ℕ} (hX : 1 ≤ X)
    {H T α σ F : ℝ} (hHT : H ≤ T) (hασ : α < σ)
    (hdet : detectorLogExcessOnZetaWindow X H T α ≤ (σ-α)*F) :
    rightInclusiveCount T σ-rightInclusiveCount H σ ≤ F := by
  rw [← rightInclusiveWindow_eq_sub hHT σ]
  exact rightInclusiveWindow_le_of_detector hX hασ hdet

/-- Conditional Littlewood consumer. hLittlewood concerns the actual detector,
including analytic orders; hboundary controls its full signed functional. -/
theorem densityDifference_le_of_logRectangle {X : ℕ} (hX : 1 ≤ X)
    {H T α β σ F : ℝ} {aH aT : ℝ → ℝ} (hHT : H ≤ T) (hασ : α < σ)
    (hLittlewood : detectorLogExcessOnZetaWindow X H T α ≤
      Complex.logRectangleBoundary (zetaDetector X) aH aT α β H T/(2*Real.pi))
    (hboundary : Complex.logRectangleBoundary (zetaDetector X) aH aT α β H T ≤
      2*Real.pi*(σ-α)*F) :
    rightInclusiveCount T σ-rightInclusiveCount H σ ≤ F := by
  apply densityDifference_le_of_detector hX hHT hασ
  have hpi : 0 < 2*Real.pi := by positivity
  exact hLittlewood.trans ((div_le_iff₀ hpi).mpr (by nlinarith [hboundary]))

/-- Full finite-rectangle version: all extra detector contributions are handled
by the proved exact finite-set split, rather than an equality of zero sets. -/
theorem densityDifference_le_of_finiteLogRectangle {X : ℕ} (hX : 1 ≤ X)
    {D : Finset ℂ} {H T α β σ F : ℝ} {aH aT : ℝ → ℝ}
    (hD : activeLogExcessWindow H T α ⊆ D) (hHT : H ≤ T) (hασ : α < σ)
    (hLittlewood : detectorLogExcessFinite X D α ≤
      Complex.logRectangleBoundary (zetaDetector X) aH aT α β H T/(2*Real.pi))
    (hboundary : Complex.logRectangleBoundary (zetaDetector X) aH aT α β H T ≤
      2*Real.pi*(σ-α)*F) :
    rightInclusiveCount T σ-rightInclusiveCount H σ ≤ F :=
  densityDifference_le_of_logRectangle hX hHT hασ
    ((detectorLogExcessOnZetaWindow_le_finite X D H T α hD).trans hLittlewood) hboundary

end RiemannResearch.Analysis.ActualZeroOrdinate

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate Zeta23 ZeroDensityRate FiniteHyperbolicHarmonicCap InghamMollifier
theorem strictHarmonicBudget_le_of_detector {X : ℕ} (hX : 1 ≤ X)
    {H T α δ F : ℝ} (d : ℕ) (hHT : H ≤ T) (hδ : 0 ≤ δ)
    (hgap : α < 1/2+δ)
    (hdet : detectorLogExcessOnZetaWindow X H T α ≤ (1/2+δ-α)*F) :
    (strictTail T δ/(Ncount 0 T : ℝ))*harmonicHyperbolicCap d ≤
      (2*(F+rightInclusiveCount H (1/2+δ)-rightBoundaryCount T (1/2+δ))/
        (Ncount 0 T : ℝ))*harmonicHyperbolicCap d :=
  strictHarmonicBudget_le_of_densityDifference T H δ F d hδ
    (densityDifference_le_of_detector hX hHT hgap hdet)

/-- Only one weighted detector point is needed, at an explicitly chosen left
line below the source count cutoff. This is a conditional research reduction. -/
theorem shrinking_harmonic_tail_of_detector
    (d : ℝ → ℕ) (X : ℝ → ℕ) (α ω : ℝ → ℝ) (C H B₂ B₃ : ℝ)
    (hC : 0 < C) (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃)
    (hd : ∀ᶠ T : ℝ in atTop, 1 ≤ d T)
    (hsmall : Tendsto (fun T : ℝ => Real.log (d T : ℝ)/Real.log T) atTop (nhds 0))
    (hω : Tendsto ω atTop atTop)
    (hωsmall : Tendsto (fun T : ℝ => ω T/Real.log T) atTop (nhds 0))
    (hX : ∀ᶠ T : ℝ in atTop, 1 ≤ X T)
    (hgap : ∀ᶠ T : ℝ in atTop, α T < 1/2+sourceCountCutoff T (d T) C (ω T))
    (hdet : ∀ᶠ T : ℝ in atTop,
      let L := Real.log T
      let δ := sourceCountCutoff T (d T) C (ω T)
      detectorLogExcessOnZetaWindow (X T) H T (α T) ≤
        (1/2+δ-α T)*((C*T*L^3)*Real.exp (-(L+Real.log L)*inghamRate δ)+
          B₂*L^2+B₃*L)) :
    let δ := fun T => sourceCountCutoff T (d T) C (ω T)
    Tendsto δ atTop (nhds 0) ∧
      Tendsto (fun T => (strictTail T (δ T)/(Ncount 0 T : ℝ))*
        harmonicHyperbolicCap (d T)) atTop (nhds 0) ∧
      Tendsto (fun T => actualSignedTailBudget T (d T) (δ T)) atTop (nhds 0) ∧
      Tendsto (fun T => ‖signedBadHyperbolic T (d T) (δ T)‖) atTop (nhds 0) := by
  apply shrinking_harmonic_tail_of_sourceDifference d ω C H B₂ B₃
    hC hB₂ hB₃ hd hsmall hω hωsmall
  filter_upwards [hX, hgap, hdet, eventually_ge_atTop H] with T hx hg ht hHT
  exact densityDifference_le_of_detector hx hHT hg ht
end RiemannResearch.Analysis.ActualZeroPhaseMoments

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate Zeta23 ZeroDensityRate FiniteHyperbolicHarmonicCap
/-- The canonical source left line is strictly to the right of 1/2, and all
counting and inverse-rate transfer is proved around one detector estimate. -/
theorem shrinking_harmonic_tail_of_admissibleDetector
    (d X : ℝ → ℕ) (ω : ℝ → ℝ) (C η H B₂ B₃ : ℝ)
    (hC : 0 < C) (hη : 0 < η) (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃)
    (hd : ∀ᶠ T : ℝ in atTop, 1 ≤ d T)
    (hsmall : Tendsto (fun T : ℝ => Real.log (d T : ℝ)/Real.log T) atTop (nhds 0))
    (hω : Tendsto ω atTop atTop)
    (hωsmall : Tendsto (fun T : ℝ => ω T/Real.log T) atTop (nhds 0))
    (hX : ∀ᶠ T : ℝ in atTop, 1 ≤ X T)
    (hdet : ∀ᶠ T : ℝ in atTop,
      let L := Real.log T
      let δ := sourceAdmissibleCutoff T (d T) C (ω T) η
      let α := 1/2+δ-η/L
      detectorLogExcessOnZetaWindow (X T) H T α ≤
        (η/L)*((C*T*L^3)*Real.exp (-(L+Real.log L)*inghamRate δ)+
          B₂*L^2+B₃*L)) :
    let δ := fun T => sourceAdmissibleCutoff T (d T) C (ω T) η
    Tendsto δ atTop (nhds 0) ∧
      Tendsto (fun T => (strictTail T (δ T)/(Ncount 0 T : ℝ))*
        harmonicHyperbolicCap (d T)) atTop (nhds 0) ∧
      Tendsto (fun T => actualSignedTailBudget T (d T) (δ T)) atTop (nhds 0) ∧
      Tendsto (fun T => ‖signedBadHyperbolic T (d T) (δ T)‖) atTop (nhds 0) := by
  apply shrinking_harmonic_tail_of_admissibleDifference d ω C η H B₂ B₃
    hC hη hB₂ hB₃ hd hsmall hω hωsmall
  filter_upwards [hX, hdet, eventually_ge_atTop H,
    Real.tendsto_log_atTop.eventually_gt_atTop 0] with T hx ht hHT hL
  let δ := sourceAdmissibleCutoff T (d T) C (ω T) η
  let α := 1/2+δ-η/Real.log T
  have hg : α < 1/2+δ :=
    (sourceAdmissibleCutoff_leftLine (d T) hη hL).2
  apply densityDifference_le_of_detector hx hHT hg
  dsimp only at ht ⊢
  convert ht using 1
  ring
end RiemannResearch.Analysis.ActualZeroPhaseMoments

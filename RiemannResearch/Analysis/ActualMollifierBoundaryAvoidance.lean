/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ComplexRectangleZeroCount
import RiemannResearch.Analysis.ActualMollifierRectangleContour
import RiemannResearch.Analysis.ActualMollifierRightBoundary
import RiemannResearch.Analysis.ActualZeroDensityWindow

/-!
# Actual zero-free outward rectangles and exact window expansion

The constructed rectangle contains the original closed upper-height cutoff.
The expanded height window is the original window plus both added windows;
its inequality preserves the original finite-height subtraction. The
boundary perturbation needed in the Chourasiya--Simonic Littlewood route is
proved from finite detector zeros and the unconditional right-side bound:
https://arxiv.org/html/2507.15184v2, Section 4.
-/

noncomputable section

namespace RiemannResearch.Analysis.InghamMollifier
open Complex Set

/-- Every positive-height closed rectangle has outward zero-free perturbations.
No top-height or finite-RH certificate is assumed. -/
theorem zetaDetector_exists_zeroFreeRectangle_expansion
    {X : ℕ} (hX : 37 ≤ X) {α H T ε : ℝ}
    (hα : α < 3 / 2) (hHT : H ≤ T) (hε : 0 < ε) (hεH : ε < H) :
    ∃ α' H' T' : ℝ, α' ∈ Ioo (α - ε) α ∧ H' ∈ Ioo (H - ε) H ∧
      T' ∈ Ioo T (T + ε) ∧
      (∀ s ∈ RectangleBorder ((α' : ℂ) + (H' : ℂ) * I)
        (((3 / 2 : ℝ) : ℂ) + (T' : ℂ) * I), zetaDetector X s ≠ 0) ∧
      Rectangle ((α : ℂ) + (H : ℂ) * I) (((3 / 2 : ℝ) : ℂ) + (T : ℂ) * I) ⊆
        Rectangle ((α' : ℂ) + (H' : ℂ) * I) (((3 / 2 : ℝ) : ℂ) + (T' : ℂ) * I) := by
  apply Complex.exists_zeroFreeRectangle_expansion hα hHT hε
  · exact zetaDetector_analyticOnNhd_rectangle X (by linarith) (by linarith) (by linarith)
  · intro t _ht
    exact (zetaDetector_right_ne_zero_and_neg_log_le_sharp hX (by simp)).1

end RiemannResearch.Analysis.InghamMollifier

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Outward height perturbation adds both side windows exactly. The original
finite-height subtraction remains in the primary term. -/
theorem rightInclusiveWindow_expansion_exact {H' H T T' : ℝ}
    (hH : H' ≤ H) (hHT : H ≤ T) (hT : T ≤ T') (σ : ℝ) :
    rightInclusiveWindow H' T' σ = rightInclusiveWindow H T σ +
      rightInclusiveWindow H' H σ + rightInclusiveWindow T T' σ := by
  rw [rightInclusiveWindow_eq_sub (hH.trans (hHT.trans hT)),
    rightInclusiveWindow_eq_sub hHT, rightInclusiveWindow_eq_sub hH,
    rightInclusiveWindow_eq_sub hT]
  ring

theorem rightInclusiveDifference_le_expandedWindow {H' H T T' : ℝ}
    (hH : H' ≤ H) (hHT : H ≤ T) (hT : T ≤ T') (σ : ℝ) :
    rightInclusiveCount T σ - rightInclusiveCount H σ ≤ rightInclusiveWindow H' T' σ := by
  rw [rightInclusiveWindow_expansion_exact hH hHT hT,
    ← rightInclusiveWindow_eq_sub hHT]
  linarith [rightInclusiveWindow_nonneg H' H σ, rightInclusiveWindow_nonneg T T' σ]

end RiemannResearch.Analysis.ActualZeroOrdinate

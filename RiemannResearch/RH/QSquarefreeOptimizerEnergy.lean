/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeAffineHead
import RiemannResearch.RH.QMobiusStretchedEnergy
import RiemannResearch.RH.QSquarefreeSublinearHeads
import RiemannResearch.RH.QMobiusExactHead
import Mathlib.Tactic.Linarith

/-!
# Complete-energy bounds for the actual squarefree affine optimizer
Source: the user's optimizer-transfer request, 30 October 2026.
The objective is residual energy. The exact Pythagorean identity is retained
before transferring the unconditional stretched and logarithmic savings.
These bounds are sublinear, not subpolynomial.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QSquarefreeOptimizerEnergy
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeAffineHead QSquarefreeLatticePackets
open RiemannResearch.Analysis

theorem baseline_succ (H : ℕ) :
    baseline H (H + 1) = QMobiusExactHead.exactHead H := rfl

theorem exactHead_mem_divisorStage (H L : ℕ) (ha : H + 1 ∣ L)
    (hsmall : ∀ d, 1 < d → d ≤ H → Squarefree d → d ∣ L) :
    QMobiusExactHead.exactHead H ∈ divisorStage L := by
  rw [← baseline_succ]
  exact baseline_mem_divisorStage H L (H + 1) ha hsmall

/-- The full trial error is the actual minimum plus its nonnegative excess. -/
theorem exactHead_optimizer_completion (H L r : ℕ) (hH : 0 < H) (hL : 0 < L)
    (hr : r ∈ conductors L) (hrH : H < r) (ha : H + 1 ∣ L)
    (hsmall : ∀ d, 1 < d → d ≤ H → Squarefree d → d ∣ L) :
    ‖qOne - QMobiusExactHead.exactHead H‖ ^ 2 = minimumError H L r hr +
      ‖QMobiusExactHead.exactHead H - optimizer H L r hr‖ ^ 2 :=
  minimumError_completion H L r hH hL hr hrH hsmall _
    (exactHead_mem_divisorStage H L ha hsmall)
    (QMobiusExactHead.exactHead_exact H)

theorem minimumError_le_exactHead (H L r : ℕ) (hH : 0 < H) (hL : 0 < L)
    (hr : r ∈ conductors L) (hrH : H < r) (ha : H + 1 ∣ L)
    (hsmall : ∀ d, 1 < d → d ≤ H → Squarefree d → d ∣ L) :
    minimumError H L r hr ≤ ‖qOne - QMobiusExactHead.exactHead H‖ ^ 2 := by
  rw [exactHead_optimizer_completion H L r hH hL hr hrH ha hsmall]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Every fixed logarithmic saving transfers, uniformly over all feasible stages. -/
theorem minimumError_eventual_log_power (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ H : ℕ in atTop,
      ∀ L r : ℕ, 0 < H → 0 < L → ∀ hr : r ∈ conductors L,
        H < r → H + 1 ∣ L →
        (∀ d, 1 < d → d ≤ H → Squarefree d → d ∣ L) →
        minimumError H L r hr ≤
          16 / zetaTwo + C * (H : ℝ) / (6 + Real.log (H : ℝ)) ^ k := by
  obtain ⟨C, hC, hbound⟩ := QMobiusStretchedEnergy.exactHead_error_eventual_log_power_energy k
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with H hB
  intro L r hH hL hr hrH ha hs
  exact (minimumError_le_exactHead H L r hH hL hr hrH ha hs).trans hB

theorem minimumError_eventual_stretched :
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ H : ℕ in atTop,
      ∀ L r : ℕ, 0 < H → 0 < L → ∀ hr : r ∈ conductors L,
        H < r → H + 1 ∣ L →
        (∀ d, 1 < d → d ≤ H → Squarefree d → d ∣ L) →
        minimumError H L r hr ≤ 16 / zetaTwo + C * (H : ℝ) *
          Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (H : ℝ))) := by
  obtain ⟨a, ha, C, hC, hbound⟩ := QMobiusStretchedEnergy.exactHead_error_eventual_stretched_energy
  refine ⟨a, ha, C, hC, ?_⟩
  filter_upwards [hbound] with H hB
  intro L r hH hL hr hrH ha' hs
  exact (minimumError_le_exactHead H L r hH hL hr hrH ha' hs).trans hB

theorem minimumError_sublinear
    (H L r : ℕ → ℕ) (hcofinal : Tendsto H atTop atTop)
    (hH : ∀ j, 0 < H j) (hL : ∀ j, 0 < L j)
    (hr : ∀ j, r j ∈ conductors (L j)) (hrH : ∀ j, H j < r j)
    (ha : ∀ j, H j + 1 ∣ L j)
    (hsmall : ∀ j d, 1 < d → d ≤ H j → Squarefree d → d ∣ L j) :
    Tendsto (fun j => minimumError (H j) (L j) (r j) (hr j) / (H j : ℝ))
      atTop (𝓝 0) := by
  apply squeeze_zero (fun j => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) ?_
    (QSquarefreeSublinearHeads.exactHead_error_sublinear.comp hcofinal)
  intro j
  exact div_le_div_of_nonneg_right
    (minimumError_le_exactHead _ _ _ (hH j) (hL j) (hr j) (hrH j) (ha j) (hsmall j))
    (Nat.cast_nonneg _)
end RiemannResearch.RH.QSquarefreeOptimizerEnergy

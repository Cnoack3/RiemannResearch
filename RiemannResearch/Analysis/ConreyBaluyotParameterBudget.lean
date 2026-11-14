/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Strict parameter budget below the Conrey--Baluyot barrier

Source: the explicit proposed budget in the user's density-closure plan
(14 November 2026), section 7, motivated by Baluyot (2017), section 3.6:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320 .

This module checks only the algebra of choosing positive parameters.
It does not prove that the analytic errors satisfy the indicated powers,
nor does it identify the independent cutoff and error-loss parameters.
-/

noncomputable section
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- The proposed strict exponent budget. This is algebra, not a moment estimate.
The fixed cutoff exponent remains independent of the error-loss parameter. -/
theorem exists_strict_error_budget {θ η : ℝ}
    (hθ : 0 < θ) (hθhi : θ < 4 / 7) (hη : 0 < η) :
    let g := 1 - 7 / 4 * θ
    let δ := g / 28
    let εerr := g / 16
    let E₁ := -1 / 2 + 7 / 2 * δ + 7 / 8 * θ + εerr
    let E₂ := -1 + 7 / 2 * δ + 7 / 4 * θ + εerr
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ η / 2 ∧ ε₀ ≤ 1 / 8 ∧
      0 < δ ∧ δ < 1 / 3 ∧ 0 < εerr ∧
      2 * θ * ε₀ ≤ g / 112 ∧ 4 * θ * ε₀ < δ ∧
      E₁ = -5 * g / 16 ∧ E₂ = -13 * g / 16 ∧
      ∀ σ : ℝ, σ ≤ 1 / 2 + ε₀ →
        E₁ < θ * (1 - 2 * σ) ∧ E₂ < θ * (1 - 2 * σ) := by
  dsimp only
  let g := 1 - 7 / 4 * θ
  let δ := g / 28
  have hg : 0 < g := by dsimp [g]; linarith
  have hg1 : g < 1 := by dsimp [g]; linarith
  have hd : 0 < δ := by dsimp [δ]; positivity
  let ε₀ := min (η / 2) (min (1 / 8) (δ / (8 * θ)))
  have he0 : 0 < ε₀ := lt_min (by positivity)
    (lt_min (by norm_num) (div_pos hd (by positivity)))
  have heη : ε₀ ≤ η / 2 := min_le_left _ _
  have he8 : ε₀ ≤ 1 / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have heδ : ε₀ ≤ δ / (8 * θ) := (min_le_right _ _).trans (min_le_right _ _)
  have hm : ε₀ * (8 * θ) ≤ δ := (le_div_iff₀ (by positivity)).mp heδ
  have hsmall : 2 * θ * ε₀ ≤ g / 112 := by dsimp [δ] at hm; nlinarith
  have hstrict : 4 * θ * ε₀ < δ := by nlinarith
  have hE₁ : -1 / 2 + 7 / 2 * δ + 7 / 8 * θ + g / 16 = -5 * g / 16 := by
    dsimp [δ, g]
    ring
  have hE₂ : -1 + 7 / 2 * δ + 7 / 4 * θ + g / 16 = -13 * g / 16 := by
    dsimp [δ, g]
    ring
  refine ⟨ε₀, he0, heη, he8, hd, ?_, by positivity, hsmall, hstrict, hE₁, hE₂, ?_⟩
  · change δ < 1 / 3
    dsimp [δ]
    linarith
  · intro σ hσ
    change _ + g / 16 < _ ∧ _ + g / 16 < _
    rw [hE₁, hE₂]
    have hs : -2 * θ * ε₀ ≤ θ * (1 - 2 * σ) := by nlinarith
    constructor <;> nlinarith

end RiemannResearch.Analysis.ConreyBaluyot

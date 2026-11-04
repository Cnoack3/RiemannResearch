/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Directional gain certificates

These are the completion-of-squares identities underlying Schur complements;
see Boyd and Vandenberghe, Convex Optimization (2004), Appendix A.5.5.
They permit certified trial directions without inversion or uniform conditioning.
The exact projection identity needed at an application site is an explicit
hypothesis, so this file does not assume an arithmetic lower gain bound.
-/
noncomputable section
namespace RiemannResearch.Analysis.DirectionalGainCertificate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem trial_exact (r u z : H)
    (hinner : inner ℝ r z = inner ℝ u z) :
    ‖u‖ ^ 2 = 2 * inner ℝ r z - ‖z‖ ^ 2 + ‖u - z‖ ^ 2 := by
  rw [norm_sub_sq_real, hinner]
  ring

theorem trial_lower (r u z : H)
    (hinner : inner ℝ r z = inner ℝ u z) :
    2 * inner ℝ r z - ‖z‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  rw [trial_exact r u z hinner]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem robust_directional_lower (G a b ahat bhat εa εb : ℝ)
    (hgain : 2 * a - b ≤ G)
    (ha : |a - ahat| ≤ εa) (hb : |b - bhat| ≤ εb) :
    2 * ahat - bhat - 2 * εa - εb ≤ G := by
  obtain ⟨ha₁, ha₂⟩ := abs_le.mp ha
  obtain ⟨hb₁, hb₂⟩ := abs_le.mp hb
  linarith

theorem scalar_optimized_lower (G a b : ℝ) (hb : 0 < b)
    (hgain : ∀ s : ℝ, 2 * s * a - s ^ 2 * b ≤ G) : a ^ 2 / b ≤ G := by
  calc
    a ^ 2 / b = 2 * (a / b) * a - (a / b) ^ 2 * b := by
      field_simp [ne_of_gt hb]
      ring
    _ ≤ G := hgain (a / b)

end RiemannResearch.Analysis.DirectionalGainCertificate

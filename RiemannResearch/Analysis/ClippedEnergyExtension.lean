/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.CountableJumpEnergy
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.Linarith

/-!
# Extending jump-energy comparisons from bounded to arbitrary functions

Source: the clipping argument in PrimeResamplingResearch20261027.md,
Section 4. The finite-head proof below strengthens that argument: it needs
no integrability premise, no finiteness of individual edge weights, and no
convergence of means. It applies to extended nonnegative pair energies.
The intended consumer is the actual countable prime-resampling Poincare
inequality and the resulting RH regularity criterion.
-/

noncomputable section
open scoped BigOperators ENNReal
namespace RiemannResearch.Analysis.ClippedEnergyExtension
open CountableJumpEnergy
variable {α : Type*}

/-- Symmetric clipping, with its nonnegative radius explicit. -/
def clip (R : ℝ) (hR : 0 ≤ R) (g : α → ℝ) (x : α) : ℝ :=
  (Set.projIcc (-R) R (by linarith) (g x) : ℝ)

theorem clip_abs_le (R : ℝ) (hR : 0 ≤ R) (g : α → ℝ) (x : α) :
    |clip R hR g x| ≤ R := by
  exact abs_le.mpr (Set.projIcc (-R) R (by linarith) (g x)).property

theorem clip_eq_of_abs_le (R : ℝ) (hR : 0 ≤ R) (g : α → ℝ)
    (x : α) (hx : |g x| ≤ R) : clip R hR g x = g x := by
  unfold clip
  rw [Set.projIcc_of_mem _ (abs_le.mp hx)]

theorem clip_abs_sub_le (R : ℝ) (hR : 0 ≤ R) (g : α → ℝ) (x y : α) :
    |clip R hR g x - clip R hR g y| ≤ |g x - g y| :=
  Set.abs_projIcc_sub_projIcc (by linarith : -R ≤ R)

theorem countableJumpEnergy_clip_le (W : α → α → ℝ≥0∞)
    (R : ℝ) (hR : 0 ≤ R) (g : α → ℝ) :
    countableJumpEnergy W (clip R hR g) ≤ countableJumpEnergy W g :=
  energy_mono_of_abs_sub_le W (clip R hR g) g (clip_abs_sub_le R hR g)

/-- Any comparison between two nonnegative jump forms that holds on bounded
functions extends to every real function, allowing either energy to be infinite. -/
theorem comparison_of_bounded
    (V W : α → α → ℝ≥0∞)
    (hbounded : ∀ f : α → ℝ, (∃ R : ℝ, 0 ≤ R ∧ ∀ x, |f x| ≤ R) →
      countableJumpEnergy V f ≤ countableJumpEnergy W f)
    (g : α → ℝ) : countableJumpEnergy V g ≤ countableJumpEnergy W g := by
  classical
  apply (countableJumpEnergy_le_iff V g _).mpr
  intro S
  let R : ℝ := ∑ x ∈ S, |g x|
  have hR : 0 ≤ R := Finset.sum_nonneg (fun x _ => abs_nonneg (g x))
  have he (x : α) (hx : x ∈ S) : clip R hR g x = g x :=
    clip_eq_of_abs_le R hR g x (Finset.single_le_sum (fun y _ => abs_nonneg (g y)) hx)
  have hfinite : finiteSetEnergy V g S = finiteSetEnergy V (clip R hR g) S := by
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    rw [he x hx, he y hy]
  calc
    _ = finiteSetEnergy V (clip R hR g) S := hfinite
    _ ≤ countableJumpEnergy V (clip R hR g) := finiteSetEnergy_le _ _ _
    _ ≤ countableJumpEnergy W (clip R hR g) :=
      hbounded _ ⟨R, hR, clip_abs_le R hR g⟩
    _ ≤ _ := countableJumpEnergy_clip_le W R hR g

/-- An extended spectral-gap estimate can be checked on bounded tests alone. -/
theorem comparison_iff_bounded (V W : α → α → ℝ≥0∞) :
    (∀ g : α → ℝ, countableJumpEnergy V g ≤ countableJumpEnergy W g) ↔
    (∀ g : α → ℝ, (∃ R : ℝ, 0 ≤ R ∧ ∀ x, |g x| ≤ R) →
      countableJumpEnergy V g ≤ countableJumpEnergy W g) := by
  constructor
  · intro h g _
    exact h g
  · intro h g
    exact comparison_of_bounded V W h g

end RiemannResearch.Analysis.ClippedEnergyExtension

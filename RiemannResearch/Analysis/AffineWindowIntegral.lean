/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Exact affine window changes of variables

These identities retain the Jacobian and support restriction for scaled
real windows. The application is the shifted Weil gamma integral.
-/
open MeasureTheory Set
noncomputable section
namespace RiemannResearch.Analysis
theorem integral_affine_window (F K : ℝ → ℝ) {T : ℝ} (hT : 0 < T) (u : ℝ) :
    (∫ t : ℝ, F (T * (t-u)) * K t) =
      T⁻¹ * ∫ x : ℝ, F x * K (u+x/T) := by
  let g : ℝ → ℝ := fun x => F x * K (u+x/T)
  have he : (fun t : ℝ => F (T * (t-u)) * K t) = fun t => g (T*(t-u)) := by
    funext t
    dsimp [g]
    congr 2
    field_simp [hT.ne']
    ring
  rw [he]
  have hs : (∫ t : ℝ, g (T*(t-u))) = ∫ t : ℝ, g (T*t) :=
    integral_sub_right_eq_self (fun t : ℝ => g (T*t)) u
  rw [hs, Measure.integral_comp_mul_left]
  simp only [abs_of_pos (inv_pos.mpr hT), smul_eq_mul]
  rfl

theorem integral_window_restrict (F K : ℝ → ℝ)
    (hF : Function.support F ⊆ Icc (-1 : ℝ) 1) :
    (∫ x : ℝ, F x * K x) = ∫ x in Icc (-1 : ℝ) 1, F x * K x := by
  have hind : (Icc (-1 : ℝ) 1).indicator (fun x => F x * K x) = fun x => F x * K x := by
    funext x
    by_cases hx : x ∈ Icc (-1 : ℝ) 1
    · simp [hx]
    · have hz : F x = 0 := by
        by_contra h
        exact hx (hF (Function.mem_support.mpr h))
      simp [hx, hz]
  have h := integral_indicator (μ := (volume : Measure ℝ)) (s := Icc (-1 : ℝ) 1)
    (f := fun x => F x * K x) measurableSet_Icc
  rw [hind] at h
  exact h
end RiemannResearch.Analysis

/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Support-length L2 bound
The real L1 integral squared is bounded by the support interval length times
the square integral. The zero-length case is included without division.
RH consumer: the sharp archimedean remainder for dyadic Haar steps.
Source: user-provided RH_Local_to_Global_Trace_Attack_Plan_2026-09-05.pdf,
page 3, supports the statement; the proof integrates a nonnegative square.
No arithmetic positivity or Weil-form identification is asserted.
-/

open MeasureTheory Set
namespace RiemannResearch.Analysis

/-- Cauchy inequality with exact support length and explicit integrability. -/
theorem integral_norm_sq_le_support_length_mul_integral_sq
    {u : ℝ → ℝ} {R : ℝ} (hR : 0 ≤ R) (hu : Integrable u)
    (hu2 : Integrable (fun x => u x ^ 2))
    (hsupp : ∀ x ∉ Icc (-R) R, u x = 0) :
    (∫ x, ‖u x‖) ^ 2 ≤ 2 * R * (∫ x, u x ^ 2) := by
  have hA : (∫ x in Icc (-R) R, ‖u x‖) = ∫ x, ‖u x‖ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (by
      intro x hx
      simp [hsupp x hx])
  have hE : (∫ x in Icc (-R) R, u x ^ 2) = ∫ x, u x ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (by
      intro x hx
      simp [hsupp x hx])
  rcases eq_or_lt_of_le hR with hR0 | hRpos
  · have hR' : R = 0 := hR0.symm
    subst R
    have hA0 : (∫ x, ‖u x‖) = 0 := by simpa using hA.symm
    rw [hA0]
    simp
  · let L : ℝ := 2 * R
    let A : ℝ := ∫ x, ‖u x‖
    have hL : 0 < L := by dsimp [L]; linarith
    have hμ : (volume.restrict (Icc (-R) R)).real univ = L := by
      rw [measureReal_restrict_apply_univ, Real.volume_real_Icc, max_eq_left]
      · dsimp [L]
        ring
      · linarith
    have : IsFiniteMeasure (volume.restrict (Icc (-R) R)) :=
      ⟨by simp [Real.volume_Icc]⟩
    have hi1 : Integrable (fun x => L ^ 2 * u x ^ 2)
        (volume.restrict (Icc (-R) R)) := hu2.restrict.const_mul _
    have hi2 : Integrable (fun x => (2 * L * A) * ‖u x‖)
        (volume.restrict (Icc (-R) R)) := hu.norm.restrict.const_mul _
    have hi3 : Integrable (fun _ : ℝ => A ^ 2)
        (volume.restrict (Icc (-R) R)) := integrable_const _
    have hn : 0 ≤ ∫ x in Icc (-R) R,
        (L ^ 2 * u x ^ 2 - (2 * L * A) * ‖u x‖ + A ^ 2) := by
      apply integral_nonneg
      intro x
      have hn2 : ‖u x‖ ^ 2 = u x ^ 2 := by simp [Real.norm_eq_abs]
      change 0 ≤ L ^ 2 * u x ^ 2 - (2 * L * A) * ‖u x‖ + A ^ 2
      rw [show L ^ 2 * u x ^ 2 - (2 * L * A) * ‖u x‖ + A ^ 2 =
          (L * ‖u x‖ - A) ^ 2 by rw [← hn2]; ring]
      exact sq_nonneg _
    rw [integral_add (f := fun x => L ^ 2 * u x ^ 2 - (2 * L * A) * ‖u x‖)
        (g := fun _ => A ^ 2) (hi1.sub hi2) hi3,
      integral_sub (f := fun x => L ^ 2 * u x ^ 2)
        (g := fun x => (2 * L * A) * ‖u x‖) hi1 hi2,
      integral_const_mul, integral_const_mul, integral_const,
      hμ, hE, hA] at hn
    simp only [smul_eq_mul] at hn
    have hc : L * A ^ 2 ≤ L * (L * (∫ x, u x ^ 2)) := by
      dsimp [A] at hn ⊢
      nlinarith
    exact (mul_le_mul_iff_right₀ hL).mp hc

end RiemannResearch.Analysis

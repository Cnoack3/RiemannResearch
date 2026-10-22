import RiemannResearch.Analysis.ShiftedLift
import Mathlib.Tactic.FieldSimp

/-!
# Exact shifted-lift defect

Source: elementary square completion from the user-provided shifted-lift handoff.
No mathematical novelty is asserted.
This identity makes no arithmetic rate assertion.
-/

noncomputable section

namespace RiemannResearch.Analysis.ShiftedLift

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Polynomial square completion, including the exact parameter mismatch. -/
theorem regularizedEnergy_defect_with_mismatch
    (S : H →ₗ[ℝ] H) (hS : ∀ x : H, ‖S x‖ = ‖x‖)
    (a v : H) (horth : inner ℝ a v = 0) (t r : ℝ) :
    r * regularizedEnergy S a t v =
      r * (1-r) * ‖a‖^2 + ‖S v - r • (v-a)‖^2 +
        (r*t^2 - (1-r)^2) * ‖v‖^2 := by
  have hSv : inner ℝ (S v) (S v) = inner ℝ v v := by
    simpa only [real_inner_self_eq_norm_sq] using
      congrArg (fun z : ℝ => z^2) (hS v)
  have horth' : inner ℝ v a = 0 := by
    rw [real_inner_comm]
    exact horth
  simp only [regularizedEnergy, difference_apply, ← real_inner_self_eq_norm_sq,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    conj_trivial, hSv, horth, horth', real_inner_comm (S v) v,
    real_inner_comm (S v) a]
  ring

/-- Exact nonnegative remainder after the parameters are matched. -/
theorem regularizedEnergy_defect
    (S : H →ₗ[ℝ] H) (hS : ∀ x : H, ‖S x‖ = ‖x‖)
    (a v : H) (horth : inner ℝ a v = 0) (t r : ℝ)
    (hparam : r*t^2 = (1-r)^2) :
    r * regularizedEnergy S a t v =
      r * (1-r) * ‖a‖^2 + ‖S v - r • (v-a)‖^2 := by
  simpa only [hparam, sub_self, zero_mul, add_zero] using
    regularizedEnergy_defect_with_mismatch S hS a v horth t r

/-- A square-root parameterization expressed without a square root. -/
theorem regularizedEnergy_defect_parameterized
    (S : H →ₗ[ℝ] H) (hS : ∀ x : H, ‖S x‖ = ‖x‖)
    (a v : H) (horth : inner ℝ a v = 0) (s : ℝ) (hs : s ≠ 0) :
    s^2 * regularizedEnergy S a ((1-s^2)/s) v =
      s^2 * (1-s^2) * ‖a‖^2 + ‖S v - s^2 • (v-a)‖^2 := by
  apply regularizedEnergy_defect S hS a v horth ((1-s^2)/s) (s^2)
  field_simp [hs]

/-- Exact divided-energy identity for a parameter in the open unit interval. -/
theorem regularizedEnergy_div_parameterized
    (S : H →ₗ[ℝ] H) (hS : ∀ x : H, ‖S x‖ = ‖x‖)
    (a v : H) (horth : inner ℝ a v = 0) (s : ℝ)
    (hs : 0 < s) (hs1 : s < 1) :
    regularizedEnergy S a ((1-s^2)/s) v / ((1-s^2)/s) =
      s * ‖a‖^2 + ‖S v - s^2 • (v-a)‖^2 / (s*(1-s^2)) := by
  have hsne : s ≠ 0 := ne_of_gt hs
  have hnum : 1-s^2 ≠ 0 := by nlinarith
  have hid := regularizedEnergy_defect_parameterized S hS a v horth s hsne
  field_simp [hsne, hnum]
  nlinarith [hid]

end RiemannResearch.Analysis.ShiftedLift

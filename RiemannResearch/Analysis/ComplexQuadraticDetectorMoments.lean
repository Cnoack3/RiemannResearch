/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Quadratic detector domination by moments of orders one through two

Chourasiya--Simonic, arXiv:2507.15184v2, proof of Theorem 1, uses
log(1+x^2) <= x^p for 4/3 <= p <= 2:
https://arxiv.org/html/2507.15184v2.
The elementary derivative argument here proves the larger range 1 <= p <= 2,
allowing a first-moment endpoint in the actual mollifier application.
This reference supports the detector strategy, not an asserted novelty claim.
The interval theorem requires genuine interval integrability of both sides.
Real.log at zero is totalized by Mathlib; no integrability is inferred from it.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory

namespace Real

theorem log_one_add_sq_le_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x ^ 2) ≤ x := by
  have hd (y : ℝ) : HasDerivAt (fun z : ℝ => z - Real.log (1 + z * z))
      (1 - (2 * y) / (1 + y * y)) y := by
    have hi : HasDerivAt (fun z : ℝ => 1 + z * z) (2 * y) y := by
      simpa only [id_eq, Pi.add_apply, Pi.mul_apply, mul_one, one_mul, zero_add, two_mul] using!
        (hasDerivAt_const y (1 : ℝ)).add ((hasDerivAt_id y).mul (hasDerivAt_id y))
    exact (hasDerivAt_id y).sub (hi.log (by nlinarith [sq_nonneg y]))
  have hm : Monotone (fun z : ℝ => z - Real.log (1 + z * z)) :=
    monotone_of_deriv_nonneg (fun y => (hd y).differentiableAt) (by
      intro y
      rw [(hd y).deriv]
      have hp : 0 < 1 + y * y := by nlinarith [sq_nonneg y]
      have hq : (2 * y) / (1 + y * y) ≤ 1 :=
        (div_le_iff₀ hp).mpr (by nlinarith [sq_nonneg (y - 1)])
      linarith)
  have hs : 0 ≤ x - Real.log (1 + x * x) := by simpa using hm hx
  simpa [pow_two] using (sub_nonneg.mp hs)

theorem log_one_add_sq_le_rpow {x p : ℝ} (hx : 0 ≤ x)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2) : Real.log (1 + x ^ 2) ≤ x ^ p := by
  by_cases hx0 : x = 0
  · subst x
    simp [Real.zero_rpow (by linarith : p ≠ 0)]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  by_cases hx1 : x ≤ 1
  · have hlog : Real.log (1 + x ^ 2) ≤ x ^ 2 := by
      have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + x ^ 2)
      linarith
    have hp := Real.rpow_le_rpow_of_exponent_ge hxpos hx1 hp2
    rw [Real.rpow_two] at hp
    exact hlog.trans hp
  · have hp := Real.rpow_le_rpow_of_exponent_le (lt_of_not_ge hx1).le hp1
    rw [Real.rpow_one] at hp
    exact (log_one_add_sq_le_self_of_nonneg hx).trans hp

end Real

namespace Complex

theorem log_norm_one_sub_sq_le_rpow (e : ℂ) {p : ℝ}
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    Real.log ‖(1 : ℂ) - e ^ 2‖ ≤ ‖e‖ ^ p := by
  by_cases hne : (1 : ℂ) - e ^ 2 = 0
  · simp only [hne, norm_zero, Real.log_zero]
    positivity
  have hb : ‖(1 : ℂ) - e ^ 2‖ ≤ 1 + ‖e‖ ^ 2 := by
    have hh := norm_sub_le (1 : ℂ) (e * e)
    rw [norm_one, Complex.norm_mul] at hh
    simpa only [pow_two] using! hh
  exact (Real.log_le_log (norm_pos_iff.mpr hne) hb).trans
    (Real.log_one_add_sq_le_rpow (norm_nonneg e) hp1 hp2)

theorem integral_log_norm_one_sub_sq_le_rpow {e : ℝ → ℂ} {H T p : ℝ}
    (hHT : H ≤ T) (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (hlog : IntervalIntegrable (fun t => Real.log ‖(1 : ℂ) - (e t) ^ 2‖) volume H T)
    (hpow : IntervalIntegrable (fun t => ‖e t‖ ^ p) volume H T) :
    (∫ t in H..T, Real.log ‖(1 : ℂ) - (e t) ^ 2‖) ≤
      ∫ t in H..T, ‖e t‖ ^ p := by
  exact intervalIntegral.integral_mono_on hHT hlog hpow
    (fun t _ => log_norm_one_sub_sq_le_rpow (e t) hp1 hp2)

end Complex

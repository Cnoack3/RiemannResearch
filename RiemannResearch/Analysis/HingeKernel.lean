/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring

/-!
# Local support of the arithmetic hinge kernel

The prime-power summand in the additive screw kernel has the form
max (abs t - log n) 0. This module proves its elementary continuity, evenness,
and exact finite-window activation bound. It does not construct the von
Mangoldt sum, prove the cubic cell-integral formula, or assert positivity.

Source: Suzuki, Aspects of the screw function corresponding to the Riemann
zeta-function (2023), equation (1.1),
https://arxiv.org/abs/2206.03682, supports the arithmetic hinge convention.
The proofs below establish only the local support bound used in the planned
finite arithmetic construction.
-/

namespace RiemannResearch.Analysis
noncomputable section

/-- The positive-part hinge occurring in a prime-power screw-kernel summand. -/
def hingeKernel (a t : ℝ) : ℝ := max (|t| - a) 0

theorem continuous_hingeKernel (a : ℝ) : Continuous (hingeKernel a) := by
  unfold hingeKernel
  exact (continuous_abs.sub continuous_const).max continuous_const

theorem hingeKernel_even (a t : ℝ) : hingeKernel a (-t) = hingeKernel a t := by
  simp [hingeKernel]

theorem hingeKernel_eq_zero_of_abs_le {a t : ℝ} (h : |t| ≤ a) :
    hingeKernel a t = 0 := by
  unfold hingeKernel
  exact max_eq_right (sub_nonpos.mpr h)

/-- On a radius-R window, a hinge with threshold at least 2R vanishes
identically on differences. -/
theorem hingeKernel_local_zero {R a x y : ℝ}
    (hx : |x| ≤ R) (hy : |y| ≤ R) (ha : 2 * R ≤ a) :
    hingeKernel a (x - y) = 0 := by
  apply hingeKernel_eq_zero_of_abs_le
  calc
    |x - y| ≤ |x| + |y| := by simpa using (abs_sub_le x 0 y)
    _ ≤ R + R := add_le_add hx hy
    _ = 2 * R := by ring
    _ ≤ a := ha

/-- A positive integer n with exp (2R) <= n has no active log n hinge
contribution on the radius-R window. -/
theorem hingeKernel_local_zero_of_exp_le {R x y : ℝ} {n : ℕ}
    (hn : 0 < n) (hx : |x| ≤ R) (hy : |y| ≤ R)
    (hactive : Real.exp (2 * R) ≤ (n : ℝ)) :
    hingeKernel (Real.log n) (x - y) = 0 := by
  apply hingeKernel_local_zero hx hy
  exact (Real.le_log_iff_exp_le (Nat.cast_pos.mpr hn)).mpr hactive

end
end RiemannResearch.Analysis

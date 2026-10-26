/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Polylogarithmic profiles for complete inverse-square tails

Source: the user's two-residual paper argument, 26 October 2026.
This elementary derivative comparison supplies the pointwise majorant
used by RH/QPolylogTailEnergy.lean. No arithmetic or projection premise
appears here. The exponent-three-halves kernel permits an exact integral
comparison without truncating the infinite tail.
-/

noncomputable section
namespace RiemannResearch.Analysis.PolylogTail

theorem logProfile_antitoneOn (k : ℕ) {a : ℝ}
    (ha : 1 ≤ a) (hk : (k : ℝ) ≤ 6 + Real.log a) :
    AntitoneOn (fun x : ℝ => (6 + Real.log x)^k / x) (Set.Ici a) := by
  cases k with
  | zero =>
      intro x hx y hy hxy
      have hxa : a ≤ x := hx
      have hx0 : 0 < x := by linarith
      simpa only [pow_zero] using one_div_le_one_div_of_le hx0 hxy
  | succ k =>
      let F : ℝ → ℝ := fun x => (6 + Real.log x)^(k+1) / x
      let D : ℝ → ℝ := fun x =>
        (6 + Real.log x)^k * (((k+1 : ℕ) : ℝ) - (6 + Real.log x)) / x ^ 2
      have hd (x : ℝ) (hx : x ∈ Set.Ici a) : HasDerivAt F (D x) x := by
        have hxa : a ≤ x := hx
        have hx0 : 0 < x := by linarith
        have h := (((Real.hasDerivAt_log hx0.ne').const_add 6).pow (k+1)).div
          (hasDerivAt_id x) hx0.ne'
        apply h.congr_deriv
        dsimp only [D, id_eq, Pi.pow_apply, Pi.mul_apply]
        simp only [Nat.add_sub_cancel]
        field_simp [hx0.ne']
        simp only [pow_succ]
        ring
      change AntitoneOn F (Set.Ici a)
      apply antitoneOn_of_deriv_nonpos (convex_Ici a)
      · intro x hx
        exact (hd x hx).continuousAt.continuousWithinAt
      · intro x hx
        exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
      · intro x hx
        have hxa : a ≤ x := interior_subset hx
        have hx1 : 1 ≤ x := ha.trans hxa
        have hL : 0 ≤ 6 + Real.log x := by linarith [Real.log_nonneg hx1]
        have hlog : Real.log a ≤ Real.log x := Real.log_le_log (by linarith) hxa
        have hsign : ((k+1 : ℕ) : ℝ) - (6 + Real.log x) ≤ 0 := by
          simpa only [Nat.succ_eq_add_one] using
            (sub_nonpos.mpr (hk.trans (by linarith)))
        rw [(hd x (interior_subset hx)).deriv]
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hL k) hsign) (sq_nonneg x)

theorem logProfile_sqrt_le (m : ℕ) {a x : ℝ} (ha : 1 ≤ a)
    (hax : a ≤ x) (hm : ((4 * m : ℕ) : ℝ) ≤ 6 + Real.log a) :
    (6 + Real.log x) ^ (2 * m) / Real.sqrt x ≤
      (6 + Real.log a) ^ (2 * m) / Real.sqrt a := by
  have h := logProfile_antitoneOn (4 * m) ha hm (le_refl a) hax hax
  have ha0 : 0 < a := by linarith
  have hx0 : 0 < x := lt_of_lt_of_le ha0 hax
  have hLa : 0 ≤ 6 + Real.log a := by linarith [Real.log_nonneg ha]
  have hLx : 0 ≤ 6 + Real.log x := by
    linarith [Real.log_nonneg (ha.trans hax)]
  have hs := Real.sqrt_le_sqrt h
  rw [Real.sqrt_div (pow_nonneg hLx _) x,
    Real.sqrt_div (pow_nonneg hLa _) a,
    show 4 * m = (2 * m)*2 by omega,
    pow_mul (6 + Real.log x) (2 * m) 2,
    pow_mul (6 + Real.log a) (2 * m) 2,
    Real.sqrt_sq (pow_nonneg hLx _),
    Real.sqrt_sq (pow_nonneg hLa _)] at hs
  exact hs

theorem rpow_neg_three_halves {x : ℝ} (hx : 0 < x) :
    x ^ (-(3/2 : ℝ)) = Real.sqrt x / x ^ 2 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_two, ← Real.rpow_sub hx]
  congr 1
  norm_num

theorem rpow_neg_half {x : ℝ} (hx : 0 < x) :
    x ^ (-(1/2 : ℝ)) = 1 / Real.sqrt x := by
  simp only [Real.rpow_neg hx.le, Real.sqrt_eq_rpow, one_div]

theorem log_pow_div_sq_le (m : ℕ) {a x : ℝ}
    (ha : 1 ≤ a) (hax : a ≤ x)
    (hm : ((4 * m : ℕ) : ℝ) ≤ 6 + Real.log a) :
    (6 + Real.log x) ^ (2 * m) / x ^ 2 ≤
      ((6 + Real.log a) ^ (2 * m) / Real.sqrt a) * x^(-(3/2 : ℝ)) := by
  have hx : 0 < x := lt_of_lt_of_le (by linarith : 0 < a) hax
  calc
    _ = ((6 + Real.log x) ^ (2 * m) / Real.sqrt x) * x^(-(3/2 : ℝ)) := by
      rw [rpow_neg_three_halves hx]
      field_simp [hx.ne', (Real.sqrt_pos.mpr hx).ne']
    _ ≤ _ := mul_le_mul_of_nonneg_right (logProfile_sqrt_le m ha hax hm)
      (Real.rpow_nonneg hx.le _)

end RiemannResearch.Analysis.PolylogTail

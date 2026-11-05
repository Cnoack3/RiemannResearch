/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.MertensLeeLeongCriterion
import RiemannResearch.Analysis.VKSecondProfile

/-!
# The critical secondary coefficient in the explicit Mertens estimate

Lee and Leong, arXiv:2208.06141v5, Theorem 1.1, give a variable
coefficient in their bound for the ordinary Mertens function.  Its
quadratic margin pays the prefactor and every fixed multiple of the
square root of the Vinogradov–Korobov profile.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QMertensFirstMoment
open RiemannResearch.Analysis RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- The coefficient of Φ / log log in the expansion of the published Mertens exponent. -/
def leeLeongSecondRate : ℝ := leeLeongRate * Real.log (53.99 : ℝ) / 5

theorem leeLeongSecondRate_pos : 0 < leeLeongSecondRate := by
  have hA : 0 < leeLeongRate :=
    Real.rpow_pos_of_pos (by positivity : 0 < 5 / (3 * (53.99 : ℝ) ^ 3)) _
  have hW : 0 < Real.log (53.99 : ℝ) := Real.log_pos (by norm_num)
  exact div_pos (mul_pos hA hW) (by norm_num)

/-- Keeping the quadratic term in the variable coefficient preserves every
fixed square-root correction at the critical secondary coefficient. -/
theorem mertens_critical_sqrt_of_leeLeong (h : LeeLeongMertensEstimate) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, |M x| ≤ Real.exp
      (-leeLeongRate * vkProfile x - leeLeongSecondRate * vkSecondProfile x -
          C * Real.sqrt (vkProfile x)) * x := by
  let A := leeLeongRate
  let r := Real.log (53.99 : ℝ)
  let B := |C| + 2
  let c := A * r ^ 2 / 50
  have hbase : 0 < 5 / (3 * (53.99 : ℝ) ^ 3) := by positivity
  have hA : 0 < A := Real.rpow_pos_of_pos hbase _
  have hr : 0 < r := Real.log_pos (by norm_num)
  have hB : 0 < B := by dsimp [B]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have htop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [eventually_ge_atTop (Real.exp (Real.exp (10.01 : ℝ))),
    htop.eventually (eventually_gt_atTop r),
    htop.eventually (eventually_ge_atTop (Real.log (25.85 : ℝ))),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_ge_atTop (0 : ℝ),
    vkProfile_tendsto_atTop.eventually (eventually_ge_atTop (0 : ℝ)),
    vkProfile_dominates_logLog_sq 1 (by norm_num),
    vkProfile_dominates_logLog_fourth ((c / B) ^ 2) (sq_pos_of_pos (div_pos hc hB))]
    with x hx hLr hLK hlogx hx0 hV hL2 hL4
  let V := vkProfile x
  let L := Real.log (Real.log x)
  change r < L at hLr
  change Real.log (25.85 : ℝ) ≤ L at hLK
  change 0 ≤ V at hV
  change L ^ 2 ≤ 1 * V at hL2
  change L ^ 4 ≤ (c / B) ^ 2 * V at hL4
  have hL : 0 < L := hr.trans hLr
  have hgap : 0 < 1 - r / L := sub_pos.mpr ((div_lt_one hL).mpr hLr)
  have hfact : |M x| ≤ 25.85 * x * Real.log x *
      Real.exp (-(A * (1 - r / L) ^ (-(1 / 5 : ℝ)) * V)) := by
    have he := (h x hx).le
    rw [Real.mul_rpow hbase.le (inv_nonneg.mpr hgap.le), Real.inv_rpow hgap.le,
      ← Real.rpow_neg hgap.le] at he
    exact he
  have hquad : 1 + (r / L) / 5 + (r / L) ^ 2 / 50 ≤
      (1 - r / L) ^ (-(1 / 5 : ℝ)) := by
    have hu : 0 ≤ (r / L) / 5 := by positivity
    have hlog := Real.log_le_sub_one_of_pos hgap
    rw [Real.rpow_def_of_pos hgap]
    calc
      _ = 1 + (r / L) / 5 + ((r / L) / 5) ^ 2 / 2 := by ring
      _ ≤ Real.exp ((r / L) / 5) := Real.quadratic_le_exp_of_nonneg hu
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hlog])
  have hscaled := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hquad hA.le) hV
  have hid : A * (1 + (r / L) / 5 + (r / L) ^ 2 / 50) * V =
      A * V + (A * r / 5) * (V / L) + c * V / L ^ 2 := by
    dsimp only [c]
    field_simp [hL.ne']
  rw [hid] at hscaled
  have hLs : L ≤ Real.sqrt V := by
    apply le_of_sq_le_sq _ (Real.sqrt_nonneg _)
    simpa only [one_mul, Real.sq_sqrt hV] using hL2
  have hLs2 : L ^ 2 ≤ c / B * Real.sqrt V := by
    apply le_of_sq_le_sq _ (mul_nonneg (div_nonneg hc.le hB.le) (Real.sqrt_nonneg _))
    rw [mul_pow, Real.sq_sqrt hV]
    nlinarith only [hL4]
  have hpay : B * Real.sqrt V ≤ c * V / L ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
    calc
      _ ≤ (B * Real.sqrt V) * ((c / B) * Real.sqrt V) :=
        mul_le_mul_of_nonneg_left hLs2 (mul_nonneg hB.le (Real.sqrt_nonneg _))
      _ = ((c / B) * B) * (Real.sqrt V) ^ 2 := by ring
      _ = _ := by rw [div_mul_cancel₀ _ hB.ne', Real.sq_sqrt hV]
  have hcost : Real.log (25.85 : ℝ) + L + C * Real.sqrt V ≤ c * V / L ^ 2 := by
    apply le_trans _ hpay
    dsimp only [B]
    linarith only [hLK, hLs,
      mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg V)]
  change |M x| ≤ Real.exp (-A * V - (A * r / 5) * (V / L) - C * Real.sqrt V) * x
  calc
    _ ≤ _ := hfact
    _ = x * Real.exp ((Real.log (25.85 : ℝ) + L) +
        (-(A * (1 - r / L) ^ (-(1 / 5 : ℝ)) * V))) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 25.85),
        show Real.exp L = Real.log x by exact Real.exp_log hlogx]
      ring
    _ ≤ x * Real.exp (-A * V - (A * r / 5) * (V / L) - C * Real.sqrt V) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hscaled, hcost])) hx0
    _ = _ := mul_comm _ _

end RiemannResearch.RH.QMertensFirstMoment

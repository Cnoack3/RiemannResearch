/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.MertensLeeLeongCriterion
import RiemannResearch.Analysis.VinogradovKorobovProfile

/-!
# The full variable exponent of Lee and Leong

Lee and Leong, arXiv:2208.06141v5, Theorem 1.1, equation (11) in the PDF,
give the arithmetic input `LeeLeongMertensEstimate`. We retain the entire
coefficient depending on the double logarithm.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QMertensFirstMoment
open RiemannResearch.Analysis RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- The full positive exponent in the published ordinary Mertens estimate. -/
def leeLeongFullProfile (x : ℝ) : ℝ :=
  leeLeongRate * ((1 - Real.log 53.99 / Real.log (Real.log x)) ^ (-(1 / 5 : ℝ))) *
    vkProfile x

private theorem fullProfile_log_ratio {x : ℝ} (ht : 0 < Real.log x)
    (hrL : Real.log (53.99 : ℝ) < Real.log (Real.log x)) :
    Real.log (leeLeongFullProfile x / Real.sqrt (vkProfile x)) =
      Real.log leeLeongRate + (3 / 10 : ℝ) * Real.log (Real.log x) +
        (1 / 10 : ℝ) * Real.log (Real.log (Real.log x)) -
        (1 / 5 : ℝ) * Real.log (Real.log (Real.log x) - Real.log 53.99) := by
  let r := Real.log (53.99 : ℝ)
  let L := Real.log (Real.log x)
  have hA : 0 < leeLeongRate := Real.rpow_pos_of_pos
    (by positivity : 0 < 5 / (3 * (53.99 : ℝ) ^ 3)) _
  have hr : 0 < r := Real.log_pos (by norm_num)
  have hL : 0 < L := hr.trans hrL
  have hdiff : 0 < L - r := sub_pos.mpr hrL
  have hfac : 0 < 1 - r / L := sub_pos.mpr ((div_lt_one hL).mpr hrL)
  have hpow := Real.rpow_pos_of_pos hfac (-(1 / 5 : ℝ))
  have hV : 0 < vkProfile x :=
    div_pos (Real.rpow_pos_of_pos ht _) (Real.rpow_pos_of_pos hL _)
  have hF : 0 < leeLeongFullProfile x := mul_pos (mul_pos hA hpow) hV
  have hlogV : Real.log (vkProfile x) = (3 / 5 : ℝ) * L - (1 / 5 : ℝ) * Real.log L := by
    unfold vkProfile
    rw [Real.log_div (Real.rpow_pos_of_pos ht _).ne' (Real.rpow_pos_of_pos hL _).ne',
      Real.log_rpow ht, Real.log_rpow hL]
  have hlogf : Real.log (1 - r / L) = Real.log (L - r) - Real.log L := by
    rw [show 1 - r / L = (L - r) / L by rw [sub_div, div_self hL.ne'],
      Real.log_div hdiff.ne' hL.ne']
  rw [Real.log_div hF.ne' (Real.sqrt_pos.2 hV).ne', leeLeongFullProfile,
    Real.log_mul (mul_pos hA hpow).ne' hV.ne', Real.log_mul hA.ne' hpow.ne',
    Real.log_rpow hfac, Real.log_sqrt hV.le, hlogf, hlogV]
  dsimp only [L, r]
  ring

private theorem fullProfile_ratio_eventually_mono :
    ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ≤ y →
      leeLeongFullProfile x / Real.sqrt (vkProfile x) ≤
      leeLeongFullProfile y / Real.sqrt (vkProfile y) := by
  let r := Real.log (53.99 : ℝ)
  have hr : 0 < r := Real.log_pos (by norm_num)
  have htop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    htop.eventually (eventually_ge_atTop (r + 1))] with x hx ht hu1 y hxy
  let u := Real.log (Real.log x)
  let v := Real.log (Real.log y)
  change r + 1 ≤ u at hu1
  have hru : r < u := by linarith
  have hu : 0 < u := hr.trans hru
  have hxy' := Real.log_le_log hx hxy
  have ht' := ht.trans_le hxy'
  have huv : u ≤ v := Real.log_le_log ht hxy'
  have hrv := hru.trans_le huv
  have hu' : 0 < u - r := sub_pos.mpr hru
  have hv' : 0 < v - r := sub_pos.mpr hrv
  have hlog := Real.log_le_log hu huv
  have hlog' := Real.log_le_log hu' (sub_le_sub_right huv r)
  have hdiff : Real.log (v - r) - Real.log (u - r) ≤ v - u := by
    have h := Real.log_le_sub_one_of_pos (div_pos hv' hu')
    rw [Real.log_div hv'.ne' hu'.ne'] at h
    have hmul := mul_le_mul_of_nonneg_right h hu'.le
    have he : ((v - r) / (u - r) - 1) * (u - r) = (v - r) - (u - r) := by
      rw [sub_mul, div_mul_cancel₀ _ hu'.ne', one_mul]
    rw [he] at hmul
    have hle := mul_le_mul_of_nonneg_left (show 1 ≤ u - r by linarith)
      (sub_nonneg.mpr hlog')
    linarith only [hmul, hle]
  have hpos (z : ℝ) (hzt : 0 < Real.log z) (hzL : r < Real.log (Real.log z)) :
      0 < leeLeongFullProfile z / Real.sqrt (vkProfile z) := by
    have hL := hr.trans hzL
    have hfac : 0 < 1 - r / Real.log (Real.log z) :=
      sub_pos.mpr ((div_lt_one hL).mpr hzL)
    have hV : 0 < vkProfile z :=
      div_pos (Real.rpow_pos_of_pos hzt _) (Real.rpow_pos_of_pos hL _)
    have hA : 0 < leeLeongRate := Real.rpow_pos_of_pos
      (by positivity : 0 < 5 / (3 * (53.99 : ℝ) ^ 3)) _
    exact div_pos (mul_pos (mul_pos hA (Real.rpow_pos_of_pos hfac _)) hV) (Real.sqrt_pos.2 hV)
  apply (Real.log_le_log_iff (hpos x ht hru) (hpos y ht' hrv)).mp
  rw [fullProfile_log_ratio ht hru, fullProfile_log_ratio ht' hrv]
  change Real.log leeLeongRate + (3 / 10 : ℝ) * u + (1 / 10 : ℝ) * Real.log u -
      (1 / 5 : ℝ) * Real.log (u - r) ≤ Real.log leeLeongRate + (3 / 10 : ℝ) * v +
      (1 / 10 : ℝ) * Real.log v - (1 / 5 : ℝ) * Real.log (v - r)
  linarith only [hdiff, huv, hlog]
private theorem fullProfileFactor_bounds {L : ℝ} (hL : 2 * Real.log 53.99 ≤ L) :
    1 ≤ (1 - Real.log 53.99 / L) ^ (-(1 / 5 : ℝ)) ∧
      (1 - Real.log 53.99 / L) ^ (-(1 / 5 : ℝ)) ≤ 2 := by
  have hr : 0 < Real.log (53.99 : ℝ) := Real.log_pos (by norm_num)
  have hpos : 0 < L := by linarith
  have hhalf : (1 / 2 : ℝ) ≤ 1 - Real.log 53.99 / L := by
    have h := (div_le_iff₀ hpos).mpr (show Real.log 53.99 ≤ (1 / 2 : ℝ) * L by linarith)
    linarith
  have hunit : 1 - Real.log 53.99 / L ≤ 1 := sub_le_self _ (div_nonneg hr.le hpos.le)
  constructor
  · exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by linarith) hunit (by norm_num)
  · calc
      _ ≤ (1 / 2 : ℝ) ^ (-(1 / 5 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hhalf (by norm_num)
      _ ≤ (1 / 2 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
      _ = 2 := by rw [Real.rpow_neg_one]; norm_num

/-- The exact exponent in the Lee–Leong estimate has leading scale Φ. -/
theorem leeLeongFullProfile_eventually_bounds :
    ∀ᶠ x : ℝ in atTop, leeLeongRate * vkProfile x ≤ leeLeongFullProfile x ∧
      leeLeongFullProfile x ≤ (2 * leeLeongRate) * vkProfile x := by
  have hL := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hA : 0 ≤ leeLeongRate := by unfold leeLeongRate; positivity
  filter_upwards [hL.eventually (eventually_ge_atTop (2 * Real.log (53.99 : ℝ))),
    vkProfile_tendsto_atTop.eventually (eventually_ge_atTop (0 : ℝ))] with x hx hv
  change 2 * Real.log 53.99 ≤ Real.log (Real.log x) at hx
  obtain ⟨hc₁, hc₂⟩ := fullProfileFactor_bounds hx
  unfold leeLeongFullProfile
  constructor
  · apply mul_le_mul_of_nonneg_right _ hv
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hc₁ hA
  · apply mul_le_mul_of_nonneg_right _ hv
    simpa only [mul_comm 2 leeLeongRate] using mul_le_mul_of_nonneg_left hc₂ hA

/-- The logarithmic correction is decreasing, so the increment of the full profile
is bounded above by the corresponding increment of the leading profile. -/
theorem leeLeongFullProfile_eventually_increment :
    ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ≤ y →
      leeLeongFullProfile y - leeLeongFullProfile x ≤
        (2 * leeLeongRate) * (vkProfile y - vkProfile x) := by
  have hL := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hA : 0 ≤ leeLeongRate := by unfold leeLeongRate; positivity
  have hr : 0 < Real.log (53.99 : ℝ) := Real.log_pos (by norm_num)
  filter_upwards [hL.eventually (eventually_ge_atTop (2 * Real.log (53.99 : ℝ))),
    eventually_gt_atTop (1 : ℝ), vkProfile_eventually_mono,
    vkProfile_tendsto_atTop.eventually (eventually_ge_atTop (0 : ℝ))]
    with x hx hx1 hvx hxv y hxy
  change 2 * Real.log 53.99 ≤ Real.log (Real.log x) at hx
  have hxL : 0 < Real.log (Real.log x) := by linarith
  have hxyL := Real.log_le_log (Real.log_pos hx1)
    (Real.log_le_log (zero_lt_one.trans hx1) hxy)
  have hLx : Real.log 53.99 / Real.log (Real.log x) < 1 :=
    (div_lt_one hxL).mpr (by linarith)
  have hcxy := div_le_div_of_nonneg_left hr.le hxL hxyL
  let c (u : ℝ) := (1 - Real.log 53.99 / Real.log (Real.log u)) ^ (-(1 / 5 : ℝ))
  have hc : c y ≤ c x := Real.rpow_le_rpow_of_nonpos (sub_pos.mpr hLx)
    (sub_le_sub_left hcxy 1) (by norm_num)
  have hcup : leeLeongRate * c x ≤ 2 * leeLeongRate := by
    simpa only [mul_comm 2 leeLeongRate] using
      mul_le_mul_of_nonneg_left (fullProfileFactor_bounds hx).2 hA
  have hv := hvx y hxy
  change leeLeongRate * c y * vkProfile y - leeLeongRate * c x * vkProfile x ≤ _
  calc
    _ ≤ leeLeongRate * c x * vkProfile y - leeLeongRate * c x * vkProfile x :=
      sub_le_sub_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hA) (hxv.trans hv)) _
    _ = (leeLeongRate * c x) * (vkProfile y - vkProfile x) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcup (sub_nonneg.mpr hv)

/-- The full exponent stays increasing after subtracting any fixed square-root
term. The quotient by the square root is eventually increasing as well. -/
theorem leeLeongFullProfile_sub_sqrt_eventually_mono (δ : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ≤ y →
      leeLeongFullProfile x - δ * Real.sqrt (vkProfile x) ≤
      leeLeongFullProfile y - δ * Real.sqrt (vkProfile y) := by
  have hA : 0 < leeLeongRate := Real.rpow_pos_of_pos
    (by positivity : 0 < 5 / (3 * (53.99 : ℝ) ^ 3)) _
  filter_upwards [fullProfile_ratio_eventually_mono, leeLeongFullProfile_eventually_bounds,
    vkProfile_eventually_mono, vkProfile_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    vkProfile_tendsto_atTop.eventually (eventually_ge_atTop ((δ / leeLeongRate) ^ 2))]
    with x hratio hF hmono hx hlarge y hxy
  have hV := hmono y hxy
  have hy := hx.trans_le hV
  have hsx := Real.sqrt_pos.2 hx
  have hsy := Real.sqrt_pos.2 hy
  have hδ : δ / leeLeongRate ≤ Real.sqrt (vkProfile x) :=
    (le_abs_self _).trans (by simpa only [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt hlarge)
  have hδ' := (div_le_iff₀ hA).mp hδ
  have hsmall : δ ≤ leeLeongFullProfile x / Real.sqrt (vkProfile x) := by
    apply (le_div_iff₀ hsx).mpr
    calc
      _ ≤ (Real.sqrt (vkProfile x) * leeLeongRate) * Real.sqrt (vkProfile x) :=
        mul_le_mul_of_nonneg_right hδ' hsx.le
      _ = leeLeongRate * (Real.sqrt (vkProfile x)) ^ 2 := by ring
      _ ≤ _ := by rw [Real.sq_sqrt hx.le]; exact hF.1
  have hh := mul_le_mul (sub_le_sub_right (hratio y hxy) δ) (Real.sqrt_le_sqrt hV)
    hsx.le ((sub_nonneg.mpr hsmall).trans (sub_le_sub_right (hratio y hxy) δ))
  simpa only [sub_mul, div_mul_cancel₀ _ hsx.ne', div_mul_cancel₀ _ hsy.ne'] using hh

/-- The published input gives the full variable exponent with an arbitrarily
small square-root loss, absorbing its logarithmic prefactor. -/
theorem mertens_fullProfile_of_leeLeong (h : LeeLeongMertensEstimate) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, |M x| ≤
      Real.exp (-leeLeongFullProfile x + δ * Real.sqrt (vkProfile x)) * x := by
  have hbase : 0 < 5 / (3 * (53.99 : ℝ) ^ 3) := by positivity
  have hr : 0 < Real.log (53.99 : ℝ) := Real.log_pos (by norm_num)
  have htop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [eventually_ge_atTop (Real.exp (Real.exp (10.01 : ℝ))),
    htop.eventually (eventually_gt_atTop (Real.log (53.99 : ℝ))),
    htop.eventually (eventually_ge_atTop (Real.log (25.85 : ℝ))),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ)), eventually_ge_atTop (0 : ℝ),
    vkProfile_tendsto_atTop.eventually (eventually_ge_atTop (0 : ℝ)),
    vkProfile_dominates_logLog_sq ((δ / 2) ^ 2) (sq_pos_of_pos (half_pos hδ))]
    with x hx hlog hK ht hx0 hV hdom
  let L := Real.log (Real.log x)
  change Real.log (53.99 : ℝ) < L at hlog
  change Real.log (25.85 : ℝ) ≤ L at hK
  have hL := hr.trans hlog
  have hfac : 0 ≤ 1 - Real.log 53.99 / L := sub_nonneg.mpr ((div_le_one hL).mpr hlog.le)
  have hraw : |M x| ≤ 25.85 * x * Real.log x * Real.exp (-leeLeongFullProfile x) := by
    have he := (h x hx).le
    rw [Real.mul_rpow hbase.le (inv_nonneg.mpr hfac), Real.inv_rpow hfac,
      ← Real.rpow_neg hfac] at he
    exact he
  have hLs : L ≤ (δ / 2) * Real.sqrt (vkProfile x) := by
    refine le_of_sq_le_sq ?_ (mul_nonneg (half_pos hδ).le (Real.sqrt_nonneg _))
    simpa only [mul_pow, Real.sq_sqrt hV] using hdom
  calc
    _ ≤ _ := hraw
    _ = x * Real.exp ((Real.log (25.85 : ℝ) + L) + (-leeLeongFullProfile x)) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 25.85),
        show Real.exp L = Real.log x by exact Real.exp_log ht]
      ring
    _ ≤ x * Real.exp (-leeLeongFullProfile x + δ * Real.sqrt (vkProfile x)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hK, hLs])) hx0
    _ = _ := mul_comm _ _

end RiemannResearch.RH.QMertensFirstMoment

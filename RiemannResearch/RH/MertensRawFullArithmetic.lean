import RiemannResearch.RH.MertensFullProfile

/-! # The raw arithmetic cutoff in the full Lee–Leong estimate

Retain the logarithmic prefactor instead of absorbing it in a square-root margin.
-/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QMertensFirstMoment
open RiemannResearch.Analysis RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- Logarithm of the published relative Mertens error, including its prefactor. -/
def leeLeongRawLogError (x : ℝ) : ℝ :=
  Real.log (25.85 * Real.log x) - leeLeongFullProfile x

private theorem raw_log_sqrt_vk {x : ℝ} (ht : 0 < Real.log x)
    (hL : 0 < Real.log (Real.log x)) :
    Real.log (Real.sqrt (vkProfile x)) = (3 / 10 : ℝ) * Real.log (Real.log x) -
      (1 / 10 : ℝ) * Real.log (Real.log (Real.log x)) := by
  have hV : 0 < vkProfile x :=
    div_pos (Real.rpow_pos_of_pos ht _) (Real.rpow_pos_of_pos hL _)
  rw [Real.log_sqrt hV.le, vkProfile,
    Real.log_div (Real.rpow_pos_of_pos ht _).ne' (Real.rpow_pos_of_pos hL _).ne',
    Real.log_rpow ht, Real.log_rpow hL]
  ring

/-- Without differentiating the profile, lower-bound the increment of its square root. -/
private theorem sqrt_vk_dominates_logLog_increment :
    ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ≤ y →
      Real.log (Real.log y) - Real.log (Real.log x) ≤
        Real.sqrt (vkProfile y) - Real.sqrt (vkProfile x) := by
  have htop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    htop.eventually (eventually_ge_atTop (1 : ℝ)),
    vkProfile_tendsto_atTop.eventually (eventually_ge_atTop (25 : ℝ))]
    with x hx ht hL hV y hxy
  let L := Real.log (Real.log x)
  let K := Real.log (Real.log y)
  let u := Real.sqrt (vkProfile x)
  let v := Real.sqrt (vkProfile y)
  change 1 ≤ L at hL
  have hL0 : 0 < L := by linarith only [hL]
  have htt := Real.log_le_log hx hxy
  have ht' := ht.trans_le htt
  have hLK : L ≤ K := Real.log_le_log ht htt
  have hK0 := hL0.trans_le hLK
  have hVx : 0 < vkProfile x := lt_of_lt_of_le (by norm_num) hV
  have hVy : 0 < vkProfile y :=
    div_pos (Real.rpow_pos_of_pos ht' _) (Real.rpow_pos_of_pos hK0 _)
  have hu : 0 < u := Real.sqrt_pos.mpr hVx
  have hv : 0 < v := Real.sqrt_pos.mpr hVy
  have h5 : (5 : ℝ) ≤ u := by
    calc
      5 = Real.sqrt 25 := by norm_num
      _ ≤ _ := Real.sqrt_le_sqrt hV
  have hd : Real.log K - Real.log L ≤ K - L := by
    have hh := Real.log_le_sub_one_of_pos (div_pos hK0 hL0)
    rw [Real.log_div hK0.ne' hL0.ne'] at hh
    have h1 := mul_le_mul_of_nonneg_right hh hL0.le
    rw [sub_mul (K / L) 1 L, div_mul_cancel₀ _ hL0.ne', one_mul] at h1
    have h2 := mul_le_mul_of_nonneg_left hL (sub_nonneg.mpr (Real.log_le_log hL0 hLK))
    linarith only [h1, h2]
  have hxlog : Real.log u = (3/10:ℝ)*L - (1/10:ℝ)*Real.log L := raw_log_sqrt_vk ht hL0
  have hylog : Real.log v = (3/10:ℝ)*K - (1/10:ℝ)*Real.log K := raw_log_sqrt_vk ht' hK0
  have hgap : K - L ≤ 5 * (Real.log v - Real.log u) := by
    linarith only [hxlog, hylog, hd]
  have hnon : 0 ≤ Real.log v - Real.log u := by linarith only [hgap, hLK]
  have hsup := Real.log_le_sub_one_of_pos (div_pos hv hu)
  rw [Real.log_div hv.ne' hu.ne'] at hsup
  have hp := mul_le_mul_of_nonneg_right hsup hu.le
  rw [sub_mul (v / u) 1 u, div_mul_cancel₀ _ hu.ne', one_mul] at hp
  have hh := mul_le_mul_of_nonneg_left h5 hnon
  change K - L ≤ v - u
  linarith only [hgap, hh, hp]

/-- The raw logarithmic error decreases along every sufficiently distant ray. -/
theorem leeLeongRawLogError_eventually_antitone :
    ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ≤ y → leeLeongRawLogError y ≤ leeLeongRawLogError x := by
  filter_upwards [sqrt_vk_dominates_logLog_increment, leeLeongFullProfile_sub_sqrt_eventually_mono 1,
    eventually_gt_atTop (0:ℝ), Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0:ℝ))]
    with x hx hF hx0 hlog y hxy
  have hy := hlog.trans_le (Real.log_le_log hx0 hxy)
  have hm := hF y hxy
  simp only [one_mul] at hm
  unfold leeLeongRawLogError
  rw [Real.log_mul (by norm_num : (25.85:ℝ) ≠ 0) hy.ne',
    Real.log_mul (by norm_num : (25.85:ℝ) ≠ 0) hlog.ne']
  linarith only [hm, hx y hxy]

theorem leeLeongRawLogError_tendsto_atBot : Tendsto leeLeongRawLogError atTop atBot := by
  have hA : 0 < leeLeongRate := Real.rpow_pos_of_pos
    (by positivity : 0 < 5 / (3 * (53.99 : ℝ) ^ 3)) _
  have hc : 0 < leeLeongRate / 2 := by positivity
  have htop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  apply tendsto_atBot.2
  intro b
  filter_upwards [leeLeongFullProfile_eventually_bounds, vkProfile_dominates_logLog_sq _ hc,
    (Tendsto.const_mul_atTop hc vkProfile_tendsto_atTop).eventually
      (eventually_ge_atTop (Real.log 25.85 - b)),
    htop.eventually (eventually_ge_atTop (1 : ℝ)),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ))]
    with x hF hL hV hL1 ht
  let L := Real.log (Real.log x)
  change 1 ≤ L at hL1
  change L^2 ≤ leeLeongRate / 2 * vkProfile x at hL
  change Real.log 25.85 - b ≤ leeLeongRate / 2 * vkProfile x at hV
  have hL2 : L ≤ L^2 := by nlinarith only [hL1, sq_nonneg (L-1)]
  unfold leeLeongRawLogError
  rw [Real.log_mul (by norm_num : (25.85:ℝ) ≠ 0) ht.ne']
  change Real.log (25.85:ℝ) + L - leeLeongFullProfile x ≤ b
  linarith only [hF.1, hV, hL, hL2]

/-- Repackage Lee–Leong with its printed logarithmic prefactor and the full
exponent intact. The external arithmetic estimate is explicit. -/
theorem mertens_rawLogError_of_leeLeong (h : LeeLeongMertensEstimate) :
    ∀ᶠ x : ℝ in atTop, |M x| ≤ Real.exp (leeLeongRawLogError x) * x := by
  have hbase : 0 < 5 / (3 * (53.99 : ℝ) ^ 3) := by positivity
  have hr : 0 < Real.log (53.99 : ℝ) := Real.log_pos (by norm_num)
  have htop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [eventually_ge_atTop (Real.exp (Real.exp (10.01 : ℝ))),
    htop.eventually (eventually_gt_atTop (Real.log (53.99 : ℝ))),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hlog ht
  let L := Real.log (Real.log x)
  change Real.log (53.99 : ℝ) < L at hlog
  have hL := hr.trans hlog
  have hfac : 0 ≤ 1 - Real.log 53.99 / L := sub_nonneg.mpr ((div_le_one hL).mpr hlog.le)
  have hraw : |M x| ≤ 25.85 * x * Real.log x * Real.exp (-leeLeongFullProfile x) := by
    have he := (h x hx).le
    rw [Real.mul_rpow hbase.le (inv_nonneg.mpr hfac), Real.inv_rpow hfac,
      ← Real.rpow_neg hfac] at he
    exact he
  apply hraw.trans_eq
  unfold leeLeongRawLogError
  rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (mul_pos (by norm_num) ht)]
  ring

/-- The raw logarithmic coefficient specializes to its explicit product on all
sufficiently large positive integer cutoffs. -/
theorem exp_leeLeongRawLogError_eventually_nat :
    ∀ᶠ N : ℕ in atTop, Real.exp (leeLeongRawLogError N) =
      25.85 * Real.log (N : ℝ) * Real.exp (-leeLeongFullProfile N) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hnat.eventually
    (Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0:ℝ)))] with N hN
  change 0 < Real.log (N : ℝ) at hN
  unfold leeLeongRawLogError
  rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (mul_pos (by norm_num) hN)]

end RiemannResearch.RH.QMertensFirstMoment

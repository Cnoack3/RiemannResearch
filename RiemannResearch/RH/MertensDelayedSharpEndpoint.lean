/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.MertensDelayedSummability

/-! # Lee–Leong's logarithmic slope on the translated window

The logarithm of the printed full profile is an affine combination of two
logarithms. On the window, the exact change of the latter has a favorable
sign. Secant bounds for log then give the coefficient 3/5 in the numerator.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QMertensFirstMoment
open RiemannResearch.Analysis

private theorem sharp_full_profile_log {x : ℝ} (ht : 0 < Real.log x)
    (hrL : Real.log (53.99 : ℝ) < Real.log (Real.log x)) :
    0 < leeLeongFullProfile x ∧
    Real.log (leeLeongFullProfile x) =
      Real.log leeLeongRate + (3 / 5 : ℝ) * Real.log (Real.log x) -
        (1 / 5 : ℝ) * Real.log (Real.log (Real.log x) - Real.log 53.99) := by
  let r := Real.log (53.99 : ℝ)
  let L := Real.log (Real.log x)
  have hA : 0 < leeLeongRate := by unfold leeLeongRate; positivity
  have hr : 0 < r := Real.log_pos (by norm_num)
  have hL : 0 < L := hr.trans hrL
  have hdiff : 0 < L - r := sub_pos.mpr hrL
  have hfac : 0 < 1 - r / L := sub_pos.mpr ((div_lt_one hL).mpr hrL)
  have hpow := Real.rpow_pos_of_pos hfac (-(1 / 5 : ℝ))
  have hV : 0 < vkProfile x :=
    div_pos (Real.rpow_pos_of_pos ht _) (Real.rpow_pos_of_pos hL _)
  refine ⟨mul_pos (mul_pos hA hpow) hV, ?_⟩
  have hlogV : Real.log (vkProfile x) = (3 / 5 : ℝ) * L - (1 / 5 : ℝ) * Real.log L := by
    unfold vkProfile
    rw [Real.log_div (Real.rpow_pos_of_pos ht _).ne' (Real.rpow_pos_of_pos hL _).ne',
      Real.log_rpow ht, Real.log_rpow hL]
  have hlogf : Real.log (1 - r / L) = Real.log (L - r) - Real.log L := by
    rw [show 1 - r / L = (L - r) / L by rw [sub_div, div_self hL.ne'], Real.log_div hdiff.ne' hL.ne']
  rw [leeLeongFullProfile, Real.log_mul (mul_pos hA hpow).ne' hV.ne',
    Real.log_mul hA.ne' hpow.ne', Real.log_rpow hfac, hlogf, hlogV]
  dsimp only [L, r]
  ring

/-- The iterated logarithm in the printed exponent saves a positive term in
the coefficient of the finite-window secant. -/
theorem leeLeongDelayedArg_eventually_secant_gain :
    ∀ᶠ x : ℝ in atTop, leeLeongFullProfile x - leeLeongFullProfile (leeLeongDelayedArg x) ≤
      ((3 / 5 : ℝ) - (1 / 5) / (Real.log (Real.log x) - Real.log 53.99)) * leeLeongFullProfile x ^ 2 / (Real.log x - leeLeongFullProfile x) := by
  let hd := leeLeongDelayedArg_tendsto_atTop
  have hll := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have ht := Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0:ℝ))
  have hL := hll.eventually (eventually_gt_atTop (Real.log (53.99 : ℝ)))
  filter_upwards [ht, hL, hd.eventually ht, hd.eventually hL,
    hll.eventually (eventually_ge_atTop (Real.log (53.99:ℝ) + 1))] with x htx hLx hty hLy hxlarge
  let d := leeLeongDelayedArg x
  let F := leeLeongFullProfile x
  let G := leeLeongFullProfile d
  let t := Real.log x
  let s := Real.log d
  have hs : 0 < s := hty
  have ht' : 0 < t := htx
  have hsval : s = t - F := Real.log_exp _
  obtain ⟨hF, hx⟩ := sharp_full_profile_log htx hLx
  obtain ⟨hG, hy⟩ := sharp_full_profile_log hty hLy
  change 0 < F at hF
  change 0 < G at hG
  have hst : s ≤ t := by linarith
  have hLs : Real.log s ≤ Real.log t := Real.log_le_log hs hst
  change Real.log (53.99:ℝ) < Real.log s at hLy
  let L := Real.log t
  let J := Real.log s
  let c := Real.log (53.99 : ℝ)
  let a := (3/5:ℝ) - (1/5)/(L-c)
  change c + 1 ≤ L at hxlarge
  have hden : 0 < L-c := by linarith
  have hJ : 0 < J-c := sub_pos.mpr hLy
  have ha : 0 ≤ a := by
    have h := div_le_self (by norm_num : (0:ℝ) ≤ 1/5) (show 1 ≤ L-c by linarith)
    dsimp only [a]
    linarith
  have huD := Real.log_le_sub_one_of_pos (div_pos hJ hden)
  rw [Real.log_div hJ.ne' hden.ne'] at huD
  have hmD := mul_le_mul_of_nonneg_right huD hden.le
  rw [sub_mul ((J-c)/(L-c)) 1 (L-c), div_mul_cancel₀ _ hden.ne', one_mul] at hmD
  have hLL : (L-J)/(L-c) ≤ Real.log (L-c) - Real.log (J-c) := by
    apply (div_le_iff₀ hden).mpr
    linarith only [hmD]
  change Real.log F = Real.log leeLeongRate + (3/5:ℝ) * Real.log t -
    (1/5:ℝ) * Real.log (Real.log t - Real.log 53.99) at hx
  change Real.log G = Real.log leeLeongRate + (3/5:ℝ) * Real.log s -
    (1/5:ℝ) * Real.log (Real.log s - Real.log 53.99) at hy
  change Real.log F = Real.log leeLeongRate + (3/5:ℝ)*L - (1/5:ℝ)*Real.log (L-c) at hx
  change Real.log G = Real.log leeLeongRate + (3/5:ℝ)*J - (1/5:ℝ)*Real.log (J-c) at hy
  have hlogFG : Real.log F - Real.log G ≤ a * (Real.log t - Real.log s) := by
    change _ ≤ a * (L-J)
    calc
      _ ≤ (3/5:ℝ)*(L-J) - (1/5:ℝ)*((L-J)/(L-c)) := by linarith only [hLL, hx, hy]
      _ = _ := by dsimp only [a]; ring
  have hz := Real.log_le_sub_one_of_pos (div_pos hG hF)
  rw [Real.log_div hG.ne' hF.ne'] at hz
  have hu := mul_le_mul_of_nonneg_right hz hF.le
  rw [sub_mul (G/F) 1 F, div_mul_cancel₀ _ hF.ne', one_mul] at hu
  have hsec := Real.log_le_sub_one_of_pos (div_pos ht' hs)
  rw [Real.log_div ht'.ne' hs.ne'] at hsec
  have hgap : t / s - 1 = F / s := by
    field_simp [hs.ne'] <;> linarith only [hsval]
  rw [hgap] at hsec
  change F - G ≤ a*F^2/(t - F)
  rw [← hsval]
  calc
    _ ≤ F * (Real.log F - Real.log G) := by linarith only [hu]
    _ ≤ F * (a * (Real.log t - Real.log s)) :=
      mul_le_mul_of_nonneg_left hlogFG hF.le
    _ ≤ F * (a * (F / s)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsec ha) hF.le
    _ = _ := by ring

/-- On the window [t − F, t], the loss is at most (3/5)F²/(t−F).
The denominator is exactly the logarithm of the translated argument. -/
theorem leeLeongDelayedArg_eventually_three_fifths :
    ∀ᶠ x : ℝ in atTop, leeLeongFullProfile x - leeLeongFullProfile (leeLeongDelayedArg x) ≤
      (3 / 5 : ℝ) * leeLeongFullProfile x ^ 2 / (Real.log x - leeLeongFullProfile x) := by
  have hh := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [leeLeongDelayedArg_eventually_secant_gain,
    hh.eventually (eventually_ge_atTop (Real.log (53.99:ℝ))),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (0:ℝ)),
    leeLeongFullProfile_eventually_le_mul_log (1/2) (by norm_num)] with x h hL ht hhalf
  apply h.trans
  apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ Real.log x - leeLeongFullProfile x)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact sub_le_self _ (div_nonneg (by norm_num) (sub_nonneg.mpr hL))

/-- Concrete envelope cost with the printed logarithmic prefactor retained. -/
theorem leeLeongDelayedDamping_eventually_three_fifths :
    ∀ᶠ x : ℝ in atTop, leeLeongDelayedDamping x ≤ (Real.log x)^2 *
      Real.exp (-leeLeongFullProfile x +
        (3/5:ℝ) * leeLeongFullProfile x^2 / (Real.log x - leeLeongFullProfile x)) := by
  filter_upwards [leeLeongDelayedArg_eventually_three_fifths] with x hx
  unfold leeLeongDelayedDamping
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hx])) (sq_nonneg _)

/-- The logarithmic factor saved by the printed profile pays for both the
denominator shift and the two logarithms outside the delayed exponential. -/
theorem leeLeongDelayedDamping_eventually_sharp_log_reserve :
    ∀ᶠ x : ℝ in atTop, leeLeongDelayedDamping x ≤ Real.exp (-leeLeongFullProfile x +
      (3/5:ℝ) * leeLeongFullProfile x^2 / Real.log x - 2*Real.log (Real.log x)) := by
  let c := Real.log (53.99 : ℝ)
  let KA := Real.log leeLeongRate
  have hc : 0 < c := Real.log_pos (by norm_num)
  have h100 : 0 < Real.log (100:ℝ) := Real.log_pos (by norm_num)
  have h40 : Real.log (40:ℝ) ≤ Real.log 100 := Real.log_le_log (by norm_num) (by norm_num)
  have h10 : Real.log (10:ℝ) ≤ Real.log 100 := Real.log_le_log (by norm_num) (by norm_num)
  have hh := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [leeLeongDelayedArg_eventually_secant_gain,
    hh.eventually (eventually_ge_atTop (100 * (|KA| + c + Real.log 100 + 10))),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0:ℝ)),
    leeLeongFullProfile_eventually_le_mul_log (1/2) (by norm_num)] with x hgain hbig ht hhalf
  let t := Real.log x
  let L := Real.log t
  let F := leeLeongFullProfile x
  let G := leeLeongFullProfile (leeLeongDelayedArg x)
  let s := t-F
  change (0:ℝ) < t at ht
  change 100 * (|KA| + c + Real.log 100 + 10) ≤ L at hbig
  change F ≤ (1/2)*t at hhalf
  have hL : 0 < L := by linarith only [hbig, abs_nonneg KA, hc, h100]
  have hcL : c < L := by linarith only [hbig, abs_nonneg KA, hc, h100]
  have hU := sub_pos.mpr hcL
  obtain ⟨hF, hf⟩ := sharp_full_profile_log ht hcL
  change 0 < F at hF
  change Real.log F = KA + (3/5:ℝ)*L - (1/5:ℝ)*Real.log (L-c) at hf
  have hs : 0 < s := by dsimp only [s]; linarith only [ht, hhalf]
  have hst : s ≤ t := sub_le_self _ hF.le
  have hlogL : Real.log L ≤ L / 50 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hL (by norm_num : (0:ℝ)<100))
    rw [Real.log_div hL.ne' (by norm_num : (100:ℝ) ≠ 0)] at h
    linarith only [h, hbig, abs_nonneg KA, hc, h100]
  have hlogU : Real.log (L-c) ≤ L/50 :=
    (Real.log_le_log hU (sub_le_self L hc.le)).trans hlogL
  have hsmall : 10 * (L-c) * F ≤ t := by
    apply (Real.log_le_log_iff (mul_pos (mul_pos (by norm_num) hU) hF) ht).mp
    rw [Real.log_mul (mul_pos (by norm_num : (0:ℝ)<10) hU).ne' hF.ne',
      Real.log_mul (by norm_num : (10:ℝ) ≠ 0) hU.ne', hf]
    change Real.log 10 + Real.log (L-c) + (KA + 3/5*L-1/5*Real.log (L-c)) ≤ L
    linarith only [hbig, le_abs_self KA, abs_nonneg KA, h10, hlogU, hc, h100]
  have hlarge : 40 * L * (L-c) * t ≤ F^2 := by
    have h40p : (0:ℝ)<40 := by norm_num
    apply (Real.log_le_log_iff (mul_pos (mul_pos (mul_pos h40p hL) hU) ht) (sq_pos_of_pos hF)).mp
    rw [Real.log_mul (mul_pos (mul_pos h40p hL) hU).ne' ht.ne',
      Real.log_mul (mul_pos h40p hL).ne' hU.ne', Real.log_mul h40p.ne' hL.ne',
      pow_two, Real.log_mul hF.ne' hF.ne', hf]
    change Real.log 40 + Real.log L + Real.log (L-c) + L ≤
      (KA + 3/5*L-1/5*Real.log (L-c)) + (KA + 3/5*L-1/5*Real.log (L-c))
    linarith only [hbig, neg_abs_le KA, abs_nonneg KA, h40, hlogU, hlogL, hc, h100]
  have hbr : t/10 ≤ (1/5)*t - (3/5)*(L-c)*F := by
    linarith only [hsmall, ht.le]
  have hpoly : (4*L)*t*s*(L-c) ≤ F^2 * ((1/5)*t - (3/5)*(L-c)*F) := by
    have h₁ := mul_le_mul_of_nonneg_left hst (show 0 ≤ (4*L)*t*(L-c) by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hlarge (show 0 ≤ t/10 by positivity)
    have h₃ := mul_le_mul_of_nonneg_left hbr (sq_nonneg F)
    nlinarith only [h₁, h₂, h₃]
  have hsum : ((3/5:ℝ) - (1/5)/(L-c))*F^2/s + 4*L ≤ (3/5:ℝ)*F^2/t := by
    apply (mul_le_mul_iff_left₀ (mul_pos (mul_pos hU hs) ht)).mp
    have e₁ : (((3/5:ℝ) - (1/5)/(L-c))*F^2/s + 4*L)*((L-c)*s*t) =
        ((3/5:ℝ)*(L-c)-1/5)*F^2*t + 4*L*(L-c)*s*t := by
      field_simp [hU.ne', hs.ne'] <;> ring
    have e₂ : ((3/5:ℝ)*F^2/t)*((L-c)*s*t) = (3/5:ℝ)*F^2*(L-c)*s := by
      field_simp [ht.ne'] <;> ring
    rw [e₁, e₂]
    dsimp only [s] at hpoly ⊢
    nlinarith only [hpoly]
  change F-G ≤ ((3/5:ℝ)-(1/5)/(L-c))*F^2/s at hgain
  change t^2 * Real.exp (-G) ≤ Real.exp (-F + (3/5:ℝ)*F^2/t - 2*L)
  have hpow : t^2 = Real.exp (2*L) := by
    rw [two_mul, Real.exp_add]
    change t^2 = Real.exp (Real.log t)*Real.exp (Real.log t)
    rw [Real.exp_log ht, pow_two]
  rw [hpow, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith only [hgain, hsum])

/-- Dropping the logarithmic reserve yields the sharp exponential envelope. -/
theorem leeLeongDelayedDamping_eventually_sharp_endpoint :
    ∀ᶠ x : ℝ in atTop, leeLeongDelayedDamping x ≤ Real.exp (-leeLeongFullProfile x +
      (3/5:ℝ) * leeLeongFullProfile x^2 / Real.log x) := by
  filter_upwards [leeLeongDelayedDamping_eventually_sharp_log_reserve,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually (eventually_ge_atTop (0:ℝ))]
    with x hx hL
  apply hx.trans (Real.exp_le_exp.mpr ?_)
  change 0 ≤ Real.log (Real.log x) at hL
  linarith

end RiemannResearch.RH.QMertensFirstMoment

/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.Quantitative.ClassicalStrongPNT
import Mathlib.Tactic

/-!
# The reciprocal of zeta in a classical zero-free strip

The Borel–Carathéodory argument for a logarithm of zeta uses only the
classical zero-free region and the logarithmic upper bound for zeta in
the repository. Compare the use of reciprocal estimates in Lee and Leong,
arXiv:2208.06141, §5.1, and the Möbius contour implementation of
G. Bialer, `MathExtras/NumberTheory/PrimeCounting/MobiusBoundaryBoundsClose.lean`.
-/
noncomputable section
open Complex Set
namespace RiemannResearch.NumberTheory.PrimeNumberTheorem
open Quantitative.ClassicalRegion

/-- If an analytic nonzero function is bounded by H on a disk and its
reciprocal at the center is at most H, the reciprocal is bounded by H²
on the concentric disk with one fifth of the radius. -/
theorem reciprocal_disk_fifth {f : ℂ → ℂ} {R r H : ℝ} (hr : 0 < r) (hrR : 5*r ≤ R)
    (hH : 1 < H) (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 R))
    (hn : ∀ z ∈ Metric.closedBall 0 R, f z ≠ 0)
    (hu : ∀ z ∈ Metric.ball 0 R, ‖f z‖ ≤ H) (hi : ‖(f 0)⁻¹‖ ≤ H) :
    ∀ z ∈ Metric.closedBall 0 r, ‖(f z)⁻¹‖ ≤ H^2 := by
  have hR : 0 < R := by linarith
  have hrR' : r < R := by linarith
  have hlog := Real.log_pos hH
  have hn0 : 0 < ‖f 0‖ := norm_pos_iff.mpr (hn 0 (Metric.mem_closedBall_self hR.le))
  have hc := Real.log_le_log (inv_pos.mpr hn0)
    (show ‖f 0‖⁻¹ ≤ H by simpa only [norm_inv] using hi)
  rw [Real.log_inv] at hc
  obtain ⟨J,hJa,hJ0,_,hJr⟩ := LogOfAnalyticFunction hr hrR' hf hn
  have hupper (z : ℂ) (hz : z ∈ Metric.ball 0 R) : (J z).re ≤ 2*Real.log H := by
    rw [← hJr z hz]
    have hp := norm_pos_iff.mpr (hn z (Metric.ball_subset_closedBall hz))
    linarith only [Real.log_le_log hp (hu z hz),hc]
  intro z hz
  have hsmall := borelCaratheodory' (by positivity : 0 < 2*Real.log H) hR hrR'
    hJa.analyticOn hJ0 hupper hz
  have hJle : ‖J z‖ ≤ Real.log H := hsmall.trans (by
    apply (div_le_iff₀ (sub_pos.mpr hrR')).2
    nlinarith only [mul_le_mul_of_nonneg_right hrR hlog.le])
  have hzR : z ∈ Metric.ball 0 R := Metric.closedBall_subset_ball hrR' hz
  have hzpos := norm_pos_iff.mpr (hn z (Metric.ball_subset_closedBall hzR))
  have hlo := (abs_le.mp ((Complex.abs_re_le_norm _).trans hJle)).1
  have hlogbound : -Real.log ‖f z‖ ≤ 2*Real.log H := by
    linarith only [hlo,hJr z hzR,hc]
  have he := Real.exp_le_exp.mpr hlogbound
  rw [Real.exp_neg, Real.exp_log hzpos, show 2*Real.log H = Real.log H + Real.log H by ring,
    Real.exp_add, Real.exp_log (zero_lt_one.trans hH)] at he
  simpa only [norm_inv, pow_two] using he

private theorem inv_zeta_right_of_log_center {a K σ t : ℝ} (ha : 0 < a)
    (hK : 0 ≤ K) (ht : 3 < |t|) (hσ : σ ≤ 2)
    (hlower : a / Real.log |t| ≤ σ-1)
    (hr : ∀ {u : ℝ}, u ∈ Ioc 1 2 → ∀ v : ℝ, 3 < |v| →
      1 / ‖riemannZeta ((u : ℂ) + v*I)‖ ≤
        K * (u-1)^(-(3:ℝ)/4) * (Real.log |v|)^((1:ℝ)/4)) :
    ‖(riemannZeta ((σ : ℂ) + t*I))⁻¹‖ ≤ (K * a^(-(3:ℝ)/4)) * Real.log |t| := by
  let L := Real.log |t|
  have hL : 0 < L := Real.log_pos (by linarith)
  have haL : 0 < a/L := div_pos ha hL
  have hσ1 : 1 < σ := by linarith
  have hm := Real.rpow_le_rpow_of_nonpos haL hlower (by norm_num : -(3:ℝ)/4 ≤ 0)
  have he : (a/L)^(-(3:ℝ)/4) * L^((1:ℝ)/4) = a^(-(3:ℝ)/4) * L := by
    have hsum : L^((3:ℝ)/4) * L^((1:ℝ)/4) = L := by rw [← Real.rpow_add hL]; norm_num
    rw [Real.div_rpow ha.le hL.le,
      show -(3:ℝ)/4 = -((3:ℝ)/4) by ring, Real.rpow_neg hL.le,
      div_inv_eq_mul, mul_assoc, hsum]
  have hraw := hr (u := σ) ⟨hσ1,hσ⟩ t ht
  rw [norm_inv, ← one_div]
  calc
    _ ≤ K * (σ-1)^(-(3:ℝ)/4) * L^((1:ℝ)/4) := hraw
    _ ≤ K * (a/L)^(-(3:ℝ)/4) * L^((1:ℝ)/4) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hK) (Real.rpow_nonneg hL.le _)
    _ = _ := by rw [mul_assoc, he, mul_assoc]

/-- A single log-squared reciprocal bound on the full high strip. The
coefficient of its width can be chosen at most the PNT+ classical constant F. -/
theorem classical_inv_zeta_high_strip :
    ∃ a : ℝ, 0 < a ∧ a ≤ F ∧ ∃ C : ℝ, 0 < C ∧
      ∀ σ t : ℝ, 4 ≤ |t| → 1 - a / Real.log |t| ≤ σ → σ ≤ 2 →
        ‖(riemannZeta ((σ : ℂ) + t*I))⁻¹‖ ≤ C * (Real.log (2 + |t|))^2 := by
  obtain ⟨A,hA,U,hU,hupper⟩ := ZetaUpperBnd
  obtain ⟨K,hK,hright⟩ := ZetaInvBound2
  let a : ℝ := min F A / 24
  have ha : 0 < a := div_pos (lt_min FinIoo.1 hA.1) (by norm_num)
  have haF : 24*a ≤ F := by dsimp [a]; linarith [min_le_left F A]
  have haA : 24*a ≤ A := by dsimp [a]; linarith [min_le_right F A]
  have hat : a ≤ 1/48 := by linarith [hA.2]
  let k : ℝ := max 2 (max (2*U) (K*a^(-(3:ℝ)/4)))
  have hk2 : 2 ≤ k := le_max_left _ _
  have hkU : 2*U ≤ k := (le_max_left _ _).trans (le_max_right _ _)
  have hkK : K*a^(-(3:ℝ)/4) ≤ k := (le_max_right _ _).trans (le_max_right _ _)
  have hk0 : 0 < k := by linarith
  refine ⟨a,ha,by linarith,k^2,sq_pos_of_pos hk0, ?_⟩
  intro σ t ht hσ hσ2
  let L := Real.log |t|
  let u := 1+a/L
  let R := 12*a/L
  let r := 2*a/L
  let w : ℂ := (u : ℂ) + t*I
  let f : ℂ → ℂ := fun z => riemannZeta (z+w)
  have hL1 : 1 ≤ L := (logt_gt_one (by linarith : 3 ≤ |t|)).le
  have hL : 0 < L := by linarith
  have haL : 0 < a/L := div_pos ha hL
  have hRlo : 0 < R := div_pos (by positivity) hL
  have hRsmall : R ≤ 1/2 := by
    exact (div_le_self (by positivity : 0 ≤ 12*a) hL1).trans (by linarith)
  have hulo : 1 < u := by dsimp [u]; linarith
  have huhi : u ≤ 2 := by
    dsimp [u]; linarith [div_le_self ha.le hL1]
  have Hgt : 1 < k*L := by nlinarith [mul_le_mul_of_nonneg_left hL1 (by linarith : 0 ≤ k)]
  have hright' (s : ℝ) (hus : u ≤ s) (hs2 : s ≤ 2) :
      ‖(riemannZeta ((s : ℂ)+t*I))⁻¹‖ ≤ k*L :=
    (inv_zeta_right_of_log_center ha hK.le (by linarith) hs2 (by dsimp [u] at hus; linarith) hright).trans
      (mul_le_mul_of_nonneg_right hkK hL.le)
  have hwwRe : w.re = u := by simp [w]
  have hwwIm : w.im = t := by simp [w]
  have hgeom (z : ℂ) (hz : z ∈ Metric.closedBall 0 R) :
      z+w ≠ 1 ∧ riemannZeta (z+w) ≠ 0 ∧ ‖riemannZeta (z+w)‖ ≤ k*L := by
    have hn : ‖z‖ ≤ R := by simpa only [dist_zero_right] using Metric.mem_closedBall.mp hz
    have hzre := abs_le.mp ((Complex.abs_re_le_norm z).trans hn)
    have hzim := (Complex.abs_im_le_norm z).trans hn
    have hire : (z+w).re = z.re+u := by rw [Complex.add_re,hwwRe]
    have hiim : (z+w).im = z.im+t := by rw [Complex.add_im,hwwIm]
    have htLo : |t| - R ≤ |(z+w).im| := by
      have hh := abs_add_le (z.im+t) (-z.im)
      rw [show z.im+t + -z.im = t by ring,abs_neg] at hh
      rw [hiim]; linarith only [hh,hzim]
    have htHi : |(z+w).im| ≤ |t|+1 := by
      rw [hiim]; linarith [abs_add_le z.im t]
    have hhi : 3 < |(z+w).im| := by linarith
    have hhp : 0 < |(z+w).im| := by linarith
    have hlogp : 0 < Real.log |(z+w).im| := Real.log_pos (by linarith)
    have htSq : |(z+w).im| ≤ |t|^2 := by nlinarith only [ht, htHi, sq_nonneg (|t|-2)]
    have hloghi : Real.log |(z+w).im| ≤ 2*L := by
      simpa only [Real.log_pow, Nat.cast_ofNat, L] using Real.log_le_log hhp htSq
    have hwidth (P : ℝ) (hp : 22*a ≤ P) :
        11*a/L ≤ P/Real.log |(z+w).im| := by
      apply (div_le_div_iff₀ hL hlogp).2
      calc
        _ ≤ (11*a)*(2*L) := mul_le_mul_of_nonneg_left hloghi (by positivity)
        _ = (22*a)*L := by ring
        _ ≤ P*L := mul_le_mul_of_nonneg_right hp hL.le
    have hReLo : 1-11*a/L ≤ (z+w).re := by
      rw [hire]; dsimp [u]; dsimp [R] at hzre
      have he : a/L - 12*a/L = -(11*a/L) := by ring
      linarith only [hzre.1,he]
    have hReHi : (z+w).re ≤ 2 := by
      rw [hire]; dsimp [u]; linarith [hzre.2,div_le_self ha.le hL1]
    have hnot1 : z+w ≠ 1 := by rintro hz; rw [hz] at hhi; norm_num at hhi
    have hFE : F < E := by rw [Fequ]; linarith [EinIoo.1]
    have hnz : riemannZeta (z+w) ≠ 0 := by
      intro hzero
      have hzb := ZeroInequalitySpec (z+w) hzero _ rfl _ rfl (by linarith)
      have hw := hwidth F (by linarith)
      linarith only [hReLo,hzb,hw,div_lt_div_of_pos_right hFE hlogp]
    have hwA := hwidth A (by linarith)
    have hzeroU := hupper (z+w).re (z+w).im hhi ⟨by linarith,hReHi⟩
    rw [Complex.re_add_im] at hzeroU
    refine ⟨hnot1, hnz, hzeroU.trans ?_⟩
    calc
      _ ≤ U*(2*L) := mul_le_mul_of_nonneg_left hloghi hU.le
      _ = (2*U)*L := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hkU hL.le
  have hbnd : ‖(riemannZeta ((σ : ℂ) + t*I))⁻¹‖ ≤ (k*L)^2 := by
    by_cases hsu : u ≤ σ
    · exact (hright' σ hsu hσ2).trans (by nlinarith only [Hgt, sq_nonneg (k*L-1)])
    have hr : 0 < r := div_pos (by positivity) hL
    have hrR : 5*r ≤ R := by
      calc
        5*r = 10*a/L := by dsimp [r]; ring
        _ ≤ 12*a/L := div_le_div_of_nonneg_right (by linarith) hL.le
    have hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 R) := by
      intro z hz
      have hg : AnalyticAt ℂ (fun v : ℂ => v+w) z := analyticAt_id.add analyticAt_const
      change AnalyticAt ℂ (riemannZeta ∘ (fun v : ℂ => v+w)) z
      apply AnalyticAt.comp
      · exact analyticAt_riemannZeta (hgeom z hz).1
      · exact hg
    have hb := reciprocal_disk_fifth hr hrR Hgt hf (fun z hz => (hgeom z hz).2.1)
      (fun z hz => (hgeom z (Metric.ball_subset_closedBall hz)).2.2)
      (by simpa [f,w] using hright' u le_rfl huhi)
    let z : ℂ := ((σ-u : ℝ) : ℂ)
    have hz : z ∈ Metric.closedBall 0 r := by
      apply Metric.mem_closedBall.mpr
      rw [dist_zero_right]
      change ‖((σ-u : ℝ) : ℂ)‖ ≤ 2*a/L
      rw [Complex.norm_real, Real.norm_eq_abs]
      apply abs_le.mpr
      constructor
      · dsimp [u]; change 1-a/L ≤ σ at hσ
        have he : a/L+a/L=2*a/L := by ring
        linarith only [hσ,he]
      · have hs : σ ≤ u := le_of_not_ge hsu
        exact (sub_nonpos.mpr hs).trans (by positivity : 0 ≤ 2*a/L)
    have harg : z+w = (σ : ℂ)+t*I := by dsimp [z,w]; push_cast; ring
    simpa only [f,harg] using hb z hz
  have hbig : L ≤ Real.log (2+|t|) := Real.log_le_log (by linarith) (by linarith)
  have hs := pow_le_pow_left₀ hL.le hbig 2
  exact hbnd.trans (by simpa only [mul_pow] using mul_le_mul_of_nonneg_left hs (sq_nonneg k))

end RiemannResearch.NumberTheory.PrimeNumberTheorem

/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ActualMollifierSignedBoundaryBudget
import RiemannResearch.Analysis.ActualZeroDensityCauchyDetector
import RiemannResearch.Analysis.ConreyBaluyotHorizontalPhase
import Mathlib.Tactic

/-!
# The horizontal argument of the actual Ingham detector

Jensen's formula for the real-part symmetrization bounds the crossings on
the segment from 1/2 to 3/2. The right-hand real part anchors the logarithm
of the quadratic detector. The resulting two horizontal integrals are
uniform in the height and in the independent Möbius cutoff.
-/

noncomputable section

open Complex Set MeasureTheory
namespace RiemannResearch.Analysis.InghamMollifier
open RiemannResearch.Analysis.ConreyBaluyot

private theorem detector_right_real_lower {X : ℕ} (hX : 72 ≤ X)
    {s : ℂ} (hs : s.re = 3 / 2) : 1 / 2 ≤ (zetaDetector X s).re := by
  let e := riemannZeta s * mollifier X s - 1
  have hXp : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hX' : (72 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have he : ‖e‖ ≤ 6 / Real.sqrt (X : ℝ) := mollifier_error_norm_le_right (by omega) hs
  have he2 : ‖e‖ ^ 2 ≤ 36 / (X : ℝ) := by
    calc
      ‖e‖ ^ 2 ≤ (6 / Real.sqrt (X : ℝ)) ^ 2 := by
        simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg e) he
      _ = 36 / (X : ℝ) := by rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg X)]; norm_num
  have h2 : 36 / (X : ℝ) ≤ 1 / 2 := (div_le_iff₀ hXp).mpr (by linarith)
  have hreal := Complex.re_le_norm (e ^ 2)
  rw [norm_pow] at hreal
  rw [zetaDetector_eq_one_sub_error_sq, Complex.sub_re, Complex.one_re]
  change _ ≤ 1 - (e ^ 2).re
  linarith

private theorem detector_disk_bound (X : ℕ) {t : ℝ} (ht : 3 ≤ t)
    {w : ℂ} (hw : 1 / 4 ≤ w.re) (hi : 1 ≤ w.im) (hn : |w.im - t| ≤ 5 / 4) :
    ‖zetaDetector X w‖ ≤ 128 * ((t + 2) * ((X : ℝ) + 1)) ^ 2 := by
  let P := (t + 2) * ((X : ℝ) + 1)
  have hP : 1 ≤ P := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith [Nat.cast_nonneg (α := ℝ) X])
  have him : 1 ≤ |w.im| := by rwa [abs_of_nonneg (by linarith : 0 ≤ w.im)]
  have hz : ‖riemannZeta w‖ ≤ 13 / 2 * |w.im| := by
    have h := Zeta23.RvM.riemannZeta_linear_growth (δ := (1 / 4 : ℝ)) (by norm_num) hw him
    norm_num at h ⊢
    exact h
  have hi' := (abs_le.mp hn).2
  rw [abs_of_nonneg (by linarith : 0 ≤ w.im)] at hz
  have hz' : ‖riemannZeta w‖ ≤ 7 * (t + 2) := by linarith
  have hm := mollifier_norm_le_cutoff X (by linarith : 0 ≤ w.re)
  have hprod : ‖riemannZeta w * mollifier X w‖ ≤ 7 * P := by
    rw [norm_mul]
    have hm' : ‖mollifier X w‖ ≤ (X : ℝ) + 1 := by linarith
    simpa only [P, mul_assoc] using
      mul_le_mul hz' hm' (norm_nonneg _) (by linarith : 0 ≤ 7 * (t + 2))
  have he := norm_sub_le (riemannZeta w * mollifier X w) 1
  rw [norm_one] at he
  have he' : ‖riemannZeta w * mollifier X w - 1‖ ≤ 8 * P := by linarith
  have he2 := mul_self_le_mul_self (norm_nonneg _) he'
  have h := norm_sub_le (1 : ℂ) ((riemannZeta w * mollifier X w - 1) ^ 2)
  rw [norm_one, norm_pow] at h
  rw [zetaDetector_eq_one_sub_error_sq]
  change _ ≤ 128 * P ^ 2
  nlinarith [sq_nonneg (P - 1)]

private def horizontalLogConstant : ℝ :=
  ((Real.log 256 + 2) / Real.log (5/4) + 3) * Real.pi

private theorem horizontalLogConstant_pos : 0 < horizontalLogConstant := by
  have h₁ : 0 < Real.log 256 := Real.log_pos (by norm_num)
  have h₂ : 0 < Real.log (5/4) := Real.log_pos (by norm_num)
  unfold horizontalLogConstant
  positivity

/-- The normalized lift on any zero-free horizontal segment satisfies a
logarithmic integral estimate; its cutoff and its ordinate are independent. -/
private theorem detector_horizontal_logLift {X : ℕ} (hX : 72 ≤ X) {t α : ℝ}
    (ht : 3 ≤ t) (hα : 1 / 2 ≤ α) (hab : α ≤ 3 / 2)
    {L : ℝ → ℂ} (hL : Continuous L)
    (he : ∀ x ∈ Icc α (3 / 2), exp (L x) = zetaDetector X ((x : ℂ) + (t : ℂ) * I))
    (hright : L (3 / 2) = log (zetaDetector X (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I))) :
    ‖∫ x in α..(3 / 2), (L x).im‖ ≤
      horizontalLogConstant * (1 + Real.log (t + 2) + Real.log ((X : ℝ) + 1)) := by
  classical
  let P := (t + 2) * ((X : ℝ) + 1)
  let M := 128 * P ^ 2
  let K := 1 + Real.log (t + 2) + Real.log ((X : ℝ) + 1)
  have hP : 1 ≤ P := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith [Nat.cast_nonneg (α := ℝ) X])
  have hM : 1 ≤ M := by dsimp [M]; nlinarith [sq_nonneg (P - 1)]
  have hf (w : ℂ) (hw : 0 < w.im) : DifferentiableAt ℂ (zetaDetector X) w := by
    have hne : w ≠ 1 := by rintro rfl; simp at hw
    exact (Complex.quadraticZeroDetector_analyticAt
      (analyticAt_riemannZeta hne) (mollifier_analyticAt X w)).differentiableAt
  obtain ⟨hfin, hcard⟩ := horizontalRealZeros_jensen_bound (zetaDetector X)
    t (3/2) (1/4) 1 (5/4) M (by norm_num) (by norm_num) (by linarith) (by norm_num)
    hM hf (fun _w hw hi hn => detector_disk_bound X ht hw hi hn)
    (detector_right_real_lower hX (by simp))
  let S := hfin.toFinset
  have hcover (x : ℝ) (hx : x ∈ Icc α (3/2)) (hc : Real.cos (L x).im = 0) : x ∈ S := by
    apply hfin.mem_toFinset.mpr
    refine ⟨⟨by linarith [hx.1], hx.2⟩, ?_⟩
    rw [← he x hx, Complex.exp_re, hc, mul_zero]
  have hdisp := continuous_phase_uniform_le_of_crossing_cover (fun x => (L x).im)
    α (3/2) S hab (Complex.continuous_im.comp hL).continuousOn hcover
  have harg : |(L (3/2)).im| ≤ Real.pi := by
    rw [hright, Complex.log_im]
    exact Complex.abs_arg_le_pi _
  have ht0 : 0 < t + 2 := by linarith
  have hx0 : 0 < (X : ℝ) + 1 := by positivity
  have hlt : 0 ≤ Real.log (t + 2) := Real.log_nonneg (by linarith)
  have hlx : 0 ≤ Real.log ((X : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) X])
  have hK : 1 ≤ K := by dsimp [K]; linarith
  have hc : 0 ≤ Real.log 256 := Real.log_nonneg (by norm_num)
  have hd : 0 < Real.log (5/4) := Real.log_pos (by norm_num)
  have hlog : Real.log (2 * M) ≤ (Real.log 256 + 2) * K := by
    have hp : 2 * M = 256 * P ^ 2 := by dsimp [M]; ring
    rw [hp, Real.log_mul (by norm_num) (pow_ne_zero 2 (ne_of_gt (by linarith : 0 < P))),
      Real.log_pow, show Real.log P = Real.log (t + 2) + Real.log ((X : ℝ) + 1)
        from Real.log_mul ht0.ne' hx0.ne']
    dsimp [K]
    nlinarith [mul_nonneg hc hlt, mul_nonneg hc hlx]
  have hS : (S.card : ℝ) ≤ (Real.log 256 + 2) / Real.log (5/4) * K := by
    have hcard' : (S.card : ℝ) ≤ Real.log (2 * M) / Real.log (5/4) := by
      simpa only [div_one] using hcard
    refine hcard'.trans ((div_le_div_of_nonneg_right hlog hd.le).trans_eq ?_)
    ring
  have hbound (x : ℝ) (hx : x ∈ Icc α (3/2)) : |(L x).im| ≤ horizontalLogConstant * K := by
    have htriangle : |(L x).im| ≤ |(L x).im - (L (3/2)).im| + |(L (3/2)).im| := by
      calc
        _ = |((L x).im - (L (3/2)).im) + (L (3/2)).im| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
    have hxc := (htriangle.trans (add_le_add (hdisp x hx) harg))
    have hsc : (S.card : ℝ) + 3 ≤ ((Real.log 256 + 2) / Real.log (5/4) + 3) * K := by
      linarith
    unfold horizontalLogConstant
    nlinarith only [hxc, mul_le_mul_of_nonneg_right hsc Real.pi_pos.le]
  have hInt : ‖∫ x in α..(3/2), (L x).im‖ ≤ (horizontalLogConstant * K) * |3/2 - α| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    simpa only [Real.norm_eq_abs] using hbound x ⟨hx.1.le, hx.2⟩
  have hh : |3/2 - α| ≤ 1 := by rw [abs_of_nonneg (sub_nonneg.mpr hab)]; linarith
  exact hInt.trans (mul_le_of_le_one_right
    (mul_nonneg horizontalLogConstant_pos.le (by linarith)) hh)

/-- The two horizontal integrals in the classical Littlewood count are
uniformly logarithmic for every compatible contour pair. -/
theorem exists_zetaDetector_horizontal_difference_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : ℕ}, 72 ≤ X → ∀ {H T α : ℝ}, 3 ≤ H → H ≤ T →
      1 / 2 ≤ α → α ≤ 3 / 2 →
      (∀ s ∈ RectangleBorder ((α : ℂ) + (H : ℂ) * I)
        (((3/2 : ℝ) : ℂ) + (T : ℂ) * I), zetaDetector X s ≠ 0) →
      ∀ B U : ℝ → ℂ, Continuous B → Continuous U →
        (RectangleIntegral'
          (fun s => (s - ((α : ℂ) + (H : ℂ) * I)) * logDeriv (zetaDetector X) s)
          ((α : ℂ) + (H : ℂ) * I) (((3/2 : ℝ) : ℂ) + (T : ℂ) * I)).re =
          logRectangleBoundary (zetaDetector X)
            (fun x => (B x).im) (fun x => (U x).im) α (3/2) H T / (2 * Real.pi) →
        (∫ x in α..(3/2), (U x).im) - (∫ x in α..(3/2), (B x).im) ≤
          C * (1 + Real.log (T + 2) + Real.log ((X : ℝ) + 1)) := by
  refine ⟨2 * horizontalLogConstant, mul_pos (by norm_num) horizontalLogConstant_pos, ?_⟩
  intro X hX H T α hH hHT hα hab hborder B U _hBc _hUc hBU
  obtain ⟨B₀, U₀, hB₀, hU₀, heB, heU, hid, hrB, hrU⟩ :=
    Complex.exists_logRectangleBoundary_eq_contour hab hHT
      (zetaDetector_analyticOnNhd_rectangle X hab (by linarith) hHT) hborder
  have hslit (t : ℝ) (_ : t ∈ Icc H T) :
      zetaDetector X (((3/2 : ℝ) : ℂ) + (t : ℂ) * I) ∈ Complex.slitPlane := by
    have hr := detector_right_real_lower hX
      (s := ((3/2 : ℝ) : ℂ) + (t : ℂ) * I) (by simp)
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith))
  have hbottom := detector_horizontal_logLift hX hH hα hab hB₀ heB hrB
  have htop := detector_horizontal_logLift hX (hH.trans hHT) hα hab hU₀ heU (hrU hslit)
  have hsame := (div_left_inj' (by positivity : 2 * Real.pi ≠ 0)).mp (hBU.symm.trans hid)
  unfold logRectangleBoundary at hsame
  have hbottom' := (neg_abs_le (∫ x in α..(3/2), (B₀ x).im))
  rw [Real.norm_eq_abs] at hbottom htop
  have htop' := le_abs_self (∫ x in α..(3/2), (U₀ x).im)
  have hlog := Real.log_le_log (by linarith : 0 < H + 2) (by linarith : H + 2 ≤ T + 2)
  have hbound := mul_le_mul_of_nonneg_left hlog horizontalLogConstant_pos.le
  linarith

end RiemannResearch.Analysis.InghamMollifier

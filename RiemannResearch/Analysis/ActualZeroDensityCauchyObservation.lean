import RiemannResearch.Analysis.ActualZeroDensityCauchyDetector
import RiemannResearch.Analysis.ActualInghamCriticalMoment
import Mathlib.Tactic

/-! # A critical-line integral detecting one zero off the critical line -/

noncomputable section
open Complex Filter Set MeasureTheory
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.InghamMollifier
open MontgomeryPoisson

theorem critical_error_continuous (X : ℕ) :
    Continuous (fun t : ℝ => ‖mollifiedError X ((1 / 2 : ℂ) + (t : ℂ) * I)‖) := by
  simpa [mollifiedError, mul_comm (I : ℂ) _] using
    (((continuous_critical_zeta.mul (continuous_vertical_mollifier X (1 / 2))).sub
      continuous_const).norm)

private theorem gaussian_detector_norm_le {X : ℕ} {L a v : ℝ} {s ρ : ℂ}
    (hre : (s.re - ρ.re) ^ 2 ≤ 1) (ha : 0 < a) (hd : a ≤ ‖s - ρ‖)
    (hv : ‖mollifiedError X s‖ * Real.exp (L * (s.re - 1 / 2)) ≤ v) :
    ‖cauchyDetector X L ρ s‖ ≤
      (v * Real.exp 1 / a) * cauchyWeight (s.im - ρ.im) := by
  have hga := gaussian_le_cauchyWeight (s.im - ρ.im)
  have hw : 0 ≤ cauchyWeight (s.im - ρ.im) := by unfold cauchyWeight; positivity
  rw [norm_cauchyDetector, sub_eq_add_neg, Real.exp_add, Real.exp_add]
  calc
    _ = ((‖mollifiedError X s‖ * Real.exp (L * (s.re - 1 / 2))) *
          Real.exp ((s.re - ρ.re) ^ 2) * Real.exp (-(s.im - ρ.im) ^ 2)) / ‖s - ρ‖ := by ring
    _ ≤ (v * Real.exp 1 * cauchyWeight (s.im - ρ.im)) / a := by
      have hv0 : 0 ≤ v := (show 0 ≤ ‖mollifiedError X s‖ * Real.exp (L * (s.re - 1 / 2)) by positivity).trans hv
      have hprod := mul_le_mul (mul_le_mul hv (Real.exp_le_exp.mpr hre) (Real.exp_pos _).le hv0)
        hga (Real.exp_pos _).le (mul_nonneg hv0 (Real.exp_pos _).le)
      exact (div_le_div_of_nonneg_right hprod (norm_nonneg _)).trans
        (div_le_div_of_nonneg_left (by positivity) ha hd)
    _ = _ := by ring

private theorem detector_horizontal_bound {X : ℕ} {L T : ℝ} {ρ s : ℂ}
    (hL : 1 ≤ L) (hT : T = Real.exp (4 * L)) (hX : (X : ℝ) ≤ 2 * T)
    (hβ : 1 / 2 ≤ ρ.re) (hβ' : ρ.re ≤ 1)
    (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 3 / 2)
    (hy : 1 ≤ |s.im|) (hy' : |s.im| ≤ 2 * T)
    (hd : 4 * L ≤ |s.im - ρ.im|) :
    ‖cauchyDetector X L ρ s‖ ≤ 20 * Real.exp 1 := by
  have hT1 : 1 ≤ T := by rw [hT]; exact Real.one_le_exp (by linarith)
  have hm := mollifiedError_norm_le_on_horizontal hT1 hX hs hy hy'
  have hsq : (s.re - ρ.re) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - (s.re - ρ.re) by linarith)
      (show 0 ≤ 1 + (s.re - ρ.re) by linarith)]
  have hds : 9 * L ≤ (s.im - ρ.im) ^ 2 := by
    nlinarith [sq_abs (s.im - ρ.im), mul_self_le_mul_self (by linarith : 0 ≤ 4 * L) hd,
      mul_nonneg (show 0 ≤ L by linarith) (show 0 ≤ L - 1 by linarith)]
  have hfac : L * (s.re - 1 / 2) ≤ L := by
    nlinarith [mul_nonneg (show 0 ≤ L by linarith) (show 0 ≤ 3 / 2 - s.re by linarith)]
  have he : Real.exp (L * (s.re - 1 / 2) + (s.re - ρ.re) ^ 2 - (s.im - ρ.im) ^ 2) ≤
      Real.exp (1 - 8 * L) := Real.exp_le_exp.mpr (by linarith)
  have hn : 1 ≤ ‖s - ρ‖ := by
    have hi := Complex.abs_im_le_norm (s - ρ)
    rw [Complex.sub_im] at hi
    linarith
  rw [norm_cauchyDetector]
  calc
    _ ≤ (20 * T ^ 2) * Real.exp (1 - 8 * L) := by
      apply (div_le_self (by positivity) hn).trans
      exact mul_le_mul hm he (Real.exp_pos _).le (by positivity)
    _ = 20 * Real.exp 1 := by
      rw [hT, sq, ← Real.exp_add]
      calc
        _ = 20 * (Real.exp (4 * L + 4 * L) * Real.exp (1 - 8 * L)) := by ring
        _ = _ := by rw [← Real.exp_add]; ring_nf

/-- The residue is exponentially large at a zero right of the chosen line.
The left contribution is a local average of the actual mixed moment error. -/
theorem cauchyDetector_one_zero {X : ℕ} {L T : ℝ} {ρ : ℂ}
    (hL : 2 ≤ L) (hT : T = Real.exp (4 * L))
    (hX : T ≤ (X : ℝ)) (hX' : (X : ℝ) ≤ 2 * T)
    (hβ : 1 ≤ L * (ρ.re - 1 / 2)) (hβ' : ρ.re < 1)
    (hγ : Real.exp (2 * L) < ρ.im) (hγ' : ρ.im ≤ T) (hz : riemannZeta ρ = 0) :
    Real.exp (L * (ρ.re - 1 / 2)) ≤ 40 * Real.exp 1 +
      ∫ t in (1 : ℝ)..2 * T, (12 * Real.exp 1 +
        L * Real.exp 1 * ‖mollifiedError X ((1 / 2 : ℂ) + (t : ℂ) * I)‖) *
          cauchyWeight (t - ρ.im) := by
  let K := cauchyDetector X L ρ
  let A : ℝ → ℝ := fun t => ‖mollifiedError X ((1 / 2 : ℂ) + (t : ℂ) * I)‖
  let w : ℝ → ℝ := fun t => cauchyWeight (t - ρ.im)
  let z₀ : ℂ := (1 / 2 : ℂ) + I
  let z₁ : ℂ := (3 / 2 : ℂ) + ((2 * T : ℝ) : ℂ) * I
  have hLp : 0 < L := by linarith
  have hT1 : 1 ≤ T := by rw [hT]; exact Real.one_le_exp (by linarith)
  have hHs : 1 + 4 * L ≤ Real.exp (2 * L) := by
    have h := Real.add_one_le_exp L
    rw [show 2 * L = L + L by ring, Real.exp_add]
    nlinarith [mul_self_le_mul_self (show 0 ≤ L + 1 by linarith) h,
      mul_nonneg (show 0 ≤ L by linarith) (show 0 ≤ L - 2 by linarith)]
  have hHT : Real.exp (2 * L) ≤ T := by rw [hT]; exact Real.exp_le_exp.mpr (by linarith)
  have hb : 1 / 2 < ρ.re := by by_contra! h; nlinarith [mul_nonpos_of_nonneg_of_nonpos hLp.le (sub_nonpos.mpr h)]
  have hre : z₀.re ≤ z₁.re := by norm_num [z₀,z₁]
  have him : z₀.im ≤ z₁.im := by simp [z₀,z₁]; linarith
  have hint : Rectangle z₀ z₁ ∈ 𝓝 ρ := by
    rw [rectangle_mem_nhds_iff, uIoo_of_le hre, uIoo_of_le him, mem_reProdIm, mem_Ioo]
    simp [z₀,z₁]
    exact ⟨⟨by simpa [one_div] using hb, by linarith⟩, by linarith, by linarith⟩
  have hres := cauchyDetector_rectangle X L hre him (by norm_num [z₀]) hint hz
  have fac : ‖(1 / (2 * (Real.pi : ℂ) * I) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [show ‖(2 : ℂ)‖ = 2 by norm_num, mul_one, div_le_one (by positivity)]
    linarith [Real.pi_gt_three]
  have hraw : Real.exp (L * (ρ.re - 1 / 2)) ≤ ‖RectangleIntegral K z₀ z₁‖ := by
    have hr := congrArg norm hres
    rw [norm_neg, Complex.norm_exp] at hr
    have he : (((L : ℂ) * (ρ - (1 / 2 : ℂ))).re) = L * (ρ.re - 1 / 2) := by simp [Complex.mul_re]
    rw [he] at hr
    calc
      _ = ‖(1 / (2 * (Real.pi : ℂ) * I) : ℂ)‖ * ‖RectangleIntegral K z₀ z₁‖ := by
        simpa [RectangleIntegral', K, norm_smul] using hr.symm
      _ ≤ _ := mul_le_of_le_one_left (norm_nonneg _) fac
  have hH {y : ℝ} (hy : 1 ≤ y) (hy' : y ≤ 2 * T) (hd : 4 * L ≤ |y - ρ.im|) :
      ‖HIntegral K (1 / 2) (3 / 2) y‖ ≤ 20 * Real.exp 1 := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (1 / 2 : ℝ)) (b := (3 / 2 : ℝ)) (C := 20 * Real.exp 1)
      (f := fun x : ℝ => K ((x : ℂ) + (y : ℂ) * I)) (by
        intro x hx
        rw [uIoc_of_le (by norm_num)] at hx
        apply detector_horizontal_bound (by linarith : 1 ≤ L) hT hX' hb.le hβ'.le
        · simpa using hx.1.le
        · simpa using hx.2
        · simpa [abs_of_nonneg (by linarith : 0 ≤ y)] using hy
        · simpa [abs_of_nonneg (by linarith : 0 ≤ y)] using hy'
        · simpa using hd)
    norm_num [HIntegral] at hh ⊢
    exact hh
  have hB := hH (y := 1) le_rfl (by linarith) (by rw [abs_of_nonpos (by linarith : 1 - ρ.im ≤ 0)]; linarith)
  have hU := hH (y := 2 * T) (by linarith) le_rfl (by rw [abs_of_nonneg (by linarith : 0 ≤ 2 * T - ρ.im)]; linarith)
  have hw : Continuous w := by
    unfold w cauchyWeight
    exact continuous_const.div (continuous_const.add ((continuous_id.sub continuous_const).pow 2))
      (fun x => by dsimp; positivity)
  have hA : Continuous A := critical_error_continuous X
  have hX1 : 1 ≤ X := by exact_mod_cast hT1.trans hX
  have hsqrt : Real.exp L ≤ Real.sqrt (X : ℝ) := by
    apply (Real.le_sqrt (Real.exp_pos L).le (Nat.cast_nonneg _)).mpr
    rw [sq, ← Real.exp_add]
    exact (Real.exp_le_exp.mpr (show L + L ≤ 4 * L by linarith)).trans (hT ▸ hX)
  have hVright : ‖VIntegral K (3 / 2) 1 (2 * T)‖ ≤
      ∫ t in (1 : ℝ)..2 * T, (12 * Real.exp 1) * w t := by
    rw [VIntegral, norm_smul, Complex.norm_I, one_mul]
    apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
      (Filter.Eventually.of_forall fun t _ => ?_) ((continuous_const.mul hw).intervalIntegrable _ _)
    let s : ℂ := (3 / 2 : ℂ) + (t : ℂ) * I
    have sr : s.re = 3 / 2 := by norm_num [s]
    have hm := mollifier_error_norm_le_right (X := X) hX1 sr
    have hp : ‖mollifiedError X s‖ * Real.exp (L * (s.re - 1 / 2)) ≤ 6 := by
      rw [sr, show (3 / 2 - 1 / 2 : ℝ) = 1 by norm_num, mul_one]
      calc
        _ ≤ (6 / Real.sqrt (X : ℝ)) * Real.sqrt (X : ℝ) :=
          mul_le_mul hm hsqrt (Real.exp_pos _).le (by positivity)
        _ = _ := div_mul_cancel₀ _ (ne_of_gt ((Real.exp_pos L).trans_le hsqrt))
    have hden : 1 / 2 ≤ ‖s - ρ‖ := by
      have hr := Complex.abs_re_le_norm (s - ρ)
      rw [Complex.sub_re, sr] at hr
      linarith [le_abs_self (3 / 2 - ρ.re)]
    have hsq : (s.re - ρ.re) ^ 2 ≤ 1 := by
      rw [sr]
      nlinarith [mul_nonneg (show 0 ≤ ρ.re - 1 / 2 by linarith) (show 0 ≤ 5 / 2 - ρ.re by linarith)]
    have hh := gaussian_detector_norm_le hsq (by norm_num : 0 < (1 / 2 : ℝ)) hden hp
    convert hh using 1 <;> simp [s, w, K] <;> ring <;> simp
  have hVleft : ‖VIntegral K (1 / 2) 1 (2 * T)‖ ≤
      ∫ t in (1 : ℝ)..2 * T, (L * Real.exp 1 * A t) * w t := by
    rw [VIntegral, norm_smul, Complex.norm_I, one_mul]
    apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
      (Filter.Eventually.of_forall fun t _ => ?_)
      (((continuous_const.mul hA).mul hw).intervalIntegrable _ _)
    let s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I
    have sr : s.re = 1 / 2 := by norm_num [s]
    have hden : 1 / L ≤ ‖s - ρ‖ := by
      have hr := Complex.abs_re_le_norm (s - ρ)
      rw [Complex.sub_re, sr] at hr
      have hg : 1 / L ≤ ρ.re - 1 / 2 := (div_le_iff₀ hLp).mpr (by linarith [mul_comm L (ρ.re - 1 / 2)])
      linarith [neg_le_abs (1 / 2 - ρ.re)]
    have hsq : (s.re - ρ.re) ^ 2 ≤ 1 := by
      rw [sr]
      nlinarith [mul_nonneg (show 0 ≤ 3 / 2 - ρ.re by linarith) (show 0 ≤ 1 / 2 + ρ.re by linarith)]
    have hp : ‖mollifiedError X s‖ * Real.exp (L * (s.re - 1 / 2)) ≤ A t := by simp [sr,s,A]
    have hh := gaussian_detector_norm_le hsq (one_div_pos.mpr hLp) hden hp
    convert hh using 1 <;> simp [s,w,K,A] <;> ring <;> simp
  have htri (a b c d : ℂ) : ‖a - b + c - d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    linarith only [norm_sub_le (a - b + c) d, norm_add_le (a - b) c, norm_sub_le a b]
  have hsum := hraw.trans (htri _ _ _ _)
  simp [z₀,z₁] at hsum
  have hi : (∫ t in (1 : ℝ)..2 * T, (12 * Real.exp 1) * w t) +
      (∫ t in (1 : ℝ)..2 * T, (L * Real.exp 1 * A t) * w t) =
      ∫ t in (1 : ℝ)..2 * T, (12 * Real.exp 1 + L * Real.exp 1 * A t) * w t := by
    simp_rw [add_mul]
    exact (intervalIntegral.integral_add
      (f := fun t => (12 * Real.exp 1) * w t)
      (g := fun t => (L * Real.exp 1 * A t) * w t)
      ((continuous_const.mul hw).intervalIntegrable _ _)
      (((continuous_const.mul hA).mul hw).intervalIntegrable _ _)).symm
  change _ ≤ 40 * Real.exp 1 + ∫ t in (1 : ℝ)..2 * T, (12 * Real.exp 1 + L * Real.exp 1 * A t) * w t
  linarith

end RiemannResearch.Analysis.InghamMollifier

/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotGaussianReflection
import RiemannResearch.RH.WeilExplicitFormula.FromPNTPlus.ResidueCalcOnRectangles
import RiemannResearch.RH.WeilExplicitFormula.FromPNTPlus.ZetaBounds
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import RiemannResearch.Analysis.GammaMellinBounds
import RiemannResearch.RH.WeilExplicitFormula.RvM.ZetaGrowth
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import RiemannResearch.Analysis.ConreyBaluyotMollifierLinearGrowth

/-!
# Exact rightward shift of the actual Gaussian moment

The finite rectangle has only the candidate pole at 1. The signed residue
is retained in the whole-line identity. Both horizontal integrals vanish
by a Gaussian majorant, including when the reflected zeta argument crosses
the imaginary axis. For this limit the functional equation, the Euler Gamma
integral and a positive-half-plane zeta bound suffice. The last estimate
also bounds the actual pole coefficient uniformly on the coupled strip.

Source for the proof strategy: S. A. C. Baluyot, *On the Zeros of
Riemann's Zeta-function* (2017), Chapter 3,
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320 .
This is the initial contour shift in Section 3.3, before (3.3.6).
-/

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.ConreyBaluyot

/-- The coefficient of the rightward-crossed simple pole at s = 1.
It can vanish if the actual mollifier cancels the pole. -/
def mollifiedGaussianPoleCoeff (σ y ε l Δ u : ℝ) : ℂ :=
  Complex.exp ((1 - (l : ℂ) - I * u) ^ 2 / (Δ : ℂ) ^ 2) *
    nonstandardMollifier σ y ε 1 * mollifiedZeta σ y ε ((2 * l : ℝ) - 1)

theorem norm_gaussianContourFactor (l Δ u x t : ℝ) :
    ‖Complex.exp ((((x : ℂ) + (t : ℂ) * I) - (l : ℂ) - I * u) ^ 2 / (Δ : ℂ) ^ 2)‖ =
      Real.exp (((x - l) ^ 2 - (t - u) ^ 2) / Δ ^ 2) := by
  rw [Complex.norm_exp, ← Complex.ofReal_pow, Complex.div_ofReal_re, pow_two, Complex.mul_re]
  congr 1
  simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im]
  ring

/-- The actual contour kernel is analytic off the two possible product poles. -/
theorem analyticAt_mollifiedGaussianContourKernel (σ y ε l Δ u : ℝ) {s : ℂ}
    (hs : s ≠ 1) (hs' : ((2 * l : ℝ) : ℂ) - s ≠ 1) :
    AnalyticAt ℂ (mollifiedGaussianContourKernel σ y ε l Δ u) s := by
  have he : AnalyticAt ℂ (fun z : ℂ => Complex.exp ((z - (l : ℂ) - I * u) ^ 2 /
      (Δ : ℂ) ^ 2)) s := by fun_prop
  have hf : AnalyticAt ℂ (fun z : ℂ => ((2 * l : ℝ) : ℂ) - z) s :=
    analyticAt_const.sub analyticAt_id
  exact (he.mul (analyticAt_mollifiedZeta σ y ε hs)).mul
    ((analyticAt_mollifiedZeta σ y ε hs').comp hf)

/-- The actual pole coefficient, as a limit on the punctured plane. -/
theorem mollifiedGaussianContourKernel_residue_limit (σ y ε Δ u : ℝ) {l : ℝ}
    (hl : l < 1) :
    Tendsto (fun s : ℂ => (s - 1) * mollifiedGaussianContourKernel σ y ε l Δ u s)
      (𝓝[≠] (1 : ℂ)) (𝓝 (mollifiedGaussianPoleCoeff σ y ε l Δ u)) := by
  have hne : ((2 * l : ℝ) : ℂ) - 1 ≠ 1 := by
    intro heq
    have h := congrArg Complex.re heq
    simp at h
    linarith
  let A : ℂ → ℂ := fun z =>
    Complex.exp ((z - (l : ℂ) - I * u) ^ 2 / (Δ : ℂ) ^ 2) *
      nonstandardMollifier σ y ε z * mollifiedZeta σ y ε ((2 * l : ℝ) - z)
  have he : AnalyticAt ℂ (fun z : ℂ => Complex.exp ((z - (l : ℂ) - I * u) ^ 2 /
      (Δ : ℂ) ^ 2)) 1 := by fun_prop
  have href : AnalyticAt ℂ (fun z : ℂ => ((2 * l : ℝ) : ℂ) - z) 1 :=
    analyticAt_const.sub analyticAt_id
  have ha : AnalyticAt ℂ A 1 := (he.mul (analyticAt_nonstandardMollifier σ y ε 1)).mul
    ((analyticAt_mollifiedZeta σ y ε hne).comp href)
  have hta : Tendsto A (𝓝[≠] (1 : ℂ)) (𝓝 (A 1)) :=
    ha.continuousAt.continuousWithinAt
  convert riemannZeta_residue_one.mul hta using 1
  · funext z
    simp only [mollifiedGaussianContourKernel, mollifiedZeta, A]
    ring
  · simp [A, mollifiedGaussianPoleCoeff]

/-- The finite rightward rectangle crosses only s = 1. This identity retains
both horizontal sides and the signed coefficient, with no large-height limit. -/
theorem rectangleIntegral_mollifiedGaussianContourKernel (σ y ε Δ u : ℝ)
    {l c R : ℝ} (hl : l < 1) (hc : 1 < c) (hR : 0 < R) :
    RectangleIntegral' (mollifiedGaussianContourKernel σ y ε l Δ u)
      ((l : ℂ) - (R : ℂ) * I) ((c : ℂ) + (R : ℂ) * I) =
      mollifiedGaussianPoleCoeff σ y ε l Δ u := by
  let a : ℂ := (l : ℂ) - (R : ℂ) * I
  let b : ℂ := (c : ℂ) + (R : ℂ) * I
  let F := mollifiedGaussianContourKernel σ y ε l Δ u
  have hre : a.re ≤ b.re := by simp [a, b]; linarith
  have him : a.im ≤ b.im := by simp [a, b]; linarith
  have hp : Rectangle a b ∈ 𝓝 (1 : ℂ) := by
    rw [rectangle_mem_nhds_iff, uIoo_of_le hre, uIoo_of_le him]
    simp [mem_reProdIm, a, b, hl, hc, hR]
  have hhol : HolomorphicOn F (Rectangle a b \ {(1 : ℂ)}) := by
    intro z hz
    have hzlo : l ≤ z.re := by
      have hh := ((mem_Rect hre him z).mp hz.1).1
      simpa [a] using hh
    have hz' : ((2 * l : ℝ) : ℂ) - z ≠ 1 := by
      intro h
      have hx := congrArg Complex.re h
      simp at hx
      linarith
    have ha := analyticAt_mollifiedGaussianContourKernel σ y ε l Δ u hz.2 hz'
    exact ha.differentiableAt.differentiableWithinAt
  obtain ⟨V, hV, hbounded⟩ := ResidueOfTendsTo hp hhol
    (mollifiedGaussianContourKernel_residue_limit σ y ε Δ u hl)
  exact ResidueTheoremOnRectangleWithSimplePole' hre him hp hhol
    (by simpa only [div_eq_mul_inv] using BddAbove_to_IsBigO hV hbounded)

private theorem norm_cos_le_exp_abs_im (z : ℂ) :
    ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  unfold Complex.cos
  rw [norm_div]
  simp only [Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ Real.exp |z.im| + Real.exp |z.im| := by
      rw [Complex.norm_exp, Complex.norm_exp]
      apply add_le_add <;> apply Real.exp_le_exp.mpr
      · simpa [Complex.mul_re] using neg_le_abs z.im
      · simpa [Complex.mul_re] using le_abs_self z.im
    _ = _ := by ring

private theorem exists_reflectedZeta_exp_growth {d b : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re ∈ Icc d b → 1 ≤ |s.im| →
      ‖riemannZeta (1 - s)‖ ≤ C * |s.im| * Real.exp ((Real.pi / 2) * |s.im|) := by
  have hcont : ContinuousOn (fun x : ℝ => Complex.Gamma (x : ℂ)) (Icc d b) := by
    intro x hx
    have hpos : 0 < x := hd.trans_le hx.1
    have hne : ∀ n : ℕ, (x : ℂ) ≠ -n := by
      intro n h
      have he := congrArg Complex.re h
      simp at he
      linarith [show 0 ≤ (n : ℝ) from Nat.cast_nonneg n]
    exact ((Complex.differentiableAt_Gamma _ hne).continuousAt.comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc d b) hcont
  refine ⟨2 * |B| * (5 / 2 + d⁻¹), by positivity, ?_⟩
  intro s hs ht
  have hspos : 0 < s.re := hd.trans_le hs.1
  have hne : ∀ n : ℕ, s ≠ -n := by
    intro n h
    have he := congrArg Complex.re h
    simp at he
    linarith [show 0 ≤ (n : ℝ) from Nat.cast_nonneg n]
  have hne1 : s ≠ 1 := by
    rintro rfl
    norm_num at ht
  have hpow : ‖(2 * Real.pi : ℂ) ^ (-s)‖ ≤ 1 := by
    have hπ : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hc : (2 * (Real.pi : ℂ) : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; rfl
    rw [hc, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]
    simpa using (Real.rpow_le_rpow_of_exponent_le hπ (neg_nonpos.mpr hspos.le) :
      (2 * Real.pi) ^ (-s.re) ≤ (2 * Real.pi) ^ (0 : ℝ))
  have hg : ‖Complex.Gamma s‖ ≤ |B| := by
    have h := (hB s.re hs).trans (le_abs_self B)
    rw [Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs] at h
    exact (Complex.gamma_norm_le_real_part hspos).trans ((le_abs_self _).trans h)
  have hcos : ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖ ≤
      Real.exp ((Real.pi / 2) * |s.im|) := by
    have hi : (((Real.pi : ℂ) * s / 2)).im = (Real.pi / 2) * s.im := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_im, Complex.mul_im]
      simp
      ring
    simpa only [hi, abs_mul, abs_of_pos (show 0 < Real.pi / 2 by positivity)] using
      norm_cos_le_exp_abs_im ((Real.pi : ℂ) * s / 2)
  have hz := Zeta23.RvM.riemannZeta_linear_growth hd hs.1 ht
  rw [riemannZeta_one_sub hne hne1]
  simp only [norm_mul, Complex.norm_ofNat]
  calc
    _ ≤ 2 * 1 * |B| * Real.exp ((Real.pi / 2) * |s.im|) *
        ((5 / 2 + d⁻¹) * |s.im|) := by
      gcongr
    _ = _ := by ring

private theorem norm_mollifier_le_of_re_ge (σ y ε r : ℝ) {s : ℂ} (hs : r ≤ s.re) :
    ‖nonstandardMollifier σ y ε s‖ ≤
      ∑ n ∈ Finset.Icc 1 ⌊y ^ (1 + ε)⌋₊, ‖mollifierCoefficient σ y n‖ / (n : ℝ) ^ r := by
  unfold nonstandardMollifier
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : 0 < n := by omega
  rw [norm_div, Complex.norm_natCast_cpow_of_pos hn0]
  exact div_le_div_of_nonneg_left (norm_nonneg _)
    (Real.rpow_pos_of_pos (by exact_mod_cast hn0) _)
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) hs)

private theorem gaussian_strip_absorption {q k x l c t u : ℝ} (hq : 0 < q)
    (hx : x ∈ Icc l c) :
    q * ((x - l) ^ 2 - (t - u) ^ 2) + k * |t| ≤
      q * (c - l) ^ 2 + (2 * q * |u| + k) ^ 2 / (2 * q) - (q / 2) * t ^ 2 := by
  let A := 2 * q * |u| + k
  have habs : t * u ≤ |t| * |u| := by rw [← abs_mul]; exact le_abs_self _
  have hprod := mul_le_mul_of_nonneg_left habs (show 0 ≤ 2 * q by positivity)
  have hx' : (x - l) ^ 2 ≤ (c - l) ^ 2 := by
    exact pow_le_pow_left₀ (sub_nonneg.mpr hx.1) (sub_le_sub_right hx.2 _) 2
  have hxx := mul_le_mul_of_nonneg_left hx' hq.le
  have hs : q / 2 * (|t| - A / q) ^ 2 =
      q / 2 * t ^ 2 - A * |t| + A ^ 2 / (2 * q) := by
    rw [← sq_abs t]
    field_simp [hq.ne']
    ring
  have hsq : 0 ≤ q / 2 * t ^ 2 - A * |t| + A ^ 2 / (2 * q) :=
    hs ▸ mul_nonneg (by positivity) (sq_nonneg _)
  dsimp [A] at hsq
  nlinarith only [hprod, hxx, hsq, mul_nonneg hq.le (sq_nonneg u)]

/-- For fixed parameters, the kernel has a Gaussian majorant throughout
the strip, even where the reflected zeta argument moves left of Re s = 0. -/
theorem exists_mollifiedGaussianContourKernel_tail_bound (σ y ε u : ℝ) {l c Δ : ℝ}
    (hl : 0 < l) (hl' : l < 1) (hΔ : 0 < Δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc l c, ∀ t : ℝ, 1 ≤ |t| →
      ‖mollifiedGaussianContourKernel σ y ε l Δ u ((x : ℂ) + (t : ℂ) * I)‖ ≤
        C * Real.exp (-(1 / (4 * Δ ^ 2)) * t ^ 2) := by
  obtain ⟨C₁, hC₁, href⟩ := exists_reflectedZeta_exp_growth (b := 1 - 2 * l + c)
    (show 0 < 1 - l by linarith)
  let m := min l (2 * l - c)
  let B := ∑ n ∈ Finset.Icc 1 ⌊y ^ (1 + ε)⌋₊, ‖mollifierCoefficient σ y n‖ / (n : ℝ) ^ m
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let q := 1 / Δ ^ 2
  have hq : 0 < q := by dsimp [q]; positivity
  let k := Real.pi / 2
  let K := (5 / 2 + l⁻¹) * C₁ * B ^ 2
  let E := q * (c - l) ^ 2 + (2 * q * |u| + k) ^ 2 / (2 * q)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K * Real.exp E / (q / 4), by positivity, ?_⟩
  intro x hx t ht
  let z : ℂ := (x : ℂ) + (t : ℂ) * I
  let w : ℂ := ((2 * l : ℝ) : ℂ) - z
  have hzre : z.re = x := by simp [z]
  have hzim : z.im = t := by simp [z]
  have hwre : w.re = 2 * l - x := by simp [w, hzre]
  have hwim : w.im = -t := by simp [w, hzim]
  have hin : (1 - w).re ∈ Icc (1 - l) (1 - 2 * l + c) := by
    simp only [Complex.sub_re, Complex.one_re, hwre, mem_Icc]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have him : (1 - w).im = t := by simp [hwim]
  have hz := Zeta23.RvM.riemannZeta_linear_growth hl
    (s := z) (by rw [hzre]; exact hx.1) (by simpa only [hzim] using ht)
  have hw : ‖riemannZeta w‖ ≤ C₁ * |t| * Real.exp (k * |t|) := by
    simpa only [sub_sub_cancel, him, k] using href (1-w) hin (by simpa only [him] using ht)
  have hMz : ‖nonstandardMollifier σ y ε z‖ ≤ B :=
    norm_mollifier_le_of_re_ge σ y ε m ((min_le_left _ _).trans (hzre ▸ hx.1))
  have hm : m ≤ w.re := by
    rw [hwre]
    exact (min_le_right _ _).trans (sub_le_sub_left hx.2 _)
  have hMw : ‖nonstandardMollifier σ y ε w‖ ≤ B :=
    norm_mollifier_le_of_re_ge σ y ε m hm
  rw [hzim] at hz
  change ‖mollifiedGaussianContourKernel σ y ε l Δ u z‖ ≤ _
  unfold mollifiedGaussianContourKernel mollifiedZeta
  simp only [norm_mul]
  rw [show ‖Complex.exp ((z - (l : ℂ) - I * u) ^ 2 / (Δ : ℂ) ^ 2)‖ =
      Real.exp (((x-l)^2-(t-u)^2) / Δ^2) from norm_gaussianContourFactor l Δ u x t]
  have hexp : ((x - l) ^ 2 - (t - u) ^ 2) / Δ ^ 2 + k * |t| ≤ E - (q / 2) * t ^ 2 := by
    simpa only [E, q, one_div_mul_eq_div] using
      gaussian_strip_absorption (k := k) (t := t) (u := u) hq hx
  have hpoly : t ^ 2 ≤ Real.exp ((q / 4) * t ^ 2) / (q / 4) := by
    apply (le_div_iff₀ (show 0 < q / 4 by positivity)).2
    linarith only [Real.add_one_le_exp ((q / 4) * t ^ 2)]
  calc
    _ ≤ Real.exp (((x-l)^2-(t-u)^2)/Δ^2) *
        (((5 / 2 + l⁻¹) * |t|) * B) * ((C₁ * |t| * Real.exp (k * |t|)) * B) := by
      gcongr
    _ = K * t ^ 2 * Real.exp ((((x-l)^2-(t-u)^2)/Δ^2) + k * |t|) := by
      rw [Real.exp_add, ← sq_abs t]
      dsimp [K]
      ring
    _ ≤ K * t ^ 2 * Real.exp (E - (q / 2) * t ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
    _ ≤ K * (Real.exp ((q/4)*t^2) / (q/4)) * Real.exp (E - (q/2)*t^2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hK) (by positivity)
    _ = K / (q / 4) *
        (Real.exp ((q / 4) * t ^ 2) * Real.exp (E - (q / 2) * t ^ 2)) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      have hqeq : (q / 4) * t ^ 2 + (E - (q / 2) * t ^ 2) =
          E + (-(1 / (4 * Δ ^ 2)) * t ^ 2) := by dsimp [q]; ring
      rw [hqeq, Real.exp_add]
      ring

/-- Baluyot's initial rightward contour shift with the exact signed residue.
The Gaussian kills both horizontal edges, and the shifted integral is
absolutely convergent. Every c > 1 is admissible, including 2*l < c < 2. -/
theorem mollifiedGaussianMoment_eq_right_shift (σ ε u : ℝ)
    {y l c Δ : ℝ} (hy : 0 < y) (hl : 0 < l) (hl' : l < 1) (hc : 1 < c) (hΔ : 0 < Δ) :
    (mollifiedGaussianMoment σ y ε l Δ u : ℂ) =
      ((1 / (Δ * Real.sqrt Real.pi) : ℝ) : ℂ) *
        ((∫ t : ℝ, mollifiedGaussianContourKernel σ y ε l Δ u ((c : ℂ) + (t : ℂ) * I)) -
          (2 * Real.pi : ℂ) * mollifiedGaussianPoleCoeff σ y ε l Δ u) := by
  let F := mollifiedGaussianContourKernel σ y ε l Δ u
  let f (x : ℝ) (t : ℝ) := F ((x : ℂ) + t * I)
  let H (t : ℝ) := ∫ x in l..c, f x t
  let q := 1 / (4 * Δ ^ 2)
  have hq : 0 < q := by dsimp [q]; positivity
  have hlc : l ≤ c := hl'.le.trans hc.le
  obtain ⟨C, hC, htail⟩ := exists_mollifiedGaussianContourKernel_tail_bound σ y ε u hl hl' hΔ
  have hcLine {x : ℝ} (hx : l ≤ x) (hx1 : x ≠ 1) : Continuous (f x) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hne : ((x : ℂ) + (t : ℂ) * I) ≠ 1 := by
      intro he
      exact hx1 (by simpa using congrArg Complex.re he)
    have hne' : ((2 * l : ℝ) : ℂ) - ((x : ℂ) + (t : ℂ) * I) ≠ 1 := by
      intro he
      have hr := congrArg Complex.re he
      simp at hr
      linarith
    have ht : ContinuousAt (fun v : ℝ => (x : ℂ) + (v : ℂ) * I) t := by fun_prop
    have hf := (analyticAt_mollifiedGaussianContourKernel σ y ε l Δ u hne hne').continuousAt
    exact ContinuousAt.comp (g := F) (f := fun v : ℝ => (x : ℂ) + (v : ℂ) * I) hf ht
  have hline {x : ℝ} (hx : x ∈ Icc l c) (hx1 : x ≠ 1) : Integrable (f x) := by
    have hcont := hcLine hx.1 hx1
    obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (s := Icc (-1 : ℝ) 1) hcont.continuousOn
    have hdom := (integrable_exp_neg_mul_sq hq).const_mul (C + |D| * Real.exp q)
    apply hdom.mono' hcont.aestronglyMeasurable
    apply Eventually.of_forall
    intro t
    by_cases ht : 1 ≤ |t|
    · exact (htail x hx t ht).trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (by positivity)) (Real.exp_nonneg _))
    · have hmem : t ∈ Icc (-1 : ℝ) 1 :=
        ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
      have hminus : 0 ≤ 1 - t := sub_nonneg.mpr hmem.2
      have hplus : 0 ≤ 1 + t := by linarith [hmem.1]
      have hs : t ^ 2 ≤ 1 := by nlinarith [mul_nonneg hminus hplus]
      have he : 1 ≤ Real.exp q * Real.exp (-q * t ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hs)]
      calc
        _ ≤ |D| := (hD t hmem).trans (le_abs_self D)
        _ ≤ |D| * (Real.exp q * Real.exp (-q * t^2)) := le_mul_of_one_le_right (abs_nonneg _) he
        _ ≤ _ := by
          rw [add_mul]
          linarith [mul_nonneg hC (Real.exp_nonneg (-q * t^2))]
  have hH (t : ℝ) (ht : 1 ≤ |t|) : ‖H t‖ ≤ C * Real.exp (-q * t ^ 2) * |c - l| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    apply htail x _ t ht
    simpa only [uIcc_of_le hlc] using uIoc_subset_uIcc hx
  have hInv : Tendsto (fun t : ℝ => (1 + q * t ^ 2)⁻¹) atTop (𝓝 0) := by
    apply tendsto_inv_atTop_zero.comp
    apply tendsto_atTop.2
    intro b
    have hp : Tendsto (fun t : ℝ => t ^ 2) atTop atTop :=
      tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
    filter_upwards [tendsto_atTop.mp hp ((b - 1) / q)] with t ht
    rw [div_le_iff₀ hq] at ht
    linarith
  have hExp (t : ℝ) : Real.exp (-q * t ^ 2) ≤ (1 + q * t ^ 2)⁻¹ := by
    rw [show -q * t ^ 2 = -(q * t ^ 2) by ring, Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos _) (by positivity)).2
      (by linarith only [Real.add_one_le_exp (q * t ^ 2)])
  have hlim : Tendsto (fun t : ℝ => C * (1 + q * t ^ 2)⁻¹ * |c - l|) atTop (𝓝 0) := by
    simpa using (hInv.const_mul C).mul_const |c-l|
  have hbound (t : ℝ) (ht : 1 ≤ |t|) : ‖H t‖ ≤ C * (1 + q * t ^ 2)⁻¹ * |c - l| :=
    (hH t ht).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hExp t) hC) (by positivity))
  have hpos : Tendsto H atTop (𝓝 0) := squeeze_zero_norm'
    ((eventually_ge_atTop (1 : ℝ)).mono (fun t ht => hbound t (ht.trans (le_abs_self t)))) hlim
  have hneg : Tendsto (fun t => H (-t)) atTop (𝓝 0) := squeeze_zero_norm'
    ((eventually_ge_atTop (1 : ℝ)).mono (fun t ht => by
      simpa only [neg_sq] using hbound (-t) (by simpa only [abs_neg] using ht.trans (le_abs_self t))))
    hlim
  have ha := intervalIntegral_tendsto_integral (hline ⟨le_rfl, hlc⟩ hl'.ne)
    tendsto_neg_atTop_atBot tendsto_id
  have hb := intervalIntegral_tendsto_integral (hline ⟨hlc, le_rfl⟩ hc.ne')
    tendsto_neg_atTop_atBot tendsto_id
  have hrect (R : ℝ) (hR : 0 < R) :
      (2 * Real.pi * I : ℂ)⁻¹ *
        (H (-R) - H R + I * (∫ t in -R..R, f c t) - I * (∫ t in -R..R, f l t)) =
      mollifiedGaussianPoleCoeff σ y ε l Δ u := by
    simpa [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral, H, f, F, smul_eq_mul]
      using rectangleIntegral_mollifiedGaussianContourKernel σ y ε Δ u hl' hc hR
  have hlimrect :=
    (((hneg.sub hpos).add (hb.const_mul I)).sub (ha.const_mul I)).const_mul
      (2 * Real.pi * I : ℂ)⁻¹
  have h := tendsto_nhds_unique hlimrect
    (tendsto_const_nhds.congr' ((eventually_ge_atTop (1 : ℝ)).mono
      fun R hR => (hrect R (by linarith)).symm))
  simp only [sub_self, zero_add] at h
  have hπ : (2 * (Real.pi : ℂ) : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hdiff : (∫ t : ℝ, f c t) - (∫ t : ℝ, f l t) =
      (2 * Real.pi : ℂ) * mollifiedGaussianPoleCoeff σ y ε l Δ u := by
    have he : ((∫ t : ℝ, f c t) - (∫ t : ℝ, f l t)) / (2 * Real.pi : ℂ) =
        mollifiedGaussianPoleCoeff σ y ε l Δ u := by
      convert h using 1
      field_simp [hπ, Complex.I_ne_zero]
      <;> ring
    exact ((div_eq_iff hπ).mp he).trans (mul_comm _ _)
  have hleft : (∫ t : ℝ, f l t) =
      (∫ t : ℝ, f c t) - (2 * Real.pi : ℂ) * mollifiedGaussianPoleCoeff σ y ε l Δ u := by
    rw [← hdiff]
    ring
  rw [mollifiedGaussianMoment_eq_vertical_integral σ ε l hy hΔ u]
  exact congrArg (fun z : ℂ => ((1 / (Δ * Real.sqrt Real.pi) : ℝ) : ℂ) * z) hleft

/-- Uniform estimate for the actual signed pole coefficient. The constant
uses linear mollifier growth on both of its real arguments. -/
theorem exists_uniform_mollifiedGaussianPoleCoeff_bound :
    ∃ η Y C : ℝ, 0 < η ∧ η < 1 / 4 ∧ 1 < Y ∧ 0 ≤ C ∧
      ∀ y : ℝ, Y ≤ y → ∀ σ : ℝ,
        1 / 2 + 1 / Real.log y ≤ σ → σ ≤ 1 / 2 + η →
        ∀ (ε : ℝ) (Δ : ℝ), 1 ≤ Δ → ∀ u : ℝ,
          ‖mollifiedGaussianPoleCoeff σ y ε σ Δ u‖ ≤
            C * y ^ 2 * Real.exp (-(u / Δ) ^ 2) := by
  obtain ⟨η, Y, K, hη, hηhi, hY, hK, hM⟩ :=
    exists_uniform_nonstandardMollifier_linear_growth
  have hcont : ContinuousOn (fun x : ℝ => riemannZeta (x : ℂ)) (Icc 0 (1 / 2)) := by
    intro x hx
    have hne : (x : ℂ) ≠ 1 := by
      intro h
      have hx1 : x = 1 := by simpa using congrArg Complex.re h
      linarith [hx.2]
    have hz := (differentiableAt_riemannZeta hne).continuousAt
    exact (ContinuousAt.comp (g := riemannZeta) (f := (fun r : ℝ => (r : ℂ)))
      hz Complex.continuous_ofReal.continuousAt).continuousWithinAt
  obtain ⟨Z, hZ⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 (1 / 2)) hcont
  refine ⟨η, Y, Real.exp 1 * |Z| * K ^ 2, hη, hηhi, hY, by positivity, ?_⟩
  intro y hy σ hσ hση ε Δ hΔ u
  have hy1 : 1 < y := hY.trans_le hy
  have hσlo : 1 / 2 ≤ σ := by
    linarith [one_div_pos.mpr (Real.log_pos hy1)]
  have hσ1 : σ < 1 := by linarith
  let r : ℝ := 2 * σ - 1
  have hr : r ∈ Icc 0 (1 / 2) := ⟨by dsimp [r]; linarith, by dsimp [r]; linarith⟩
  have hrC : ((2 * σ : ℝ) : ℂ) - 1 = (r : ℂ) := by push_cast [r]; rfl
  have hZr : ‖riemannZeta (r : ℂ)‖ ≤ |Z| := (hZ r hr).trans (le_abs_self Z)
  have hM1 := hM y hy σ hσ hση ε 1 (by norm_num)
  have hMr := hM y hy σ hσ hση ε (r : ℂ) (by simpa using hr.1)
  have hG : ‖Complex.exp ((1 - (σ : ℂ) - I * u) ^ 2 / (Δ : ℂ) ^ 2)‖ ≤
      Real.exp 1 * Real.exp (-(u / Δ) ^ 2) := by
    have hn : ‖Complex.exp ((1 - (σ : ℂ) - I * u) ^ 2 / (Δ : ℂ) ^ 2)‖ =
        Real.exp (((1-σ)^2-u^2)/Δ^2) := by
      simpa only [Complex.ofReal_one, Complex.ofReal_zero, zero_mul, add_zero, zero_sub, neg_sq]
        using norm_gaussianContourFactor σ Δ u 1 0
    rw [hn, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [sub_div, div_pow, ← sub_eq_add_neg]
    apply sub_le_sub_right
    apply (div_le_iff₀ (show 0 < Δ ^ 2 by positivity)).2
    simpa only [one_mul] using pow_le_pow_left₀ (show 0 ≤ 1 - σ by linarith)
      (show 1 - σ ≤ Δ by linarith) 2
  unfold mollifiedGaussianPoleCoeff mollifiedZeta
  simp only [norm_mul]
  rw [hrC]
  calc
    _ ≤ (Real.exp 1 * Real.exp (-(u / Δ) ^ 2)) * (K * y) * (|Z| * (K * y)) := by
      gcongr
    _ = _ := by ring

end RiemannResearch.Analysis.ConreyBaluyot

/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import RiemannResearch.Analysis.SymmetricZetaRatio
import RiemannResearch.RH.WeilExplicitFormula.XiPrime.Hardy.EFContour.Analytic
import RiemannResearch.Analysis.DampedGammaStripBounds
import RiemannResearch.Analysis.DivisorPolynomialMoment
import RiemannResearch.Analysis.RectanglePoleSubtraction
import RiemannResearch.Analysis.VerticalResidueShift
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp

/-!
# Moving the actual reflected divisor head to the right

The finite head in the functional-equation expansion of the zeta-square
Mellin kernel has only the Gamma pole at zero in -1 < Re z < 1/2.
Its residue is the exact reflected critical divisor polynomial multiplied
by chi(1/2+it)^2. The full contour identity below keeps that sign explicit.

The contour organization follows Chourasiya--Simonic, Section 5.1,
https://arxiv.org/html/2507.15184v2.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory Set Filter
open scoped Topology BigOperators ComplexConjugate
namespace RiemannResearch.Analysis

/-- The actual reflected finite divisor head, in exponential coordinates. -/
def reflectedDivisorHead (N : ℕ) (t : ℝ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, criticalDivisorCoefficient n *
    Complex.exp ((z + I * t) * (Real.log n : ℂ))

/-- The finite head after applying the zeta functional equation. -/
def zetaSquareFiniteHeadKernel (N : ℕ) (Y t : ℝ) (z : ℂ) : ℂ :=
  Gamma z * (Y : ℂ) ^ z *
    Zeta23.XiPrime.chiFE ((1 / 2 : ℂ) + I * t + z) ^ 2 *
      reflectedDivisorHead N t z

theorem reflectedDivisorHead_zero (N : ℕ) (t : ℝ) :
    reflectedDivisorHead N t 0 = conj (divisorPolynomial N (fun _ => 1) t) := by
  have hhalf : conj (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      Complex.conj_ofReal (1 / 2)
  have hc (n : ℕ) : conj (criticalDivisorCoefficient n) =
      criticalDivisorCoefficient n := by
    simp only [criticalDivisorCoefficient, map_mul, map_natCast, ← Complex.exp_conj,
      map_neg, hhalf, Complex.conj_ofReal]
  simp only [reflectedDivisorHead, divisorPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [one_mul, map_mul, hc, ← Complex.exp_conj, zero_add,
    map_neg, Complex.conj_I, Complex.conj_ofReal]
  congr 2
  push_cast
  ring

theorem analyticAt_reflectedDivisorHead (N : ℕ) (t : ℝ) (z : ℂ) :
    AnalyticAt ℂ (reflectedDivisorHead N t) z := by
  unfold reflectedDivisorHead
  fun_prop

theorem norm_reflectedDivisorHead_le (N : ℕ) (t : ℝ) {z : ℂ} (hz : z.re ≤ 1) :
    ‖reflectedDivisorHead N t z‖ ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ 2 := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by linarith
  have hl := Real.log_nonneg hn1
  have he : ‖Complex.exp ((z + I * t) * (Real.log n : ℂ))‖ ≤ n := by
    rw [Complex.norm_exp]
    have hr : ((z + I * t) * (Real.log n : ℂ)).re = z.re * Real.log n := by
      simp only [Complex.mul_re, Complex.add_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    rw [hr]
    calc
      _ ≤ Real.exp (Real.log n) := Real.exp_le_exp.mpr (by nlinarith)
      _ = n := Real.exp_log hn0
  rw [norm_mul]
  calc
    _ ≤ (n : ℝ) * n :=
      mul_le_mul (criticalDivisorCoefficient_norm_le n) he (norm_nonneg _) (by positivity)
    _ = _ := by ring

private theorem analyticAt_Gamma_add_one_of_re {z : ℂ} (hz : -1 < z.re) :
    AnalyticAt ℂ (fun w : ℂ => Gamma (w + 1)) z := by
  have hd : DifferentiableOn ℂ (fun w : ℂ => Gamma (w + 1)) {w | -1 < w.re} := by
    intro w hw
    apply DifferentiableAt.differentiableWithinAt
    apply (Complex.differentiableAt_Gamma _ ?_).comp w (differentiableAt_id.add_const 1)
    intro n hn
    have he := congrArg Complex.re hn
    simp at he
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    change -1 < w.re at hw
    linarith
  exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)

private theorem Gamma_eq_shift_div : Gamma = fun z : ℂ => Gamma (z + 1) / z := by
  funext z
  by_cases hz : z = 0
  · simp [hz]
  · rw [Complex.Gamma_add_one z hz]
    field_simp

private theorem analyticAt_finiteHeadFactor (N : ℕ) {Y : ℝ} (hY : 0 < Y)
    (t : ℝ) {z : ℂ} (hz : z.re < 1 / 2) :
    AnalyticAt ℂ (fun w : ℂ => (Y : ℂ) ^ w *
      Zeta23.XiPrime.chiFE ((1 / 2 : ℂ) + I * t + w) ^ 2 *
        reflectedDivisorHead N t w) z := by
  have hs : ((1 / 2 : ℂ) + I * t + z).re < 1 := by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.mul_re,
      Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero,
      sub_zero, add_zero]
    linarith
  have hs1 : (1 / 2 : ℂ) + I * t + z ≠ 1 := by
    intro he; rw [he] at hs; norm_num at hs
  have hχ := Zeta23.XiPrime.Hardy.EFContour.chiFE_analyticAt'
    (Zeta23.XiPrime.Hardy.EFContour.Gammaℝ_one_sub_ne_zero_of_re
      (by linarith) hs1)
  have hp : AnalyticAt ℂ (fun w : ℂ => (Y : ℂ) ^ w) z := by
    simp only [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hY.ne')]
    fun_prop
  exact (hp.mul ((hχ.comp (analyticAt_const.add analyticAt_id)).pow 2)).mul
    (analyticAt_reflectedDivisorHead N t z)

theorem analyticAt_zetaSquareFiniteHeadKernel (N : ℕ) {Y : ℝ} (hY : 0 < Y)
    (t : ℝ) {z : ℂ} (hz : -1 < z.re) (hz' : z.re < 1 / 2) (hz0 : z ≠ 0) :
    AnalyticAt ℂ (zetaSquareFiniteHeadKernel N Y t) z := by
  have hΓ : AnalyticAt ℂ Gamma z := by
    rw [Gamma_eq_shift_div]
    exact (analyticAt_Gamma_add_one_of_re hz).div analyticAt_id hz0
  convert! hΓ.mul (analyticAt_finiteHeadFactor N hY t hz') using 1
  funext w
  dsimp [zetaSquareFiniteHeadKernel]
  ring

theorem meromorphicAt_zetaSquareFiniteHeadKernel (N : ℕ) {Y : ℝ} (hY : 0 < Y)
    (t : ℝ) {z : ℂ} (hz : -1 < z.re) (hz' : z.re < 1 / 2) :
    MeromorphicAt (zetaSquareFiniteHeadKernel N Y t) z := by
  have hΓ : MeromorphicAt Gamma z := by
    rw [Gamma_eq_shift_div]
    exact (analyticAt_Gamma_add_one_of_re hz).meromorphicAt.div analyticAt_id.meromorphicAt
  convert! hΓ.mul (analyticAt_finiteHeadFactor N hY t hz').meromorphicAt using 1
  funext w
  dsimp [zetaSquareFiniteHeadKernel]
  ring

theorem zetaSquareFiniteHeadKernel_residue_zero (N : ℕ) {Y : ℝ} (hY : 0 < Y)
    (t : ℝ) :
    Tendsto (fun z : ℂ => z * zetaSquareFiniteHeadKernel N Y t z) (𝓝[≠] 0)
      (𝓝 (Zeta23.XiPrime.chiFE ((1 / 2 : ℂ) + I * t) ^ 2 *
        conj (divisorPolynomial N (fun _ => 1) t))) := by
  have hΓ : Tendsto (fun z : ℂ => z * Gamma z) (𝓝[≠] 0) (𝓝 1) := by
    have hh := (analyticAt_Gamma_add_one_of_re (z := 0) (by norm_num)).continuousAt
    apply (show Tendsto (fun z : ℂ => Gamma (z + 1)) (𝓝[≠] 0) (𝓝 1) by
      simpa using hh.continuousWithinAt.tendsto).congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    change z ≠ 0 at hz
    rw [Complex.Gamma_add_one z hz]
  have hf := (analyticAt_finiteHeadFactor N hY t (z := 0) (by norm_num)).continuousAt
  have hh := hΓ.mul hf.continuousWithinAt.tendsto
  have hh' : Tendsto (fun z : ℂ => (z * Gamma z) *
      ((Y : ℂ) ^ z * Zeta23.XiPrime.chiFE ((1 / 2 : ℂ) + I * t + z) ^ 2 *
        reflectedDivisorHead N t z)) (𝓝[≠] 0)
      (𝓝 (Zeta23.XiPrime.chiFE ((1 / 2 : ℂ) + I * t) ^ 2 *
        conj (divisorPolynomial N (fun _ => 1) t))) := by
    simpa only [cpow_zero, one_mul, add_zero, reflectedDivisorHead_zero] using hh
  exact hh'.congr' (Eventually.of_forall fun z => by
    dsimp [zetaSquareFiniteHeadKernel]; ring)

theorem norm_chiFE_strip_le {r w : ℝ} (hr : -1 < r) (hr' : r < 1 / 2)
    (hw : 2 ≤ |w|) :
    ‖Zeta23.XiPrime.chiFE (((1 / 2 + r : ℝ) : ℂ) + I * w)‖ ≤
      (2 * Real.pi * Real.exp 20) * |w| := by
  have hπ : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hw1 : 1 ≤ |w| := by linarith
  have hw2 : 1 ≤ w ^ 2 := by nlinarith [sq_abs w]
  have hwp : 0 < w ^ 2 := by linarith
  have hp : Real.pi ^ r ≤ Real.pi := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hπ (by linarith : r ≤ 1)
  have hpow : (|w| / 2) ^ (-r) ≤ |w| := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ |w| / 2)
      (by linarith : -r ≤ 1)
    rw [Real.rpow_one] at hh
    linarith
  have he (e : ℝ) (he : |e| ≤ 1) : Real.exp (20 * |e| / w ^ 2) ≤ Real.exp 20 := by
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ hwp).mpr
    nlinarith
  by_cases hhalf : 1 / 2 ≤ -r
  · have h := SymmetricZetaRatio.norm_chiFE_symmetric_le_of_half_le
      hhalf (by linarith : -r ≤ 3 / 2) hw1
    have hab : |-r-1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hex := he (-r-1) hab
    have h' : ‖Zeta23.XiPrime.chiFE (((1 / 2 + r : ℝ) : ℂ) + I * w)‖ ≤
        2 * Real.pi ^ r * Real.exp (20 * |-r - 1| / w ^ 2) *
          (|w| / 2) ^ (-r) := by simpa using h
    exact h'.trans (by gcongr)
  · have hab : |-r| < 1 / 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
    have h := SymmetricZetaRatio.norm_chiFE_symmetric_le_of_abs_lt hab hw1
    have hex := he (-r) (by linarith [hab.le])
    have h' : ‖Zeta23.XiPrime.chiFE (((1 / 2 + r : ℝ) : ℂ) + I * w)‖ ≤
        Real.pi ^ r * (Real.exp (20 * |-r| / w ^ 2) * (|w| / 2) ^ (-r)) := by
      simpa using h
    calc
      _ ≤ Real.pi * (Real.exp 20 * |w|) := h'.trans (by gcongr)
      _ ≤ _ := by
        nlinarith [mul_nonneg Real.pi_pos.le
          (mul_nonneg (Real.exp_pos 20).le (abs_nonneg w))]

/-- Exact finite rectangle identity, with the only enclosed pole at zero. -/
theorem rectangleIntegral_zetaSquareFiniteHeadKernel (N : ℕ) {Y : ℝ}
    (hY : 0 < Y) (t : ℝ) {a b T : ℝ}
    (ha : -1 < a) (ha0 : a < 0) (hb : 0 < b) (hb' : b < 1 / 2) (hT : 0 < T) :
    RectangleIntegral' (zetaSquareFiniteHeadKernel N Y t)
      ((a : ℂ) - T * I) ((b : ℂ) + T * I) =
      Zeta23.XiPrime.chiFE ((1 / 2 : ℂ) + I * t) ^ 2 *
        conj (divisorPolynomial N (fun _ => 1) t) := by
  classical
  let z : ℂ := (a : ℂ) - T * I
  let w : ℂ := (b : ℂ) + T * I
  have hre : z.re ≤ w.re := by simp [z, w]; linarith
  have him : z.im ≤ w.im := by simp [z, w]; linarith
  have hRre {s : ℂ} (hs : s ∈ Rectangle z w) : -1 < s.re ∧ s.re < 1 / 2 := by
    have hh := (mem_Rect hre him s).mp hs
    have hh0 := hh.1
    have hh1 := hh.2.1
    simp [z] at hh0
    simp [w] at hh1
    constructor <;> linarith
  have h0in : Rectangle z w ∈ 𝓝 (0 : ℂ) := by
    rw [rectangle_mem_nhds_iff, uIoo_of_le hre, uIoo_of_le him]
    simp only [mem_reProdIm, mem_Ioo]
    constructor <;> constructor <;> simp [z, w] <;> linarith
  have hh := Complex.rectangleIntegral'_eq_sum_of_residue_limits
    (zetaSquareFiniteHeadKernel N Y t) hre him ({0} : Finset ℂ)
    (fun _ => Zeta23.XiPrime.chiFE ((1 / 2 : ℂ) + I * t) ^ 2 *
      conj (divisorPolynomial N (fun _ => 1) t))
    (fun s hs => meromorphicAt_zetaSquareFiniteHeadKernel N hY t (hRre hs).1 (hRre hs).2)
    (by intro s hs; simp only [Finset.mem_singleton] at hs; simpa [hs] using h0in)
    (by
      intro s hs hns
      exact analyticAt_zetaSquareFiniteHeadKernel N hY t (hRre hs).1 (hRre hs).2
        (by simpa using hns))
    (by
      intro s hs
      simp only [Finset.mem_singleton] at hs
      subst s
      simpa only [sub_zero] using zetaSquareFiniteHeadKernel_residue_zero N hY t)
  simpa only [Finset.sum_singleton] using hh

/-- Actual quadratic decay of the finite-head kernel on the entire closed strip. -/
theorem exists_zetaSquareFiniteHeadKernel_strip_tail (N : ℕ) {Y : ℝ}
    (hY : 0 < Y) (t : ℝ) {a b : ℝ} (ha : -1 < a) (hb : b < 1 / 2) :
    ∃ B T₀ : ℝ, 0 ≤ B ∧ 1 ≤ T₀ ∧ ∀ r ∈ Icc a b, ∀ v : ℝ,
      T₀ ≤ |v| → ‖zetaSquareFiniteHeadKernel N Y t ((r : ℂ) + v * I)‖ ≤
        B * (1 + v ^ 2)⁻¹ := by
  let C : ℝ := 2 * Real.pi * Real.exp 20
  let D : ℝ := ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hlam : 0 < ((Y : ℂ)⁻¹).re := by
    rw [← Complex.ofReal_inv, Complex.ofReal_re]
    positivity
  obtain ⟨G, hG, hGb⟩ := Complex.exists_gamma_mul_cpow_neg_strip_pow_bound
    hlam (a := a) (b := b) 4 (by norm_num; linarith)
  refine ⟨8 * C ^ 2 * D * G, |t| + 2, by positivity,
    by linarith [abs_nonneg t], ?_⟩
  intro r hr v hv
  have hv1 : 1 ≤ |v| := by linarith [abs_nonneg t]
  have hv0 : v ≠ 0 := abs_pos.mp (by linarith : 0 < |v|)
  have hv2 : 1 ≤ v ^ 2 := by nlinarith [sq_abs v]
  have htv : |t + v| ≤ 2 * |v| := (abs_add_le t v).trans (by linarith)
  have hvrev : |v| ≤ |t| + |t + v| := by
    calc
      |v| = |-t + (t + v)| := by congr 1; ring
      _ ≤ |-t| + |t + v| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  have htv2 : 2 ≤ |t + v| := by linarith
  have hχ : ‖Zeta23.XiPrime.chiFE
      ((1 / 2 : ℂ) + I * t + ((r : ℂ) + v * I))‖ ≤ 2 * C * |v| := by
    have he : (1 / 2 : ℂ) + I * t + ((r : ℂ) + v * I) =
        (((1 / 2 + r : ℝ) : ℂ) + I * ((t + v : ℝ) : ℂ)) := by push_cast; ring
    rw [he]
    calc
      _ ≤ C * |t + v| :=
        norm_chiFE_strip_le (ha.trans_le hr.1) (hr.2.trans_lt hb) htv2
      _ ≤ C * (2 * |v|) := mul_le_mul_of_nonneg_left htv hC
      _ = _ := by ring
  have hH : ‖reflectedDivisorHead N t ((r : ℂ) + v * I)‖ ≤ D :=
    norm_reflectedDivisorHead_le N t (by simp; linarith [hr.2])
  have haY : (Y : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hY.le]
    exact Real.pi_pos.ne
  have hΓ : ‖Gamma ((r : ℂ) + v * I) * (Y : ℂ) ^ ((r : ℂ) + v * I)‖ *
      |v| ^ 4 ≤ G := by
    simpa only [Complex.inv_cpow _ _ haY, Complex.cpow_neg, inv_inv] using hGb r hr v hv0
  have hprod : ‖zetaSquareFiniteHeadKernel N Y t ((r : ℂ) + v * I)‖ * |v| ^ 2 ≤
      4 * C ^ 2 * D * G := by
    rw [zetaSquareFiniteHeadKernel, norm_mul, norm_mul, norm_pow]
    calc
      _ ≤ (‖Gamma ((r : ℂ) + v * I) * (Y : ℂ) ^ ((r : ℂ) + v * I)‖ *
          (2 * C * |v|) ^ 2 * D) * |v| ^ 2 := by gcongr
      _ = (4 * C ^ 2 * D) *
          (‖Gamma ((r : ℂ) + v * I) * (Y : ℂ) ^ ((r : ℂ) + v * I)‖ *
            |v| ^ 4) := by ring
      _ ≤ _ := by gcongr
  rw [sq_abs] at hprod
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < 1 + v ^ 2)).mpr
  have hn := norm_nonneg (zetaSquareFiniteHeadKernel N Y t ((r : ℂ) + v * I))
  nlinarith

/-- Continuity on each pole-free vertical line of the actual finite-head kernel. -/
theorem continuous_zetaSquareFiniteHeadKernel_vertical (N : ℕ) {Y : ℝ}
    (hY : 0 < Y) (t : ℝ) {r : ℝ}
    (hr : -1 < r) (hr' : r < 1 / 2) (hr0 : r ≠ 0) :
    Continuous (fun v : ℝ => zetaSquareFiniteHeadKernel N Y t ((r : ℂ) + v * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  have hz : ((r : ℂ) + v * I) ≠ 0 := by
    intro he
    apply hr0
    simpa using congrArg Complex.re he
  exact (analyticAt_zetaSquareFiniteHeadKernel N hY t
    (by simpa using hr) (by simpa using hr') hz).continuousAt.comp
      (f := fun v : ℝ => (r : ℂ) + v * I) (by fun_prop)

/-- Absolute integrability on every pole-free vertical line in the shift strip. -/
theorem integrable_zetaSquareFiniteHeadKernel_vertical (N : ℕ) {Y : ℝ}
    (hY : 0 < Y) (t : ℝ) {r : ℝ}
    (hr : -1 < r) (hr' : r < 1 / 2) (hr0 : r ≠ 0) :
    Integrable (fun v : ℝ => zetaSquareFiniteHeadKernel N Y t ((r : ℂ) + v * I)) := by
  obtain ⟨B, T₀, _, _, hbound⟩ :=
    exists_zetaSquareFiniteHeadKernel_strip_tail N hY t hr (b := r) hr'
  exact MeasureTheory.integrable_of_continuous_of_cauchy_tail
    (continuous_zetaSquareFiniteHeadKernel_vertical N hY t hr hr' hr0)
    (hbound r ⟨le_rfl, le_rfl⟩)

/-- Unconditional exact finite-head shift. The residue is added on the right line. -/
theorem zetaSquareFiniteHeadIntegral_eq_residue_add_leftIntegral (N : ℕ) {Y : ℝ}
    (hY : 0 < Y) (t : ℝ) {a b : ℝ}
    (ha : -1 < a) (ha0 : a < 0) (hb : 0 < b) (hb' : b < 1 / 2) :
    (1 / (2 * (Real.pi : ℂ))) *
        (∫ v : ℝ, zetaSquareFiniteHeadKernel N Y t ((b : ℂ) + v * I)) =
      Zeta23.XiPrime.chiFE ((1 / 2 : ℂ) + I * t) ^ 2 *
          conj (divisorPolynomial N (fun _ => 1) t) +
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ v : ℝ, zetaSquareFiniteHeadKernel N Y t ((a : ℂ) + v * I) := by
  obtain ⟨B, T₀, _, _, hbound⟩ :=
    exists_zetaSquareFiniteHeadKernel_strip_tail N hY t ha hb'
  have hab : a ≤ b := by linarith
  have hint (r : ℝ) (hr : r ∈ Icc a b) (hr0 : r ≠ 0) :
      Integrable (fun v : ℝ => zetaSquareFiniteHeadKernel N Y t ((r : ℂ) + v * I)) := by
    have hc : Continuous (fun v : ℝ => zetaSquareFiniteHeadKernel N Y t
        ((r : ℂ) + v * I)) := by
      apply continuous_iff_continuousAt.mpr
      intro v
      have hz : ((r : ℂ) + v * I) ≠ 0 := by
        intro he
        apply hr0
        simpa using congrArg Complex.re he
      exact (analyticAt_zetaSquareFiniteHeadKernel N hY t
        (by simp; linarith [hr.1]) (by simp; linarith [hr.2]) hz).continuousAt.comp
          (f := fun v : ℝ => (r : ℂ) + v * I) (by fun_prop)
    exact MeasureTheory.integrable_of_continuous_of_cauchy_tail hc (hbound r hr)
  have hrect : ∀ᶠ T : ℝ in atTop,
      RectangleIntegral' (zetaSquareFiniteHeadKernel N Y t)
        ((a : ℂ) - T * I) ((b : ℂ) + T * I) =
      Zeta23.XiPrime.chiFE ((1 / 2 : ℂ) + I * t) ^ 2 *
        conj (divisorPolynomial N (fun _ => 1) t) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact rectangleIntegral_zetaSquareFiniteHeadKernel N hY t ha ha0 hb hb' hT
  exact Complex.mellin_vertical_eq_of_rectangle_of_cauchy_tail hab
    (hint a ⟨le_rfl, hab⟩ ha0.ne) (hint b ⟨hab, le_rfl⟩ hb.ne') hbound hrect

/-- Exact evaluation of the reflected head on every vertical line. -/
theorem reflectedDivisorHead_vertical (N : ℕ) (r t v : ℝ) :
    reflectedDivisorHead N t ((r : ℂ) + v * I) =
      divisorPolynomial N (fun n => (((n : ℝ) ^ r : ℝ) : ℂ)) (-(t + v)) := by
  unfold reflectedDivisorHead divisorPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1)
  have he : (((n : ℝ) ^ r : ℝ) : ℂ) =
      Complex.exp ((r : ℂ) * (Real.log n : ℂ)) := by
    rw [Real.rpow_def_of_pos hn0, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  dsimp only
  rw [he]
  calc
    _ = criticalDivisorCoefficient n *
        Complex.exp ((r : ℂ) * (Real.log n : ℂ) +
          I * (-(t + v) : ℝ) * (-Real.log n)) := by
      congr 2
      push_cast
      ring
    _ = _ := by rw [Complex.exp_add]; ring

/-- Conjugate form of the exact vertical evaluation. -/
theorem reflectedDivisorHead_vertical_eq_conj (N : ℕ) (r t v : ℝ) :
    reflectedDivisorHead N t ((r : ℂ) + v * I) =
      conj (divisorPolynomial N (fun n => (((n : ℝ) ^ r : ℝ) : ℂ)) (t + v)) := by
  rw [reflectedDivisorHead_vertical]
  have hhalf : conj (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      Complex.conj_ofReal (1 / 2)
  have hc (n : ℕ) : conj (criticalDivisorCoefficient n) =
      criticalDivisorCoefficient n := by
    simp only [criticalDivisorCoefficient, map_mul, map_natCast, ← Complex.exp_conj,
      map_neg, hhalf, Complex.conj_ofReal]
  simp only [divisorPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [map_mul, hc, ← Complex.exp_conj, map_neg, Complex.conj_I,
    Complex.conj_ofReal]
  congr 2
  push_cast
  ring

/-- Joint continuity of the actual finite head in both ordinates. -/
theorem continuous_reflectedDivisorHead_vertical_joint (N : ℕ) (r : ℝ) :
    Continuous (fun p : ℝ × ℝ =>
      reflectedDivisorHead N p.1 ((r : ℂ) + p.2 * I)) := by
  unfold reflectedDivisorHead
  fun_prop

/-- Joint continuity of the finite-head kernel on each pole-free vertical line. -/
theorem continuous_zetaSquareFiniteHeadKernel_vertical_joint (N : ℕ) {Y : ℝ}
    (hY : 0 < Y) {r : ℝ} (hr : -1 < r) (hr' : r < 1 / 2) (hr0 : r ≠ 0) :
    Continuous (fun p : ℝ × ℝ =>
      zetaSquareFiniteHeadKernel N Y p.1 ((r : ℂ) + p.2 * I)) := by
  have hΓ : Continuous (fun p : ℝ × ℝ => Gamma ((r : ℂ) + p.2 * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hz0 : (r : ℂ) + p.2 * I ≠ 0 := by
      intro he
      exact hr0 (by simpa using congrArg Complex.re he)
    have ha : AnalyticAt ℂ Gamma ((r : ℂ) + p.2 * I) := by
      rw [Gamma_eq_shift_div]
      exact (analyticAt_Gamma_add_one_of_re (by simpa using hr)).div analyticAt_id hz0
    exact ha.continuousAt.comp
      (f := fun p : ℝ × ℝ => (r : ℂ) + p.2 * I) (by fun_prop)
  have hYc : Continuous (fun p : ℝ × ℝ => (Y : ℂ) ^ ((r : ℂ) + p.2 * I)) := by
    simp only [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hY.ne')]
    fun_prop
  have hχ : Continuous (fun p : ℝ × ℝ =>
      Zeta23.XiPrime.chiFE ((1 / 2 : ℂ) + I * p.1 + ((r : ℂ) + p.2 * I))) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hs : ((1 / 2 : ℂ) + I * p.1 + ((r : ℂ) + p.2 * I)).re < 1 := by
      simp
      linarith
    have hs1 : (1 / 2 : ℂ) + I * p.1 + ((r : ℂ) + p.2 * I) ≠ 1 := by
      intro he
      rw [he] at hs
      norm_num at hs
    exact (Zeta23.XiPrime.Hardy.EFContour.chiFE_analyticAt'
      (Zeta23.XiPrime.Hardy.EFContour.Gammaℝ_one_sub_ne_zero_of_re
        (by linarith) hs1)).continuousAt.comp
      (f := fun p : ℝ × ℝ =>
        (1 / 2 : ℂ) + I * p.1 + ((r : ℂ) + p.2 * I)) (by fun_prop)
  exact ((hΓ.mul hYc).mul (hχ.pow 2)).mul
    (continuous_reflectedDivisorHead_vertical_joint N r)

end RiemannResearch.Analysis

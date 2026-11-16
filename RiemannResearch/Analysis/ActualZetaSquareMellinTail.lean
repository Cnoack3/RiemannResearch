/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.HurwitzEulerMaclaurin
import RiemannResearch.Analysis.DampedGammaStripBounds
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
/-!
# Uniform far tails of the actual zeta-square Mellin kernel

The smoothing scale is kept outside the Gamma decay constant by using
the existing Gamma theorem with damping one. The actual quadratic Hurwitz
growth theorem supplies the actual zeta bound, including the compact range.

On Re z = -3/4 the resulting kernel has arbitrary-order inverse-power
decay when |t| <= 4 |Im z|. Both outward tail integrals beyond U/2 are
bounded by C_m Y^(-3/4) U^(-m-1), for U >= 2, |t| <= 2 U
and every real Y > 0. The scale-independent Y >= 1 estimates are retained
as corollaries.

Source for the kernel and contour setting: Chourasiya--Simonic,
arXiv:2507.15184v2, Section 5.1, equations (51)--(52):
https://arxiv.org/html/2507.15184v2
The central contour region, moving residue, and the complete uniform
actual remainder are not established by this module.
-/
noncomputable section
open Complex MeasureTheory Set Filter
open scoped Topology
namespace RiemannResearch.Analysis

theorem exists_riemannZeta_vertical_quadratic_bound {σ : ℝ}
    (hσ : -1 < σ) (hσ1 : σ ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤ C * (1 + |t|) ^ 2 := by
  obtain ⟨C,hC,hCb⟩ :=
    HurwitzEulerMaclaurin.exists_hurwitzZeta_shifted_strip_bound
      (0 : UnitAddCircle) 0 (a := σ) (b := σ) (by simpa using hσ)
  have hc : Continuous (fun t : ℝ => riemannZeta ((σ : ℂ) + t * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (differentiableAt_riemannZeta ?_).continuousAt.comp (by fun_prop)
    intro he
    apply hσ1
    have hr := congrArg Complex.re he
    simpa using hr
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-2 : ℝ) 2) hc.continuousOn
  let D := max C (max B 1)
  have hDC : C ≤ D := le_max_left _ _
  have hDB : B ≤ D := (le_max_left B 1).trans (le_max_right C _)
  have hD : 0 < D := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    ((le_max_right B 1).trans (le_max_right C _))
  refine ⟨D,hD,?_⟩
  intro t
  by_cases ht : 2 ≤ |t|
  · have hh := hCb σ ⟨le_rfl,le_rfl⟩ t (by simpa using ht)
    have hh' : ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤ C * |t| ^ 2 := by
      simpa [HurwitzZeta.hurwitzZeta_zero] using hh
    apply hh'.trans
    exact mul_le_mul hDC
      (pow_le_pow_left₀ (abs_nonneg t) (by linarith : |t| ≤ 1 + |t|) 2)
      (sq_nonneg _) hD.le
  · have ht' : t ∈ Icc (-2 : ℝ) 2 := by
      have := abs_lt.mp (lt_of_not_ge ht)
      constructor <;> linarith
    apply (hB t ht').trans
    have hp : (1 : ℝ) ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t]
    exact hDB.trans (by nlinarith [mul_le_mul_of_nonneg_left hp hD.le])

/-- The actual zeta-square integrand; the smoothing scale is retained explicitly. -/
def zetaSquareMellinKernel (Y t : ℝ) (z : ℂ) : ℂ :=
  Gamma z * (Y : ℂ) ^ z * riemannZeta ((1 / 2 : ℂ) + I * t + z) ^ 2

/-- Arbitrary-order far-tail decay, uniform in both the height and all Y ≥ 1. -/
theorem exists_zetaSquareMellinKernel_left_far_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y t v : ℝ,
      1 ≤ Y → 1 ≤ |v| → |t| ≤ 4 * |v| →
      ‖zetaSquareMellinKernel Y t ((-3 / 4 : ℂ) + v * I)‖ * |v| ^ m ≤ C := by
  obtain ⟨Z,hZ,hZb⟩ := exists_riemannZeta_vertical_quadratic_bound
    (σ := -1 / 4) (by norm_num) (by norm_num)
  obtain ⟨G,hG,hGb⟩ := Complex.exists_gamma_mul_cpow_neg_strip_pow_bound
    (lam := 1) (by norm_num) (a := -3 / 4) (b := -3 / 4) (m + 4)
    (by push_cast; have := Nat.cast_nonneg (α := ℝ) m; linarith)
  refine ⟨1296 * G * Z ^ 2, by positivity, ?_⟩
  intro Y t v hY hv ht
  have hv0 : v ≠ 0 := by intro he; norm_num [he] at hv
  have hγ := hGb (-3 / 4) ⟨le_rfl,le_rfl⟩ v hv0
  norm_num only [one_cpow, mul_one, Complex.ofReal_neg, Complex.ofReal_div,
    Complex.ofReal_ofNat] at hγ
  have hY0 : 0 < Y := by linarith
  have hp : ‖(Y : ℂ) ^ ((-3 / 4 : ℂ) + v * I)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY0]
    have hre : (((-3 / 4 : ℂ) + v * I)).re = (-3 / 4 : ℝ) := by simp
    rw [hre]
    exact Real.rpow_le_one_of_one_le_of_nonpos hY (by norm_num)
  have hzarg : (1 / 2 : ℂ) + I * t + ((-3 / 4 : ℂ) + v * I) =
      ((-1 / 4 : ℝ) : ℂ) + ((t + v : ℝ) : ℂ) * I := by push_cast; ring
  have hh : 1 + |t + v| ≤ 6 * |v| := by
    have := abs_add_le t v
    linarith
  have hz : ‖riemannZeta ((1 / 2 : ℂ) + I * t + ((-3 / 4 : ℂ) + v * I))‖ ≤
      36 * Z * |v| ^ 2 := by
    rw [hzarg]
    apply (hZb (t + v)).trans
    have hb := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hh 2) hZ.le
    nlinarith [hb]
  have hγ0 := norm_nonneg (Gamma ((-3 / 4 : ℂ) + v * I))
  calc
    _ = ‖Gamma ((-3 / 4 : ℂ) + v * I)‖ *
        ‖(Y : ℂ) ^ ((-3 / 4 : ℂ) + v * I)‖ *
        ‖riemannZeta ((1 / 2 : ℂ) + I * t + ((-3 / 4 : ℂ) + v * I))‖ ^ 2 * |v| ^ m := by
      simp only [zetaSquareMellinKernel, norm_mul, norm_pow]
    _ ≤ ‖Gamma ((-3 / 4 : ℂ) + v * I)‖ * 1 *
        (36 * Z * |v| ^ 2) ^ 2 * |v| ^ m := by
      gcongr
    _ = 1296 * Z ^ 2 * (‖Gamma ((-3 / 4 : ℂ) + v * I)‖ * |v| ^ (m + 4)) := by
      rw [pow_add]
      ring
    _ ≤ _ := by
      have hb := mul_le_mul_of_nonneg_left hγ
        (by positivity : 0 ≤ 1296 * Z ^ 2)
      nlinarith [hb]

theorem continuous_zetaSquareMellinKernel_left_of_pos {Y : ℝ} (hY : 0 < Y) (t τ : ℝ) :
    Continuous (fun v : ℝ => zetaSquareMellinKernel Y t ((-3 / 4 : ℂ) + (τ * v : ℝ) * I)) := by
  have ha : Continuous (fun v : ℝ => (-3 / 4 : ℂ) + (τ * v : ℝ) * I) := by fun_prop
  have hg : Continuous (fun v : ℝ => Gamma ((-3 / 4 : ℂ) + (τ * v : ℝ) * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    apply (Complex.continuousAt_Gamma _ ?_).comp ha.continuousAt
    intro n hn
    have hr := congrArg Complex.re hn
    norm_num at hr
    have hn' : 4 * n = 3 := by
      exact_mod_cast (show (4 : ℝ) * n = 3 by linarith)
    omega
  have hY0 : (Y : ℂ) ≠ 0 := by
    exact_mod_cast (show Y ≠ 0 by linarith)
  have hp : Continuous (fun v : ℝ => (Y : ℂ) ^ ((-3 / 4 : ℂ) + (τ * v : ℝ) * I)) :=
    ha.const_cpow (Or.inl hY0)
  have hz : Continuous (fun v : ℝ =>
      riemannZeta ((1 / 2 : ℂ) + I * t + ((-3 / 4 : ℂ) + (τ * v : ℝ) * I))) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    apply (differentiableAt_riemannZeta ?_).continuousAt.comp (by fun_prop)
    intro he
    have hr := congrArg Complex.re he
    norm_num at hr
  exact (hg.mul hp).mul (hz.pow 2)

/-- The complete smoothing-scale dependence on the left line. -/
theorem norm_zetaSquareMellinKernel_left_scale {Y : ℝ} (hY : 0 < Y) (t v : ℝ) :
    ‖zetaSquareMellinKernel Y t ((-3 / 4 : ℂ) + v * I)‖ =
      Y ^ (-3 / 4 : ℝ) * ‖zetaSquareMellinKernel 1 t ((-3 / 4 : ℂ) + v * I)‖ := by
  have hy : ‖(Y : ℂ) ^ ((-3 / 4 : ℂ) + v * I)‖ = Y ^ (-3 / 4 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
    norm_num
  simp only [zetaSquareMellinKernel, norm_mul, hy, Complex.ofReal_one,
    Complex.one_cpow, mul_one]
  ring

theorem exists_zetaSquareMellinKernel_left_far_bound_scaled (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y t v : ℝ, 0 < Y → 1 ≤ |v| → |t| ≤ 4 * |v| →
      ‖zetaSquareMellinKernel Y t ((-3 / 4 : ℂ) + v * I)‖ * |v| ^ m ≤
        C * Y ^ (-3 / 4 : ℝ) := by
  obtain ⟨C, hC, hCb⟩ := exists_zetaSquareMellinKernel_left_far_bound m
  refine ⟨C, hC, ?_⟩
  intro Y t v hY hv ht
  rw [norm_zetaSquareMellinKernel_left_scale hY]
  have hh := mul_le_mul_of_nonneg_left (hCb 1 t v (by norm_num) hv ht)
    (Real.rpow_nonneg hY.le (-3 / 4))
  nlinarith [hh]

/-- Both original left-line tails decay to every inverse-power order,
uniformly in the height, with the exact scale factor for every Y > 0. -/
theorem exists_zetaSquareMellinKernel_left_tail_integral_pow_bound_scaled (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y t U τ : ℝ,
      0 < Y → 2 ≤ U → |t| ≤ 2 * U → |τ| = 1 →
      IntegrableOn
        (fun v : ℝ => zetaSquareMellinKernel Y t ((-3 / 4 : ℂ) + (τ * v : ℝ) * I))
        (Ioi (U / 2)) volume ∧
      ‖∫ v : ℝ in Ioi (U / 2),
        zetaSquareMellinKernel Y t ((-3 / 4 : ℂ) + (τ * v : ℝ) * I)‖ * U ^ m ≤
          C * Y ^ (-3 / 4 : ℝ) / U := by
  obtain ⟨C,hC,hCb⟩ := exists_zetaSquareMellinKernel_left_far_bound_scaled (m+2)
  refine ⟨2 ^ (m+1) * C, by positivity, ?_⟩
  intro Y t U τ hY hU ht hτ
  have hU0 : 0 < U := by linarith
  have ha0 : 0 < U / 2 := by linarith
  let B : ℝ := (C * Y ^ (-3 / 4 : ℝ)) * 2 ^ m / U ^ m
  let f : ℝ → ℂ := fun v => zetaSquareMellinKernel Y t ((-3 / 4 : ℂ) + (τ * v : ℝ) * I)
  have henv : IntegrableOn (fun v : ℝ => B * v ^ (-2 : ℝ)) (Ioi (U / 2)) volume :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha0).const_mul B
  have hb (v : ℝ) (hv : v ∈ Ioi (U / 2)) : ‖f v‖ ≤ B * v ^ (-2 : ℝ) := by
    have hv1 : 1 ≤ v := by have := hv; change U / 2 < v at this; linarith
    have hv0 : 0 < v := by linarith
    have hUv : U ≤ 2 * v := by have := hv; change U / 2 < v at this; linarith
    have he : |τ * v| = v := by rw [abs_mul,hτ,one_mul,abs_of_pos hv0]
    have hh := hCb Y t (τ * v) hY (by simpa only [he] using hv1) (by
      rw [he]; linarith)
    rw [he] at hh
    have hh' : ‖f v‖ * v ^ (m+2) ≤ C * Y ^ (-3 / 4 : ℝ) := hh
    have hx : (‖f v‖ * v ^ 2) * U ^ m ≤ (C * Y ^ (-3 / 4 : ℝ)) * 2 ^ m := by
      calc
        _ ≤ (‖f v‖ * v ^ 2) * (2*v) ^ m := by gcongr
        _ = (‖f v‖ * v ^ (m+2)) * 2 ^ m := by
          rw [mul_pow, pow_add]
          ring
        _ ≤ (C * Y ^ (-3 / 4 : ℝ)) * 2 ^ m := by gcongr
    have hx' : ‖f v‖ * v ^ 2 ≤ B := (le_div_iff₀ (pow_pos hU0 m)).2 hx
    rw [Real.rpow_neg hv0.le, Real.rpow_two]
    simpa only [div_eq_mul_inv] using (le_div_iff₀ (sq_pos_of_pos hv0)).2 hx'
  have hbae : ∀ᵐ v ∂volume.restrict (Ioi (U / 2)), ‖f v‖ ≤ B * v ^ (-2 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact hb v hv
  have hi : IntegrableOn f (Ioi (U / 2)) volume :=
    henv.mono' (continuous_zetaSquareMellinKernel_left_of_pos hY t τ).aestronglyMeasurable hbae
  refine ⟨hi,?_⟩
  have hh : ‖∫ v in Ioi (U / 2), f v‖ ≤ 2 * B / U := by
    calc
      _ ≤ ∫ v in Ioi (U / 2), ‖f v‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ v in Ioi (U / 2), B * v ^ (-2 : ℝ) :=
        integral_mono_ae hi.norm henv hbae
      _ = 2 * B / U := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) ha0]
        norm_num [Real.rpow_neg_one]
        field_simp
  calc
    _ ≤ (2 * B / U) * U ^ m := mul_le_mul_of_nonneg_right hh (pow_nonneg hU0.le m)
    _ = (2 ^ (m+1) * C) * Y ^ (-3 / 4 : ℝ) / U := by
      dsimp [B]
      rw [pow_succ]
      field_simp



/-- The original continuity interface for smoothing scales at least one. -/
theorem continuous_zetaSquareMellinKernel_left {Y : ℝ} (hY : 1 ≤ Y) (t τ : ℝ) :
    Continuous (fun v : ℝ =>
      zetaSquareMellinKernel Y t ((-3 / 4 : ℂ) + (τ * v : ℝ) * I)) :=
  continuous_zetaSquareMellinKernel_left_of_pos (by linarith) t τ

/-- A scale-independent corollary for all Y >= 1. -/
theorem exists_zetaSquareMellinKernel_left_tail_integral_pow_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y t U τ : ℝ,
      1 ≤ Y → 2 ≤ U → |t| ≤ 2 * U → |τ| = 1 →
      IntegrableOn
        (fun v : ℝ => zetaSquareMellinKernel Y t ((-3 / 4 : ℂ) + (τ * v : ℝ) * I))
        (Ioi (U / 2)) volume ∧
      ‖∫ v : ℝ in Ioi (U / 2),
        zetaSquareMellinKernel Y t ((-3 / 4 : ℂ) + (τ * v : ℝ) * I)‖ * U ^ m ≤ C / U := by
  obtain ⟨C, hC, hCb⟩ := exists_zetaSquareMellinKernel_left_tail_integral_pow_bound_scaled m
  refine ⟨C, hC, ?_⟩
  intro Y t U τ hY hU ht hτ
  obtain ⟨hi, hb⟩ := hCb Y t U τ (by linarith) hU ht hτ
  refine ⟨hi, hb.trans ?_⟩
  apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ U)
  have hp := Real.rpow_le_one_of_one_le_of_nonpos hY (by norm_num : (-3 / 4 : ℝ) ≤ 0)
  nlinarith [mul_le_mul_of_nonneg_left hp hC]

/-- Both outward parametrizations of the far left-line tails are integrable
and bounded uniformly in the outer height and smoothing scale. -/
theorem exists_zetaSquareMellinKernel_left_tail_integral_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y t U τ : ℝ,
      1 ≤ Y → 2 ≤ U → |t| ≤ 2 * U → |τ| = 1 →
      IntegrableOn
        (fun v : ℝ => zetaSquareMellinKernel Y t ((-3 / 4 : ℂ) + (τ * v : ℝ) * I))
        (Ioi (U / 2)) volume ∧
      ‖∫ v : ℝ in Ioi (U / 2),
        zetaSquareMellinKernel Y t ((-3 / 4 : ℂ) + (τ * v : ℝ) * I)‖ ≤ 2 * C / U := by
  obtain ⟨C, hC, hCb⟩ := exists_zetaSquareMellinKernel_left_tail_integral_pow_bound 0
  refine ⟨C / 2, by positivity, ?_⟩
  simpa only [pow_zero, mul_one, show 2 * (C / 2) = C by ring] using hCb

end RiemannResearch.Analysis

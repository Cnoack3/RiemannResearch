/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomeryWindowVarianceCriterion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Pair correlation from differences between adjacent dyadic width averages

For every rational width interval, test the triangle error at two adjacent
dyadic rescalings of that interval. Finite triangular overlap is sublinear
under contraction. The first difference therefore bounds the unscaled
moment, and telescoping recovers the original interval average.
-/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroWindowVariance

private def widthScale (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

private theorem widthScale_bounds (n : ℕ) :
    0 ≤ widthScale n ∧ widthScale n ≤ 1 :=
  ⟨pow_nonneg (by norm_num) _, pow_le_one₀ (by norm_num) (by norm_num)⟩

/-- Each individual overlap contracts at least as rapidly as the width. -/
theorem unfoldedWindowEnergy_scale_le {T c : ℝ} (hT : 1 < T)
    (hc : 0 ≤ c) (hc₁ : c ≤ 1) (r : ℝ) :
    unfoldedWindowEnergy T (c * r) ≤ c * unfoldedWindowEnergy T r := by
  unfold unfoldedWindowEnergy actualPhysicalTriangleEnergy
  rw [← mul_div_assoc, Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ (by linarith)
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [mul_max_of_nonneg _ _ hc, mul_zero, mul_div_assoc]
  apply max_le_max_right
  have hd := abs_nonneg (i.1.1.im - j.1.1.im)
  have hm := mul_le_mul_of_nonneg_right hc₁ hd
  simp only [one_mul] at hm
  linarith

private theorem continuous_actual_width (T : ℝ) : Continuous (unfoldedWindowEnergy T) := by
  unfold unfoldedWindowEnergy actualPhysicalTriangleEnergy
  fun_prop

private theorem actual_width_nonneg {T : ℝ} (hT : 1 < T) (r : ℝ) :
    0 ≤ unfoldedWindowEnergy T r := by
  unfold unfoldedWindowEnergy actualPhysicalTriangleEnergy
  exact div_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    le_max_right _ _) (by linarith)

private theorem model_width_bounds {r b : ℝ} (hr : 0 ≤ r) (hb : r ≤ b) :
    0 ≤ sineWindowEnergy r ∧ sineWindowEnergy r ≤ r * (1 + 2 * sineGapMass b) := by
  have h0 : sineGapMass 0 = 0 := by simp [sineGapMass]
  have hn := intervalIntegral.integral_nonneg (μ := volume) hr
    (fun u hu => (h0 ▸ sineGapMass_mono hu.1 : 0 ≤ sineGapMass u))
  have hm := intervalIntegral.integral_mono_on (μ := volume) hr
    sineGapMass_mono.intervalIntegrable (g := fun _ : ℝ => sineGapMass b)
    intervalIntegrable_const (fun u hu => sineGapMass_mono (hu.2.trans hb))
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hm
  unfold sineWindowEnergy
  constructor <;> linarith

/-- Integral of the signed actual-minus-sine triangle error with widths
rescaled by `2⁻ⁿ`. Integration is always on the original interval. -/
def dyadicTriangleWidthError (T a b : ℝ) (n : ℕ) : ℝ :=
  ∫ r in a..b, unfoldedWindowEnergy T ((1 / 2 : ℝ) ^ n * r)
    - sineWindowEnergy ((1 / 2 : ℝ) ^ n * r)

/-- Test only differences between adjacent dyadic scales. The two width
tests have equal total mass in the original integration variable. -/
def RationalDyadicTriangleWidthContrasts : Prop :=
  ∀ a b : ℚ, 0 < a → a < b → ∀ n : ℕ,
    Tendsto (fun T : ℝ => dyadicTriangleWidthError T a b n -
      dyadicTriangleWidthError T a b (n + 1)) atTop (𝓝 0)

private theorem tendsto_of_dyadic_contrasts (X : ℝ → ℕ → ℝ) (Y : ℕ → ℝ) (B : ℝ)
    (hx : ∀ᶠ T : ℝ in atTop, ∀ n, 0 ≤ X T n ∧ X T n ≤ widthScale n * X T 0)
    (hy : ∀ n, 0 ≤ Y n ∧ Y n ≤ widthScale n * B)
    (h : ∀ n : ℕ, Tendsto (fun T : ℝ => (X T n - Y n) - (X T (n+1) - Y (n+1)))
      atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => X T 0 - Y 0) atTop (𝓝 0) := by
  have ht (n : ℕ) : Tendsto (fun T : ℝ => (X T 0 - Y 0) - (X T n - Y n))
      atTop (𝓝 0) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hh := ih.add (h n)
      simp only [zero_add] at hh
      exact hh.congr' (Eventually.of_forall fun T => by dsimp; ring)
  have hbound : ∀ᶠ T : ℝ in atTop, X T 0 ≤ 2 * (Y 0 + 1) := by
    filter_upwards [hx, (h 0).eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with T hX hh
    have hs := (hX 1).2
    norm_num [widthScale] at hs
    dsimp at hh
    linarith [(hy 1).1]
  let C := 2 * (Y 0 + 1) + B
  have hc : Tendsto (fun n : ℕ => widthScale n * C) atTop (𝓝 0) := by
    simpa [widthScale] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (show (0:ℝ) ≤ 1 / 2 by norm_num)
        (show (1/2:ℝ) < 1 by norm_num)).mul_const C
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := (hc.eventually (gt_mem_nhds (show 0 < ε / 2 by linarith))).exists
  filter_upwards [hx, hbound, Metric.tendsto_nhds.1 (ht n) (ε / 2) (by linarith)] with T hX hM hδ
  have hp := mul_le_mul_of_nonneg_left hM (widthScale_bounds n).1
  have hk : X T n + Y n < ε / 2 := by
    dsimp [C] at hn
    rw [mul_add] at hn
    linarith [(hX n).2, (hy n).2]
  rw [Real.dist_eq, sub_zero, abs_lt] at hδ ⊢
  constructor <;> linarith [(hX n).1, (hy n).1, hδ.1, hδ.2]

/-- Balanced dyadic tests recover the signed rational interval averages.
The necessary uniform height bound follows from the first contrast. -/
theorem rationalTriangleWidthAverages_of_dyadicContrasts
    (h : RationalDyadicTriangleWidthContrasts) : RationalTriangleWidthAverages := by
  intro a b ha hab
  have ha' : 0 ≤ (a : ℝ) := by exact_mod_cast ha.le
  have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab.le
  let X (T : ℝ) (n : ℕ) :=
    ∫ r in (a : ℝ)..(b : ℝ), unfoldedWindowEnergy T (widthScale n * r)
  let Y (n : ℕ) := ∫ r in (a : ℝ)..(b : ℝ), sineWindowEnergy (widthScale n * r)
  have he (T : ℝ) (n : ℕ) : dyadicTriangleWidthError T a b n = X T n - Y n := by
    apply intervalIntegral.integral_sub
    · exact ((continuous_actual_width T).comp
        (continuous_const.mul continuous_id)).intervalIntegrable _ _
    · exact (continuous_sineWindowEnergy.comp
        (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hX : ∀ᶠ T : ℝ in atTop, ∀ n, 0 ≤ X T n ∧ X T n ≤ widthScale n * X T 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    intro n
    constructor
    · exact intervalIntegral.integral_nonneg hab' (fun r _ => actual_width_nonneg hT _)
    · have hh := intervalIntegral.integral_mono_on (μ := volume) hab'
        (f := fun r : ℝ => unfoldedWindowEnergy T (widthScale n * r))
        (g := fun r : ℝ => widthScale n * unfoldedWindowEnergy T r)
        (((continuous_actual_width T).comp
          (continuous_const.mul continuous_id)).intervalIntegrable _ _)
        (((continuous_actual_width T).const_mul _).intervalIntegrable _ _)
        (fun r _ => unfoldedWindowEnergy_scale_le hT
          (widthScale_bounds n).1 (widthScale_bounds n).2 r)
      simpa [X, widthScale, intervalIntegral.integral_const_mul] using hh
  let B := ((b : ℝ) - (a : ℝ)) * (b : ℝ) * (1 + 2 * sineGapMass b)
  have hY (n : ℕ) : 0 ≤ Y n ∧ Y n ≤ widthScale n * B := by
    have hpos : 0 ≤ (1 + 2 * sineGapMass (b : ℝ)) := by
      have hh := sineGapMass_mono (ha'.trans hab')
      rw [show sineGapMass 0 = 0 by simp [sineGapMass]] at hh
      linarith
    have hrange (r : ℝ) (hr : r ∈ Icc (a : ℝ) (b : ℝ)) :
        0 ≤ widthScale n * r ∧ widthScale n * r ≤ (b : ℝ) := by
      have hp := ha'.trans hr.1
      exact ⟨mul_nonneg (widthScale_bounds n).1 hp,
        (mul_le_of_le_one_left hp (widthScale_bounds n).2).trans hr.2⟩
    constructor
    · exact intervalIntegral.integral_nonneg hab' (fun r hr =>
        (model_width_bounds (hrange r hr).1 (hrange r hr).2).1)
    · have hh := intervalIntegral.integral_mono_on (μ := volume) hab'
        (f := fun r : ℝ => sineWindowEnergy (widthScale n * r))
        (g := fun _ : ℝ => (widthScale n * (b : ℝ)) * (1 + 2 * sineGapMass b))
        ((continuous_sineWindowEnergy.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)
        intervalIntegrable_const (fun r hr =>
          (model_width_bounds (hrange r hr).1 (hrange r hr).2).2.trans
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hr.2 (widthScale_bounds n).1) hpos))
      simp only [intervalIntegral.integral_const, smul_eq_mul] at hh
      simpa only [Y, B, mul_assoc, mul_left_comm, mul_comm] using hh
  have hh := tendsto_of_dyadic_contrasts X Y B hX hY (fun n =>
    (h a b ha hab n).congr' (Eventually.of_forall fun T => by rw [he, he]))
  exact hh.congr' (Eventually.of_forall fun T => by
    rw [← he T 0]
    simp [dyadicTriangleWidthError])

theorem positiveGapPCC_of_rationalDyadicTriangleWidthContrasts
    (h : RationalDyadicTriangleWidthContrasts) : PositiveGapPCC :=
  positiveGapPCC_of_rationalTriangleWidthAverages
    (rationalTriangleWidthAverages_of_dyadicContrasts h)

/-- Rational rescaling turns every adjacent dyadic contrast into the
first contrast on another rational interval. Thus a single pair of
width scales suffices on each interval. -/
theorem rationalDyadicTriangleWidthContrasts_of_first
    (h : ∀ a b : ℚ, 0 < a → a < b →
      Tendsto (fun T : ℝ => dyadicTriangleWidthError T a b 0 -
        dyadicTriangleWidthError T a b 1) atTop (𝓝 0)) :
    RationalDyadicTriangleWidthContrasts := by
  intro a b ha hab n
  let q := (1 / 2 : ℚ) ^ n
  have hq : 0 < q := pow_pos (by norm_num) _
  have hqc : (q : ℝ) = (1 / 2 : ℝ) ^ n := by norm_num [q]
  have hqn : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have he (k : ℕ) (T : ℝ) :
      dyadicTriangleWidthError T a b (n + k) =
        (q : ℝ)⁻¹ * dyadicTriangleWidthError T (q * a) (q * b) k := by
    let f (r : ℝ) := unfoldedWindowEnergy T ((1 / 2 : ℝ)^k * r) -
      sineWindowEnergy ((1 / 2 : ℝ)^k * r)
    have hh := intervalIntegral.integral_comp_mul_right
      (a := (a : ℝ)) (b := (b : ℝ)) f hqn
    simpa only [dyadicTriangleWidthError, f, Rat.cast_mul, hqc, pow_add,
      smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using hh
  have hlim := (h (q * a) (q * b) (mul_pos hq ha)
    (mul_lt_mul_of_pos_left hab hq)).const_mul (q : ℝ)⁻¹
  simp only [mul_zero] at hlim
  exact hlim.congr' (Eventually.of_forall fun T => by
    dsimp
    rw [show dyadicTriangleWidthError T a b n =
      (q : ℝ)⁻¹ * dyadicTriangleWidthError T (q * a) (q * b) 0 by simpa using he 0 T, he 1 T]
    simp only [Rat.cast_mul]
    ring)

/-- The scale-one and scale-one-half signed averages on each positive
rational interval alone imply ordinary ordinate pair correlation. -/
theorem positiveGapPCC_of_rationalHalfWidthContrasts
    (h : ∀ a b : ℚ, 0 < a → a < b →
      Tendsto (fun T : ℝ => dyadicTriangleWidthError T a b 0 -
        dyadicTriangleWidthError T a b 1) atTop (𝓝 0)) : PositiveGapPCC :=
  positiveGapPCC_of_rationalDyadicTriangleWidthContrasts
    (rationalDyadicTriangleWidthContrasts_of_first h)

end RiemannResearch.Analysis.MontgomeryPositiveGap

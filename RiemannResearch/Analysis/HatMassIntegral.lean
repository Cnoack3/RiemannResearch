import RiemannResearch.Analysis.HatIntegrability
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Exact mass and squared mass of the actual centered hat

Source: user-provided argument,
`RH_Layer_Cake_Sublevel_Program_and_Next_Attack_2026-09-16_Continued.md`,
Section 29.2.  The proof integrates the two affine pieces, so neither integral
formula is assumed.  Mathlib's elementary polynomial integral formulas are used:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Integrals/Basic.html
-/

noncomputable section

namespace RiemannResearch.Analysis

open MeasureTheory

theorem centeredHat_eq_left {h x : ℝ} (hh : 0 < h)
    (hl : -h ≤ x) (hr : x ≤ 0) :
    centeredHat h x = 1 + x / h := by
  have h₁ : -1 ≤ x / h := (le_div_iff₀ hh).mpr (by linarith)
  have h₂ : x / h ≤ 0 := div_nonpos_of_nonpos_of_nonneg hr hh.le
  unfold centeredHat
  rw [rootTent_eq_left (a := -1) (x := x / h) h₁ (by linarith)]
  ring

theorem centeredHat_eq_right {h x : ℝ} (hh : 0 < h)
    (hl : 0 ≤ x) (hr : x ≤ h) :
    centeredHat h x = 1 - x / h := by
  have h₁ : 0 ≤ x / h := div_nonneg hl hh.le
  have h₂ : x / h ≤ 1 := (div_le_iff₀ hh).mpr (by linarith)
  unfold centeredHat
  rw [rootTent_eq_right (a := -1) (x := x / h) (by linarith) (by linarith)]
  ring

theorem integral_centeredHat_left {h : ℝ} (hh : 0 < h) :
    (∫ x in (-h)..0, centeredHat h x) = h / 2 := by
  calc
    (∫ x in (-h)..0, centeredHat h x) = ∫ x in (-h)..0, (1 + x / h) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by linarith : -h ≤ 0)] at hx
      exact centeredHat_eq_left hh hx.1 hx.2
    _ = h / 2 := by
      have hi : IntervalIntegrable (fun x : ℝ => x / h) volume (-h) 0 :=
        (continuous_id.div_const h).intervalIntegrable (-h) 0
      rw [intervalIntegral.integral_add
        (f := fun _ : ℝ => 1) (g := fun x : ℝ => x / h) intervalIntegrable_const hi]
      rw [integral_one, intervalIntegral.integral_div, integral_id]
      field_simp [ne_of_gt hh]
      ring

theorem integral_centeredHat_right {h : ℝ} (hh : 0 < h) :
    (∫ x in 0..h, centeredHat h x) = h / 2 := by
  calc
    (∫ x in 0..h, centeredHat h x) = ∫ x in 0..h, (1 - x / h) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hh.le] at hx
      exact centeredHat_eq_right hh hx.1 hx.2
    _ = h / 2 := by
      have hi : IntervalIntegrable (fun x : ℝ => x / h) volume 0 h :=
        (continuous_id.div_const h).intervalIntegrable 0 h
      rw [intervalIntegral.integral_sub
        (f := fun _ : ℝ => 1) (g := fun x : ℝ => x / h) intervalIntegrable_const hi]
      rw [integral_one, intervalIntegral.integral_div, integral_id]
      field_simp [ne_of_gt hh]
      ring

theorem intervalIntegral_centeredHat {h : ℝ} (hh : 0 < h) :
    (∫ x in (-h)..h, centeredHat h x) = h := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((continuous_centeredHat h).intervalIntegrable (-h) 0)
    ((continuous_centeredHat h).intervalIntegrable 0 h),
    integral_centeredHat_left hh, integral_centeredHat_right hh]
  ring

/-- The unnormalized height-one hat has total mass exactly its half-width. -/
theorem integral_centeredHat {h : ℝ} (hh : 0 < h) :
    (∫ x, centeredHat h x) = h := by
  calc
    (∫ x, centeredHat h x) = ∫ x in Set.Ioo (-h) h, centeredHat h x := by
      simpa only [support_centeredHat hh] using
        (setIntegral_support (F := centeredHat h) (ν := volume)).symm
    _ = ∫ x in (-h)..h, centeredHat h x := by
      rw [intervalIntegral.integral_of_le (by linarith : -h ≤ h),
        integral_Ioc_eq_integral_Ioo]
    _ = h := intervalIntegral_centeredHat hh

private theorem intervalIntegral_quadratic (a b A B C : ℝ) :
    (∫ x in a..b, A + B * x + C * x ^ 2) =
      A * (b - a) + B * ((b ^ 2 - a ^ 2) / 2) +
        C * ((b ^ 3 - a ^ 3) / 3) := by
  have h₁ : IntervalIntegrable (fun x : ℝ => A + B * x) volume a b :=
    (continuous_const.add (continuous_const.mul continuous_id)).intervalIntegrable a b
  have h₂ : IntervalIntegrable (fun x : ℝ => C * x ^ 2) volume a b :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable a b
  have hB : IntervalIntegrable (fun x : ℝ => B * x) volume a b :=
    (continuous_const.mul continuous_id).intervalIntegrable a b
  rw [intervalIntegral.integral_add
    (f := fun x : ℝ => A + B * x) (g := fun x : ℝ => C * x ^ 2) h₁ h₂]
  rw [intervalIntegral.integral_add
    (f := fun _ : ℝ => A) (g := fun x : ℝ => B * x) intervalIntegrable_const hB]
  rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_id, integral_pow]
  norm_num
  ring

theorem integral_centeredHat_sq_left {h : ℝ} (hh : 0 < h) :
    (∫ x in (-h)..0, centeredHat h x ^ 2) = h / 3 := by
  calc
    (∫ x in (-h)..0, centeredHat h x ^ 2) =
        ∫ x in (-h)..0, (1 + (2 / h) * x + (1 / h ^ 2) * x ^ 2) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by linarith : -h ≤ 0)] at hx
      dsimp only
      rw [centeredHat_eq_left hh hx.1 hx.2]
      field_simp [ne_of_gt hh]
      ring
    _ = h / 3 := by
      rw [intervalIntegral_quadratic]
      field_simp [ne_of_gt hh]
      ring

theorem integral_centeredHat_sq_right {h : ℝ} (hh : 0 < h) :
    (∫ x in 0..h, centeredHat h x ^ 2) = h / 3 := by
  calc
    (∫ x in 0..h, centeredHat h x ^ 2) =
        ∫ x in 0..h, (1 + (-2 / h) * x + (1 / h ^ 2) * x ^ 2) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hh.le] at hx
      dsimp only
      rw [centeredHat_eq_right hh hx.1 hx.2]
      field_simp [ne_of_gt hh]
      ring
    _ = h / 3 := by
      rw [intervalIntegral_quadratic]
      field_simp [ne_of_gt hh]
      ring

theorem intervalIntegral_centeredHat_sq {h : ℝ} (hh : 0 < h) :
    (∫ x in (-h)..h, centeredHat h x ^ 2) = 2 * h / 3 := by
  have hiL : IntervalIntegrable (fun x : ℝ => centeredHat h x ^ 2) volume (-h) 0 :=
    ((continuous_centeredHat h).pow 2).intervalIntegrable (-h) 0
  have hiR : IntervalIntegrable (fun x : ℝ => centeredHat h x ^ 2) volume 0 h :=
    ((continuous_centeredHat h).pow 2).intervalIntegrable 0 h
  rw [← intervalIntegral.integral_add_adjacent_intervals hiL hiR,
    integral_centeredHat_sq_left hh, integral_centeredHat_sq_right hh]
  ring

/-- The diagonal autocorrelation entry is the actual squared-mass integral. -/
theorem integral_centeredHat_sq {h : ℝ} (hh : 0 < h) :
    (∫ x, centeredHat h x ^ 2) = 2 * h / 3 := by
  have hsupp : Function.support (fun x => centeredHat h x ^ 2) =
      Set.Ioo (-h) h := by
    rw [← support_centeredHat hh]
    ext x
    simp only [Function.mem_support, ne_eq, sq_eq_zero_iff]
  calc
    (∫ x, centeredHat h x ^ 2) = ∫ x in Set.Ioo (-h) h, centeredHat h x ^ 2 := by
      have he :=
        (setIntegral_support (F := fun x => centeredHat h x ^ 2) (ν := volume)).symm
      change (∫ x, centeredHat h x ^ 2) =
        ∫ x in Function.support (fun x => centeredHat h x ^ 2), centeredHat h x ^ 2 at he
      rw [hsupp] at he
      exact he
    _ = ∫ x in (-h)..h, centeredHat h x ^ 2 := by
      rw [intervalIntegral.integral_of_le (by linarith : -h ≤ h),
        integral_Ioc_eq_integral_Ioo]
    _ = 2 * h / 3 := intervalIntegral_centeredHat_sq hh

end RiemannResearch.Analysis

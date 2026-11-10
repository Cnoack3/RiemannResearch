/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ShiftedSechTransform
import RiemannResearch.Analysis.ActualZeroOrdinate
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-! # Positive sech smoothing of the actual zeta-zero multiset

The density sums kernel(rho.re-1/2, v-rho.im) with every analytic
multiplicity in the complete cutoff 0 < rho.im <= T. It is nonnegative
and integrable, has exact mass Ncount(0,T), and its positive-frequency
Fourier transform is landauSum(T,u)/cosh(u/2).

All strip conditions are discharged by the actual critical-strip theorem.
The formula retains fixed-width sech attenuation. It is not an estimate
for the unsmoothed ordinate pairs, and removing attenuation requires
matching analytic error control.

Source: the actual-zero positive smoothing construction in the
user-provided Montgomery continuation handoff, route A. The kernel
transform is proved in ShiftedSechTransform.lean; the conversion to the
Landau sum uses the previously proved multiplicity-preserving reflection.
-/

noncomputable section
open MeasureTheory Zeta23
open scoped BigOperators

namespace RiemannResearch.Analysis.ShiftedSech

theorem integrable_kernel_translate {δ : ℝ} (hδ : |δ| < 1 / 2) (t : ℝ) :
    Integrable (fun v : ℝ => kernel δ (v-t)) := by
  simpa only [sub_eq_add_neg] using (integrable_kernel hδ).comp_add_right (-t)

theorem integrable_kernel_translate_phase {δ : ℝ} (hδ : |δ| < 1 / 2) (t u : ℝ) :
    Integrable (fun v : ℝ => (kernel δ (v-t) : ℂ) *
      Complex.exp ((u*v : ℝ)*Complex.I)) := by
  have hi : Integrable (fun v : ℝ => (kernel δ (v-t) : ℂ)) :=
    (integrable_kernel_translate hδ t).ofReal
  have hb := hi.bdd_mul (c := 1)
    (show AEStronglyMeasurable (fun v : ℝ => Complex.exp ((u*v : ℝ)*Complex.I)) by
      exact (show Continuous (fun v : ℝ => Complex.exp ((u*v : ℝ)*Complex.I)) by fun_prop).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun v => by simp [Complex.norm_exp]))
  simpa only [mul_comm] using hb

theorem integral_kernel_translate_phase {δ : ℝ} (hδ : |δ| < 1 / 2) (t u : ℝ) :
    (∫ v : ℝ, (kernel δ (v-t) : ℂ) * Complex.exp ((u*v : ℝ)*Complex.I)) =
      Complex.exp ((u*t : ℝ)*Complex.I) * (spectrum δ u : ℂ) := by
  calc
    _ = ∫ v : ℝ, (kernel δ v : ℂ) * Complex.exp ((u*(v+t) : ℝ)*Complex.I) := by
      have h := integral_sub_right_eq_self (μ := volume)
        (fun v : ℝ => (kernel δ v : ℂ) * Complex.exp ((u*(v+t) : ℝ)*Complex.I)) t
      simpa only [sub_add_cancel] using h
    _ = Complex.exp ((u*t : ℝ)*Complex.I) *
        (∫ v : ℝ, (kernel δ v : ℂ) * Complex.exp ((u*v : ℝ)*Complex.I)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with v
      have he : ((u*(v+t):ℝ):ℂ)*Complex.I =
          ((u*v:ℝ):ℂ)*Complex.I + ((u*t:ℝ):ℂ)*Complex.I := by push_cast; ring
      rw [he, Complex.exp_add]
      ring
    _ = _ := by rw [integral_kernel_phase hδ]

end RiemannResearch.Analysis.ShiftedSech

namespace RiemannResearch.Analysis.ActualZeroSechSmoothing
open ActualZeroOrdinate ShiftedSech ZeroOrdinate

def density (T v : ℝ) : ℝ :=
  realSum T (fun ρ => kernel (ρ.re - 1 / 2) (v - ρ.im))

theorem density_nonneg (T v : ℝ) : 0 ≤ density T v :=
  realSum_nonneg T _ (fun ρ hρ => (kernel_pos (displacement_lt_half hρ) _).le)

theorem integrable_density (T : ℝ) : Integrable (density T) := by
  unfold density realSum
  exact integrable_finsetSum _ (fun ρ hρ =>
    (integrable_kernel_translate (displacement_lt_half hρ) ρ.im).const_mul _)

theorem integral_density (T : ℝ) :
    (∫ v : ℝ, density T v) = (Ncount 0 T : ℝ) := by
  unfold density realSum
  rw [integral_finsetSum _ (fun ρ hρ =>
    (integrable_kernel_translate (displacement_lt_half hρ) ρ.im).const_mul _)]
  calc
    _ = ∑ ρ ∈ cutoff T, (zeroMult ρ : ℝ) * 1 := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      rw [integral_const_mul, integral_sub_right_eq_self,
        integral_kernel (displacement_lt_half hρ)]
    _ = _ := by simp [count_eq_sum]

theorem integrable_density_phase (T u : ℝ) :
    Integrable (fun v : ℝ => (density T v : ℂ) *
      Complex.exp ((u*v : ℝ)*Complex.I)) := by
  have hi : Integrable (fun v : ℝ => (density T v : ℂ)) := (integrable_density T).ofReal
  have hb := hi.bdd_mul (c := 1)
    (show AEStronglyMeasurable (fun v : ℝ => Complex.exp ((u*v : ℝ)*Complex.I)) by
      exact (show Continuous (fun v : ℝ => Complex.exp ((u*v : ℝ)*Complex.I)) by fun_prop).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun v => by simp [Complex.norm_exp]))
  simpa only [mul_comm] using hb

theorem integral_density_phase (T u : ℝ) :
    (∫ v : ℝ, (density T v : ℂ) * Complex.exp ((u*v : ℝ)*Complex.I)) =
      ((1 / Real.cosh (u/2) : ℝ) : ℂ) * landauSum T u := by
  have he (v : ℝ) :
      (density T v : ℂ) * Complex.exp ((u*v : ℝ)*Complex.I) =
        ∑ ρ ∈ cutoff T, (zeroMult ρ : ℂ) *
          ((kernel (ρ.re - 1 / 2) (v - ρ.im) : ℂ) *
            Complex.exp ((u*v : ℝ)*Complex.I)) := by
    simp [density, realSum, Finset.sum_mul, mul_assoc]
  simp_rw [he]
  rw [integral_finsetSum _ (fun ρ hρ =>
    (integrable_kernel_translate_phase (displacement_lt_half hρ) ρ.im u).const_mul _)]
  rw [landauSum_eq_cosh]
  unfold sum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [integral_const_mul, integral_kernel_translate_phase (displacement_lt_half hρ)]
  unfold ShiftedSech.spectrum phase
  rw [show (ρ.re - 1 / 2)*u = u*(ρ.re - 1 / 2) by ring]
  push_cast
  ring

end RiemannResearch.Analysis.ActualZeroSechSmoothing

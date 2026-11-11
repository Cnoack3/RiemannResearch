/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteOscillatoryKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Saturated finite-height resonance factors

Source: FRZ_Strengthening_2026-11-10, Section 5, equations (18)--(23).
The exact phase window retains both endpoints and its resonant value. A
moving gap `c / T` has exactly the same nonzero window factor at every
positive height; pointwise nonresonance cannot justify a uniform limit.
These elementary identities do not assume a zeta-density theorem or the
unformalized sharp nearest-prime-power Landau estimate.
-/

noncomputable section
open Complex MeasureTheory

namespace RiemannResearch.Analysis.ZeroOrdinate

/-- The normalized unit-interval phase window from the finite Landau main term. -/
def resonanceWindow (z : ℝ) : ℂ := finitePhaseKernel 0 1 z

@[simp] theorem resonanceWindow_zero : resonanceWindow 0 = 1 := by
  simp [resonanceWindow, finitePhaseKernel_zero]

theorem resonanceWindow_integral (z : ℝ) :
    resonanceWindow z = ∫ t in (0 : ℝ)..1,
      Complex.exp (((z : ℂ) * Complex.I) * (t : ℂ)) :=
  (integral_phase_eq_finitePhaseKernel 0 1 z).symm

theorem resonanceWindow_nonzero (z : ℝ) (hz : z ≠ 0) :
    resonanceWindow z = (Complex.exp ((z : ℂ) * Complex.I) - 1) /
      ((z : ℂ) * Complex.I) := by
  simp [resonanceWindow, finitePhaseKernel, hz]

theorem norm_resonanceWindow_le_one (z : ℝ) : ‖resonanceWindow z‖ ≤ 1 := by
  rw [resonanceWindow_integral]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := (1 : ℝ))
    (f := fun t : ℝ => Complex.exp (((z : ℂ) * Complex.I) * (t : ℂ)))
    (fun t _ => by rw [Complex.norm_exp]; simp)
  simpa using h

/-- The trivial and nonresonant estimates are simultaneously available. -/
theorem norm_resonanceWindow_le_min (z : ℝ) (hz : z ≠ 0) :
    ‖resonanceWindow z‖ ≤ min 1 (2 / |z|) :=
  le_min (norm_resonanceWindow_le_one z) (norm_finitePhaseKernel_le hz 0 1)

/-- Exact scaling, including the resonant case; no endpoint is discarded. -/
theorem finitePhaseKernel_zero_height (T u : ℝ) :
    finitePhaseKernel 0 T u = (T : ℂ) * resonanceWindow (T * u) := by
  by_cases hT : T = 0
  · simp [hT, finitePhaseKernel]
  by_cases hu : u = 0
  · simp [hu, finitePhaseKernel_zero]
  rw [finitePhaseKernel, if_neg hu, resonanceWindow_nonzero _ (mul_ne_zero hT hu)]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, Complex.ofReal_mul]
  have he : ((u : ℂ) * Complex.I) * (T : ℂ) =
      ((T : ℂ) * (u : ℂ)) * Complex.I := by ring
  rw [he]
  field_simp [hT, hu]

theorem normalized_finitePhaseKernel (T u : ℝ) (hT : T ≠ 0) :
    finitePhaseKernel 0 T u / (T : ℂ) = resonanceWindow (T * u) := by
  rw [finitePhaseKernel_zero_height]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast hT)

/-- Every inverse-height moving gap retains its entire finite resonance. -/
theorem normalized_kernel_inverse_height_gap (T c : ℝ) (hT : T ≠ 0) :
    finitePhaseKernel 0 T (c / T) / (T : ℂ) = resonanceWindow c := by
  rw [normalized_finitePhaseKernel T _ hT]
  congr 1
  field_simp

/-- A nonzero fixed profile prevents vanishing along any such moving gaps. -/
theorem inverse_height_gap_norm_exact (T c : ℝ) (hT : T ≠ 0) :
    ‖finitePhaseKernel 0 T (c / T) / (T : ℂ)‖ = ‖resonanceWindow c‖ := by
  rw [normalized_kernel_inverse_height_gap T c hT]

end RiemannResearch.Analysis.ZeroOrdinate

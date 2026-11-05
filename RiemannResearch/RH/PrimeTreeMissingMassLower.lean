/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.PrimeTreeProbabilityMixture

/-! # A matching lower bound on conductor total variation
The interval below the first nonzero grid cell has zero mass at finite
depth. Its positive limiting mass exhibits the sharp order of (13). -/
noncomputable section
open Set MeasureTheory
namespace RiemannResearch.RH.PrimeTreeMellinLaws

theorem logWeight_left_integral (D : ℕ) (hD : 1 ≤ D) (σ : ℝ) (hσ : σ < 1) :
    (∫ t in Iio (-Real.log D), logWeight σ t) =
      missingMass D σ / (1 - σ) := by
  have hd : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hp := zero_lt_one.trans_le hd
  have he (t : ℝ) (ht : t < -Real.log D) : logWeight σ t = Real.exp ((1 - σ) * t) := by
    have ht0 : t < 0 := by linarith [Real.log_nonneg hd]
    rw [logWeight, Int.fract_eq_self.mpr ⟨(Real.exp_pos t).le, Real.exp_lt_one_iff.mpr ht0⟩,
      ← Real.exp_add]
    congr 1
    ring
  rw [setIntegral_congr_fun measurableSet_Iio (fun t ht => he t ht),
    ← integral_Iic_eq_integral_Iio, integral_exp_mul_Iic (sub_pos.mpr hσ),
    missingMass, Real.rpow_def_of_pos hp]
  congr 2
  ring

theorem logDepthWeight_left_integral (D : ℕ) (hD : 0 < D) (σ : ℝ) :
    (∫ t in Iio (-Real.log D), logDepthWeight D σ t) = 0 := by
  have hd : 0 < (D : ℝ) := by exact_mod_cast hD
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro t ht
  have he : (D : ℝ) * Real.exp t < 1 := by
    calc
      _ = Real.exp (Real.log D + t) := by rw [Real.exp_add, Real.exp_log hd]
      _ < 1 := Real.exp_lt_one_iff.mpr (by change t < -Real.log D at ht; linarith)
  simp [logDepthWeight, staircase, Nat.floor_eq_zero.mpr he]

end RiemannResearch.RH.PrimeTreeMellinLaws

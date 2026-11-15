/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
/-!
# Mixed moments for the Ingham quadratic detector

The centered product estimate is the Holder step of Chourasiya--Simonic,
arXiv:2507.15184v2, equation (41). Both moments are retained on the same
interval, before any enlargement of the mollifier interval.
https://arxiv.org/html/2507.15184v2

These inequalities supply no asymptotic fourth or second moment estimate.
-/

open MeasureTheory Set
noncomputable section
namespace Complex

private theorem continuous_memLp_interval {f : ℝ → ℝ} (hf : Continuous f)
    (H T p : ℝ) (hp : 0 < p) :
    MemLp f (ENNReal.ofReal p) (volume.restrict (Ioc H T)) := by
  apply (integrable_norm_rpow_iff hf.aestronglyMeasurable
    (by simpa using hp) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal hp.le]
  have hc := hf.norm.rpow_const (by intro x; exact Or.inr hp.le)
  exact hc.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem integral_mul_four_thirds_le {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    {H T : ℝ} (hHT : H ≤ T) :
    (∫ t in H..T, ‖f t * g t‖ ^ (4/3 : ℝ)) ≤
      (∫ t in H..T, ‖f t‖ ^ 4) ^ (1/3 : ℝ) *
      (∫ t in H..T, ‖g t‖ ^ 2) ^ (2/3 : ℝ) := by
  have hcF : Continuous (fun t => ‖f t‖ ^ (4/3 : ℝ)) :=
    hf.norm.rpow_const (by intro t; exact Or.inr (by norm_num))
  have hcG : Continuous (fun t => ‖g t‖ ^ (4/3 : ℝ)) :=
    hg.norm.rpow_const (by intro t; exact Or.inr (by norm_num))
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (Ioc H T))
    (show (3 : ℝ).HolderConjugate (3/2) by rw [Real.holderConjugate_iff]; norm_num)
    (f := fun t => ‖f t‖ ^ (4/3 : ℝ))
    (g := fun t => ‖g t‖ ^ (4/3 : ℝ))
    (Filter.Eventually.of_forall (fun t => Real.rpow_nonneg (norm_nonneg _) _))
    (Filter.Eventually.of_forall (fun t => Real.rpow_nonneg (norm_nonneg _) _))
    (continuous_memLp_interval hcF H T 3 (by norm_num))
    (continuous_memLp_interval hcG H T (3/2) (by norm_num))
  simp_rw [← Real.rpow_mul (norm_nonneg _)] at hh
  norm_num at hh
  simp_rw [intervalIntegral.integral_of_le hHT, norm_mul,
    Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  exact hh

theorem norm_mul_sub_one_four_thirds_le (z w : ℂ) :
    ‖z*w-1‖ ^ (4/3 : ℝ) ≤
      (2 : ℝ) ^ (1/3 : ℝ) * (‖z*w‖ ^ (4/3 : ℝ)+1) := by
  have hn : ‖z*w-1‖ ≤ ‖z*w‖+1 := by simpa using norm_sub_le (z*w) (1 : ℂ)
  have hh := NNReal.rpow_add_le_mul_rpow_add_rpow ‖z*w‖₊ 1
    (show (1 : ℝ) ≤ 4/3 by norm_num)
  have hh' : (‖z*w‖+1) ^ (4/3 : ℝ) ≤
      (2 : ℝ) ^ (1/3 : ℝ) * (‖z*w‖ ^ (4/3 : ℝ)+1) := by
    exact_mod_cast (by norm_num at hh ⊢; exact hh)
  exact (Real.rpow_le_rpow (norm_nonneg _) hn (by norm_num)).trans hh'


/-- The centered product moment, retaining the same interval for both inputs. -/
theorem integral_mul_sub_one_four_thirds_le {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) {H T : ℝ} (hHT : H ≤ T) :
    (∫ t in H..T, ‖f t*g t-1‖ ^ (4/3 : ℝ)) ≤
      (2 : ℝ) ^ (1/3 : ℝ) *
        ((∫ t in H..T, ‖f t‖ ^ 4) ^ (1/3 : ℝ) *
         (∫ t in H..T, ‖g t‖ ^ 2) ^ (2/3 : ℝ) + (T-H)) := by
  have hc : Continuous (fun t => ‖f t*g t-1‖ ^ (4/3 : ℝ)) :=
    ((hf.mul hg).sub continuous_const).norm.rpow_const
      (by intro t; exact Or.inr (by norm_num))
  have hp : Continuous (fun t => ‖f t*g t‖ ^ (4/3 : ℝ)) :=
    (hf.mul hg).norm.rpow_const (by intro t; exact Or.inr (by norm_num))
  calc
    _ ≤ ∫ t in H..T, (2 : ℝ) ^ (1/3 : ℝ) * (‖f t*g t‖ ^ (4/3 : ℝ)+1) :=
      intervalIntegral.integral_mono_on hHT hc.continuousOn.intervalIntegrable
        ((continuous_const.mul (hp.add continuous_const)).continuousOn.intervalIntegrable)
        (fun t _ => norm_mul_sub_one_four_thirds_le (f t) (g t))
    _ = (2 : ℝ) ^ (1/3 : ℝ) *
        ((∫ t in H..T, ‖f t*g t‖ ^ (4/3 : ℝ)) + (T-H)) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
        hp.continuousOn.intervalIntegrable intervalIntegrable_const]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by have hh := integral_mul_four_thirds_le hf hg hHT; linarith) (by positivity)
end Complex

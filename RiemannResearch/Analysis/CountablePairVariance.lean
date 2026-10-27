/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.CountableJumpEnergy
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Complete weighted pair differences equal variance

The exact signed first/second moment expansion is justified by `HasSum`
before conversion to nonnegative ENNReal energy. The concrete consumer is
the actual inverse-square law and its countable prime-resampling Poincare
inequality. Source: direct variance expansion from the user research agenda.
-/

noncomputable section
open scoped BigOperators ENNReal
namespace RiemannResearch.Analysis.CountablePairVariance
open CountableJumpEnergy

variable {α : Type*}

theorem weighted_pair_energy_eq
    (w f : α → ℝ) (μ ν : ℝ) (hw0 : ∀ x, 0 ≤ w x)
    (hw : HasSum w 1) (hf1 : HasSum (fun x => w x * f x) μ)
    (hf2 : HasSum (fun x => w x * (f x) ^ 2) ν) :
    countableJumpEnergy (fun x y => ENNReal.ofReal (w x) * ENNReal.ofReal (w y)) f =
      ENNReal.ofReal (ν - μ ^ 2) := by
  have hrow (x : α) : HasSum (fun y => w y * (f x - f y) ^ 2 / 2)
      (((f x) ^ 2 - 2 * f x * μ + ν) / 2) := by
    have h : HasSum
        (fun y => (((f x) ^ 2 * w y - (2 * f x) * (w y * f y)) +
          w y * (f y) ^ 2) / 2)
        (((f x) ^ 2 * 1 - (2 * f x) * μ + ν) / 2) :=
      (((hw.mul_left ((f x) ^ 2)).sub (hf1.mul_left (2 * f x))).add hf2).div_const 2
    have h' : HasSum (fun y => w y * (f x - f y) ^ 2 / 2)
        (((f x) ^ 2 * 1 - (2 * f x) * μ + ν) / 2) :=
      h.congr_fun (fun y => by ring)
    simpa only [mul_one] using h'
  have hrows : HasSum
      (fun x => w x * (((f x) ^ 2 - 2 * f x * μ + ν) / 2))
      (ν - μ ^ 2) := by
    have h : HasSum
        (fun x => (w x * (f x) ^ 2 - (2 * μ) * (w x * f x) + ν * w x) / 2)
        ((ν - (2 * μ) * μ + ν * 1) / 2) :=
      ((hf2.sub (hf1.mul_left (2 * μ))).add (hw.mul_left ν)).div_const 2
    have h' : HasSum (fun x => w x * (((f x) ^ 2 - 2 * f x * μ + ν) / 2))
        ((ν - (2 * μ) * μ + ν * 1) / 2) := h.congr_fun (fun x => by ring)
    rwa [show (ν - (2 * μ) * μ + ν * 1) / 2 = ν - μ ^ 2 by ring] at h'
  have hrow0 (x : α) : 0 ≤ ((f x) ^ 2 - 2 * f x * μ + ν) / 2 := by
    rw [← (hrow x).tsum_eq]
    exact tsum_nonneg (fun y => div_nonneg (mul_nonneg (hw0 y) (sq_nonneg _)) (by norm_num))
  unfold countableJumpEnergy
  calc
    _ = ∑' x, ∑' y, ENNReal.ofReal (w x * (w y * (f x - f y) ^ 2 / 2)) := by
      apply tsum_congr
      intro x
      apply tsum_congr
      intro y
      rw [show w x * (w y * (f x - f y) ^ 2 / 2) =
          (w x * w y) * ((f x - f y) ^ 2 / 2) by ring,
        ENNReal.ofReal_mul (mul_nonneg (hw0 x) (hw0 y)),
        ENNReal.ofReal_mul (hw0 x)]
    _ = ∑' x, ENNReal.ofReal
        (w x * (((f x) ^ 2 - 2 * f x * μ + ν) / 2)) := by
      apply tsum_congr
      intro x
      rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun y => mul_nonneg (hw0 x)
          (div_nonneg (mul_nonneg (hw0 y) (sq_nonneg _)) (by norm_num)))
        ((hrow x).mul_left (w x)).summable,
        ((hrow x).mul_left (w x)).tsum_eq]
    _ = _ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun x => mul_nonneg (hw0 x) (hrow0 x))
        hrows.summable, hrows.tsum_eq]

end RiemannResearch.Analysis.CountablePairVariance

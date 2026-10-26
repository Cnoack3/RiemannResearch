/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.StretchedExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Stretched-exponential tail weights

These scalar profiles and their elementary limit have no squarefree,
Hilbert-space, or Riemann-hypothesis assumption. The exponent 1/11 matches
an existing arithmetic provider; its positivity is all that the limit uses.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.Analysis.StretchedTailWeights
open RiemannResearch.Analysis

def arithmeticDecay (a : ℝ) (N : ℕ) : ℝ :=
  Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (N : ℝ)))

def arithmeticWeight (a : ℝ) (N : ℕ) : ℝ := (N : ℝ) * arithmeticDecay a N

theorem arithmeticDecay_pos (a : ℝ) (N : ℕ) : 0 < arithmeticDecay a N :=
  Real.exp_pos _

theorem arithmeticWeight_nonneg (a : ℝ) (N : ℕ) : 0 ≤ arithmeticWeight a N :=
  mul_nonneg (Nat.cast_nonneg N) (arithmeticDecay_pos a N).le

theorem arithmeticDecay_tendsto_zero (a : ℝ) (ha : 0 < a) :
    Tendsto (arithmeticDecay a) atTop (𝓝 0) := by
  have hL : Tendsto (fun N : ℕ => 6 + Real.log (N : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop 6
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hφ := (tendsto_logProductPower_atTop (1 / 11) (by norm_num)).comp hL
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hφ.const_mul_atTop ha)
  unfold arithmeticDecay
  simpa only [Function.comp_def, neg_mul] using h

theorem arithmeticWeight_eq_half (a : ℝ) (N : ℕ) :
    arithmeticWeight a N =
      arithmeticDecay (a / 2) N * arithmeticWeight (a / 2) N := by
  unfold arithmeticWeight arithmeticDecay
  rw [show -a * logProductPower (1 / 11) (6 + Real.log (N : ℝ)) =
      -(a / 2) * logProductPower (1 / 11) (6 + Real.log (N : ℝ)) +
        -(a / 2) * logProductPower (1 / 11) (6 + Real.log (N : ℝ)) by ring,
    Real.exp_add]
  ring

end RiemannResearch.Analysis.StretchedTailWeights

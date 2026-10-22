/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoMellinHardyNorm
import RiemannResearch.Analysis.WeightedMellinEnergy
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Mellin linearity for bounded Pareto vectors on the positive half-plane

The bounded finite combinations used by Balazard--de Roton,
https://arxiv.org/abs/0812.1689, Section 2, have ordinary Mellin integrals
even on the critical line. This module supplies that elementary analytic
ingredient using the existing weighted-energy theorems; it assumes no RH.
-/
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RiemannResearch.RH.Pareto

theorem paretoMellin_step_integrable_of_bounded (f : ThresholdHilbert)
    (C : ℝ) (hC : ∀ n, |hilbertSequence f n| ≤ C)
    (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ =>
      (hilbertSequence f ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) := by
  exact WeightedMellin.transform_integrable
    (complexPhysicalStep_finiteEnergy_of_bounded f C hC hs)
    (by linarith : s.re / 2 < s.re)

theorem paretoMellin_add_of_bounded (f g : ThresholdHilbert)
    (C D : ℝ) (hC : ∀ n, |hilbertSequence f n| ≤ C)
    (hD : ∀ n, |hilbertSequence g n| ≤ D)
    (s : ℂ) (hs : 0 < s.re) :
    paretoMellin (f + g) s = paretoMellin f s + paretoMellin g s := by
  simp only [paretoMellin_eq_step_integral]
  have he (x : ℝ) :
      (hilbertSequence (f + g) ⌊x⌋₊ : ℂ) =
        (hilbertSequence f ⌊x⌋₊ : ℂ) + (hilbertSequence g ⌊x⌋₊ : ℂ) := by
    change ((hilbertSequenceLinear (f + g) ⌊x⌋₊ : ℝ) : ℂ) = _
    rw [map_add]
    simp only [Pi.add_apply, Complex.ofReal_add]
    rfl
  simp_rw [he, add_mul]
  exact integral_add (paretoMellin_step_integrable_of_bounded f C hC s hs)
    (paretoMellin_step_integrable_of_bounded g D hD s hs)

theorem paretoMellin_finset_sum_of_bounded {ι : Type*} (S : Finset ι)
    (f : ι → ThresholdHilbert) (C : ι → ℝ)
    (hC : ∀ i ∈ S, ∀ n, |hilbertSequence (f i) n| ≤ C i)
    (s : ℂ) (hs : 0 < s.re) :
    paretoMellin (∑ i ∈ S, f i) s = ∑ i ∈ S, paretoMellin (f i) s := by
  simp only [paretoMellin_eq_step_integral]
  have he (x : ℝ) :
      (hilbertSequence (∑ i ∈ S, f i) ⌊x⌋₊ : ℂ) =
        ∑ i ∈ S, (hilbertSequence (f i) ⌊x⌋₊ : ℂ) := by
    change ((hilbertSequenceLinear (∑ i ∈ S, f i) ⌊x⌋₊ : ℝ) : ℂ) = _
    simp only [map_sum, Finset.sum_apply, Complex.ofReal_sum]
    rfl
  simp_rw [he, Finset.sum_mul]
  exact integral_finsetSum S
    (fun i hi => paretoMellin_step_integrable_of_bounded (f i) (C i) (hC i hi) s hs)

theorem paretoMellin_one_of_pos (s : ℂ) (hs : 0 < s.re) :
    paretoMellin hilbertOne s = 1 / s := by
  rw [paretoMellin_eq_step_integral]
  have he : (∫ x in Ioi (1 : ℝ), (hilbertSequence hilbertOne ⌊x⌋₊ : ℂ) *
      (x : ℂ)^(-s - 1)) = ∫ x in Ioi (1 : ℝ), (x : ℂ)^(-s - 1) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    have hx' : (1 : ℝ) < x := hx
    have hf : 1 ≤ ⌊x⌋₊ :=
      (Nat.le_floor_iff (by linarith : (0 : ℝ) ≤ x)).2 (by simpa using hx'.le)
    rw [hilbertOne_sequence]
    simp [zeroAnchor, show ⌊x⌋₊ ≠ 0 by omega]
  have hexp : (-s - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  rw [he, integral_Ioi_cpow_of_lt hexp (by norm_num : (0 : ℝ) < 1)]
  simp

end RiemannResearch.RH.Pareto

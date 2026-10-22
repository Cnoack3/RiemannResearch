/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroBadPhaseTail
import RiemannResearch.Analysis.ActualZeroTailDensityTransfer
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual bad operator correction from scalar strict-tail estimates

The finite operator provider and the scalar layer cake use exactly the same
strict bad mask. Their composition retains the original `Ncount 0 T` and the
rank-one centering factor `d/(2N)`. Only the actual scalar zero-density bound
remains an explicit analytic premise in the density consumer below.
-/

noncomputable section
open Complex Zeta23 Set
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate

theorem badRealWeight_mul_eq_strict_indicator (δ : ℝ) (ρ : ℂ) (f : ℝ → ℝ) :
    badRealWeight δ ρ * f |ρ.re - 1 / 2| =
      if δ < |ρ.re - 1 / 2| then f |ρ.re - 1 / 2| else 0 := by
  by_cases h : |ρ.re - 1 / 2| ≤ δ
  · simp only [badRealWeight, if_pos h, zero_mul, if_neg (not_lt.mpr h)]
  · simp only [badRealWeight, if_neg h, one_mul, if_pos (lt_of_not_ge h)]

theorem badRealWeightSum_eq_badWeightedSum (T δ : ℝ) (f : ℝ → ℝ) :
    realSum T (fun ρ => badRealWeight δ ρ * f |ρ.re - 1 / 2|) =
      badWeightedSum T δ f := by
  rw [badWeightedSum_eq_realSum]
  congr 1
  funext ρ
  exact badRealWeight_mul_eq_strict_indicator δ ρ f

/-- The operator and scalar tail providers agree on the complete bad mask. -/
theorem badCorrection_norm_le_badWeightedSum
    (T : ℝ) (d : ℕ) (hd : 1 ≤ d) (δ : ℝ) :
    ‖badCorrection T d δ‖ ≤ (d : ℝ) / (2 * (Ncount 0 T : ℝ)) *
      badWeightedSum T δ (fun t => Real.cosh (Real.log (d : ℝ) * t) - 1) := by
  have h := badCorrection_norm_le_cosh T d hd δ
  have hs : realSum T (fun ρ => badRealWeight δ ρ *
      (Real.cosh (|ρ.re - 1 / 2| * Real.log (d : ℝ)) - 1)) =
      badWeightedSum T δ (fun t => Real.cosh (Real.log (d : ℝ) * t) - 1) := by
    simpa only [mul_comm] using
      badRealWeightSum_eq_badWeightedSum T δ
        (fun t => Real.cosh (Real.log (d : ℝ) * t) - 1)
  rw [hs] at h
  exact h

/-- An unconditional finite-strip bound; it has no decay with height. -/
theorem badCorrection_norm_le_strip
    (T : ℝ) (d : ℕ) (hd : 1 ≤ d) (δ : ℝ) :
    ‖badCorrection T d δ‖ ≤
      ((d : ℝ) / 2) * (Real.cosh (Real.log (d : ℝ) / 2) - 1) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hdR
  calc
    _ ≤ (d : ℝ) / (2 * (Ncount 0 T : ℝ)) *
        badWeightedSum T δ (fun t => Real.cosh (Real.log (d : ℝ) * t) - 1) :=
      badCorrection_norm_le_badWeightedSum T d hd δ
    _ = ((d : ℝ) / 2) *
        (badWeightedSum T δ (fun t => Real.cosh (Real.log (d : ℝ) * t) - 1) /
          (Ncount 0 T : ℝ)) := by
      simp only [div_eq_mul_inv, mul_inv]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (normalized_badCoshSum_le T δ (Real.log (d : ℝ)) hL) (by positivity)

/-- The complete reflected bad-operator bound from an actual scalar strict
tail estimate. Both finite endpoint terms and the original normalizer remain. -/
theorem badCorrection_norm_le_of_expTail
    (T : ℝ) (d : ℕ) (hd : 1 ≤ d) (δ K q : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (hql : Real.log (d : ℝ) < q)
    (htail : ∀ t ∈ Icc δ (1 / 2), strictTail T t ≤ K * Real.exp (-q * t)) :
    ‖badCorrection T d δ‖ ≤
      (d : ℝ) / (2 * (Ncount 0 T : ℝ)) *
        (K * ((Real.cosh (Real.log (d : ℝ) * δ) - 1) * Real.exp (-q * δ) +
          (Real.log (d : ℝ) / 2) *
            ((Real.exp (-(q - Real.log (d : ℝ)) * δ) -
                Real.exp (-(q - Real.log (d : ℝ)) / 2)) / (q - Real.log (d : ℝ)) -
              (Real.exp (-(q + Real.log (d : ℝ)) * δ) -
                Real.exp (-(q + Real.log (d : ℝ)) / 2)) / (q + Real.log (d : ℝ))))) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hdR
  apply (badCorrection_norm_le_badWeightedSum T d hd δ).trans
  exact mul_le_mul_of_nonneg_left
    (badCoshSum_le_of_expTail_closed T δ (Real.log (d : ℝ)) K q
      hδ0 hδ hL hql htail) (by positivity)

end RiemannResearch.Analysis.ActualZeroPhaseMoments

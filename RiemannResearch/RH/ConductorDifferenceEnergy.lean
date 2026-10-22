import RiemannResearch.Analysis.ActualL2Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Exact energy of the spatial conductor difference

Source: direct application of the translation-energy identity developed
for the user's RH arithmetic-tail program. The square remainder retains all
covariance. For n at least two the operator is bounded below in actual L2,
so applying it to a tail cannot remove a positive energy-growth exponent.
Commutation with a separately defined canonical construction is not asserted.
-/

open MeasureTheory

namespace RiemannResearch.RH
open RiemannResearch.Analysis

noncomputable def conductorDifference (n : ℕ) (f : ℝ → ℂ) : ℝ → ℂ :=
  (1 / (n : ℝ)) • f -
    (1 / Real.sqrt n) • (fun y => f (y - Real.log n))

theorem conductorDifference_energy_exact (n : ℕ)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) (hc : Continuous f) :
    actualL2Norm (conductorDifference n f) ^ 2 =
      (1 / (n : ℝ) - 1 / Real.sqrt n) ^ 2 * actualL2Norm f ^ 2 +
        (1 / (n : ℝ)) * (1 / Real.sqrt n) *
          actualL2Norm (f - (fun y => f (y - Real.log n))) ^ 2 :=
  actualL2Norm_sub_smul_translate_sq_exact (1 / (n : ℝ))
    (1 / Real.sqrt n) (Real.log n) hf hc

theorem conductorDifference_norm_lower_bound (n : ℕ)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) (hc : Continuous f) :
    (1 / Real.sqrt n - 1 / (n : ℝ)) * actualL2Norm f ≤
      actualL2Norm (conductorDifference n f) := by
  have ha : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have hb : (0 : ℝ) ≤ 1 / Real.sqrt n := by positivity
  simpa only [conductorDifference, abs_of_nonneg ha, abs_of_nonneg hb] using
    actualL2Norm_sub_smul_translate_lower_bound (1 / (n : ℝ))
      (1 / Real.sqrt n) (Real.log n) hf hc

theorem conductorDifference_gap_pos (n : ℕ) (hn : 2 ≤ n) :
    0 < 1 / Real.sqrt n - 1 / (n : ℝ) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hn)
  have hn0 : (0 : ℝ) < n := lt_trans zero_lt_one hnR
  have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hs : Real.sqrt n < (n : ℝ) := by
    nlinarith [Real.sq_sqrt hn0.le, Real.sqrt_nonneg (n : ℝ)]
  apply sub_pos.mpr
  apply (div_lt_div_iff₀ hn0 hs0).mpr
  simpa only [one_mul] using hs

end RiemannResearch.RH

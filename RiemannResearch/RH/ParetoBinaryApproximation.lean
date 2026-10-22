import RiemannResearch.RH.ParetoResidueMoments
import RiemannResearch.RH.ParetoNoiseSignal
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Exact binary Pareto approximation
Source: user-provided argument, RH_Candid_Assessment_Pareto_Green_CRT_2026-09-07.md,
Section 10. The exact minimum uses the complete infinite Pareto moments.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

theorem paretoError_scale_residue_two (a : ℝ) :
    paretoError (fun k => a * residue 2 k) =
      1 - Real.log 2 + Real.log 2 * (a - 1)^2 := by
  have hr : ∀ k, |residue 2 k| ≤ (2 : ℝ) :=
    fun k => residue_abs_le 2 k (by norm_num)
  rw [paretoError_scale hr, paretoVariance_eq hr,
    paretoMean_residue_two, paretoInner_residue_two]
  ring

theorem paretoError_residue_two :
    paretoError (residue 2) = 1 - Real.log 2 := by
  simpa only [one_mul, sub_self, zero_pow (by decide : 2 ≠ 0),
    mul_zero, add_zero] using paretoError_scale_residue_two 1

theorem paretoError_residue_two_minimizes (a : ℝ) :
    paretoError (residue 2) ≤ paretoError (fun k => a * residue 2 k) := by
  rw [paretoError_residue_two, paretoError_scale_residue_two]
  exact le_add_of_nonneg_right
    (mul_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) (sq_nonneg _))

end
end RiemannResearch.RH.Pareto

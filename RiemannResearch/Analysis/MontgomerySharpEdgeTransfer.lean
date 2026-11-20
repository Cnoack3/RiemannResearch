/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.MontgomeryBGSTBTransitionComponents
import RiemannResearch.Analysis.MontgomeryHorizontalTransfer
import RiemannResearch.Analysis.MontgomeryLogMeanSquare
import RiemannResearch.Analysis.MontgomeryPrimeCrossIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Positive-height normalization and pole energy at the Montgomery edge

Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh, Lemmas 1 and 4,
https://doi.org/10.4064/aa230612-20-3 , supply the explicit-formula and
height-cutoff conventions. The integral isolates the rational pole term.
The transfer theorem takes the bound on the third residual as an argument. -/

noncomputable section
open MeasureTheory Set Filter
namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel
open MontgomeryPrimeCrossIntegral MontgomeryHorizontalTransfer

/-- Remove the form-factor normalization at the frequency `log x / log T`. -/
theorem edgePairNormalization {T : ℝ} (hT : 1 < T) (x : ℝ) :
    T * Real.log T * sharpFormFactor T (Real.log x / Real.log T) =
      2 * Real.pi * (actualComplexPairSum T (Real.log x)).re := by
  have hL := (Real.log_pos hT).ne'
  have ht := (zero_lt_one.trans hT).ne'
  rw [sharpFormFactor_eq_actualComplexPairSum, div_mul_cancel₀ _ hL]
  field_simp [ht, hL, Real.pi_ne_zero]

/-- The logarithmic signal contributes at most `4 * x` on the upper edge. -/
theorem edgeLogEnergyBound {T x : ℝ} (hT : 2 ≤ T) (hx : T ≤ x) :
    |logSignalEnergy T x| ≤ 4 * x := by
  have ht : 0 ≤ T := by linarith
  have hxp : 0 < x := by linarith
  have hn : 0 ≤ logSignalEnergy T x :=
    intervalIntegral.integral_nonneg ht fun t _ => sq_nonneg _
  rw [abs_of_nonneg hn]
  calc
    logSignalEnergy T x ≤ ∫ t in (0:ℝ)..T, (4:ℝ) := by
      apply intervalIntegral.integral_mono_on ht
      · exact (((MontgomeryLogMeanSquare.shifted_log_continuousOn ht).div_const x).pow 2).intervalIntegrable
      · exact continuous_const.intervalIntegrable _ _
      intro t hm
      have ha : 0 < t+2 := by linarith [hm.1]
      have hb : 0 ≤ Real.log (t+2) := Real.log_nonneg (by linarith [hm.1])
      have hd : Real.log (t+2) / x ≤ 2 := (div_le_iff₀ hxp).mpr (by
        linarith [Real.log_le_sub_one_of_pos ha,hm.2])
      nlinarith only [sq_nonneg (Real.log (t+2)/x), mul_nonneg
        (sub_nonneg.mpr hd) (show 0 ≤ 2 + Real.log (t+2)/x by positivity)]
    _ = 4 * T := by simp [mul_comm]
    _ ≤ 4 * x := by linarith

/-- Transfer a bound for the third residual to the full prime-to-sharp energy error. -/
theorem edgeTransfer_of_thirdResidual {T x C : ℝ} (hT : 2 ≤ T) (hx : T ≤ x)
    (hthird : |thirdSignalResidual T x| ≤ C * x) :
    |T * Real.log T * sharpFormFactor T (Real.log x / Real.log T) -
      primeSignalEnergy T x| ≤
      (C + 4 + 2 * (4/Real.log 2 * ∑' n : ℕ, mangoldtThreeHalves n)) * x := by
  let X := 4/Real.log 2 * ∑' n : ℕ, mangoldtThreeHalves n
  have hn : 0 ≤ ∑' n : ℕ, mangoldtThreeHalves n := tsum_nonneg fun n =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hcross : |(crossIntegral x T).re| ≤ X*x :=
    (primeCross_linear_bound hT (by linarith)).trans (mul_le_mul_of_nonneg_left hx hX)
  rw [edgePairNormalization (by linarith : 1 < T)]
  rw [show 2 * Real.pi * (actualComplexPairSum T (Real.log x)).re - primeSignalEnergy T x =
       thirdSignalResidual T x + logSignalEnergy T x + 2*(crossIntegral x T).re by
       unfold thirdSignalResidual; ring]
  apply (abs_add_le _ _).trans
  have hl := (abs_add_le _ _).trans (add_le_add hthird (edgeLogEnergyBound hT hx))
  rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  change _ ≤ (C+4+2*X)*x
  linarith only [hl,hcross]
end RiemannResearch.Analysis.MontgomeryHorizontalBessel

open Filter Set MeasureTheory Real
open scoped Topology

namespace RiemannResearch.Analysis.MontgomeryHorizontalTransfer

/-- Energy of the two pole terms on the positive time half-line. -/
theorem edgePoleEnergy_integral :
    (∫ t : ℝ in Ioi 0, 4 / ((t ^ 2 + 1 / 4) * (t ^ 2 + 9 / 4))) = 4 * π / 3 := by
  let G : ℝ → ℝ := fun t => 4 * arctan (2 * t) - (4 / 3) * arctan ((2 / 3) * t)
  have hd (t : ℝ) : HasDerivAt G (4 / ((t ^ 2 + 1 / 4) * (t ^ 2 + 9 / 4))) t := by
    have ha := ((hasDerivAt_arctan' (2 * t)).comp t ((hasDerivAt_id t).const_mul 2)).const_mul 4
    have hb := ((hasDerivAt_arctan' ((2 / 3) * t)).comp t
      ((hasDerivAt_id t).const_mul (2 / 3))).const_mul (4 / 3)
    have h1 : (1 + (2 * t) ^ 2 : ℝ) ≠ 0 := by positivity
    have h2 : (1 + ((2 / 3) * t) ^ 2 : ℝ) ≠ 0 := by positivity
    have h3 : (t ^ 2 + 1 / 4 : ℝ) ≠ 0 := by positivity
    have h4 : (t ^ 2 + 9 / 4 : ℝ) ≠ 0 := by positivity
    have he : 4 * ((1 + (2 * t) ^ 2)⁻¹ * 2) - (4 / 3) * ((1 + ((2 / 3) * t) ^ 2)⁻¹ * (2 / 3)) =
        4 / ((t ^ 2 + 1 / 4) * (t ^ 2 + 9 / 4)) := by
      field_simp [h1, h2, h3, h4] <;> ring
    exact (ha.sub hb).congr_deriv (by simpa only [mul_one] using he)
  have ha : Tendsto (fun t : ℝ => arctan (2 * t)) atTop (𝓝 (π / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop).comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hb : Tendsto (fun t : ℝ => arctan ((2 / 3) * t)) atTop (𝓝 (π / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop).comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2 / 3))
  have hG : Tendsto G atTop (𝓝 (4 * (π / 2) - (4 / 3) * (π / 2))) :=
    (ha.const_mul 4).sub (hb.const_mul (4 / 3))
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun t _ => hd t) (fun t _ => by positivity) hG]
  simp [G]
  <;> ring

end RiemannResearch.Analysis.MontgomeryHorizontalTransfer

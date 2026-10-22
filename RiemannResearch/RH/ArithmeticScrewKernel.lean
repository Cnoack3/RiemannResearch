/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.ScrewPrimePart
import RiemannResearch.RH.ScrewArchimedeanSeries
import RiemannResearch.RH.FiniteDyadicCellKernel
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Explicit arithmetic screw function and its actual Haar matrix

Assemble the polar, prime-power, linear and archimedean terms with their signs.
The resulting real function is continuous, even and zero at zero. Its anchored
kernel is continuous and symmetric, and its actual integral on a dyadic Haar
step equals the arithmetic cell-matrix compression. Finite truncations have
explicit pointwise errors on bounded windows.

Source: Suzuki (2023), equations (1.1) and (1.4),
https://arxiv.org/abs/2206.03682, supports the intended g=-Psi normalization
and anchored-kernel convention; the elementary rewrite is recorded in the
user-provided RH trace attack plan (2026-09-05). This module does not identify
the defined expression with a Weil distribution, a zero sum, or the source's
Lerch formula. Those identifications, density and full positivity remain open.
-/

namespace RiemannResearch.RH
open scoped BigOperators
open MeasureTheory Set Filter
open RiemannResearch.Analysis
open RiemannResearch.RH.PrimeGapCurvature
noncomputable section

def screwLinearCoefficient : ℝ :=
  (Real.eulerMascheroniConstant + Real.pi/2 + 3*Real.log 2 + Real.log Real.pi)/2

def screwPolarPart (t : ℝ) : ℝ :=
  -4 * (Real.exp (t/2) + Real.exp (-t/2) - 2)

def arithmeticScrewFunction (t : ℝ) : ℝ :=
  screwPolarPart t + screwPrimePart t + screwLinearCoefficient*|t| - archimedeanScrewSeries t

theorem continuous_screwPolarPart : Continuous screwPolarPart :=
  continuous_const.mul (((Real.continuous_exp.comp (continuous_id.div_const 2)).add
    (Real.continuous_exp.comp (continuous_neg.div_const 2))).sub continuous_const)

theorem continuous_arithmeticScrewFunction : Continuous arithmeticScrewFunction :=
  ((continuous_screwPolarPart.add continuous_screwPrimePart).add
    (continuous_const.mul continuous_abs)).sub continuous_archimedeanScrewSeries

theorem screwPolarPart_neg (t : ℝ) : screwPolarPart (-t) = screwPolarPart t := by
  simp [screwPolarPart, add_comm]

theorem arithmeticScrewFunction_neg (t : ℝ) :
    arithmeticScrewFunction (-t) = arithmeticScrewFunction t := by
  simp only [arithmeticScrewFunction, screwPolarPart_neg, screwPrimePart_neg,
    abs_neg, archimedeanScrewSeries_neg]

theorem arithmeticScrewFunction_zero : arithmeticScrewFunction 0 = 0 := by
  norm_num [arithmeticScrewFunction, screwPolarPart, screwPrimePart_zero, archimedeanScrewSeries_zero]

def arithmeticScrewKernel (x y : ℝ) : ℝ :=
  arithmeticScrewFunction (x-y) - arithmeticScrewFunction x - arithmeticScrewFunction y

theorem continuous_arithmeticScrewKernel : Continuous (Function.uncurry arithmeticScrewKernel) :=
  ((continuous_arithmeticScrewFunction.comp (continuous_fst.sub continuous_snd)).sub
    (continuous_arithmeticScrewFunction.comp continuous_fst)).sub
    (continuous_arithmeticScrewFunction.comp continuous_snd)

theorem arithmeticScrewKernel_symm (x y : ℝ) :
    arithmeticScrewKernel x y = arithmeticScrewKernel y x := by
  have h : arithmeticScrewFunction (y-x) = arithmeticScrewFunction (x-y) := by
    rw [show y-x = -(x-y) by ring, arithmeticScrewFunction_neg]
  unfold arithmeticScrewKernel
  rw [h]
  ring

def arithmeticScrewHaarMatrix (R : ℝ) (m : ℕ) :
    Matrix (FiniteDyadicHaarIndex m) (FiniteDyadicHaarIndex m) ℝ :=
  finiteDyadicHaarCompression m (dyadicCellKernel R m
    (fun x y => arithmeticScrewFunction (x-y)))

theorem arithmeticScrewHaarMatrix_quadratic {R : ℝ} (hR : 0 ≤ R) (m : ℕ)
    (c : FiniteDyadicHaarIndex m → ℝ) :
    (∫ x, dyadicHaarStep R m c x *
      (∫ y, arithmeticScrewKernel x y * dyadicHaarStep R m c y)) =
    dotProduct c ((arithmeticScrewHaarMatrix R m).mulVec c) := by
  have h := dyadicHaarStep_screw_compression hR m arithmeticScrewFunction
    continuous_arithmeticScrewFunction c
  simpa only [arithmeticScrewKernel, arithmeticScrewHaarMatrix,
    arithmeticScrewFunction_neg, arithmeticScrewFunction_zero, add_zero]
    using h

def arithmeticScrewApprox (N J : ℕ) (t : ℝ) : ℝ :=
  screwPolarPart t + (∑ n ∈ Finset.range N, primePowerHingeTerm n t)
    + screwLinearCoefficient*|t| - ∑ k ∈ Finset.range J, archimedeanScrewTerm k t

theorem continuous_arithmeticScrewApprox (N J : ℕ) : Continuous (arithmeticScrewApprox N J) :=
  ((continuous_screwPolarPart.add (continuous_finsetSum _ (fun n _ =>
    continuous_primePowerHingeTerm n))).add (continuous_const.mul continuous_abs)).sub
    (continuous_finsetSum _ (fun k _ => continuous_archimedeanScrewTerm k))

theorem arithmeticScrewApprox_sub_eq_tail {R t : ℝ} (ht : |t| ≤ R) (N J : ℕ)
    (hN : Real.exp R < N) :
    arithmeticScrewApprox N J t - arithmeticScrewFunction t =
      ∑' k : ℕ, archimedeanScrewTerm (k+J) t := by
  unfold arithmeticScrewApprox arithmeticScrewFunction
  rw [screwPrimePart_eq_sum_of_bound ht N hN, archimedeanScrewSeries_eq_sum_add_tail J]
  ring

theorem arithmeticScrewApprox_error_bounds {R t : ℝ} (ht : |t| ≤ R) (N J : ℕ)
    (hN : Real.exp R < N) :
    0 ≤ arithmeticScrewApprox N J t - arithmeticScrewFunction t ∧
    ‖arithmeticScrewApprox N J t - arithmeticScrewFunction t‖ ≤ 4*archimedeanTailMajorant J := by
  rw [arithmeticScrewApprox_sub_eq_tail ht N J hN]
  have h := archimedeanScrewSeries_tail_bounds J t
  exact ⟨h.1, by simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2⟩

end
end RiemannResearch.RH

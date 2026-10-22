/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroCoshMass
import RiemannResearch.RH.ParetoHorizontalZeroBridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Actual Pareto residuals control the regularized cosh mass

Source: `FMZ_Haar_Poisson_Pareto_Paper_Proofs_20261011.md`, Theorem 4.
This module combines the sharp scalar cosh comparison with the actual Pareto
Mellin obstruction. Both imports retain actual zeros and analytic
multiplicity. The physical signed approximation error is unchanged.

No RH or residual-convergence hypothesis is needed for these estimates.
The estimates detect an off-line zero; they supply no approximation tending
to zero. The sibling `ActualZeroReciprocalConstant` evaluates the all-sign
reciprocal sum and supplies the explicit constant.

The existing regularized mass is reused; no second cosh energy is introduced.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualZeroParetoCoshBridge

open RiemannResearch.RH.Pareto
open RiemannResearch.RH.ParetoBeurlingMellinObstruction
open RiemannResearch.RH.ParetoHorizontalZeroBridge
open ActualZeroHorizontalEnergy ActualZeroCoshMass

/-- The sharp cosh coefficient combines with the actual Pareto residual
without replacing it by a Haar or coefficient norm. -/
theorem regularizedCoshMass_le_pareto_error (u : ℝ)
    (f : ThresholdHilbert) (hf : f ∈ normalizedResidueClosure) :
    regularizedCoshMass u ≤ (Real.cosh (|u| / 2) - 1) *
      ‖hilbertOne - f‖ ^ 2 * ordinateInverseSquareSum := by
  have hC := regularizedCoshMass_le_fourthEnergy_sharp u
  have hE := horizontalFourthEnergy_le_pareto_error f hf
  have h := mul_le_mul_of_nonneg_left hE
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
      (sub_nonneg.mpr (Real.one_le_cosh (|u| / 2))))
  nlinarith only [hC, h]

/-- Every finite legal signed candidate automatically satisfies the bridge. -/
theorem regularizedCoshMass_le_finiteResidue_error (u : ℝ)
    (D : Finset LegalConductor) (c : LegalConductor → ℝ) :
    regularizedCoshMass u ≤ (Real.cosh (|u| / 2) - 1) *
      ‖hilbertOne - finiteResidueCandidate D c‖ ^ 2 * ordinateInverseSquareSum :=
  regularizedCoshMass_le_pareto_error u _ (finiteResidueCandidate_mem_closure D c)

/-- A bound stated entirely with the previously available unconditional
gammaOf reciprocal-square sum. -/
theorem regularizedCoshMass_le_pareto_error_gammaOf (u : ℝ)
    (f : ThresholdHilbert) (hf : f ∈ normalizedResidueClosure) :
    regularizedCoshMass u ≤ (5 / 4 : ℝ) * (Real.cosh (|u| / 2) - 1) *
      ‖hilbertOne - f‖ ^ 2 *
        ∑' ρ : ActualZero, (Zeta23.zeroMult (ρ : ℂ) : ℝ) /
          (1 + Complex.normSq (Zeta23.gammaOf (ρ : ℂ))) := by
  have hC := regularizedCoshMass_le_fourthEnergy_sharp u
  have hE := horizontalFourthEnergy_le_pareto_error_gammaOf f hf
  have h := mul_le_mul_of_nonneg_left hE
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
      (sub_nonneg.mpr (Real.one_le_cosh (|u| / 2))))
  nlinarith only [hC, h]

/-- An independently established ordinate-sum constant specializes the
actual residual bound. No Hadamard evaluation is assumed implicitly. -/
theorem regularizedCoshMass_le_of_ordinate_sum_le (u : ℝ)
    (f : ThresholdHilbert) (hf : f ∈ normalizedResidueClosure)
    (C : ℝ) (hC : ordinateInverseSquareSum ≤ C) :
    regularizedCoshMass u ≤
      (Real.cosh (|u| / 2) - 1) * C * ‖hilbertOne - f‖ ^ 2 := by
  have hcosh := regularizedCoshMass_le_fourthEnergy_sharp u
  have hE := horizontalFourthEnergy_le_of_ordinate_sum_le f hf C hC
  have h := mul_le_mul_of_nonneg_left hE
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
      (sub_nonneg.mpr (Real.one_le_cosh (|u| / 2))))
  nlinarith only [hcosh, h]

end RiemannResearch.Analysis.ActualZeroParetoCoshBridge

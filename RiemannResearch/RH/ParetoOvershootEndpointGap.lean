/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoProjectionOvershoot
import RiemannResearch.RH.ParetoParityOptimizer
import RiemannResearch.RH.ParetoGibbsTailBasis
import RiemannResearch.RH.ParetoHilbertPhysical
import RiemannResearch.RH.ThresholdHilbertL1
import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.RH.FirstCoordinateEndpoint
import RiemannResearch.RH.FiniteDyadicDefect
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact overshoot endpoint gaps and quantitative energy control

Source: an equality-first continuation of Christian Noack's Pareto parity
research agenda, 19 October 2026. The bounded sign test and the exact dyadic
remainder give the gap decomposition. No arithmetic endpoint estimate is
assumed in the identities or the quadratic lower bounds. The final quantitative
consumer retains its endpoint-error hypothesis explicitly.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open ParityOptimizer
set_option backward.isDefEq.respectTransparency false

/-- The exact slack in the bounded sign test, before taking any estimates. -/
theorem odd_orthogonal_signTest_gap_eq (f : ThresholdHilbert)
    (ho : inner ℝ f oddIndicator = 0) :
    hilbertL1Norm f - inner ℝ f firstPointSignTest =
      2 * hilbertNegativeMass f - hilbertSequence f 1 := by
  have hz : inner ℝ f (residueAtom 0) = 0 := by
    have hh := ho
    rw [oddIndicator, inner_smul_right] at hh
    linarith
  rw [firstPointSignTest, inner_sub_right, inner_add_right,
    inner_smul_right, inner_smul_right, hz, mul_zero, sub_zero,
    inner_paretoPoint, hilbertGibbsPhysical_eq]
  rw [show paretoWeight 0 = (1 / 2 : ℝ) by norm_num [paretoWeight]]
  change hilbertL1Norm f -
    (inner ℝ f hilbertOne + 2 * ((1 / 2 : ℝ) * hilbertSequence f 1)) = _
  rw [hilbertNegativeMass_eq]
  ring

/-- Both terms on the right are nonnegative; no signed term is discarded. -/
theorem limitOvershoot_endpoint_gap_identity :
    limitOvershoot - (1 - Real.sqrt 2 / 2) * limitEnergy =
      (hilbertL1Norm limitResidual - inner ℝ limitResidual firstPointSignTest) / 2 +
        (Real.sqrt 2 / 4) *
          ‖limitResidual - (Real.sqrt 2 / 2) • doubleDilation limitResidual‖ ^ 2 := by
  have hg := odd_orthogonal_signTest_gap_eq limitResidual limitResidual_odd_inner
  change hilbertL1Norm limitResidual - inner ℝ limitResidual firstPointSignTest =
    2 * limitOvershoot - hilbertSequence limitResidual 1 at hg
  have he := firstCoordinate_eq_energy_add_dyadicRemainder
  linarith

/-- The finite equality keeps the signed projection defect at its actual stage. -/
theorem projectionOvershoot_endpoint_gap_identity (n : ℕ) :
    projectionOvershoot (n + 1) - (1 - Real.sqrt 2 / 2) * energy (n + 1) +
        finiteDyadicDefect (n + 1) / 2 =
      (hilbertL1Norm (projectionResidual (n + 1)) -
        inner ℝ (projectionResidual (n + 1)) firstPointSignTest) / 2 +
          (Real.sqrt 2 / 4) * finiteDyadicResidualRemainder (n + 1) := by
  have hg := odd_orthogonal_signTest_gap_eq (projectionResidual (n + 1))
    (projectionResidual_odd_inner n)
  change hilbertL1Norm (projectionResidual (n + 1)) -
    inner ℝ (projectionResidual (n + 1)) firstPointSignTest =
      2 * projectionOvershoot (n + 1) -
        hilbertSequence (projectionResidual (n + 1)) 1 at hg
  have he := finite_firstCoordinate_eq_dyadicSquare_sub_defect (n + 1)
  rw [finiteDyadicSquare_eq_energy_add_remainder] at he
  linarith

/-- A complete finite lower bound including the boundary correction. -/
theorem projectionOvershoot_endpoint_quadratic_lower (n : ℕ) :
    (1 - Real.sqrt 2 / 2) * energy (n + 1) +
        (Real.sqrt 2 / 8) * (hilbertSequence (projectionResidual (n + 1)) 1) ^ 2 ≤
      projectionOvershoot (n + 1) + finiteDyadicDefect (n + 1) / 2 := by
  have hq := finite_firstCoordinate_quadratic_lower (n + 1)
  have ho := odd_orthogonal_first_le_negativeMass (projectionResidual (n + 1))
    (projectionResidual_odd_inner n)
  change hilbertSequence (projectionResidual (n + 1)) 1 ≤
    2 * projectionOvershoot (n + 1) at ho
  linarith

/-- The critical overshoot bound has a quantified first-coordinate gap. -/
theorem limitOvershoot_endpoint_quadratic_lower :
    (1 - Real.sqrt 2 / 2) * limitEnergy +
        (Real.sqrt 2 / 8) * (hilbertSequence limitResidual 1) ^ 2 ≤
      limitOvershoot := by
  have hq := firstCoordinate_energy_quadratic_lower
  have ho := odd_orthogonal_first_le_negativeMass limitResidual limitResidual_odd_inner
  change hilbertSequence limitResidual 1 ≤ 2 * limitOvershoot at ho
  linarith

/-- A lower bound involving only the actual limiting energy. -/
theorem limitOvershoot_endpoint_energy_quadratic_lower :
    (1 - Real.sqrt 2 / 2) * limitEnergy +
        ((3 * Real.sqrt 2 - 4) / 4) * limitEnergy ^ 2 ≤ limitOvershoot := by
  have hc : 0 ≤ 2 - Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have he : 0 ≤ limitEnergy := sq_nonneg _
  have hx := firstCoordinate_energy_bounds.1
  have hsum : 0 ≤ hilbertSequence limitResidual 1 +
      (2 - Real.sqrt 2) * limitEnergy :=
    add_nonneg firstCoordinate_nonneg (mul_nonneg hc he)
  have hs : ((2 - Real.sqrt 2) * limitEnergy) ^ 2 ≤
      (hilbertSequence limitResidual 1) ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hx) hsum]
  have hm := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ Real.sqrt 2 / 8 by positivity)
  have hk : (Real.sqrt 2 / 8) * (2 - Real.sqrt 2) ^ 2 =
      (3 * Real.sqrt 2 - 4) / 4 := by
    calc
      _ = (3 * Real.sqrt 2 - 4) / 4 +
          ((Real.sqrt 2 - 4) / 8) * ((Real.sqrt 2) ^ 2 - 2) := by ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring
  have hid : (Real.sqrt 2 / 8) * ((2 - Real.sqrt 2) * limitEnergy) ^ 2 =
      ((3 * Real.sqrt 2 - 4) / 4) * limitEnergy ^ 2 := by
    rw [mul_pow, ← mul_assoc, hk]
  rw [hid] at hm
  linarith [limitOvershoot_endpoint_quadratic_lower]

/-- An endpoint error controls the square of the remaining energy.
Open arithmetic input: establish the displayed overshoot estimate with a
sufficiently small error for the actual optimizer. -/
theorem limitEnergy_sq_le_of_overshoot_endpoint_error (η : ℝ)
    (h : limitOvershoot ≤ (1 - Real.sqrt 2 / 2) * limitEnergy + η) :
    ((3 * Real.sqrt 2 - 4) / 4) * limitEnergy ^ 2 ≤ η := by
  linarith [limitOvershoot_endpoint_energy_quadratic_lower]

end RiemannResearch.RH.Pareto.CoefficientStabilization

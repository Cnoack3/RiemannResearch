/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.FirstCoordinateEndpoint
import RiemannResearch.RH.FiniteDyadicDefect

/-!
# Finite mixed-scale endpoint identities

Source: the user-provided dyadic argument and polarization of the exact
normalized dilation square. The equality retains the energy gain and the
whole squared mismatch. The quadratic bound uses only the first coordinate
of that mismatch. No arithmetic decay hypothesis is discharged here.
-/

noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto.CoefficientStabilization

open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.RH.ArithmeticCumulative

/-- Cross-scale orthogonality removes the smaller projection after dilation. -/
theorem mixedDyadicResidual_inner_dilation_one (n : ℕ) :
    inner ℝ (projectionResidual (doubleStage n)) (doubleDilation hilbertOne) =
      inner ℝ (projectionResidual (doubleStage n))
        (doubleDilation (projectionResidual n)) := by
  have ho : inner ℝ (projectionResidual (doubleStage n))
      (doubleDilation (projection n)) = 0 :=
    projectionResidual_inner_mem (doubleStage n) _
      (doubleDilation_mem_double
        ((finiteSpace n).starProjection_apply_mem hilbertOne))
  have he : hilbertOne = projectionResidual n + projection n := by
    unfold projectionResidual
    abel
  rw [he, map_add, inner_add_right, ho, add_zero]

/-- The first-coordinate pairing at two adjacent conductor scales. -/
theorem mixedDyadicResidual_first_pairing (n : ℕ) :
    hilbertSequence (projectionResidual (doubleStage n)) 1 =
      2 * energy (doubleStage n) -
        inner ℝ (projectionResidual (doubleStage n))
          (doubleDilation (projectionResidual n)) := by
  have h := congrArg
    (fun f => inner ℝ (projectionResidual (doubleStage n)) f)
    firstPoint_eq_dilation_difference
  rw [inner_paretoPoint, hilbertGibbsPhysical_eq,
    inner_sub_right, inner_smul_right, projectionResidual_inner_one] at h
  rw [show paretoWeight 0 = (1 / 2 : ℝ) by norm_num [paretoWeight]] at h
  change (1 / 2 : ℝ) * hilbertSequence (projectionResidual (doubleStage n)) 1 =
    energy (doubleStage n) - (1 / 2 : ℝ) *
      inner ℝ (projectionResidual (doubleStage n)) (doubleDilation hilbertOne) at h
  rw [mixedDyadicResidual_inner_dilation_one] at h
  linarith

/-- Exact finite endpoint identity. The full normalized mismatch and the
actual energy gain are retained. -/
theorem mixedDyadicResidual_first_endpoint_identity (n : ℕ) :
    hilbertSequence (projectionResidual (doubleStage n)) 1 +
        (Real.sqrt 2 / 2) * (energy n - energy (doubleStage n)) =
      (2 - Real.sqrt 2) * energy (doubleStage n) +
        (Real.sqrt 2 / 2) *
          ‖projectionResidual (doubleStage n) - (Real.sqrt 2 / 2) •
            doubleDilation (projectionResidual n)‖ ^ 2 := by
  have ht := mixedDyadicResidual_first_pairing n
  rw [doubleDilation_inner_eq_norm_remainder] at ht
  change hilbertSequence (projectionResidual (doubleStage n)) 1 =
    2 * energy (doubleStage n) - (Real.sqrt 2 / 2) *
      (energy (doubleStage n) + energy n -
        ‖projectionResidual (doubleStage n) - (Real.sqrt 2 / 2) •
          doubleDilation (projectionResidual n)‖ ^ 2) at ht
  nlinarith

/-- Root's previously proved coordinate bound converts the exact mismatch
into a finite quadratic strengthening of the endpoint lower bound. -/
theorem mixedDyadicResidual_first_endpoint_quadratic (n : ℕ) :
    (2 - Real.sqrt 2) * energy (doubleStage n) +
        (Real.sqrt 2 / 4) *
          (hilbertSequence (projectionResidual (doubleStage n)) 1) ^ 2 ≤
      hilbertSequence (projectionResidual (doubleStage n)) 1 +
        (Real.sqrt 2 / 2) * (energy n - energy (doubleStage n)) := by
  have hid := mixedDyadicResidual_first_endpoint_identity n
  have hfirst := normalized_dyadic_mismatch_first_sq_le
    (projectionResidual (doubleStage n)) (projectionResidual n)
  have hweighted := mul_le_mul_of_nonneg_left hfirst
    (show 0 ≤ Real.sqrt 2 / 4 by positivity)
  nlinarith

/-- An equivalent deficit estimate that displays the energy gain as the only
finite-scale loss in the limiting sharp quadratic inequality. -/
theorem mixedDyadicResidual_first_endpoint_deficit (n : ℕ) :
    (2 - Real.sqrt 2) * energy (doubleStage n) -
        (Real.sqrt 2 / 2) * (energy n - energy (doubleStage n)) +
        (Real.sqrt 2 / 4) *
          (hilbertSequence (projectionResidual (doubleStage n)) 1) ^ 2 ≤
      hilbertSequence (projectionResidual (doubleStage n)) 1 := by
  have h := mixedDyadicResidual_first_endpoint_quadratic n
  linarith

end RiemannResearch.RH.Pareto.CoefficientStabilization

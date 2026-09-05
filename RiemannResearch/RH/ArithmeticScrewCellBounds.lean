/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.ArithmeticScrewKernel
import RiemannResearch.LinearAlgebra.FiniteQuadraticError

/-!
# Certified finite-cell approximations to the arithmetic screw kernel

On a dyadic window [-R,R], any N>exp(2R) makes the prime contribution exactly
finite, with explicit hinge entries. Truncating the archimedean series at J
then bounds each cell error by 4*B_J*h^2 and every slope quadratic error by
4*B_J*h^2*(sum_i |s_i|)^2. Here h is the actual cell width and B_J tends to zero.
These enclosures hold in all finite directions and make no positivity claim
for the complete arithmetic matrix.

Source: user-provided handoff v16 and RH trace attack plan (2026-09-05),
exact cell formulas and effective archimedean-tail strategy.
-/

namespace RiemannResearch.RH
open MeasureTheory Set
open RiemannResearch.Analysis RiemannResearch.RH.PrimeGapCurvature
open scoped BigOperators
noncomputable section

theorem dyadicCell_screwPrimePart_eq_finite {R : ℝ} (hR : 0 ≤ R) (m N : ℕ)
    (hN : Real.exp (2*R) < N) (i j : Fin (2^m)) :
    dyadicCellKernel R m (fun x y => screwPrimePart (x-y)) i j =
      ∑ n ∈ Finset.range N, primePowerHingeCell n
        (dyadicCellLeft R m i) (dyadicCellRight R m i)
        (dyadicCellLeft R m j) (dyadicCellRight R m j) := by
  unfold dyadicCellKernel
  rw [← integral_integral_sum_primePowerHingeTerm]
  apply intervalIntegral.integral_congr
  intro x hx
  apply intervalIntegral.integral_congr
  intro y hy
  apply screwPrimePart_eq_sum_of_bound _ N hN
  have hx' := abs_le_of_mem_dyadicCell hR m i hx
  have hy' := abs_le_of_mem_dyadicCell hR m j hy
  exact (abs_sub x y).trans (by linarith)

theorem dyadicCell_arithmeticScrewApprox_error {R : ℝ} (hR : 0 ≤ R)
    (m N J : ℕ) (hN : Real.exp (2*R) < N) (i j : Fin (2^m)) :
    ‖dyadicCellKernel R m (fun x y => arithmeticScrewApprox N J (x-y)) i j
      - dyadicCellKernel R m (fun x y => arithmeticScrewFunction (x-y)) i j‖ ≤
      4*archimedeanTailMajorant J*(dyadicCellWidth R m)^2 := by
  unfold dyadicCellKernel
  rw [integral_integral_sub
    (k := fun x y => arithmeticScrewApprox N J (x-y))
    (l := fun x y => arithmeticScrewFunction (x-y))
    ((continuous_arithmeticScrewApprox N J).comp (continuous_fst.sub continuous_snd))
    (continuous_arithmeticScrewFunction.comp (continuous_fst.sub continuous_snd))]
  have hb : ∀ x ∈ uIoc (dyadicCellLeft R m i) (dyadicCellRight R m i),
      ∀ y ∈ uIoc (dyadicCellLeft R m j) (dyadicCellRight R m j),
      ‖arithmeticScrewApprox N J (x-y) - arithmeticScrewFunction (x-y)‖ ≤
        4*archimedeanTailMajorant J := by
    intro x hx y hy
    have hx' := abs_le_of_mem_dyadicCell hR m i (uIoc_subset_uIcc hx)
    have hy' := abs_le_of_mem_dyadicCell hR m j (uIoc_subset_uIcc hy)
    exact (arithmeticScrewApprox_error_bounds
      ((abs_sub x y).trans (by linarith)) N J hN).2
  have h := norm_integral_integral_le hb
  simpa only [dyadicCellRight, add_sub_cancel_left,
    abs_of_nonneg (dyadicCellWidth_nonneg hR m), pow_two, mul_assoc] using h

end
end RiemannResearch.RH

namespace RiemannResearch.RH
open scoped BigOperators Topology
open Filter MeasureTheory Set RiemannResearch.RH.PrimeGapCurvature
noncomputable section


theorem dyadicCell_arithmeticScrewApprox_quadratic_error {R : ℝ} (hR : 0 ≤ R)
    (m N J : ℕ) (hN : Real.exp (2*R) < N) (s : Fin (2^m) → ℝ) :
    ‖dotProduct s ((dyadicCellKernel R m (fun x y => arithmeticScrewApprox N J (x-y))).mulVec s)
      - dotProduct s ((dyadicCellKernel R m (fun x y => arithmeticScrewFunction (x-y))).mulVec s)‖ ≤
      4*archimedeanTailMajorant J*(dyadicCellWidth R m)^2*(∑ i, ‖s i‖)^2 :=
  RiemannResearch.LinearAlgebra.quadratic_error_of_entrywise_bound _ _ _
    (dyadicCell_arithmeticScrewApprox_error hR m N J hN) s

end
end RiemannResearch.RH

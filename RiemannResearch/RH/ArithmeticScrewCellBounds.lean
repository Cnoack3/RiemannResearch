/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.ArithmeticScrewKernel
import RiemannResearch.RH.ScrewArchimedeanPositivity
import RiemannResearch.LinearAlgebra.FiniteQuadraticError

/-!
# Certified finite-cell approximations to the arithmetic screw kernel

On a dyadic window [-R,R], any N>exp(2R) makes the prime contribution exactly
finite, with explicit hinge entries. Truncating the archimedean series at J
then bounds each cell error by 4*B_J*h^2 and every slope quadratic error by
4*B_J*h^2*(sum_i |s_i|)^2. Here h is the actual cell width and B_J tends to zero.
These enclosures hold in all finite directions. On mean-zero Haar steps,
the actual-minus-approximate quadratic form is exactly the negative
archimedean tail, hence lies between zero and 8*R*B_J*integral(u^2).
This supplies a lower approximation, not positivity of the complete matrix.

Source: user-provided handoff v16 and RH trace attack plan (2026-09-05),
exact cell formulas and effective archimedean-tail strategy.
-/

namespace RiemannResearch.RH
open MeasureTheory Set
open RiemannResearch.Analysis RiemannResearch.RH.PrimeGapCurvature
open scoped BigOperators
noncomputable section

theorem dyadicCell_screwPrimePart_eq_finite {R : ℝ} (hR : 0 ≤ R) (m N : ℕ)
    (hN : Real.exp (2 * R) < N) (i j : Fin (2 ^ m)) :
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
    (m N J : ℕ) (hN : Real.exp (2 * R) < N) (i j : Fin (2 ^ m)) :
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
    (m N J : ℕ) (hN : Real.exp (2 * R) < N) (s : Fin (2 ^ m) → ℝ) :
    ‖dotProduct s ((dyadicCellKernel R m (fun x y => arithmeticScrewApprox N J (x-y))).mulVec s)
      - dotProduct s ((dyadicCellKernel R m (fun x y => arithmeticScrewFunction (x-y))).mulVec s)‖ ≤
      4*archimedeanTailMajorant J*(dyadicCellWidth R m)^2*(∑ i, ‖s i‖)^2 :=
  RiemannResearch.LinearAlgebra.quadratic_error_of_entrywise_bound _ _ _
    (dyadicCell_arithmeticScrewApprox_error hR m N J hN) s

/-- Exact signed quadratic truncation error on the support window.
The prime-power cutoff includes every active arithmetic atom. -/
theorem arithmeticScrewFunction_sub_approx_dyadic_integral_eq_tail
    {R : ℝ} (hR : 0 ≤ R) (m N J : ℕ) (hN : Real.exp (2 * R) < N)
    (c : FiniteDyadicHaarIndex m → ℝ) :
    (∫ x, dyadicHaarStep R m c x *
      (∫ y, arithmeticScrewFunction (x-y) * dyadicHaarStep R m c y)) -
    (∫ x, dyadicHaarStep R m c x *
      (∫ y, arithmeticScrewApprox N J (x-y) * dyadicHaarStep R m c y)) =
    (∫ x, dyadicHaarStep R m c x *
      (∫ y, (-archimedeanScrewTail J (x-y)) * dyadicHaarStep R m c y)) := by
  rw [show (∫ x, dyadicHaarStep R m c x *
        (∫ y, arithmeticScrewFunction (x-y) * dyadicHaarStep R m c y)) -
      (∫ x, dyadicHaarStep R m c x *
        (∫ y, arithmeticScrewApprox N J (x-y) * dyadicHaarStep R m c y)) =
      (∫ x, dyadicHaarStep R m c x *
        (∫ y, (arithmeticScrewFunction (x-y) - arithmeticScrewApprox N J (x-y)) *
          dyadicHaarStep R m c y)) from
    RiemannResearch.Analysis.finiteCellKernel_quadratic_sub _ _ _ (dyadicCell_ordered hR m) _ _
      (continuous_arithmeticScrewFunction.comp (continuous_fst.sub continuous_snd))
      ((continuous_arithmeticScrewApprox N J).comp (continuous_fst.sub continuous_snd))]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ Icc (-R) R
  · congr 1
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ Icc (-R) R
    · have ht : |x-y| ≤ 2 * R :=
        (abs_sub x y).trans (by
          have hx' := abs_le.mpr hx
          have hy' := abs_le.mpr hy
          linarith)
      have he := arithmeticScrewApprox_sub_eq_tail ht N J hN
      change arithmeticScrewApprox N J (x-y) - arithmeticScrewFunction (x-y) =
        archimedeanScrewTail J (x-y) at he
      have hd : arithmeticScrewFunction (x-y) - arithmeticScrewApprox N J (x-y) =
          -archimedeanScrewTail J (x-y) := by linarith
      rw [hd]
    · simp [dyadicHaarStep_eq_zero_of_not_mem hR m c hy]
  · simp [dyadicHaarStep_eq_zero_of_not_mem hR m c hx]

theorem arithmeticScrewFunction_sub_approx_dyadic_integral_bounds
    {R : ℝ} (hR : 0 ≤ R) (m N J : ℕ) (hN : Real.exp (2 * R) < N)
    (c : FiniteDyadicHaarIndex m → ℝ) :
    0 ≤
      (∫ x, dyadicHaarStep R m c x *
        (∫ y, arithmeticScrewFunction (x-y) * dyadicHaarStep R m c y)) -
      (∫ x, dyadicHaarStep R m c x *
        (∫ y, arithmeticScrewApprox N J (x-y) * dyadicHaarStep R m c y)) ∧
    (∫ x, dyadicHaarStep R m c x *
      (∫ y, arithmeticScrewFunction (x-y) * dyadicHaarStep R m c y)) -
      (∫ x, dyadicHaarStep R m c x *
        (∫ y, arithmeticScrewApprox N J (x-y) * dyadicHaarStep R m c y)) ≤
      8 * R * archimedeanTailMajorant J * (∫ x, dyadicHaarStep R m c x ^ 2) := by
  rw [arithmeticScrewFunction_sub_approx_dyadic_integral_eq_tail hR m N J hN c]
  exact neg_archimedeanScrewTail_dyadic_integral_bounds_l2 hR m J c

end
end RiemannResearch.RH

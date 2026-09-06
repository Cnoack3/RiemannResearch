/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.ArithmeticFiniteEntryFormulas
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# First-level arithmetic finite approximations

The first nonempty unnormalized Haar index is a singleton. Its native finite
PSD condition is therefore exactly the nonnegativity of its unique diagonal.

At the positive rational window R = 1/4, the admissible finite cutoffs N = 2,
J = 0 give a strictly negative diagonal. The exact polar contribution remains
positive; the unchanged linear contribution dominates it. This excludes that
particular finite approximation as a PSD certificate. It does not refute
positivity of the actual arithmetic quadratic: the published comparison has
the direction q_approx ≤ q_actual.

Source: user-provided continuation task, supporting the first-level reduction
and concrete obstruction question. Finite exponential estimates use Mathlib.
-/

open scoped BigOperators

namespace RiemannResearch.RH.PrimeGapCurvature
noncomputable section

def finiteDyadicHaarIndexOne : FiniteDyadicHaarIndex 1 := ⟨0, 0⟩

theorem finiteDyadicHaarIndex_one_eq (i : FiniteDyadicHaarIndex 1) :
    i = finiteDyadicHaarIndexOne := by
  rcases i with ⟨⟨l, hl⟩, q⟩
  have hl0 : l = 0 := by omega
  subst l
  have hq : q = 0 := by
    apply Fin.ext
    have h := q.isLt
    norm_num at h ⊢
    omega
  subst q
  rfl

theorem finiteDyadicHaarIndex_one_univ :
    (Finset.univ : Finset (FiniteDyadicHaarIndex 1)) =
      {finiteDyadicHaarIndexOne} := by
  ext i
  simp [finiteDyadicHaarIndex_one_eq i]

theorem finiteDyadicHaarCompression_one_entry
    (K : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℝ) :
    finiteDyadicHaarCompression 1 K
        finiteDyadicHaarIndexOne finiteDyadicHaarIndexOne =
      K 0 0 - K 0 1 - K 1 0 + K 1 1 := by
  rw [finiteDyadicHaarCompression_apply]
  change (∑ i : Fin 2, finiteDyadicHaarAtom 1 0 0 i *
    ∑ j : Fin 2, K i j * finiteDyadicHaarAtom 1 0 0 j) = _
  simp only [Fin.sum_univ_two]
  norm_num [finiteDyadicHaarAtom]
  ring

theorem finiteDyadicHaarIndex_one_quadratic
    (A : Matrix (FiniteDyadicHaarIndex 1) (FiniteDyadicHaarIndex 1) ℝ)
    (c : FiniteDyadicHaarIndex 1 → ℝ) :
    dotProduct c (A.mulVec c) =
      c finiteDyadicHaarIndexOne ^ 2 *
        A finiteDyadicHaarIndexOne finiteDyadicHaarIndexOne := by
  simp only [dotProduct, Matrix.mulVec, finiteDyadicHaarIndex_one_univ,
    Finset.sum_singleton]
  ring

end
end RiemannResearch.RH.PrimeGapCurvature

namespace RiemannResearch.RH
open RiemannResearch.RH.PrimeGapCurvature RiemannResearch.Analysis
noncomputable section

theorem arithmeticScrewApproxHaarMatrix_one_posSemidef_iff
    (R : ℝ) (N J : ℕ) :
    (arithmeticScrewApproxHaarMatrix R 1 N J).PosSemidef ↔
      0 ≤ arithmeticScrewApproxHaarMatrix R 1 N J
        finiteDyadicHaarIndexOne finiteDyadicHaarIndexOne := by
  constructor
  · exact fun h => h.diag_nonneg
  · intro hd
    apply (arithmeticScrewApproxHaarMatrix_posSemidef_iff R 1 N J).mpr
    intro c
    rw [finiteDyadicHaarIndex_one_quadratic]
    exact mul_nonneg (sq_nonneg _) hd

theorem arithmeticScrewApproxHaarMatrix_one_entry
    (R : ℝ) (N J : ℕ) :
    arithmeticScrewApproxHaarMatrix R 1 N J
        finiteDyadicHaarIndexOne finiteDyadicHaarIndexOne =
      arithmeticScrewApproxCell N J (-R) 0 (-R) 0 -
      arithmeticScrewApproxCell N J (-R) 0 0 R -
      arithmeticScrewApproxCell N J 0 R (-R) 0 +
      arithmeticScrewApproxCell N J 0 R 0 R := by
  unfold arithmeticScrewApproxHaarMatrix
  rw [finiteDyadicHaarCompression_one_entry]
  simp only [dyadicCellKernel, integral_integral_arithmeticScrewApprox]
  norm_num [dyadicCellLeft, dyadicCellRight, dyadicCellWidth]

theorem arithmeticScrewApproxHaarMatrix_one_not_posSemidef_iff
    (R : ℝ) (N J : ℕ) :
    ¬ (arithmeticScrewApproxHaarMatrix R 1 N J).PosSemidef ↔
      arithmeticScrewApproxHaarMatrix R 1 N J
        finiteDyadicHaarIndexOne finiteDyadicHaarIndexOne < 0 := by
  rw [arithmeticScrewApproxHaarMatrix_one_posSemidef_iff, not_le]

theorem arithmeticScrewApproxHaarMatrix_one_posSemidef_iff_finite_cells
    (R : ℝ) (N J : ℕ) :
    (arithmeticScrewApproxHaarMatrix R 1 N J).PosSemidef ↔
      0 ≤ arithmeticScrewApproxCell N J (-R) 0 (-R) 0 -
        arithmeticScrewApproxCell N J (-R) 0 0 R -
        arithmeticScrewApproxCell N J 0 R (-R) 0 +
        arithmeticScrewApproxCell N J 0 R 0 R := by
  rw [arithmeticScrewApproxHaarMatrix_one_posSemidef_iff,
    arithmeticScrewApproxHaarMatrix_one_entry]

theorem arithmeticScrewApproxHaarMatrix_zero_window (m N J : ℕ) :
    arithmeticScrewApproxHaarMatrix 0 m N J = 0 := by
  have hk : dyadicCellKernel 0 m
      (fun x y => arithmeticScrewApprox N J (x-y)) = 0 := by
    ext i j
    simp [dyadicCellKernel, dyadicCellLeft, dyadicCellRight, dyadicCellWidth]
  simp [arithmeticScrewApproxHaarMatrix, finiteDyadicHaarCompression, hk]

theorem arithmeticScrewApproxHaarMatrix_zero_level_posSemidef
    (R : ℝ) (N J : ℕ) :
    (arithmeticScrewApproxHaarMatrix R 0 N J).PosSemidef := by
  apply (arithmeticScrewApproxHaarMatrix_posSemidef_iff R 0 N J).mpr
  intro c
  simp [dotProduct, FiniteDyadicHaarIndex]

private theorem screwLinearCoefficient_gt_one :
    1 < screwLinearCoefficient := by
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hπ := Real.pi_gt_three
  have hlog2 := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  have hlogπ := Real.log_pos (show 1 < Real.pi by linarith)
  unfold screwLinearCoefficient
  linarith

/-- The prime cutoff is genuinely admissible at the positive rational window. -/
theorem arithmeticScrewApprox_quarter_cutoff :
    Real.exp (2 * (1/4 : ℝ)) < (2 : ℕ) := by
  have h := Real.exp_bound' (x := (1/2 : ℝ)) (by norm_num) (by norm_num)
    (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem quarter_polar_le :
    32 * (Real.exp (1/8 : ℝ) + Real.exp (-1/8 : ℝ) - 2)^2 ≤ 9/512 := by
  have hp := Real.exp_bound (x := (1/8 : ℝ)) (by norm_num)
    (n := 2) (by norm_num)
  have hn := Real.exp_bound (x := (-1/8 : ℝ)) (by norm_num)
    (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ] at hp hn
  have hu :
      Real.exp (1/8 : ℝ) + Real.exp (-1/8 : ℝ) - 2 ≤ 3/128 := by
    linarith [(abs_le.mp hp).2, (abs_le.mp hn).2]
  have hl :
      0 ≤ Real.exp (1/8 : ℝ) + Real.exp (-1/8 : ℝ) - 2 := by
    linarith [Real.add_one_le_exp (1/8 : ℝ),
      Real.add_one_le_exp (-1/8 : ℝ)]
  have hm := mul_nonneg hl (sub_nonneg.mpr hu)
  nlinarith

/-- Exact first-level entry of the original signed approximation. The full
von Mangoldt weights at 0 and 1 vanish; the archimedean cutoff here is zero. -/
theorem arithmeticScrewApproxHaarMatrix_quarter_two_zero_entry :
    arithmeticScrewApproxHaarMatrix (1/4) 1 2 0
      finiteDyadicHaarIndexOne finiteDyadicHaarIndexOne =
      32 * (Real.exp (1/8) + Real.exp (-1/8) - 2)^2 -
        screwLinearCoefficient / 48 := by
  rw [arithmeticScrewApproxHaarMatrix_one_entry]
  norm_num [arithmeticScrewApproxCell, screwPolarCell, exponentialCell,
    secondPrimitiveCell, primePowerHingeCell, primePowerWeight,
    absCell, hingeKernelSecondPrimitive, Finset.sum_range_succ]
  have hp : Real.exp (1/4) = Real.exp (1/8) ^ 2 := by
    rw [show (1/4 : ℝ) = 1/8+1/8 by ring, Real.exp_add, pow_two]
  have hn : Real.exp (-(1/4)) = Real.exp (-(1/8)) ^ 2 := by
    rw [show (-(1/4) : ℝ) = -(1/8)+(-(1/8)) by ring,
      Real.exp_add, pow_two]
  have hprod : Real.exp (1/8) * Real.exp (-(1/8)) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [hp, hn]
  nlinarith

/-- A strict rational negative margin, certified using finite exponential bounds. -/
theorem arithmeticScrewApproxHaarMatrix_quarter_two_zero_diag_lt :
    arithmeticScrewApproxHaarMatrix (1/4) 1 2 0
      finiteDyadicHaarIndexOne finiteDyadicHaarIndexOne < -(5/1536 : ℝ) := by
  rw [arithmeticScrewApproxHaarMatrix_quarter_two_zero_entry]
  linarith [quarter_polar_le, screwLinearCoefficient_gt_one]

/-- This admissible, nonempty finite approximation is not PSD. This does not
refute positivity of the actual arithmetic form: the published comparison
has the direction q_approx ≤ q_actual. -/
theorem arithmeticScrewApproxHaarMatrix_quarter_two_zero_not_posSemidef :
    ¬ (arithmeticScrewApproxHaarMatrix (1/4) 1 2 0).PosSemidef := by
  rw [arithmeticScrewApproxHaarMatrix_one_not_posSemidef_iff]
  linarith [arithmeticScrewApproxHaarMatrix_quarter_two_zero_diag_lt]

/-- The constant coefficient 1 on the singleton Haar index gives an explicit
negative witness; it represents the original unnormalized two-cell Haar atom. -/
theorem arithmeticScrewApproxHaarMatrix_quarter_two_zero_witness :
    dotProduct (fun _ : FiniteDyadicHaarIndex 1 => (1 : ℝ))
      ((arithmeticScrewApproxHaarMatrix (1/4) 1 2 0).mulVec
        (fun _ => 1)) < -(5/1536 : ℝ) := by
  rw [finiteDyadicHaarIndex_one_quadratic]
  simpa using arithmeticScrewApproxHaarMatrix_quarter_two_zero_diag_lt

end
end RiemannResearch.RH

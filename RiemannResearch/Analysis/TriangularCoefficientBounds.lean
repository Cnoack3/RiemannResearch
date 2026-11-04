/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Normalization and coefficient-space bounds

Source: the user's triangular-matrix request, 4 November 2026.
The application is RH.QResidueNormalizationBounds.
-/

noncomputable section
open Filter InnerProductSpace
open scoped Topology BigOperators RealInnerProductSpace

namespace RiemannResearch.Analysis.TriangularCoefficientBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]

/-- Exact signed inner product identity for the raw Gram-Schmidt innovation. -/
theorem gramSchmidt_inner_input (v : ι → E) (j : ι) :
    inner ℝ (gramSchmidt ℝ v j) (v j) = ‖gramSchmidt ℝ v j‖ ^ 2 := by
  rw [gramSchmidt_def'' ℝ v j, inner_add_right, inner_sum,
    real_inner_self_eq_norm_sq]
  calc
    _ = ‖gramSchmidt ℝ v j‖ ^ 2 + 0 := by
      congr 1
      apply Finset.sum_eq_zero
      intro k hk
      rw [inner_smul_right,
        gramSchmidt_orthogonal ℝ v (ne_of_gt (Finset.mem_Iio.mp hk)), mul_zero]
    _ = _ := add_zero _

/-- Orthogonalization never increases the norm of the current atom. -/
theorem norm_gramSchmidt_le (v : ι → E) (j : ι) :
    ‖gramSchmidt ℝ v j‖ ≤ ‖v j‖ := by
  have h := real_inner_le_norm (gramSchmidt ℝ v j) (v j)
  rw [gramSchmidt_inner_input] at h
  by_cases hz : ‖gramSchmidt ℝ v j‖ = 0
  · rw [hz]
    exact norm_nonneg _
  · have hp : 0 < ‖gramSchmidt ℝ v j‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

/-- Standard square-summable coefficient space, distinct from physical Q coordinates. -/
abbrev Coefficients := lp (fun _ : ℕ => ℝ) 2

def coordinateUnit (j : ℕ) : Coefficients := lp.single 2 j 1

theorem coordinateUnit_norm (j : ℕ) : ‖coordinateUnit j‖ = 1 := by
  simpa only [coordinateUnit, norm_one] using
    (lp.norm_single (E := fun _ : ℕ => ℝ) (by norm_num : (0 : ENNReal) < 2) j 1)

/-- Any diagonal matrix entry of a bounded operator is bounded by its operator norm. -/
theorem diagonal_abs_le_opNorm (T : Coefficients →L[ℝ] Coefficients) (j : ℕ) :
    |(T (coordinateUnit j)) j| ≤ ‖T‖ := by
  calc
    _ ≤ ‖T (coordinateUnit j)‖ := by
      simpa only [Real.norm_eq_abs] using
        (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
          (T (coordinateUnit j)) j)
    _ ≤ ‖T‖ * ‖coordinateUnit j‖ := T.le_opNorm _
    _ = _ := by rw [coordinateUnit_norm, mul_one]

/-- Diverging diagonal entries prohibit a bounded operator realizing the columns. -/
theorem no_bounded_matrix_columns (A : ℕ → ℕ → ℝ)
    (hA : Tendsto (fun j => A j j) atTop atTop) :
    ¬ ∃ T : Coefficients →L[ℝ] Coefficients,
      ∀ i j, (T (coordinateUnit j)) i = A i j := by
  rintro ⟨T, hT⟩
  obtain ⟨j, hj⟩ := (hA.eventually (eventually_gt_atTop ‖T‖)).exists
  have hb := diagonal_abs_le_opNorm T j
  rw [hT j j] at hb
  have ha := le_abs_self (A j j)
  linarith

end RiemannResearch.Analysis.TriangularCoefficientBounds

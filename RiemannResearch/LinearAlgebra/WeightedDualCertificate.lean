import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Exact finite weighted dual completion and its lower-bound consequence. -/
open scoped BigOperators
namespace RiemannResearch.LinearAlgebra
noncomputable section

/-- Exact completion of every weighted square; duality cancels the signed mixed sum. -/
theorem weighted_error_dual_exact {ι : Type*} [Fintype ι]
    (w z f : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hz : (∑ i, z i * f i) = 0) :
    (∑ i, w i * (1-f i)^2) =
      (∑ i, (2*z i-(z i)^2/w i)) +
        ∑ i, w i*(1-f i-z i/w i)^2 := by
  have h (i : ι) : w i*(1-f i)^2 =
      ((2*z i-(z i)^2/w i) - 2*(z i*f i)) +
        w i*(1-f i-z i/w i)^2 := by
    field_simp [ne_of_gt (hw i)] <;> ring
  calc
    _ = ∑ i, (((2*z i-(z i)^2/w i) - 2*(z i*f i)) +
        w i*(1-f i-z i/w i)^2) := by
      apply Finset.sum_congr rfl
      intro i _
      exact h i
    _ = ((∑ i, (2*z i-(z i)^2/w i)) - 2*(∑ i, z i*f i)) +
        ∑ i, w i*(1-f i-z i/w i)^2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    _ = _ := by rw [hz, mul_zero, sub_zero]

/-- The exact dual identity implies a lower bound because every remaining square is nonnegative. -/
theorem weighted_error_lower_of_dual {ι : Type*} [Fintype ι]
    (w z f : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hz : (∑ i, z i * f i) = 0) :
    (∑ i, (2*z i-(z i)^2/w i)) ≤ ∑ i, w i*(1-f i)^2 := by
  rw [weighted_error_dual_exact w z f hw hz]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ =>
    mul_nonneg (le_of_lt (hw i)) (sq_nonneg _))

end
end RiemannResearch.LinearAlgebra

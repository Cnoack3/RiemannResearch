import RiemannResearch.LinearAlgebra.WeightedFiniteQuotient
import Mathlib.Tactic.Linarith

/-!
# Exact signed mixed covariance on a finite weighted fiber

Source: user-provided `RH_Controlled_Conductor_Schur_2026-09-10.md`,
equations (3.4)--(3.5). The weights are arbitrary normalized real weights;
positivity is only needed when interpreting the diagonal as a variance.
-/

open scoped BigOperators
namespace RiemannResearch.LinearAlgebra.WeightedFiniteQuotient
noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Centering at the actual normalized mean has exactly zero weighted mass. -/
theorem normalized_centered_sum (w x : ι → ℝ) (hw : (∑ i, w i) = 1) :
    (∑ i, w i * (x i - ∑ j, w j * x j)) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw, one_mul,
    sub_self]

/-- The mixed covariance retains both signed cross contributions. -/
theorem normalized_centered_product (w x y : ι → ℝ)
    (hw : (∑ i, w i) = 1) :
    (∑ i, w i * (x i - ∑ j, w j * x j) * (y i - ∑ j, w j * y j)) =
      (∑ i, w i * x i * y i) - (∑ i, w i * x i) * (∑ i, w i * y i) := by
  calc
    _ = ∑ i, (w i * x i * y i - (w i * x i) * (∑ j, w j * y j) -
        (∑ j, w j * x j) * (w i * y i) +
        w i * ((∑ j, w j * x j) * (∑ j, w j * y j))) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul, ← Finset.mul_sum, hw, one_mul]
      ring

/-- Pairwise signed covariance; no independence assumption enters. -/
theorem normalized_centered_product_pairwise (w x y : ι → ℝ)
    (hw : (∑ i, w i) = 1) :
    (∑ i, w i * (x i - ∑ j, w j * x j) * (y i - ∑ j, w j * y j)) =
      (1 / 2 : ℝ) * ∑ i, ∑ j,
        w i * w j * (x i - x j) * (y i - y j) := by
  rw [normalized_centered_product w x y hw]
  have hpair : (∑ i, ∑ j, w i * w j * (x i - x j) * (y i - y j)) =
      2 * ((∑ i, w i * x i * y i) - (∑ i, w i * x i) * (∑ i, w i * y i)) := by
    calc
      _ = ∑ i, ∑ j,
          ((w i * x i * y i) * w j - (w i * x i) * (w j * y j) -
            (w i * y i) * (w j * x j) + w i * (w j * x j * y j)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.sum_mul, ← Finset.mul_sum, hw, one_mul, mul_one]
        ring
  rw [hpair]
  ring

end
end RiemannResearch.LinearAlgebra.WeightedFiniteQuotient

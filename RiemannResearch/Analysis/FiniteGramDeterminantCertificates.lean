import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.Analysis.FiniteHilbertConstraints
import RiemannResearch.Analysis.FiniteGramCapacity
import RiemannResearch.LinearAlgebra.OptionSchurDeterminant
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sharp determinant certificates for finite Hilbert interpolation

Source: user-requested fifth Ramanujan dual continuation, 24 October 2026.
The ordinary bordered Schur determinant is interpreted as an exact norm
budget certificate for actual finite observations. Its sign characterizes
attainable budgets, and its value at a feasible vector retains the complete
squared displacement from the unique minimum. No inverse is postulated.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteGramDeterminantCertificates
open FiniteHilbertGram FiniteHilbertConstraints FiniteGramCapacity
open RiemannResearch.LinearAlgebra

variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The none coordinate contains the proposed squared-norm budget. -/
def bordered (v : ι → H) (b : ι → ℝ) (s : ℝ) : Matrix (Option ι) (Option ι) ℝ
  | none, none => s
  | none, some j => b j
  | some i, none => b i
  | some i, some j => gramMatrix v i j

/-- The complete bordered determinant retains the full inverse Gram quadratic. -/
theorem bordered_det {v : ι → H} (hv : LinearIndependent ℝ v) (b : ι → ℝ) (s : ℝ) :
    (bordered v b s).det = (gramMatrix v).det * (s - capacity hv b) := by
  have hA : IsUnit ((bordered v b s).submatrix some some).det := by
    change IsUnit (gramMatrix v).det
    exact isUnit_iff_ne_zero.mpr (ne_of_gt (gramMatrix_det_pos hv))
  have h := det_option_schur (bordered v b s) hA
  change (bordered v b s).det = (gramMatrix v).det *
    (s - dotProduct b ((gramMatrix v)⁻¹.mulVec b)) at h
  rw [gramMatrix_inverseSource hv] at h
  have hp : dotProduct b (inverseSource hv b) = capacity hv b := by
    unfold dotProduct capacity
    apply Finset.sum_congr rfl
    intro i _
    ring
  rwa [hp] at h

theorem bordered_det_ratio {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (s : ℝ) :
    (bordered v b s).det / (gramMatrix v).det = s - capacity hv b := by
  rw [bordered_det hv b s]
  exact mul_div_cancel_left₀ _ (ne_of_gt (gramMatrix_det_pos hv))

theorem bordered_det_nonneg_iff {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (s : ℝ) :
    0 ≤ (bordered v b s).det ↔ capacity hv b ≤ s := by
  rw [bordered_det hv b s, mul_nonneg_iff_of_pos_left (gramMatrix_det_pos hv), sub_nonneg]

theorem bordered_det_pos_iff {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (s : ℝ) :
    0 < (bordered v b s).det ↔ capacity hv b < s := by
  rw [bordered_det hv b s, mul_pos_iff_of_pos_left (gramMatrix_det_pos hv), sub_pos]

theorem bordered_det_zero_iff {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (s : ℝ) :
    (bordered v b s).det = 0 ↔ s = capacity hv b := by
  rw [bordered_det hv b s, mul_eq_zero]
  simp only [ne_of_gt (gramMatrix_det_pos hv), false_or, sub_eq_zero]

/-- Nonnegativity is exactly the existence of a feasible vector within the budget. -/
theorem bounded_interpolation_iff_det_nonneg {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (s : ℝ) :
    (∃ x : H, (∀ i, inner ℝ (v i) x = b i) ∧ ‖x‖ ^ 2 ≤ s) ↔
      0 ≤ (bordered v b s).det := by
  rw [bordered_det_nonneg_iff hv b s]
  constructor
  · rintro ⟨x, hx, hs⟩
    rw [capacity_eq_norm_sq]
    exact (minimumVector_minimizes hv b x hx).trans hs
  · intro hs
    refine ⟨minimumVector hv b, minimumVector_observation hv b, ?_⟩
    rwa [← capacity_eq_norm_sq]

/-- At every feasible vector, the normalized determinant is its complete excess energy. -/
theorem feasible_determinant_completion {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (x : H) (hx : ∀ i, inner ℝ (v i) x = b i) :
    (bordered v b (‖x‖ ^ 2)).det / (gramMatrix v).det =
      ‖x - minimumVector hv b‖ ^ 2 := by
  rw [bordered_det_ratio hv b]
  have h := feasible_norm_sq_completion hv b x hx
  rw [← capacity_eq_norm_sq] at h
  linarith

/-- A singular budget matrix identifies the unique feasible minimum vector. -/
theorem feasible_determinant_zero_iff {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (x : H) (hx : ∀ i, inner ℝ (v i) x = b i) :
    (bordered v b (‖x‖ ^ 2)).det = 0 ↔ x = minimumVector hv b := by
  rw [bordered_det_zero_iff hv b, capacity_eq_norm_sq]
  exact feasible_norm_sq_eq_iff hv b x hx

/-- The all-real determinant polynomial records the same full minimum cost. -/
theorem source_determinant_polynomial {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (z : ℝ) :
    (gramMatrix v + z • Matrix.vecMulVec b b).det / (gramMatrix v).det =
      1 + z * capacity hv b := by
  rw [gramMatrix_det_update hv b z]
  exact mul_div_cancel_left₀ _ (ne_of_gt (gramMatrix_det_pos hv))

end RiemannResearch.Analysis.FiniteGramDeterminantCertificates

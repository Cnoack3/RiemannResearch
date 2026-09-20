import RiemannResearch.Probability.FiniteDeterminantalLaw

/-!
# Finite determinantal generating functions

Source: Lyons, Determinantal Probability Measures, arXiv:math/0204325,
Sections 5 and 8, for the configuration-law terminology and generating-function
statement. The proof applies determinant row multilinearity to the explicit
configuration weights already constructed in FiniteDeterminantalLaw.
-/

noncomputable section
open Matrix
open scoped BigOperators Classical
namespace RiemannResearch.Probability.DPP
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The complete multivariate generating polynomial of the exact determinant
weights, without symmetry or positivity hypotheses. -/
theorem sum_exactWeight_generating (K : Matrix ι ι ℝ) (z : ι → ℝ) :
    (∑ S : Finset ι, (∏ i : ι, if i ∈ S then z i else 1) * exactWeight K S) =
      (Matrix.diagonal z * K + (1 - K)).det := by
  let A := Matrix.diagonal z * K
  let B : Matrix ι ι ℝ := 1 - K
  have hterm (S : Finset ι) :
      Matrix.det (Matrix.of (S.piecewise A.row B.row)) =
        (∏ i : ι, if i ∈ S then z i else 1) * exactWeight K S := by
    have he : Matrix.of (S.piecewise A.row B.row) =
        Matrix.diagonal (fun i => if i ∈ S then z i else 1) * mixedRows K S := by
      ext i j
      by_cases hi : i ∈ S <;>
        simp [A, B, mixedRows, Finset.piecewise, Matrix.diagonal_mul, hi]
    rw [he, Matrix.det_mul, Matrix.det_diagonal]
    rfl
  have h := (Matrix.detRowAlternating (R := ℝ) (n := ι)).map_add_univ A.row B.row
  change Matrix.det (A + B) =
    ∑ S : Finset ι, Matrix.det (Matrix.of (S.piecewise A.row B.row)) at h
  calc
    _ = ∑ S : Finset ι, Matrix.det (Matrix.of (S.piecewise A.row B.row)) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact (hterm S).symm
    _ = (A + B).det := h.symm
    _ = _ := rfl

/-- The same polynomial is the probability generating function of the actual
finite determinantal probability mass function. -/
theorem finiteLaw_generating (K : Matrix ι ι ℝ)
    (hpos : ∀ S, 0 ≤ exactWeight K S) (z : ι → ℝ) :
    (∑ S : Finset ι, (∏ i : ι, if i ∈ S then z i else 1) *
      ((finiteLaw K hpos) S).toReal) =
      (Matrix.diagonal z * K + (1 - K)).det := by
  have hp (S : Finset ι) : ((finiteLaw K hpos) S).toReal = exactWeight K S := by
    change (ENNReal.ofReal (exactWeight K S)).toReal = _
    exact ENNReal.toReal_ofReal (hpos S)
  simp_rw [hp]
  exact sum_exactWeight_generating K z

/-- The univariate count generating function, with its determinant endpoint. -/
theorem finiteLaw_count_generating (K : Matrix ι ι ℝ)
    (hpos : ∀ S, 0 ≤ exactWeight K S) (z : ℝ) :
    (∑ S : Finset ι, z ^ S.card * ((finiteLaw K hpos) S).toReal) =
      (Matrix.diagonal (fun _ : ι => z) * K + (1 - K)).det := by
  have hp (S : Finset ι) :
      (∏ i : ι, if i ∈ S then z else 1) = z ^ S.card := by
    rw [← Finset.prod_filter]
    simp
  simpa only [hp] using finiteLaw_generating K hpos (fun _ => z)

end RiemannResearch.Probability.DPP

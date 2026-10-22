import RiemannResearch.RH.IntegerDPPGramDeterminant
import RiemannResearch.RH.IntegerDPPWindowGenerating

/-!
# Multivariate Gram determinant formulas for the arithmetic DPP

Source: the user-provided DPP/Fredholm conversation, 20 September 2026.
The finite determinant ratio below represents the actual expectation of a
finite multiplicative statistic, with a separate weight at each observed site.
The full-Gram computation records why the unlocalized finite-rank determinant
vanishes at z = 1 irrespective of the RH vacancy question. No infinite-dimensional
Fredholm determinant is introduced here.
-/

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Classical

namespace RiemannResearch.RH.Pareto.IntegerDPP

/-- Full Pareto Gram contribution of finitely many separately weighted sites. -/
def weightedWindowGram (N m : ℕ) (e : Fin m → ℕ) (a : Fin m → ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  (windowFeatures N m e).transpose * Matrix.diagonal a * windowFeatures N m e

theorem weighted_window_determinant_eq_gram_ratio
    (N m : ℕ) (e : Fin m → ℕ) (a : Fin m → ℝ) :
    (1 - Matrix.diagonal a *
      Matrix.of (fun i j => integerKernel N (e i) (e j))).det =
      (fullGram N - weightedWindowGram N m e a).det / (fullGram N).det := by
  have h := Matrix.det_sub_mul_div (fullGram N)
    (isUnit_iff_ne_zero.mpr (ne_of_gt (fullGram_det_pos N)))
    (windowFeatures N m e).transpose
    (Matrix.diagonal a * windowFeatures N m e)
  rw [integerKernel_window_matrix]
  simpa only [weightedWindowGram, Matrix.mul_assoc] using h.symm

/-- Multivariate finite multiplicative expectation as an actual arithmetic
Gram determinant ratio. There is no independence assumption on the sites. -/
theorem integerLaw_multiplicative_gram_determinant
    (N m : ℕ) (e : Fin m ↪ ℕ) (a : Fin m → ℝ) :
    (∫ x, ∏ i : Fin m, if x (e i) = true then 1 - a i else 1 ∂integerLaw N) =
      (fullGram N - weightedWindowGram N m e a).det / (fullGram N).det := by
  rw [integerLaw_window_generating]
  have hm :
      Matrix.diagonal (fun i => 1 - a i) *
          Matrix.of (fun i j => integerKernel N (e i) (e j)) +
        (1 - Matrix.of (fun i j => integerKernel N (e i) (e j))) =
      1 - Matrix.diagonal a *
          Matrix.of (fun i j => integerKernel N (e i) (e j)) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_mul]
    ring
  rw [hm]
  exact weighted_window_determinant_eq_gram_ratio N m e a

/-- The full finite-rank characteristic factor. This is the algebraic
finite-rank Fredholm computation; it is not a localized vacancy probability. -/
theorem full_gram_determinant_polynomial (N : ℕ) (z : ℝ) :
    (fullGram N - z • fullGram N).det / (fullGram N).det = (1 - z) ^ N := by
  have hm : fullGram N - z • fullGram N = (1 - z) • fullGram N := by
    rw [sub_smul, one_smul]
  rw [hm, Matrix.det_smul]
  simp only [Fintype.card_fin]
  exact mul_div_cancel_right₀ _ (ne_of_gt (fullGram_det_pos N))

/-- Positive rank makes the full determinant zero at one with no RH assumption. -/
theorem full_gram_determinant_at_one (N : ℕ) (hN : 0 < N) :
    (fullGram N - fullGram N).det / (fullGram N).det = 0 := by
  have h := full_gram_determinant_polynomial N 1
  simpa only [one_smul, sub_self, zero_pow (Nat.ne_of_gt hN)] using h

end RiemannResearch.RH.Pareto.IntegerDPP

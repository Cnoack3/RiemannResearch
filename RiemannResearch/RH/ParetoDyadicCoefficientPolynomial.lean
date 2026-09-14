import RiemannResearch.RH.ParetoDilationLogMoments
import RiemannResearch.RH.ParetoDyadicMomentFeasibility
import RiemannResearch.RH.ParetoResidueLogMean

/-!
# Actual dyadic Laguerre coefficient matrix

Source: the user-provided Ramanujan--Laguerre continuation, Section 6.
The matrix is constructed from actual ordinary moments and the proved dilation
law. Its lower triangularity, exact nonzero diagonal, and polynomial evaluation
identity discharge DyadicCoefficientPolynomialProvider without extra hypotheses.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.RamanujanLaguerre
open RiemannResearch.Analysis
open RiemannResearch.Analysis.DyadicMomentEvaluation

private theorem extend_polynomial_sum {n j : ℕ} (hj : j < n) (f : ℕ → ℝ)
    (hf : ∀ i, j < i → f i = 0) :
    (∑ i ∈ Finset.range (j + 1), f i) = ∑ i : Fin n, f i := by
  rw [Fin.sum_univ_eq_sum_range]
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt hj))
  intro i hi hnot
  apply hf
  have hni : ¬ i < j + 1 := by simpa using hnot
  omega

private theorem laguerreCoefficient_eq_zero_above {j k : ℕ} (hjk : j < k) :
    laguerreCoefficient j k = 0 := by
  simp [laguerreCoefficient, Nat.choose_eq_zero_of_lt hjk]

private theorem coefficient_eq_finite_moments {n : ℕ} (F : ℕ → ℝ)
    (hI : AllMomentsIntegrable F) (j : Fin n) :
    coefficient F j = ∑ k : Fin n, laguerreCoefficient j k * ordinaryMoment F k := by
  rw [coefficient_eq_momentTransform F hI]
  apply extend_polynomial_sum j.isLt
  intro k hk
  rw [laguerreCoefficient_eq_zero_above hk, zero_mul]

private theorem dyadic_moment_finite {n : ℕ} (k : Fin n) (v : ℕ) :
    ordinaryMoment (dyadicPacket v) k = ∑ i : Fin n,
      ((k : ℕ).choose i : ℝ) * Real.log 2 ^ (i : ℕ) *
        ordinaryMoment (residue 2) ((k : ℕ) - i) * (v : ℝ) ^ (i : ℕ) := by
  have hB : AllMomentsIntegrable (residue 2) :=
    allMomentsIntegrable_of_bounded (fun k => residue_abs_le 2 k (by norm_num))
  rw [dyadicPacket, ordinaryMoment_dilation (by simp [residue]) hB
    (2 ^ v) (pow_pos (by norm_num) _) k]
  rw [show Real.log ((2 ^ v : ℕ) : ℝ) = (v : ℝ) * Real.log 2 by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]]
  calc
    _ = ∑ i ∈ Finset.range ((k : ℕ) + 1),
        ((k : ℕ).choose i : ℝ) * Real.log 2 ^ i *
          ordinaryMoment (residue 2) ((k : ℕ) - i) * (v : ℝ) ^ i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [mul_pow]
      ring
    _ = _ := by
      apply extend_polynomial_sum k.isLt
      intro i hi
      simp [Nat.choose_eq_zero_of_lt hi]

def dyadicCoefficientMatrix (K : ℕ) : Matrix (Fin (K + 1)) (Fin (K + 1)) ℝ :=
  fun j i => ∑ k : Fin (K + 1), laguerreCoefficient j k *
    ((k : ℕ).choose i : ℝ) * Real.log 2 ^ (i : ℕ) *
      ordinaryMoment (residue 2) ((k : ℕ) - i)

theorem dyadicCoefficientMatrix_lower (K : ℕ) :
    (dyadicCoefficientMatrix K).IsLowerTriangular := by
  intro j i hji
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hjk : (j : ℕ) < k
  · simp [laguerreCoefficient_eq_zero_above hjk]
  · have hki : (k : ℕ) < i := by
      have hji' : (j : ℕ) < i := hji
      omega
    simp [Nat.choose_eq_zero_of_lt hki]

theorem dyadicCoefficientMatrix_diagonal (K : ℕ) (j : Fin (K + 1)) :
    dyadicCoefficientMatrix K j j = dyadicLeading j := by
  unfold dyadicCoefficientMatrix
  rw [Finset.sum_eq_single j]
  · have hmean : ordinaryMoment (residue 2) 0 = Real.log 2 := by
      rw [ordinaryMoment_zero_of_bounded
        (fun k => residue_abs_le 2 k (by norm_num)), paretoMean_residue 2 (by norm_num)]
      norm_num
    simp only [Nat.choose_self, Nat.cast_one, mul_one, Nat.sub_self, hmean,
      laguerreCoefficient_diagonal]
    unfold dyadicLeading
    rw [neg_eq_neg_one_mul (Real.log 2), mul_pow]
    ring
  · intro k hk hkj
    rcases lt_or_gt_of_ne hkj with hlt | hgt
    · simp [Nat.choose_eq_zero_of_lt (show (k : ℕ) < j from hlt)]
    · simp [laguerreCoefficient_eq_zero_above (show (j : ℕ) < k from hgt)]
  · simp

theorem dyadicCoefficientMatrix_evaluation (K : ℕ) (j v : Fin (K + 1)) :
    coefficient (dyadicPacket v) j =
      ∑ i : Fin (K + 1), dyadicCoefficientMatrix K j i * (v : ℝ) ^ (i : ℕ) := by
  have hI : AllMomentsIntegrable (dyadicPacket v) := by
    apply allMomentsIntegrable_of_bounded
      (dilation_abs_le (fun k => residue_abs_le 2 k (by norm_num)) (2 ^ (v : ℕ)))
  rw [coefficient_eq_finite_moments (dyadicPacket v) hI j]
  simp_rw [dyadic_moment_finite, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [dyadicCoefficientMatrix, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem dyadicCoefficientPolynomialProvider : DyadicCoefficientPolynomialProvider := by
  intro K
  exact ⟨dyadicCoefficientMatrix K, dyadicCoefficientMatrix_lower K,
    dyadicCoefficientMatrix_diagonal K, dyadicCoefficientMatrix_evaluation K⟩

end RiemannResearch.RH.Pareto.RamanujanLaguerre

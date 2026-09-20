import RiemannResearch.RH.IntegerDPPMultiplicativeGram

/-!
# Symmetric finite damping of the arithmetic DPP kernel

Source: the user-provided DPP/Fredholm conversation, 20 September 2026.
For nonnegative site weights this identifies the symmetric square-root-damped
kernel determinant with the actual multiplicative expectation. This is a finite
matrix identity; an infinite trace-class operator is not postulated.
-/

noncomputable section
open Matrix MeasureTheory
open scoped BigOperators Classical

namespace RiemannResearch.RH.Pareto.IntegerDPP

theorem symmetric_damping_determinant_eq_gram_ratio
    (N m : ℕ) (e : Fin m → ℕ) (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (1 - Matrix.diagonal (fun i => Real.sqrt (a i)) *
      Matrix.of (fun i j => integerKernel N (e i) (e j)) *
        Matrix.diagonal (fun i => Real.sqrt (a i))).det =
      (fullGram N - weightedWindowGram N m e a).det / (fullGram N).det := by
  let D : Matrix (Fin m) (Fin m) ℝ := Matrix.diagonal (fun i => Real.sqrt (a i))
  let Q : Matrix (Fin m) (Fin m) ℝ :=
    Matrix.of (fun i j => integerKernel N (e i) (e j))
  have hsq : D * D = Matrix.diagonal a := by
    ext i j
    by_cases hij : i = j
    · subst j
      simpa [D, Matrix.diagonal_mul, pow_two] using Real.sq_sqrt (ha i)
    · simp [D, Matrix.diagonal_mul, Matrix.diagonal_apply, hij]
  have h := Matrix.det_one_sub_mul_comm D (D * Q)
  rw [← Matrix.mul_assoc, hsq] at h
  change (1 - D * Q * D).det = _
  rw [← h]
  exact weighted_window_determinant_eq_gram_ratio N m e a

theorem integerLaw_symmetric_damping_expectation
    (N m : ℕ) (e : Fin m ↪ ℕ) (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∫ x, ∏ i : Fin m, if x (e i) = true then 1 - a i else 1 ∂integerLaw N) =
      (1 - Matrix.diagonal (fun i => Real.sqrt (a i)) *
        Matrix.of (fun i j => integerKernel N (e i) (e j)) *
          Matrix.diagonal (fun i => Real.sqrt (a i))).det := by
  rw [integerLaw_multiplicative_gram_determinant,
    symmetric_damping_determinant_eq_gram_ratio N m e a ha]

/-- Finite square-root damping of the genuine limiting arithmetic law. -/
theorem limitingLaw_symmetric_damping_expectation
    (m : ℕ) (e : Fin m ↪ ℕ) (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∫ x, ∏ i : Fin m, if x (e i) = true then 1 - a i else 1 ∂limitingLaw) =
      (1 - Matrix.diagonal (fun i => Real.sqrt (a i)) *
        Matrix.of (fun i j => limitingKernel (e i) (e j)) *
          Matrix.diagonal (fun i => Real.sqrt (a i))).det := by
  let D : Matrix (Fin m) (Fin m) ℝ := Matrix.diagonal (fun i => Real.sqrt (a i))
  let Q : Matrix (Fin m) (Fin m) ℝ :=
    Matrix.of (fun i j => limitingKernel (e i) (e j))
  have hsq : D * D = Matrix.diagonal a := by
    ext i j
    by_cases hij : i = j
    · subst j
      simpa [D, Matrix.diagonal_mul, pow_two] using Real.sq_sqrt (ha i)
    · simp [D, Matrix.diagonal_mul, Matrix.diagonal_apply, hij]
  rw [limitingLaw_window_generating]
  have hm : Matrix.diagonal (fun i => 1 - a i) * Q + (1 - Q) =
      1 - Matrix.diagonal a * Q := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_mul]
    ring
  change (Matrix.diagonal (fun i => 1 - a i) * Q + (1 - Q)).det =
    (1 - D * Q * D).det
  rw [hm]
  have h := Matrix.det_one_sub_mul_comm D (D * Q)
  rw [← Matrix.mul_assoc, hsq] at h
  exact h

end RiemannResearch.RH.Pareto.IntegerDPP

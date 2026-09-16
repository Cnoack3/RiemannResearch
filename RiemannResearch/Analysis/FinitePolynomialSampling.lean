import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Finite polynomial sampling cannot control unrestricted coefficients

Source: user-provided `V_Zeta_Vector_Spaces_Research_2026-09-16.md`, §4.
This file formalizes the finite algebra behind the null-polynomial obstruction.
The finite sample indices preserve multiplicities, even when their phases agree.
Specializing the phases to `2^(I*t)` turns a polynomial with `P.eval 0 = 0`
into a Dirichlet polynomial on positive powers of 2. No statement here assumes
RH or claims a formalized zero-counting asymptotic.
-/

noncomputable section
open scoped BigOperators
namespace Polynomial

def coefficientSquareEnergy (P : Polynomial ℂ) : ℝ :=
  ∑ k ∈ P.support, ‖P.coeff k‖ ^ 2

def sampledSquareEnergy {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (P : Polynomial ℂ) : ℝ := ∑ i ∈ s, ‖P.eval (z i)‖ ^ 2

/-- The factor `X` excludes the constant coefficient. -/
theorem exists_nonzero_vanishing_with_eval_zero (s : Finset ℂ) :
    ∃ P : Polynomial ℂ, P ≠ 0 ∧ P.eval 0 = 0 ∧
      ∀ z ∈ s, P.eval z = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨X, X_ne_zero, by simp, by simp⟩
  | @insert a s ha ih =>
    rcases ih with ⟨P, hP, hP0, hroots⟩
    have hf : (X - C a : Polynomial ℂ) ≠ 0 := by
      intro h
      have hc := congrArg (fun Q : Polynomial ℂ => Q.coeff 1) h
      simp at hc
    refine ⟨(X - C a) * P, mul_ne_zero hf hP, ?_, ?_⟩
    · simp [hP0]
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · simp
      · simp [hroots z hz]

theorem coefficientSquareEnergy_pos {P : Polynomial ℂ} (hP : P ≠ 0) :
    0 < coefficientSquareEnergy P := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, P.coeff k ≠ 0 := by
    by_contra h
    apply hP
    ext k
    simpa using (not_not.mp ((not_exists.mp h) k))
  apply Finset.sum_pos'
  · intro k hk
    exact sq_nonneg _
  · refine ⟨k, ?_, ?_⟩
    · simpa only [Polynomial.mem_support_iff] using hk
    · exact sq_pos_of_pos (norm_pos_iff.mpr hk)

theorem exists_zero_sample_energy {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    ∃ P : Polynomial ℂ, P ≠ 0 ∧ P.eval 0 = 0 ∧
      sampledSquareEnergy s z P = 0 ∧ 0 < coefficientSquareEnergy P := by
  classical
  rcases exists_nonzero_vanishing_with_eval_zero (s.image z) with
    ⟨P, hP, hP0, hroots⟩
  refine ⟨P, hP, hP0, ?_, coefficientSquareEnergy_pos hP⟩
  unfold sampledSquareEnergy
  apply Finset.sum_eq_zero
  intro i hi
  simp [hroots (z i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)]

theorem no_positive_lower_sampling_bound {ι : Type*} (s : Finset ι)
    (z : ι → ℂ) (A : ℝ) (hA : 0 < A) :
    ¬ ∀ P : Polynomial ℂ, P.eval 0 = 0 →
      A * coefficientSquareEnergy P ≤ sampledSquareEnergy s z P := by
  intro h
  rcases exists_zero_sample_energy s z with ⟨P, hP, hP0, hz, hE⟩
  have hb := h P hP0
  rw [hz] at hb
  exact (not_le_of_gt (mul_pos hA hE)) hb

/-- Every unrestricted centered lower bound must pay at least the sample density. -/
theorem centered_lower_bound_requires_sample_density {ι : Type*}
    (s : Finset ι) (z : ι → ℂ) (T C : ℝ) (hT : 0 < T)
    (hbound : ∀ P : Polynomial ℂ, P.eval 0 = 0 →
      -(C * coefficientSquareEnergy P) ≤
        (sampledSquareEnergy s z P - (s.card : ℝ) * coefficientSquareEnergy P) / T) :
    (s.card : ℝ) / T ≤ C := by
  rcases exists_zero_sample_energy s z with ⟨P, hP, hP0, hz, hE⟩
  apply (div_le_iff₀ hT).mpr
  apply (mul_le_mul_iff_right₀ hE).mp
  have hb := hbound P hP0
  rw [hz] at hb
  have hb' := (le_div_iff₀ hT).mp hb
  nlinarith

/-- This corollary isolates the exact counting input needed for growing-height samples. -/
theorem no_uniform_centered_lower_bound_of_unbounded_density {ι : Type*}
    (s : ℕ → Finset ι) (z : ℕ → ι → ℂ) (T : ℕ → ℝ)
    (hT : ∀ n, 0 < T n)
    (hdensity : ∀ C : ℝ, ∃ n, C < ((s n).card : ℝ) / T n) :
    ¬ ∃ C : ℝ, ∀ n (P : Polynomial ℂ), P.eval 0 = 0 →
      -(C * coefficientSquareEnergy P) ≤
        (sampledSquareEnergy (s n) (z n) P -
          ((s n).card : ℝ) * coefficientSquareEnergy P) / T n := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := hdensity C
  exact (not_lt_of_ge
    (centered_lower_bound_requires_sample_density (s n) (z n) (T n) C
      (hT n) (hC n))) hn

end Polynomial

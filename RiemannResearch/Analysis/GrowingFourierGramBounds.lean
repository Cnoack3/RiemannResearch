import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite Fourier Gram error bounds

Source: user-provided manuscript `Prime_Phases_Agenda_Proof_Attempts.tex`,
Theorem `growing-phase-gram` (entrywise-error part of the proof).

The uniform rational-character estimate, the weighted Schur estimate for
the von Mangoldt covariance matrix, and all zeta-zero providers are explicit
external analytic obligations. The results here prove the finite support
loss exactly, without presuming any of those providers.
-/

open scoped BigOperators

namespace RiemannResearch.Fourier

variable {ι : Type*}

/-- Exact complex Gram-error pairing over a finite dictionary. -/
def finiteGramErrorPairing (s : Finset ι) (a : ι → ℂ) (R : ι → ι → ℂ) : ℂ :=
  ∑ i ∈ s, ∑ j ∈ s, star (a i) * R i j * a j

/-- The entrywise error has a sharp elementary Wiener-square loss. -/
theorem finiteGramErrorPairing_norm_le_wiener_sq
    (s : Finset ι) (a : ι → ℂ) (R : ι → ι → ℂ) (η : ℝ)
    (hR : ∀ i ∈ s, ∀ j ∈ s, ‖R i j‖ ≤ η) :
    ‖finiteGramErrorPairing s a R‖ ≤ η * (∑ i ∈ s, ‖a i‖) ^ 2 := by
  unfold finiteGramErrorPairing
  calc
    _ ≤ ∑ i ∈ s, ‖∑ j ∈ s, star (a i) * R i j * a j‖ := norm_sum_le s _
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, ‖star (a i) * R i j * a j‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_sum_le s _
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * η * ‖a j‖ := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      simp only [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hR i hi j hj) (norm_nonneg _)) (norm_nonneg _)
    _ = η * (∑ i ∈ s, ‖a i‖) ^ 2 := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      ring

/-- Consequently the support loss is exactly cardinality in the squared
    Euclidean coefficient norm. No spectral or zeta-specific assumptions enter. -/
theorem finiteGramErrorPairing_norm_le_card_l2
    (s : Finset ι) (a : ι → ℂ) (R : ι → ι → ℂ) (η : ℝ)
    (hη : 0 ≤ η) (hR : ∀ i ∈ s, ∀ j ∈ s, ‖R i j‖ ≤ η) :
    ‖finiteGramErrorPairing s a R‖ ≤
      η * (s.card : ℝ) * (∑ i ∈ s, ‖a i‖ ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖a i‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  calc
    _ ≤ η * (∑ i ∈ s, ‖a i‖) ^ 2 :=
      finiteGramErrorPairing_norm_le_wiener_sq s a R η hR
    _ ≤ η * ((∑ i ∈ s, ‖a i‖ ^ 2) * (s.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hcs hη
    _ = _ := by ring

end RiemannResearch.Fourier

import RiemannResearch.Analysis.GrowingFourierGramBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A finite weighted Schur test for complex quadratic pairings

Source: user manuscript `Prime_Phases_Agenda_Proof_Attempts.tex`, weighted
Schur proof of Theorem `growing-phase-gram`. This generic test needs no
analytic asymptotic input. Its row bounds and positive weights are explicit.
-/

open scoped BigOperators

namespace RiemannResearch.Fourier

private theorem weighted_young (x y b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    2 * x * y ≤ x ^ 2 * c / b + y ^ 2 * b / c := by
  have hsq : 2 * x * y * (b * c) ≤ x ^ 2 * c ^ 2 + y ^ 2 * b ^ 2 := by
    nlinarith [sq_nonneg (x * c - y * b)]
  calc
    _ ≤ (x ^ 2 * c ^ 2 + y ^ 2 * b ^ 2) / (b * c) :=
      (le_div_iff₀ (mul_pos hb hc)).mpr hsq
    _ = _ := by field_simp [hb.ne', hc.ne'] <;> ring

/-- Positive weighted absolute row bounds control the exact complex quadratic
    pairing, with the full finite dictionary retained. -/
theorem finiteGramErrorPairing_norm_le_weighted_schur
    {ι : Type*} (s : Finset ι) (a : ι → ℂ) (R : ι → ι → ℂ)
    (b : ι → ℝ) (A : ℝ) (hb : ∀ i ∈ s, 0 < b i)
    (hsym : ∀ i ∈ s, ∀ j ∈ s, ‖R i j‖ = ‖R j i‖)
    (hrow : ∀ i ∈ s, (∑ j ∈ s, ‖R i j‖ * b j) ≤ A * b i) :
    ‖finiteGramErrorPairing s a R‖ ≤ A * (∑ i ∈ s, ‖a i‖ ^ 2) := by
  let Q : ℝ := ∑ i ∈ s, ∑ j ∈ s, ‖R i j‖ * ‖a i‖ * ‖a j‖
  let U : ℝ := ∑ i ∈ s, ∑ j ∈ s, ‖R i j‖ * (‖a i‖ ^ 2 * b j / b i)
  let V : ℝ := ∑ i ∈ s, ∑ j ∈ s, ‖R i j‖ * (‖a j‖ ^ 2 * b i / b j)
  have hnorm : ‖finiteGramErrorPairing s a R‖ ≤ Q := by
    unfold finiteGramErrorPairing Q
    calc
      _ ≤ ∑ i ∈ s, ‖∑ j ∈ s, star (a i) * R i j * a j‖ := norm_sum_le s _
      _ ≤ ∑ i ∈ s, ∑ j ∈ s, ‖star (a i) * R i j * a j‖ := by
        exact Finset.sum_le_sum (fun i hi => norm_sum_le s _)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        simp only [norm_mul, norm_star]
        ring
  have hUV : V = U := by
    unfold V U
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym j hj i hi]
  have htwo : 2 * Q ≤ U + V := by
    unfold Q U V
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j hj
    have h := mul_le_mul_of_nonneg_left
      (weighted_young ‖a i‖ ‖a j‖ (b i) (b j) (hb i hi) (hb j hj)) (norm_nonneg (R i j))
    convert h using 1 <;> ring
  have hU : U ≤ A * (∑ i ∈ s, ‖a i‖ ^ 2) := by
    unfold U
    calc
      _ = ∑ i ∈ s, (‖a i‖ ^ 2 / b i) * (∑ j ∈ s, ‖R i j‖ * b j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ ∑ i ∈ s, (‖a i‖ ^ 2 / b i) * (A * b i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hrow i hi)
          (div_nonneg (sq_nonneg _) (hb i hi).le)
      _ = A * (∑ i ∈ s, ‖a i‖ ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        field_simp [(hb i hi).ne'] <;> ring
  rw [hUV] at htwo
  linarith

end RiemannResearch.Fourier

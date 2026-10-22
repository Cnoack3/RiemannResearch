import RiemannResearch.RH.ParetoResidueMean
import RiemannResearch.RH.OptimizedResidueHarmonic

/-!
# Arbitrary-cutoff Pareto summation by parts

Source: uploaded `Pasted markdown.md`, equation (7), 22 September 2026.
The existing residue mean proof uses complete periods. This companion proves
the displayed formula at every cutoff, retaining the exact last boundary.

-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

/-- Discrete Pareto summation by parts, with both endpoint conventions explicit. -/
theorem pareto_partial_summation (f : ℕ → ℝ) (hf0 : f 0 = 0) (M : ℕ) :
    (∑ k ∈ Finset.range (M + 1), positiveWeight k * f k) =
      (∑ k ∈ Finset.range M, (f (k + 1) - f k) / ((k : ℝ) + 1)) -
        f M / ((M : ℝ) + 1) := by
  induction M with
  | zero => simp [hf0, positiveWeight]
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    unfold positiveWeight
    push_cast
    have h1 : (M : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (M : ℝ) + 1 + 1 ≠ 0 := by positivity
    field_simp [h1, h2]
    ring

private theorem real_harmonic_range (M : ℕ) :
    (∑ k ∈ Finset.range M, 1 / ((k : ℝ) + 1)) = (harmonic M : ℝ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, harmonic_succ, ih]
    push_cast
    simp only [one_div]

/-- Exact full residue partial sum at an arbitrary cutoff, including its boundary. -/
theorem residue_partial_sum_harmonic_arbitrary (d M : ℕ) (hd : 0 < d) :
    (∑ k ∈ Finset.range (M + 1), positiveWeight k * residue d k) =
      (harmonic M : ℝ) - (harmonic (M / d) : ℝ) -
        residue d M / ((M : ℝ) + 1) := by
  have hz : residue d 0 = 0 := by simp [residue]
  rw [pareto_partial_summation (residue d) hz M]
  have hjump (k : ℕ) :
      (residue d (k + 1) - residue d k) / ((k : ℝ) + 1) =
        1 / ((k : ℝ) + 1) -
          (if d ∣ k + 1 then (d : ℝ) / ((k : ℝ) + 1) else 0) := by
    have h := residue_difference d (k + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h
    rw [h]
    split_ifs <;> ring
  simp_rw [hjump]
  rw [Finset.sum_sub_distrib, real_harmonic_range, harmonic_divisibility_sum d M hd]

/-- Equation (7) of the uploaded proof for g_d = residue_d / d. -/
theorem normalizedResidue_partial_sum_harmonic (d M : ℕ) (hd : 0 < d) :
    (∑ k ∈ Finset.range (M + 1), positiveWeight k * (residue d k / (d : ℝ))) =
      ((harmonic M : ℝ) - (harmonic (M / d) : ℝ)) / (d : ℝ) -
        (residue d M / (d : ℝ)) / ((M : ℝ) + 1) := by
  calc
    _ = (∑ k ∈ Finset.range (M + 1), positiveWeight k * residue d k) / (d : ℝ) := by
      simp only [mul_div_assoc, Finset.sum_div]
    _ = _ := by
      rw [residue_partial_sum_harmonic_arbitrary d M hd]
      ring

end RiemannResearch.RH.Pareto

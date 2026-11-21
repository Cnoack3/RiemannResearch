import RiemannResearch.RH.ThresholdHilbertAdjoint
import Mathlib.Tactic.Linarith

/-! # Pareto cost of a fresh dilation difference

A dilation difference that fits a head below its first dilation block has an explicit lower bound in the full Hilbert norm. -/

noncomputable section
namespace RiemannResearch.RH.Pareto

/-- The actual Pareto dilation scales norm by sqrt(p), so subtracting the
undilated vector has a uniform coercivity bound on the whole Hilbert space. -/
theorem freshDilation_reverse_triangle (p : ℕ) (hp : 0 < p)
    (f : ThresholdHilbert) :
    (Real.sqrt (p : ℝ) - 1) * ‖f‖ ≤ ‖hilbertDilation p hp f - f‖ := by
  have ht : ‖hilbertDilation p hp f‖ ≤ ‖hilbertDilation p hp f - f‖ + ‖f‖ := by
    calc
      _ = ‖(hilbertDilation p hp f - f) + f‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  rw [hilbertDilation_norm] at ht
  linarith only [ht]

/-- If f-D_p f interpolates g below the first dilation block, every matched
physical site contributes to the explicit lower bound for its complete cost. -/
theorem freshDilation_exact_head_cost (p h : ℕ) (hp : 0 < p) (hhp : h < p)
    (f : ThresholdHilbert) (g : ℕ → ℝ)
    (hhead : ∀ n ∈ Finset.Icc 1 h,
      hilbertSequence (f - hilbertDilation p hp f) n = g n) :
    (Real.sqrt (p : ℝ) - 1) ^ 2 *
      (∑ n ∈ Finset.Icc 1 h, positiveWeight n * g n ^ 2) ≤
      ‖f - hilbertDilation p hp f‖ ^ 2 := by
  have hval (n : ℕ) (hn : n ∈ Finset.Icc 1 h) : g n = hilbertSequence f n := by
    have hlt := lt_of_le_of_lt (Finset.mem_Icc.mp hn).2 hhp
    rw [← hhead n hn, hilbertSequence_sub, Pi.sub_apply, hilbertDilation_sequence]
    simp [dilation, Nat.div_eq_of_lt hlt]
  have hsum : (∑ n ∈ Finset.Icc 1 h, positiveWeight n * g n ^ 2) ≤ ‖f‖ ^ 2 := by
    rw [hilbert_norm_weighted_sq]
    calc
      _ = ∑ n ∈ Finset.Icc 1 h, positiveWeight n * hilbertSequence f n ^ 2 := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [hval n hn]
      _ ≤ _ := Summable.sum_le_tsum _ (fun n _ =>
        mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _))
        (hilbertSequence_square_summable f)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hs : 0 ≤ Real.sqrt (p : ℝ) - 1 := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg p), Real.sqrt_nonneg (p : ℝ)]
  have ht := freshDilation_reverse_triangle p hp f
  rw [norm_sub_rev (hilbertDilation p hp f) f] at ht
  have hsq := (sq_le_sq₀ (mul_nonneg hs (norm_nonneg f)) (norm_nonneg _)).mpr ht
  rw [mul_pow] at hsq
  exact (mul_le_mul_of_nonneg_left hsum (sq_nonneg _)).trans hsq

end RiemannResearch.RH.Pareto

#print axioms RiemannResearch.RH.Pareto.freshDilation_reverse_triangle
#print axioms RiemannResearch.RH.Pareto.freshDilation_exact_head_cost

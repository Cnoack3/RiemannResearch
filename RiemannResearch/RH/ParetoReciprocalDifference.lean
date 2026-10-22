import RiemannResearch.RH.ThresholdHilbertMean
import Mathlib.Analysis.Real.Sqrt

/-!
# Physical sublinearity and reciprocal first differences

Source: Michel Balazard, "An arithmetical function related to Baez-Duarte's
criterion for the Riemann hypothesis", arXiv:1812.04309, Section 1 and
Proposition 8 (the real point s=1 in D_0):
https://arxiv.org/abs/1812.04309 .
The proof here uses the project's weighted sequence realization and exact
finite summation by parts.

Every Hilbert vector has square-summable physical values divided by n, with
total at most twice its squared norm. Hence its physical values are o(n).
Ordered reciprocal first-difference sums converge to pairing with the
constant vector. This does not assert absolute convergence of that series,
nor does it formalize Balazard's distinct Mobius sum rule (Proposition 7).
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

private theorem physical_div_sq_le_weighted (f : ThresholdHilbert) (n : ℕ) :
    (hilbertSequence f n / (n : ℝ)) ^ 2 ≤
      2 * (positiveWeight n * hilbertSequence f n ^ 2) := by
  cases n with
  | zero => simp [positiveWeight]
  | succ n =>
    have ha : 0 < (n : ℝ) + 1 := by positivity
    have hb : 0 < (n : ℝ) + 2 := by positivity
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hc : 1 / ((n : ℝ) + 1) ^ 2 ≤
        2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
      apply (div_le_div_iff₀ (sq_pos_of_pos ha) (mul_pos ha hb)).2
      nlinarith [sq_nonneg (n : ℝ)]
    rw [positiveWeight_succ]
    simp only [Nat.cast_succ]
    calc
      (hilbertSequence f (n + 1) / ((n : ℝ) + 1)) ^ 2 =
          hilbertSequence f (n + 1) ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by rw [div_pow]; ring
      _ ≤ hilbertSequence f (n + 1) ^ 2 *
          (2 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) :=
        mul_le_mul_of_nonneg_left hc (sq_nonneg _)
      _ = 2 * (paretoWeight n * hilbertSequence f (n + 1) ^ 2) := by
        unfold paretoWeight
        ring

theorem physical_div_square_summable (f : ThresholdHilbert) :
    Summable (fun n : ℕ => (hilbertSequence f n / (n : ℝ)) ^ 2) :=
  Summable.of_nonneg_of_le (fun _n => sq_nonneg _)
    (physical_div_sq_le_weighted f)
    ((hilbertSequence_square_summable f).mul_left 2)

theorem physical_div_square_tsum_le (f : ThresholdHilbert) :
    (∑' n : ℕ, (hilbertSequence f n / (n : ℝ)) ^ 2) ≤ 2 * ‖f‖ ^ 2 := by
  calc
    _ ≤ ∑' n : ℕ, 2 * (positiveWeight n * hilbertSequence f n ^ 2) :=
      (physical_div_square_summable f).tsum_le_tsum
        (physical_div_sq_le_weighted f)
        ((hilbertSequence_square_summable f).mul_left 2)
    _ = 2 * ‖f‖ ^ 2 := by rw [tsum_mul_left, ← hilbert_norm_weighted_sq]

theorem hilbert_physical_sublinear (f : ThresholdHilbert) :
    Tendsto (fun n : ℕ => hilbertSequence f n / (n : ℝ)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Real.norm_eq_abs, Real.sqrt_sq_eq_abs, Real.sqrt_zero] using
    (physical_div_square_summable f).tendsto_atTop_zero.sqrt

theorem anchored_difference_reciprocal_sum (F : ℕ → ℝ) (h0 : F 0 = 0) (N : ℕ) :
    (∑ n ∈ Finset.range N, (F (n + 1) - F n) / ((n : ℝ) + 1)) =
      (∑ n ∈ Finset.range N, paretoWeight n * F (n + 1)) +
        F N / ((N : ℝ) + 1) := by
  induction N with
  | zero => simp [h0]
  | succ N ih =>
    simp only [Finset.sum_range_succ, ih, Nat.cast_succ]
    rw [paretoWeight_eq_inv_sub]
    have he : (N : ℝ) + 1 + 1 = (N : ℝ) + 2 := by ring
    rw [he]
    ring

theorem hilbert_difference_reciprocal_tendsto (f : ThresholdHilbert) :
    Tendsto (fun N => ∑ n ∈ Finset.range N,
      (hilbertSequence f (n + 1) - hilbertSequence f n) / ((n : ℝ) + 1))
      atTop (𝓝 (inner ℝ f hilbertOne)) := by
  have hs := weighted_summable_of_square (hilbertSequence_square_summable f)
  have hs' : Summable (fun n => paretoWeight n * hilbertSequence f (n + 1)) := by
    simpa only [positiveWeight_succ] using (summable_nat_add_iff 1).mpr hs
  have hm : (∑' n, paretoWeight n * hilbertSequence f (n + 1)) =
      inner ℝ f hilbertOne := by
    rw [hilbert_inner_one]
    unfold paretoMean
    rw [hs.tsum_eq_zero_add]
    simp only [hilbertSequence_zero, mul_zero, zero_add, positiveWeight_succ]
  have hb : Tendsto (fun N => hilbertSequence f N / ((N : ℝ) + 1))
      atTop (𝓝 0) := by
    have he (N : ℕ) : hilbertSequence f N / ((N : ℝ) + 1) =
        hilbertSequence f N / (N : ℝ) - positiveWeight N * hilbertSequence f N := by
      by_cases hN : N = 0
      · subst N; simp [positiveWeight]
      · have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN
        have hn1 : (N : ℝ) + 1 ≠ 0 := by positivity
        unfold positiveWeight
        field_simp
        ring
    have hh : Tendsto (fun N => hilbertSequence f N / (N : ℝ) -
        positiveWeight N * hilbertSequence f N) atTop (𝓝 0) := by
      simpa only [sub_zero] using
        (hilbert_physical_sublinear f).sub hs.tendsto_atTop_zero
    exact hh.congr' (Eventually.of_forall fun N => (he N).symm)
  have ht := hs'.hasSum.tendsto_sum_nat.add hb
  rw [hm, add_zero] at ht
  exact ht.congr' (Eventually.of_forall fun N =>
    (anchored_difference_reciprocal_sum
      (hilbertSequence f) (hilbertSequence_zero f) N).symm)

end RiemannResearch.RH.Pareto

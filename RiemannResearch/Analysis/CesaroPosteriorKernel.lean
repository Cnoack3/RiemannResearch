import RiemannResearch.RH.ConditionalUniformMixture
import Mathlib.Tactic

/-!
# Actual posterior tails and the conditional-row kernel

Source: user-provided `Conditional_IID_Cesaro_Mathematical_Completion_2026-09-17.md`,
Section 4, and `CesaroOperatorProof.md`. The posterior is normalized using the
proved uniform-mixture marginal. Adjoint tails are absolutely summable for every
actual weighted-square-summable sequence, not only bounded sequences. The module
proves the explicit inverse-tail identity and injectivity at positive indices.
-/
noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.Cesaro
open RH.ArithmeticCumulative

/-- The joint mass at `(K = n, T = n+k)`, divided by the marginal mass of `K`. -/
def posteriorTail (n k : ℕ) : ℝ :=
  (mixtureWeight (n + k) / ((n + k : ℕ) : ℝ)) / weight n

private theorem weight_pos (n : ℕ) (hn : 0 < n) : 0 < weight n := by
  unfold weight
  positivity

private theorem mixtureWeight_pos (n : ℕ) : 0 < mixtureWeight n := by
  unfold mixtureWeight
  positivity

theorem posteriorTail_nonneg (n k : ℕ) : 0 ≤ posteriorTail n k := by
  unfold posteriorTail
  exact div_nonneg (div_nonneg (mixtureWeight_nonneg _) (Nat.cast_nonneg _))
    (weight_nonneg _)

/-- The explicit Bayes probabilities have total mass one. -/
theorem posteriorTail_hasSum (n : ℕ) (hn : 0 < n) :
    HasSum (posteriorTail n) 1 := by
  have h := (hasSum_uniform_mixture_marginal n hn).div_const (weight n)
  change HasSum (fun k : ℕ =>
    (mixtureWeight (n + k) / ((n + k : ℕ) : ℝ)) / weight n) 1
  simpa only [div_self (ne_of_gt (weight_pos n hn))] using h

theorem posteriorTail_bayes (n k : ℕ) (hn : 0 < n) :
    weight n * posteriorTail n k =
      mixtureWeight (n + k) / ((n + k : ℕ) : ℝ) := by
  unfold posteriorTail
  field_simp [ne_of_gt (weight_pos n hn)]

/-- The hypothesis defining the actual `J = l²(q)` sequence domain. -/
def InConditionalL2 (G : ℕ → ℝ) : Prop :=
  Summable (fun k : ℕ => mixtureWeight (k + 1) * G (k + 1) ^ 2)

private theorem summable_mixture_from (n : ℕ) (hn : 0 < n) :
    Summable (fun k : ℕ => mixtureWeight (n + k)) := by
  have h := (summable_nat_add_iff (n - 1)).mpr hasSum_mixtureWeight.summable
  apply h.congr
  intro k
  rw [show k + (n - 1) + 1 = n + k by omega]

private theorem summable_square_from (G : ℕ → ℝ) (hG : InConditionalL2 G)
    (n : ℕ) (hn : 0 < n) :
    Summable (fun k : ℕ => mixtureWeight (n + k) * G (n + k) ^ 2) := by
  have h := (summable_nat_add_iff (n - 1)).mpr hG
  apply h.congr
  intro k
  rw [show k + (n - 1) + 1 = n + k by omega]

/-- Every actual `J` vector defines an absolutely convergent adjoint tail. -/
theorem adjointTail_summable (G : ℕ → ℝ) (hG : InConditionalL2 G)
    (n : ℕ) (hn : 0 < n) :
    Summable (fun k : ℕ =>
      mixtureWeight (n + k) / ((n + k : ℕ) : ℝ) * G (n + k)) := by
  have hmajor := (summable_square_from G hG n hn).add (summable_mixture_from n hn)
  apply hmajor.of_norm_bounded
  intro k
  have hp : (1 : ℝ) ≤ ((n + k : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n + k by omega)
  have hq := mixtureWeight_nonneg (n + k)
  have hqdiv : mixtureWeight (n + k) / ((n + k : ℕ) : ℝ) ≤ mixtureWeight (n + k) := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hab : |G (n + k)| ≤ G (n + k) ^ 2 + 1 := by
    nlinarith [sq_nonneg (|G (n + k)| - 1), sq_abs (G (n + k))]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (div_nonneg hq (by positivity))]
  calc
    _ ≤ mixtureWeight (n + k) * |G (n + k)| :=
      mul_le_mul_of_nonneg_right hqdiv (abs_nonneg _)
    _ ≤ mixtureWeight (n + k) * (G (n + k) ^ 2 + 1) :=
      mul_le_mul_of_nonneg_left hab hq
    _ = _ := by ring

/-- Explicit adjoint coordinate, with harmless unused coordinate zero. -/
def adjointSequence (G : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑' k : ℕ, mixtureWeight (n + k) / ((n + k : ℕ) : ℝ) * G (n + k)) /
    weight n

/-- The adjoint fixes constants at every physical coordinate. -/
theorem adjointSequence_one (n : ℕ) (hn : 0 < n) :
    adjointSequence (fun _ => 1) n = 1 := by
  simp only [adjointSequence, mul_one]
  rw [uniform_mixture_marginal n hn]
  exact div_self (ne_of_gt (weight_pos n hn))

/-- Consecutive tails recover the unsmoothed latent coordinate. -/
theorem adjointSequence_recover (G : ℕ → ℝ) (hG : InConditionalL2 G)
    (n : ℕ) (hn : 0 < n) :
    weight n * adjointSequence G n - weight (n + 1) * adjointSequence G (n + 1) =
      mixtureWeight n / (n : ℝ) * G n := by
  have h := (adjointTail_summable G hG n hn).tsum_eq_zero_add
  have he : (fun k : ℕ =>
      mixtureWeight (n + (k + 1)) / ((n + (k + 1) : ℕ) : ℝ) * G (n + (k + 1))) =
    (fun k : ℕ =>
      mixtureWeight ((n + 1) + k) / (((n + 1) + k : ℕ) : ℝ) * G ((n + 1) + k)) := by
    funext k
    rw [show n + (k + 1) = (n + 1) + k by omega]
  simp only [Nat.add_zero] at h
  rw [he] at h
  unfold adjointSequence
  rw [mul_div_cancel₀ _ (ne_of_gt (weight_pos n hn)),
    mul_div_cancel₀ _ (ne_of_gt (weight_pos (n + 1) (by omega)))]
  linarith

/-- The explicit actual adjoint tail map is injective on positive coordinates. -/
theorem adjointSequence_injective_on_positive (G H : ℕ → ℝ)
    (hG : InConditionalL2 G) (hH : InConditionalL2 H)
    (h : ∀ n, 0 < n → adjointSequence G n = adjointSequence H n)
    (n : ℕ) (hn : 0 < n) : G n = H n := by
  have h1 := adjointSequence_recover G hG n hn
  have h2 := adjointSequence_recover H hH n hn
  rw [h n hn, h (n + 1) (by omega)] at h1
  have hc : mixtureWeight n / (n : ℝ) ≠ 0 :=
    ne_of_gt (div_pos (mixtureWeight_pos n) (by positivity))
  exact (mul_left_cancel₀ hc) (h1.symm.trans h2)

/-- The actual pair-row kernel at a positive maximum coordinate. -/
def rowKernel (m : ℕ) : ℝ :=
  ∑' k : ℕ, mixtureWeight (m + k) / (((m + k : ℕ) : ℝ) ^ 2)

private theorem rowKernel_term_le (n : ℕ) (hn : 0 < n) :
    mixtureWeight n / (n : ℝ) ^ 2 ≤ mixtureWeight n / (n : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  apply div_le_div_of_nonneg_left (mixtureWeight_nonneg n) (by positivity)
  nlinarith

theorem rowKernel_summable (m : ℕ) (hm : 0 < m) :
    Summable (fun k : ℕ => mixtureWeight (m + k) / (((m + k : ℕ) : ℝ) ^ 2)) := by
  exact Summable.of_nonneg_of_le
    (fun k => div_nonneg (mixtureWeight_nonneg _) (sq_nonneg _))
    (fun k => rowKernel_term_le (m + k) (by omega))
    (hasSum_uniform_mixture_marginal m hm).summable

theorem rowKernel_nonneg (m : ℕ) : 0 ≤ rowKernel m := by
  exact tsum_nonneg (fun _ => div_nonneg (mixtureWeight_nonneg _) (sq_nonneg _))

theorem rowKernel_le_weight (m : ℕ) (hm : 0 < m) : rowKernel m ≤ weight m := by
  rw [← uniform_mixture_marginal m hm]
  exact Summable.tsum_le_tsum (fun k => rowKernel_term_le _ (by omega))
    (rowKernel_summable m hm) (hasSum_uniform_mixture_marginal m hm).summable

/-- The finite-difference identity that determines the positive kernel uniquely. -/
theorem rowKernel_recurrence (m : ℕ) (hm : 0 < m) :
    rowKernel m = mixtureWeight m / (m : ℝ) ^ 2 + rowKernel (m + 1) := by
  have h := (rowKernel_summable m hm).tsum_eq_zero_add
  simpa only [rowKernel, Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Exact partial fractions for the pair-row density. -/
theorem rowKernel_partial_fractions (t : ℕ) (ht : 0 < t) :
    mixtureWeight t / (t : ℝ) ^ 2 =
      1 / (t : ℝ) ^ 2 - 3 / (2 * (t : ℝ)) +
        2 / ((t : ℝ) + 1) - 1 / (2 * ((t : ℝ) + 2)) := by
  unfold mixtureWeight
  have h0 : (t : ℝ) ≠ 0 := by positivity
  have h1 : (t : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (t : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

/-- All endpoint terms retained in the exact finite kernel expression. -/
theorem rowKernel_finite_boundary (m R : ℕ) (hm : 0 < m) :
    (∑ k ∈ Finset.range R, mixtureWeight (m + k) / (((m + k : ℕ) : ℝ) ^ 2)) =
      (∑ k ∈ Finset.range R, 1 / (((m + k : ℕ) : ℝ) ^ 2)) -
        3 / (2 * (m : ℝ)) + 1 / (2 * ((m : ℝ) + 1)) +
        3 / (2 * ((m + R : ℕ) : ℝ)) - 1 / (2 * (((m + R : ℕ) : ℝ) + 1)) := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih,
      rowKernel_partial_fractions (m + R) (by omega)]
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- Symmetric kernel divided by the first marginal: the row-to-row transition. -/
def rowTransition (n m : ℕ) : ℝ := rowKernel (max n m) / weight n

theorem rowTransition_detailed_balance (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    weight n * rowTransition n m = weight m * rowTransition m n := by
  unfold rowTransition
  rw [mul_div_cancel₀ _ (ne_of_gt (weight_pos n hn)),
    mul_div_cancel₀ _ (ne_of_gt (weight_pos m hm)), max_comm]

end RiemannResearch.Analysis.Cesaro

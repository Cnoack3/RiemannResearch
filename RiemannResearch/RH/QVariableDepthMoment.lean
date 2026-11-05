/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.FeedbackSmoothing
import RiemannResearch.RH.MertensFullDisplacement

/-! # Square-energy control for an arbitrary physical depth schedule -/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QMertensFirstMoment
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeDisplacementRigidity
open QSquarefreeDisplacementResolvent ZetaTwoOptimizerStage

/-- Each physical site may choose its own depth, even if the depths repeat.
The diagonal's squared energy is bounded by the full nonnegative double sum. -/
theorem summable_variable_depth_resolvent_energy (m : ℕ → ℕ) :
    Summable (fun n : ℕ => (9:ℝ) ^ m n * (positiveQWeight n *
      qSequence (displacement - resolventApprox (m n)) n ^ 2)) := by
  classical
  let e (k : ℕ) := displacement - resolventApprox k
  let f (k n : ℕ) := (9 : ℝ)^k * (positiveQWeight n * qSequence (e k) n ^ 2)
  have hf (k n : ℕ) : 0 ≤ f k n := mul_nonneg (by positivity)
    (mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _))
  refine summable_of_sum_range_le (c := ‖limitingResidual‖ ^ 2 / 4)
    (fun n => hf (m n) n) ?_
  intro N
  let K := (Finset.range N).sup m + 1
  have hm (n : ℕ) (hn : n ∈ Finset.range N) : m n ∈ Finset.range K := by
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Finset.le_sup hn)
  calc
    (∑ n ∈ Finset.range N, f (m n) n) ≤
        ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range K, f k n :=
      Finset.sum_le_sum (fun n hn => Finset.single_le_sum (fun k _ => hf k n) (hm n hn))
    _ = ∑ k ∈ Finset.range K, ∑ n ∈ Finset.range N, f k n := Finset.sum_comm
    _ ≤ ∑ k ∈ Finset.range K, (9:ℝ)^k * ‖e k‖^2 := by
      apply Finset.sum_le_sum
      intro k _
      dsimp only [f]
      rw [← Finset.mul_sum, qNorm_weighted_sq]
      exact mul_le_mul_of_nonneg_left ((qSequence_square_summable (e k)).sum_le_tsum
        (Finset.range N) (fun n _ => mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _)))
        (by positivity)
    _ ≤ _ := by
      have h := resolvent_error_weighted_energy K
      dsimp only [e]
      linarith

/-- A square-summable damped budget controls the absolute error even for
repeated depths. In the Lee–Leong application take W(n)=n exp(-H(n)). -/
theorem summable_variable_depth_resolvent_error (m : ℕ → ℕ) (W : ℕ → ℝ)
    (hW : ∀ n, 0 ≤ W n)
    (hs : Summable (fun n : ℕ => positiveQWeight n * (W n / (3 : ℝ)^(m n)) ^ 2)) :
    Summable (fun n : ℕ => positiveQWeight n * W n *
      |qSequence (displacement - resolventApprox (m n)) n|) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (mul_nonneg (positiveQWeight_nonneg n) (hW n)) (abs_nonneg _))
    _ (hs.add (summable_variable_depth_resolvent_energy m))
  intro n
  let t := (3 : ℝ)^m n
  let y := qSequence (displacement - resolventApprox (m n)) n
  have ht : t ≠ 0 := by dsimp only [t]; positivity
  have ht2 : t ^ 2 = (9 : ℝ)^m n := by
    dsimp only [t]
    rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
  have hxy : W n / t * (t * |y|) = W n * |y| := by field_simp [ht] <;> ring
  have hsq : (t * |y|) ^ 2 = (9 : ℝ)^m n * y ^ 2 := by rw [mul_pow, ht2, sq_abs]
  have hle : W n * |y| ≤ (W n / t)^2 + (9:ℝ)^m n * y^2 := by
    rw [← hxy, ← hsq]
    nlinarith only [sq_nonneg (W n / t - t * |y|), sq_nonneg (W n / t), sq_nonneg (t * |y|)]
  change positiveQWeight n * W n * |y| ≤ positiveQWeight n * (W n / t)^2 +
    (9:ℝ)^m n * (positiveQWeight n * y^2)
  calc
    _ = positiveQWeight n * (W n * |y|) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hle (positiveQWeight_nonneg n)
    _ = _ := by ring

/-- To obtain RH it suffices to prove the full absolute moment for the selected
approximants and the separate scalar square budget. -/
theorem riemannHypothesis_of_variable_depth_full_moment
    (hLL : LeeLeongMertensEstimate) (δ : ℝ) (hδ : 0 < δ) (m : ℕ → ℕ)
    (hbudget : Summable (fun n : ℕ => positiveQWeight n * (((n : ℝ) *
      Real.exp (-(leeLeongFullDisplacementExponent δ n))) / (3 : ℝ) ^ m n)^2))
    (hfinite : Summable (fun n : ℕ => positiveQWeight n * ((n : ℝ) *
      Real.exp (-(leeLeongFullDisplacementExponent δ n))) * |qSequence (resolventApprox (m n)) n|)) :
    RiemannHypothesis := by
  let W (n : ℕ) := (n : ℝ) * Real.exp (-(leeLeongFullDisplacementExponent δ n))
  have hW (n : ℕ) : 0 ≤ W n := mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  apply riemannHypothesis_of_leeLeong_full_moment hLL δ hδ
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (mul_nonneg (positiveQWeight_nonneg n) (hW n)) (abs_nonneg _))
    _ (hfinite.add (summable_variable_depth_resolvent_error m W hW hbudget))
  intro n
  let v := resolventApprox (m n)
  have hp : qSequence (displacement - v) n = qSequence displacement n - qSequence v n :=
    congrFun (map_sub qSequenceLinear displacement v) n
  change positiveQWeight n * W n * |qSequence displacement n| ≤ positiveQWeight n * W n *
    |qSequence v n| + positiveQWeight n * W n * |qSequence (displacement-v) n|
  rw [← mul_add, hp]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (positiveQWeight_nonneg n) (hW n))
  calc
    _ = |qSequence v n + (qSequence displacement n - qSequence v n)| := by congr 1 <;> ring
    _ ≤ _ := abs_add_le _ _

end RiemannResearch.RH.QMertensFirstMoment

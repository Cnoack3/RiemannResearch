/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFloorDilation
import RiemannResearch.RH.QDilationMoments
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ParetoDilation
import RiemannResearch.RH.ThresholdHilbertSpace
import RiemannResearch.RH.ThresholdHilbertMean
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Exact Q dilation energy and recovery of the Pareto quadratic form

Source: B. Bagchi, "On Nyman, Beurling and Baez-Duarte's Hilbert space
reformulation of the Riemann hypothesis", 2006, Theorem 7, pp. 144–145,
https://arxiv.org/abs/math/0607733, supports the integer-dilation strategy.
The Q block identities and quantitative estimates below are an elementary
extension developed during the user-directed paper audit of 18 October 2026.
No priority claim is made. The full infinite energy and its nonnegative
remainders are retained. These estimates do not prove constant approximation.
-/

noncomputable section
open scoped BigOperators Topology
namespace RiemannResearch.RH.QFloorDilation
open ZetaTwoHilbert ZetaTwoProbability Pareto ZetaTwoParetoTransfer Filter

/-- The Q mass of a complete nonnegative quotient block. The block at zero
is retained; its energy vanishes for zero-anchored sequences. -/
def qBlockWeight (m k : ℕ) : ℝ :=
  ∑ r ∈ Finset.range m, positiveQWeight (m * k + r)

theorem qBlockWeight_nonneg (m k : ℕ) : 0 ≤ qBlockWeight m k := by
  exact Finset.sum_nonneg fun r _ => positiveQWeight_nonneg _

/-- Monotonicity is used only at strictly positive indices. -/
private theorem positiveQWeight_antitone_pos {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    positiveQWeight b ≤ positiveQWeight a := by
  have hZ := zetaTwo_pos
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have habR : (a : ℝ) ≤ b := Nat.cast_le.mpr hab
  unfold positiveQWeight
  gcongr

/-- The sharp upper block estimate. -/
theorem qBlockWeight_le (m k : ℕ) (hm : 0 < m) (hk : 0 < k) :
    qBlockWeight m k ≤ positiveQWeight k / (m : ℝ) := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hm)
  calc
    qBlockWeight m k ≤ ∑ r ∈ Finset.range m, positiveQWeight (m * k) := by
      apply Finset.sum_le_sum
      intro r hr
      exact positiveQWeight_antitone_pos (Nat.mul_pos hm hk) (Nat.le_add_right _ _)
    _ = (m : ℝ) * positiveQWeight (m * k) := by simp
    _ = positiveQWeight k / (m : ℝ) := by
      rw [positiveQWeight_mul]
      field_simp [hmR]

/-- Exact quotient on a complete floor block. -/
theorem floorBlock_div (m k r : ℕ) (hm : 0 < m) (hr : r < m) :
    (m * k + r) / m = k := by
  apply Nat.le_antisymm
  · have hlt : (m * k + r) / m < k + 1 := by
      apply (Nat.div_lt_iff_lt_mul hm).mpr
      nlinarith
    exact Nat.le_of_lt_succ hlt
  · apply (Nat.le_div_iff_mul_le hm).mpr
    nlinarith

/-- Exact finite energy regrouping; no summability assumptions are needed. -/
theorem sum_floorDilation_eq_blocks (m : ℕ) (hm : 0 < m)
    (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (m * N), positiveQWeight n * (f (n / m)) ^ 2) =
      ∑ k ∈ Finset.range N, qBlockWeight m k * (f k) ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, Finset.sum_range_succ, ih]
      congr 1
      rw [qBlockWeight, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      rw [floorBlock_div m N r hm (Finset.mem_range.mp hr)]

/-- Finite sharp energy inequality, including the initial zero block. -/
theorem sum_floorDilation_sq_le (m : ℕ) (hm : 0 < m)
    (f : ℕ → ℝ) (hf : f 0 = 0) (N : ℕ) :
    (∑ n ∈ Finset.range (m * N), positiveQWeight n * (f (n / m)) ^ 2) ≤
      (1 / (m : ℝ)) * ∑ k ∈ Finset.range N, positiveQWeight k * (f k) ^ 2 := by
  rw [sum_floorDilation_eq_blocks m hm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  by_cases hk0 : k = 0
  · simp [hk0, hf]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    calc
      qBlockWeight m k * (f k) ^ 2 ≤
          (positiveQWeight k / (m : ℝ)) * (f k) ^ 2 :=
        mul_le_mul_of_nonneg_right (qBlockWeight_le m k hm hkpos) (sq_nonneg _)
      _ = (1 / (m : ℝ)) * (positiveQWeight k * (f k) ^ 2) := by ring

/-- Each positive block's exact shortfall from the sharp constant. -/
def qBlockDefect (m k : ℕ) : ℝ :=
  positiveQWeight k / (m : ℝ) - qBlockWeight m k

theorem qBlockDefect_nonneg (m k : ℕ) (hm : 0 < m) (hk : 0 < k) :
    0 ≤ qBlockDefect m k := by
  exact sub_nonneg.mpr (qBlockWeight_le m k hm hk)

/-- Exact finite positive-defect decomposition. -/
theorem sum_floorDilation_defect (m : ℕ) (hm : 0 < m)
    (f : ℕ → ℝ) (N : ℕ) :
    (1 / (m : ℝ)) * (∑ k ∈ Finset.range N, positiveQWeight k * (f k) ^ 2) -
        (∑ n ∈ Finset.range (m * N), positiveQWeight n * (f (n / m)) ^ 2) =
      ∑ k ∈ Finset.range N, qBlockDefect m k * (f k) ^ 2 := by
  rw [sum_floorDilation_eq_blocks m hm, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  unfold qBlockDefect
  ring

/-- The complete regrouped energy is summable, including the initial block. -/
theorem qBlockEnergy_summable (m : ℕ) (hm : 0 < m) (f : QHilbert) :
    Summable (fun k => qBlockWeight m k * (qSequence f k) ^ 2) := by
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (qBlockWeight_nonneg m k) (sq_nonneg _)) _
    ((qSequence_square_summable f).div_const (m : ℝ))
  intro k
  by_cases hk : k = 0
  · simp [hk]
  · simpa only [div_mul_eq_mul_div] using
      mul_le_mul_of_nonneg_right (qBlockWeight_le m k hm (Nat.pos_of_ne_zero hk))
        (sq_nonneg (qSequence f k))

/-- Exact complete infinite Q energy, with every quotient block retained. -/
theorem floorDilation_norm_sq_eq_blocks (m : ℕ) (hm : 0 < m) (f : QHilbert) :
    ‖floorDilation m hm f‖ ^ 2 =
      ∑' k, qBlockWeight m k * (qSequence f k) ^ 2 := by
  have hmn : Tendsto (fun N : ℕ => m * N) atTop atTop := by
    exact tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N hm) tendsto_id
  have hleft := (qSequence_square_summable (floorDilation m hm f)).hasSum.tendsto_sum_nat.comp hmn
  rw [← qNorm_weighted_sq] at hleft
  simp only [Function.comp_def, floorDilation_sequence] at hleft
  have heq : (fun N => ∑ n ∈ Finset.range (m * N),
      positiveQWeight n * (qSequence f (n / m)) ^ 2) =
      (fun N => ∑ k ∈ Finset.range N, qBlockWeight m k * (qSequence f k) ^ 2) := by
    funext N
    exact sum_floorDilation_eq_blocks m hm (qSequence f) N
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft (qBlockEnergy_summable m hm f).hasSum.tendsto_sum_nat

/-- Improvement of the previous 2/m estimate to the sharp constant 1/m. -/
theorem floorDilation_norm_sq_le_sharp (m : ℕ) (hm : 0 < m) (f : QHilbert) :
    ‖floorDilation m hm f‖ ^ 2 ≤ ‖f‖ ^ 2 / (m : ℝ) := by
  rw [floorDilation_norm_sq_eq_blocks, qNorm_weighted_sq, ← tsum_div_const]
  apply Summable.tsum_le_tsum _ (qBlockEnergy_summable m hm f)
    ((qSequence_square_summable f).div_const (m : ℝ))
  intro k
  by_cases hk : k = 0
  · simp [hk]
  · simpa only [div_mul_eq_mul_div] using
      mul_le_mul_of_nonneg_right (qBlockWeight_le m k hm (Nat.pos_of_ne_zero hk))
        (sq_nonneg (qSequence f k))

/-- The estimate retains an exact nonnegative infinite remainder. -/
theorem floorDilation_norm_sq_defect (m : ℕ) (hm : 0 < m) (f : QHilbert) :
    ‖f‖ ^ 2 / (m : ℝ) - ‖floorDilation m hm f‖ ^ 2 =
      ∑' k, qBlockDefect m k * (qSequence f k) ^ 2 := by
  rw [floorDilation_norm_sq_eq_blocks, qNorm_weighted_sq, ← tsum_div_const,
    ← Summable.tsum_sub ((qSequence_square_summable f).div_const (m : ℝ))
      (qBlockEnergy_summable m hm f)]
  apply tsum_congr
  intro k
  unfold qBlockDefect
  ring

theorem floorDilation_norm_le_sharp (m : ℕ) (hm : 0 < m) (f : QHilbert) :
    ‖floorDilation m hm f‖ ≤ Real.sqrt (1 / (m : ℝ)) * ‖f‖ := by
  have hs := floorDilation_norm_sq_le_sharp m hm f
  have he : (Real.sqrt (1 / (m : ℝ)) * ‖f‖) ^ 2 = ‖f‖ ^ 2 / (m : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 / (m : ℝ))]
    ring
  rw [← he] at hs
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hs

theorem floorDilation_opNorm_le_sharp (m : ℕ) (hm : 0 < m) :
    ‖floorDilation m hm‖ ≤ Real.sqrt (1 / (m : ℝ)) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    (floorDilation_norm_le_sharp m hm)

private theorem q_pareto_weight_defect (k : ℕ) (hk : 0 < k) :
    positiveQWeight k - positiveWeight k / zetaTwo =
      positiveWeight k / (zetaTwo * (k : ℝ)) := by
  have hZ : zetaTwo ≠ 0 := ne_of_gt zetaTwo_pos
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hk)
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  unfold positiveQWeight positiveWeight
  field_simp [hZ, hkR, hk1]
  ring

private theorem paretoBlockWeight (m k : ℕ) (hm : 0 < m) (hk : 0 < k) :
    (∑ r ∈ Finset.range m, positiveWeight (m * k + r)) =
      positiveWeight k / (m : ℝ) := by
  have h := positiveWeight_block m k hm hk
  rw [Finset.sum_Ico_eq_sum_range] at h
  simpa [Nat.mul_add, Nat.add_sub_cancel_left] using h

/-- The discrepancy from the Pareto block is an explicit positive remainder. -/
theorem qBlockWeight_pareto_defect_eq (m k : ℕ) (hm : 0 < m) (hk : 0 < k) :
    (m : ℝ) * qBlockWeight m k - positiveWeight k / zetaTwo =
      (m : ℝ) * ∑ r ∈ Finset.range m,
        positiveWeight (m * k + r) / (zetaTwo * (m * k + r : ℕ)) := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hm)
  calc
    (m : ℝ) * qBlockWeight m k - positiveWeight k / zetaTwo =
        (m : ℝ) * (qBlockWeight m k -
          (∑ r ∈ Finset.range m, positiveWeight (m * k + r)) / zetaTwo) := by
      rw [paretoBlockWeight m k hm hk]
      field_simp [hmR, ne_of_gt zetaTwo_pos]
    _ = (m : ℝ) * ∑ r ∈ Finset.range m,
        (positiveQWeight (m * k + r) - positiveWeight (m * k + r) / zetaTwo) := by
      unfold qBlockWeight
      rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      exact q_pareto_weight_defect _
        (lt_of_lt_of_le (Nat.mul_pos hm hk) (Nat.le_add_right _ _))

theorem qBlockWeight_pareto_defect_nonneg (m k : ℕ) (hm : 0 < m) (hk : 0 < k) :
    0 ≤ (m : ℝ) * qBlockWeight m k - positiveWeight k / zetaTwo := by
  rw [qBlockWeight_pareto_defect_eq m k hm hk]
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro r hr
  exact div_nonneg (positiveWeight_nonneg _)
    (mul_nonneg (le_of_lt zetaTwo_pos) (Nat.cast_nonneg _))

/-- The full block discrepancy decays at least as fast as 1/m. -/
theorem qBlockWeight_pareto_defect_le (m k : ℕ) (hm : 0 < m) (hk : 0 < k) :
    (m : ℝ) * qBlockWeight m k - positiveWeight k / zetaTwo ≤
      (positiveQWeight k - positiveWeight k / zetaTwo) / (m : ℝ) := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hm)
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hk)
  have hmkR : (0 : ℝ) < (m * k : ℕ) := Nat.cast_pos.mpr (Nat.mul_pos hm hk)
  rw [qBlockWeight_pareto_defect_eq m k hm hk]
  calc
    (m : ℝ) * (∑ r ∈ Finset.range m,
        positiveWeight (m * k + r) / (zetaTwo * (m * k + r : ℕ))) ≤
        (m : ℝ) * ∑ r ∈ Finset.range m,
          positiveWeight (m * k + r) / (zetaTwo * (m * k : ℕ)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro r hr
      apply div_le_div_of_nonneg_left (positiveWeight_nonneg _)
        (mul_pos zetaTwo_pos hmkR)
      exact mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr (Nat.le_add_right _ _)) (le_of_lt zetaTwo_pos)
    _ = (m : ℝ) * ((∑ r ∈ Finset.range m, positiveWeight (m * k + r)) /
        (zetaTwo * (m * k : ℕ))) := by rw [Finset.sum_div]
    _ = (positiveQWeight k - positiveWeight k / zetaTwo) / (m : ℝ) := by
      rw [paretoBlockWeight m k hm hk, q_pareto_weight_defect k hk]
      push_cast
      field_simp [hmR, hkR, ne_of_gt zetaTwo_pos]

/-- Exact difference of the two complete quadratic forms. -/
theorem floorDilation_pareto_defect_eq (m : ℕ) (hm : 0 < m) (f : QHilbert) :
    (m : ℝ) * ‖floorDilation m hm f‖ ^ 2 - ‖toPareto f‖ ^ 2 / zetaTwo =
      ∑' k, ((m : ℝ) * qBlockWeight m k - positiveWeight k / zetaTwo) *
        (qSequence f k) ^ 2 := by
  rw [floorDilation_norm_sq_eq_blocks, hilbert_norm_weighted_sq, toPareto_sequence,
    ← tsum_mul_left, ← tsum_div_const,
    ← Summable.tsum_sub ((qBlockEnergy_summable m hm f).mul_left (m : ℝ))
      ((qSequence_pareto_square_summable f).div_const zetaTwo)]
  apply tsum_congr
  intro k
  ring

private theorem pareto_defect_summable (m : ℕ) (hm : 0 < m) (f : QHilbert) :
    Summable (fun k => ((m : ℝ) * qBlockWeight m k - positiveWeight k / zetaTwo) *
      (qSequence f k) ^ 2) := by
  apply (((qBlockEnergy_summable m hm f).mul_left (m : ℝ)).sub
    ((qSequence_pareto_square_summable f).div_const zetaTwo)).congr
  intro k
  ring

/-- Full normalized Q dilation energy dominates the Pareto quadratic form. -/
theorem floorDilation_pareto_defect_nonneg (m : ℕ) (hm : 0 < m) (f : QHilbert) :
    0 ≤ (m : ℝ) * ‖floorDilation m hm f‖ ^ 2 - ‖toPareto f‖ ^ 2 / zetaTwo := by
  rw [floorDilation_pareto_defect_eq]
  apply tsum_nonneg
  intro k
  by_cases hk : k = 0
  · simp [hk]
  · exact mul_nonneg (qBlockWeight_pareto_defect_nonneg m k hm (Nat.pos_of_ne_zero hk))
      (sq_nonneg _)

/-- Quantitative recovery of the Pareto form, retaining the exact weight gap. -/
theorem floorDilation_pareto_defect_le (m : ℕ) (hm : 0 < m) (f : QHilbert) :
    (m : ℝ) * ‖floorDilation m hm f‖ ^ 2 - ‖toPareto f‖ ^ 2 / zetaTwo ≤
      (‖f‖ ^ 2 - ‖toPareto f‖ ^ 2 / zetaTwo) / (m : ℝ) := by
  have hs : Summable (fun k => (positiveQWeight k * (qSequence f k) ^ 2 -
      (positiveWeight k * (qSequence f k) ^ 2) / zetaTwo) / (m : ℝ)) :=
    ((qSequence_square_summable f).sub
      ((qSequence_pareto_square_summable f).div_const zetaTwo)).div_const (m : ℝ)
  have he : (‖f‖ ^ 2 - ‖toPareto f‖ ^ 2 / zetaTwo) / (m : ℝ) =
      ∑' k, (positiveQWeight k * (qSequence f k) ^ 2 -
        (positiveWeight k * (qSequence f k) ^ 2) / zetaTwo) / (m : ℝ) := by
    rw [tsum_div_const, (qSequence_square_summable f).tsum_sub
      ((qSequence_pareto_square_summable f).div_const zetaTwo), tsum_div_const,
      ← qNorm_weighted_sq, ← toPareto_sequence, ← hilbert_norm_weighted_sq]
  rw [floorDilation_pareto_defect_eq, he]
  apply Summable.tsum_le_tsum _ (pareto_defect_summable m hm f) hs
  intro k
  by_cases hk : k = 0
  · simp [hk]
  · calc
      _ ≤ ((positiveQWeight k - positiveWeight k / zetaTwo) / (m : ℝ)) *
          (qSequence f k) ^ 2 :=
        mul_le_mul_of_nonneg_right
          (qBlockWeight_pareto_defect_le m k hm (Nat.pos_of_ne_zero hk)) (sq_nonneg _)
      _ = _ := by ring

/-- Uniform O(1/m) error on bounded subsets of the actual Q space. -/
theorem floorDilation_pareto_defect_le_half (m : ℕ) (hm : 0 < m) (f : QHilbert) :
    (m : ℝ) * ‖floorDilation m hm f‖ ^ 2 - ‖toPareto f‖ ^ 2 / zetaTwo ≤
      ‖f‖ ^ 2 / (2 * (m : ℝ)) := by
  have hp := zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq f
  have hgap : ‖f‖ ^ 2 - ‖toPareto f‖ ^ 2 / zetaTwo ≤ ‖f‖ ^ 2 / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have hZ := zetaTwo_pos
    have hcancel : (‖toPareto f‖ ^ 2 / zetaTwo) * zetaTwo = ‖toPareto f‖ ^ 2 :=
      div_mul_cancel₀ _ (ne_of_gt hZ)
    nlinarith
  calc
    _ ≤ (‖f‖ ^ 2 - ‖toPareto f‖ ^ 2 / zetaTwo) / (m : ℝ) :=
      floorDilation_pareto_defect_le m hm f
    _ ≤ (‖f‖ ^ 2 / 2) / (m : ℝ) := div_le_div_of_nonneg_right hgap (Nat.cast_nonneg m)
    _ = _ := by ring

/-- Normalized floor-dilation Q energy converges to the Pareto energy. -/
theorem floorDilation_normalized_energy_tendsto (f : QHilbert) :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) *
      ‖floorDilation (n + 1) (Nat.succ_pos n) f‖ ^ 2) atTop
      (𝓝 (‖toPareto f‖ ^ 2 / zetaTwo)) := by
  have hden : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono (fun n => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
    exact_mod_cast Nat.le_succ n
  have hzero : Tendsto (fun n : ℕ => ‖f‖ ^ 2 / (2 * ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 0) := by
    simpa only [div_div] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => ‖f‖ ^ 2 / 2) atTop
        (𝓝 (‖f‖ ^ 2 / 2))).div_atTop hden
  have h := squeeze_zero
    (fun n => floorDilation_pareto_defect_nonneg (n + 1) (Nat.succ_pos n) f)
    (fun n => floorDilation_pareto_defect_le_half (n + 1) (Nat.succ_pos n) f) hzero
  convert h.add_const (‖toPareto f‖ ^ 2 / zetaTwo) using 1 <;> simp

/-- Dilation does not remove relative error against the simultaneously dilated
constant. This applies to every Q vector, including each legal residual. -/
theorem floorDilation_relative_energy_tendsto (f : QHilbert) :
    Tendsto (fun n : ℕ =>
      ‖floorDilation (n + 1) (Nat.succ_pos n) f‖ ^ 2 /
        ‖floorDilation (n + 1) (Nat.succ_pos n) qOne‖ ^ 2) atTop
      (𝓝 (‖toPareto f‖ ^ 2)) := by
  have h1 := floorDilation_normalized_energy_tendsto qOne
  rw [toPareto_qOne, hilbertOne_norm_sq] at h1
  have h := (floorDilation_normalized_energy_tendsto f).div h1
    (one_div_ne_zero (ne_of_gt zetaTwo_pos))
  change Tendsto (fun n : ℕ =>
    (((n + 1 : ℕ) : ℝ) * ‖floorDilation (n + 1) (Nat.succ_pos n) f‖ ^ 2) /
      (((n + 1 : ℕ) : ℝ) * ‖floorDilation (n + 1) (Nat.succ_pos n) qOne‖ ^ 2))
    atTop _ at h
  have he : (fun n : ℕ =>
      (((n + 1 : ℕ) : ℝ) * ‖floorDilation (n + 1) (Nat.succ_pos n) f‖ ^ 2) /
        (((n + 1 : ℕ) : ℝ) * ‖floorDilation (n + 1) (Nat.succ_pos n) qOne‖ ^ 2)) =
      (fun n : ℕ => ‖floorDilation (n + 1) (Nat.succ_pos n) f‖ ^ 2 /
        ‖floorDilation (n + 1) (Nat.succ_pos n) qOne‖ ^ 2) := by
    funext n
    exact mul_div_mul_left _ _ (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0)
  rw [he] at h
  convert h using 1
  field_simp [ne_of_gt zetaTwo_pos]

/-- Strict loss in every positive floor block when the dilation exceeds one.
Source: user-requested full-conductor audit, November 2026; elementary strict
comparison of the existing inverse-square block weights. -/
theorem qBlockWeight_lt (m k : ℕ) (hm : 1 < m) (hk : 0 < k) :
    qBlockWeight m k < positiveQWeight k / (m : ℝ) := by
  have hm0 : 0 < m := by omega
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hm0)
  have hmk : (0 : ℝ) < (m * k : ℕ) := Nat.cast_pos.mpr (Nat.mul_pos hm0 hk)
  have hZ := zetaTwo_pos
  have hle (r : ℕ) : positiveQWeight (m * k + r) ≤ positiveQWeight (m * k) := by
    have hleR : ((m * k : ℕ) : ℝ) ≤ ((m * k + r : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_right (m * k) r
    unfold positiveQWeight
    gcongr
  have hlt : positiveQWeight (m * k + 1) < positiveQWeight (m * k) := by
    have hltR : ((m * k : ℕ) : ℝ) < ((m * k + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_succ_self (m * k)
    unfold positiveQWeight
    gcongr
  calc
    qBlockWeight m k < ∑ r ∈ Finset.range m, positiveQWeight (m * k) := by
      exact Finset.sum_lt_sum (fun r _ => hle r) ⟨1, Finset.mem_range.mpr hm, hlt⟩
    _ = (m : ℝ) * positiveQWeight (m * k) := by simp
    _ = positiveQWeight k / (m : ℝ) := by
      rw [positiveQWeight_mul]
      field_simp [hmR]

/-- Every positive-site coefficient of the exact energy defect is positive. -/
theorem qBlockDefect_pos (m k : ℕ) (hm : 1 < m) (hk : 0 < k) :
    0 < qBlockDefect m k := by
  exact sub_pos.mpr (qBlockWeight_lt m k hm hk)

/-- The full defect series converges, retaining every physical site. -/
theorem qBlockDefect_energy_summable (m : ℕ) (hm : 0 < m) (f : QHilbert) :
    Summable (fun k => qBlockDefect m k * (qSequence f k)^2) := by
  apply (((qSequence_square_summable f).div_const (m : ℝ)).sub
    (qBlockEnergy_summable m hm f)).congr
  intro k
  unfold qBlockDefect
  ring

/-- The sharp upper energy bound is strict for each nonzero vector.
This excludes attainment, but does not assert a uniform improvement below 1/m. -/
theorem floorDilation_norm_sq_lt (m : ℕ) (hm : 1 < m)
    (f : QHilbert) (hf : f ≠ 0) :
    ‖floorDilation m (by omega) f‖^2 < ‖f‖^2 / (m : ℝ) := by
  have hex : ∃ k, qSequence f k ≠ 0 := by
    by_contra h
    push Not at h
    apply hf
    apply qSequence_injective
    change qSequence f = qSequenceLinear 0
    rw [map_zero]
    exact funext h
  obtain ⟨k, hk⟩ := hex
  have hk0 : 0 < k := by
    by_contra hn
    have : k = 0 := by omega
    subst k
    exact hk (qSequence_zero f)
  have hnn (j : ℕ) : 0 ≤ qBlockDefect m j * (qSequence f j)^2 := by
    by_cases hj : j = 0
    · simp [hj]
    · exact mul_nonneg (qBlockDefect_nonneg m j (by omega) (Nat.pos_of_ne_zero hj)) (sq_nonneg _)
  have hp : 0 < ∑' j, qBlockDefect m j * (qSequence f j)^2 :=
    (qBlockDefect_energy_summable m (by omega) f).tsum_pos hnn k
      (mul_pos (qBlockDefect_pos m k hm hk0) (sq_pos_of_ne_zero hk))
  rw [← floorDilation_norm_sq_defect m (by omega) f] at hp
  linarith

/-- Equality at the sharp energy bound occurs only at the zero vector. -/
theorem floorDilation_sharp_equality_iff (m : ℕ) (hm : 1 < m) (f : QHilbert) :
    ‖floorDilation m (by omega) f‖^2 = ‖f‖^2 / (m : ℝ) ↔ f = 0 := by
  constructor
  · intro h
    by_contra hf
    exact (ne_of_lt (floorDilation_norm_sq_lt m hm f hf)) h
  · rintro rfl
    simp

end RiemannResearch.RH.QFloorDilation

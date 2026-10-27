/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ReversibleJumpEnergy
import Mathlib.Analysis.SpecialFunctions.Sqrt
import RiemannResearch.RH.QHeadTailLayerEnergy
import RiemannResearch.RH.QHeadCrossMoments
import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.RH.QFiniteSupportDualCriterion
import Mathlib.Analysis.InnerProductSpace.l2Space
import Lean.Elab.Tactic.Omega
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QShiftedReciprocalTail
import RiemannResearch.RH.QPolylogTailEnergy
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.Analysis.LogTailWeights
import RiemannResearch.Analysis.PolylogAbelBudget
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A small complete weighted budget for the raw reciprocal source

Source: the user's missing squarefree cross-moment bound request,
26 October 2026. These unconditional multiplier estimates precede projection;
they do not assert weighted stability of the legal projection.
The absolute mixed-product layer bound below uses the bounded multiplier aB
and controls the additive discrepancy between positive moments and capped
correction energy. It retains the exact signed identity in QHeadTailLayerEnergy;
it does not supply an upper bound on correction energy.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QShiftedReciprocal
open ZetaTwoHilbert QAnnihilatorTailEscape QPolylogTailEnergy
open RiemannResearch.Analysis.LogTailWeights

theorem reciprocal_weightedEnergyTerm_le (f : QHilbert) (n : ℕ) :
    polylogWeightedEnergyTerm 2 (B f) n ≤
      (1 / 256 : ℝ) * (positiveQWeight n * qSequence f n ^ 2) := by
  have h := mul_le_mul_of_nonneg_right (polylog_two_reciprocal_multiplier_le n)
    (mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg (qSequence f n)))
  simp only [polylogWeightedEnergyTerm, qSequence_B, div_pow]
  calc
    polylogTailProfile 2 n * positiveQWeight n *
        (qSequence f n ^ 2 / ((n : ℝ) + 1) ^ 2) =
        polylogTailProfile 2 n / ((n : ℝ) + 1) ^ 2 *
          (positiveQWeight n * qSequence f n ^ 2) := by ring
    _ ≤ _ := h

theorem reciprocal_weightedEnergy_summable (f : QHilbert) :
    Summable (polylogWeightedEnergyTerm 2 (B f)) := by
  exact Summable.of_nonneg_of_le (polylogWeightedEnergyTerm_nonneg 2 (B f))
    (reciprocal_weightedEnergyTerm_le f)
    ((qSequence_square_summable f).mul_left (1 / 256 : ℝ))

/-- The complete weighted source costs at most 1/256 of its input Q energy. -/
theorem reciprocal_weightedEnergy_le (f : QHilbert) :
    (∑' n : ℕ, polylogWeightedEnergyTerm 2 (B f) n) ≤ ‖f‖ ^ 2 / 256 := by
  have h := (reciprocal_weightedEnergy_summable f).tsum_le_tsum
    (reciprocal_weightedEnergyTerm_le f)
    ((qSequence_square_summable f).mul_left (1 / 256 : ℝ))
  rw [tsum_mul_left, ← qNorm_weighted_sq] at h
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using h

theorem reciprocal_rateWeightedEnergyTerm_le (f : QHilbert) (rate : ℕ → ℝ)
    (hrate : ∀ n, rate n ≤ (n : ℝ) + 1) (n : ℕ) :
    rate n * polylogWeightedEnergyTerm 2 (B f) n ≤
      (1 / 64 : ℝ) * (positiveQWeight n * qSequence f n ^ 2) := by
  have hm := mul_le_mul_of_nonneg_right
    (polylog_two_rate_reciprocal_multiplier_le n (rate n) (hrate n))
    (mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg (qSequence f n)))
  simp only [polylogWeightedEnergyTerm, qSequence_B, div_pow]
  calc
    _ = (rate n * polylogTailProfile 2 n / ((n : ℝ) + 1) ^ 2) *
        (positiveQWeight n * qSequence f n ^ 2) := by ring
    _ ≤ _ := hm

theorem reciprocal_rateWeightedEnergy_summable (f : QHilbert) (rate : ℕ → ℝ)
    (hnonneg : ∀ n, 0 ≤ rate n) (hrate : ∀ n, rate n ≤ (n : ℝ) + 1) :
    Summable (fun n : ℕ => rate n * polylogWeightedEnergyTerm 2 (B f) n) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (hnonneg n) (polylogWeightedEnergyTerm_nonneg 2 (B f) n))
    (reciprocal_rateWeightedEnergyTerm_le f rate hrate)
  exact (qSequence_square_summable f).mul_left (1 / 64 : ℝ)

/-- Any nonnegative exit rate growing at most linearly has a uniformly bounded
complete logarithmic energy after one reciprocal multiplication. -/
theorem reciprocal_rateWeightedEnergy_le (f : QHilbert) (rate : ℕ → ℝ)
    (hnonneg : ∀ n, 0 ≤ rate n) (hrate : ∀ n, rate n ≤ (n : ℝ) + 1) :
    (∑' n : ℕ, rate n * polylogWeightedEnergyTerm 2 (B f) n) ≤ ‖f‖ ^ 2 / 64 := by
  have hs := (reciprocal_rateWeightedEnergy_summable f rate hnonneg hrate).tsum_le_tsum
    (reciprocal_rateWeightedEnergyTerm_le f rate hrate)
    ((qSequence_square_summable f).mul_left (1 / 64 : ℝ))
  rw [tsum_mul_left, ← qNorm_weighted_sq] at hs
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hs


open RiemannResearch.Analysis.ReversibleJumpEnergy

/-- Finite-head assembly for an actual reciprocal Q source. The row hypothesis
is the weighted exit-rate envelope; it does not assert a projection bound. -/
theorem finiteRawSourceJumpEnergy_le
    (S : Finset ℕ) (f : QHilbert)
    (W : {n : ℕ // n ∈ S} → {n : ℕ // n ∈ S} → ℝ)
    (hW : ∀ x y, 0 ≤ W x y) (hsym : ∀ x y, W x y = W y x)
    (hrate : ∀ x, finiteExitRate W x ≤
      positiveQWeight x.val * ((x.val : ℝ) + 1)) :
    finiteJumpEnergy W (fun x => Real.sqrt (polylogTailProfile 2 x.val) *
      qSequence (B f) x.val) ≤ ‖f‖ ^ 2 / 32 := by
  classical
  let g (x : {n : ℕ // n ∈ S}) : ℝ :=
    Real.sqrt (polylogTailProfile 2 x.val) * qSequence (B f) x.val
  let F (n : ℕ) : ℝ := ((n : ℝ) + 1) * polylogWeightedEnergyTerm 2 (B f) n
  have hsq (x : {n : ℕ // n ∈ S}) :
      (g x) ^ 2 = polylogTailProfile 2 x.val * (qSequence (B f) x.val) ^ 2 := by
    dsimp [g]
    rw [mul_pow, Real.sq_sqrt (polylogTailProfile_nonneg 2 x.val)]
  have hterm (x : {n : ℕ // n ∈ S}) : finiteExitRate W x * (g x) ^ 2 ≤ F x.val := by
    calc
      _ ≤ (positiveQWeight x.val * ((x.val : ℝ) + 1)) *
          (g x) ^ 2 := mul_le_mul_of_nonneg_right (hrate x) (sq_nonneg (g x))
      _ = F x.val := by
        rw [hsq]
        dsimp [F, polylogWeightedEnergyTerm]
        ring
  have hFnonneg (n : ℕ) : 0 ≤ F n :=
    mul_nonneg (by positivity) (polylogWeightedEnergyTerm_nonneg 2 (B f) n)
  have hFs : Summable F :=
    reciprocal_rateWeightedEnergy_summable f (fun n => (n : ℝ) + 1)
      (fun n => by positivity) (fun n => le_rfl)
  have hFbound : (∑' n : ℕ, F n) ≤ ‖f‖ ^ 2 / 64 :=
    reciprocal_rateWeightedEnergy_le f (fun n => (n : ℝ) + 1)
      (fun n => by positivity) (fun n => le_rfl)
  have hsub : (∑ x : {n : ℕ // n ∈ S}, F x.val) = ∑ n ∈ S, F n :=
    (Finset.sum_subtype S (fun n => Iff.rfl) F).symm
  have hfinite : (∑ x : {n : ℕ // n ∈ S}, finiteExitRate W x * (g x) ^ 2) ≤
      ∑' n : ℕ, F n := by
    calc
      _ ≤ ∑ x : {n : ℕ // n ∈ S}, F x.val :=
        Finset.sum_le_sum (fun x hx => hterm x)
      _ = ∑ n ∈ S, F n := hsub
      _ ≤ _ := Summable.sum_le_tsum S (fun n hn => hFnonneg n) hFs
  have hD := finiteJumpEnergy_le_twice_exit_rate W g hW hsym
  change finiteJumpEnergy W g ≤ _
  linarith

end RiemannResearch.RH.QShiftedReciprocal

namespace RiemannResearch.RH.QHeadCrossMoments
open ZetaTwoHilbert QAnnihilatorTailEscape QFiniteSupportDualCriterion
open QShiftedReciprocal
open RiemannResearch.Analysis.LogTailWeights

private theorem abs_max_sub_sub_le (x y : ℝ) (hx : 0 ≤ x) :
    |max (x - y) 0 - x| ≤ |y| := by
  by_cases h : 0 ≤ x - y
  · rw [max_eq_left h]
    have he : x - y - x = -y := by ring
    rw [he, abs_neg]
  · rw [max_eq_right (le_of_not_ge h), zero_sub, abs_neg, abs_of_nonneg hx]
    exact (by linarith : x ≤ y).trans (le_abs_self y)

private theorem tail_coordinate (H n : ℕ) (f : QHilbert) :
    tail H f n = if H ≤ n then f n else 0 := by
  by_cases hn : H ≤ n
  · change f n - finiteHead H f n = _
    rw [finiteHead_apply_eq_zero H f n hn]
    simp [hn]
  · change f n - finiteHead H f n = _
    rw [finiteHead_apply_of_lt H f n (by omega)]
    simp [hn]

private theorem abs_coordinate_product_summable (b r : QHilbert) :
    Summable (fun j : ℕ => |b j * r j|) := by
  apply ((qCoordinate_square_summable b).add
    (qCoordinate_square_summable r)).of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_abs]
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (b j + r j),
    sq_nonneg (b j - r j), sq_nonneg (b j), sq_nonneg (r j)]

private theorem absolute_coordinate_product_young (b r : QHilbert) :
    (∑' j : ℕ, |b j * r j|) ≤ 2 * ‖b‖ ^ 2 + ‖r‖ ^ 2 / 8 := by
  have hmajor : Summable (fun j : ℕ => 2 * (b j) ^ 2 +
      (1 / 8 : ℝ) * (r j) ^ 2) :=
    ((qCoordinate_square_summable b).mul_left 2).add
      ((qCoordinate_square_summable r).mul_left (1 / 8))
  have hpoint (j : ℕ) : |b j * r j| ≤
      2 * (b j) ^ 2 + (1 / 8 : ℝ) * (r j) ^ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (4 * b j + r j),
      sq_nonneg (4 * b j - r j)]
  have hs := (abs_coordinate_product_summable b r).tsum_le_tsum hpoint hmajor
  rw [((qCoordinate_square_summable b).mul_left 2).tsum_add
      ((qCoordinate_square_summable r).mul_left (1 / 8)),
    tsum_mul_left, tsum_mul_left, ← qNorm_sq b, ← qNorm_sq r] at hs
  simpa only [div_eq_mul_inv, mul_comm, one_mul] using hs

private theorem sum_profile_increments_mask (k H n : ℕ) :
    (∑ t ∈ Finset.range H, if t ≤ n then
      polylogTailProfile k (t + 1) - polylogTailProfile k t else 0) =
      polylogTailProfile k (min H (n + 1)) := by
  induction H with
  | zero => simp [polylogTailProfile_eq]
  | succ H ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hn : H ≤ n
    · rw [if_pos hn, min_eq_left (by omega : H ≤ n + 1),
        min_eq_left (by omega : H + 1 ≤ n + 1)]
      ring
    · rw [if_neg hn, min_eq_right (by omega : n + 1 ≤ H),
        min_eq_right (by omega : n + 1 ≤ H + 1)]
      simp

/-- The smoothing multiplier controls the entire weighted absolute tail cross
term by a constant times the unweighted coordinate product. -/
theorem layer_abs_tail_inner_B_le (H : ℕ) (b r : QHilbert) :
    (∑ t ∈ Finset.range H,
      (polylogTailProfile 2 (t + 1) - polylogTailProfile 2 t) *
        |inner ℝ (tail t b) (tail t (B r))|) ≤
      (1 / 64 : ℝ) * (∑' j : ℕ, |b j * r j|) := by
  let w (t : ℕ) : ℝ := polylogTailProfile 2 (t + 1) - polylogTailProfile 2 t
  let d (j : ℕ) : ℝ := |b j * r j| / ((j : ℝ) + 2)
  let m (t j : ℕ) : ℝ := if t ≤ j then d j else 0
  have hw (t : ℕ) : 0 ≤ w t :=
    sub_nonneg.mpr (polylogTailProfile_monotone 2 (Nat.le_succ t))
  have hd (j : ℕ) : 0 ≤ d j := div_nonneg (abs_nonneg _) (by positivity)
  have hdle (j : ℕ) : d j ≤ |b j * r j| := by
    dsimp [d]
    apply (div_le_iff₀ (by positivity : 0 < (j : ℝ) + 2)).mpr
    nlinarith [abs_nonneg (b j * r j), Nat.cast_nonneg (α := ℝ) j]
  have hmnonneg (t j : ℕ) : 0 ≤ m t j := by
    dsimp [m]
    split_ifs <;> positivity
  have hmle (t j : ℕ) : m t j ≤ |b j * r j| := by
    dsimp [m]
    split_ifs
    · exact hdle j
    · exact abs_nonneg _
  have hms (t : ℕ) : Summable (m t) := by
    apply (abs_coordinate_product_summable b r).of_norm_bounded
    intro j
    rw [Real.norm_eq_abs, abs_of_nonneg (hmnonneg t j)]
    exact hmle t j
  have htail (t : ℕ) :
      |inner ℝ (tail t b) (tail t (B r))| ≤ ∑' j : ℕ, m t j := by
    let v (j : ℕ) : ℝ := if t ≤ j then b j * r j / ((j : ℝ) + 2) else 0
    have hvnorm (j : ℕ) : ‖v j‖ = m t j := by
      dsimp [v, m, d]
      split_ifs
      · rw [abs_div, abs_of_pos (by positivity : 0 < (j : ℝ) + 2)]
      · simp
    have hvns : Summable (fun j : ℕ => ‖v j‖) := by
      simpa only [hvnorm] using hms t
    have heq : inner ℝ (tail t b) (tail t (B r)) = ∑' j : ℕ, v j := by
      rw [lp.inner_eq_tsum]
      apply tsum_congr
      intro j
      rw [tail_coordinate, tail_coordinate]
      by_cases hj : t ≤ j
      · simp only [if_pos hj, B_apply, v]
        change r j / ((j : ℝ) + 2) * b j = _
        ring
      · simp [hj, v]
    rw [heq, ← Real.norm_eq_abs]
    simpa only [hvnorm] using norm_tsum_le_tsum_norm hvns
  let K (j : ℕ) : ℝ := ∑ t ∈ Finset.range H, w t * m t j
  have hKnonneg (j : ℕ) : 0 ≤ K j :=
    Finset.sum_nonneg (fun t ht => mul_nonneg (hw t) (hmnonneg t j))
  have hKeq (j : ℕ) : K j = polylogTailProfile 2 (min H (j + 1)) * d j := by
    dsimp [K]
    rw [← sum_profile_increments_mask 2 H j, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    dsimp [m, w]
    split_ifs <;> simp
  have hKle (j : ℕ) : K j ≤ (1 / 64 : ℝ) * |b j * r j| := by
    rw [hKeq]
    calc
      _ ≤ polylogTailProfile 2 (j + 1) * d j :=
        mul_le_mul_of_nonneg_right
          (polylogTailProfile_monotone 2 (min_le_right H (j + 1))) (hd j)
      _ = (polylogTailProfile 2 (j + 1) / ((j : ℝ) + 2)) * |b j * r j| := by
        dsimp [d]
        ring
      _ ≤ (1 / 64 : ℝ) * |b j * r j| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]
          using polylog_two_shifted_multiplier_le (j + 1)
  have hKs : Summable K := by
    apply ((abs_coordinate_product_summable b r).mul_left (1 / 64)).of_norm_bounded
    intro j
    rw [Real.norm_eq_abs, abs_of_nonneg (hKnonneg j)]
    exact hKle j
  calc
    _ ≤ ∑ t ∈ Finset.range H, w t * (∑' j : ℕ, m t j) := by
      apply Finset.sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_left (htail t) (hw t)
    _ = ∑' j : ℕ, K j := by
      dsimp [K]
      rw [Summable.tsum_finsetSum (fun t ht => (hms t).mul_left (w t))]
      apply Finset.sum_congr rfl
      intro t ht
      rw [tsum_mul_left]
    _ ≤ ∑' j : ℕ, (1 / 64 : ℝ) * |b j * r j| :=
      hKs.tsum_le_tsum hKle ((abs_coordinate_product_summable b r).mul_left (1 / 64))
    _ = _ := tsum_mul_left

/-- Uniform additive comparison: reciprocal smoothing makes the discrepancy
between positive cumulative variation and correction layer energy bounded
independently of the truncation height. -/
theorem positiveCrossVariation_sub_layer_B_product_le (H : ℕ) (b r : QHilbert)
    (horth : inner ℝ b (B r - b) = 0) :
    |positiveCrossVariation 2 H b (B r - b) - cappedTailEnergy 2 H b| ≤
      (1 / 64 : ℝ) * (∑' j : ℕ, |b j * r j|) := by
  have hpoint (t : ℕ) :
      |max (headCross t b (B r - b)) 0 - ‖tail t b‖ ^ 2| ≤
        |inner ℝ (tail t b) (tail t (B r))| := by
    rw [headCross_eq_tail_energy t b (B r) horth]
    exact abs_max_sub_sub_le _ _ (sq_nonneg _)
  have hsum :
      |positiveCrossVariation 2 H b (B r - b) - cappedTailEnergy 2 H b| ≤
      ∑ t ∈ Finset.range H,
        (polylogTailProfile 2 (t + 1) - polylogTailProfile 2 t) *
          |inner ℝ (tail t b) (tail t (B r))| := by
    unfold positiveCrossVariation cappedTailEnergy
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ t ∈ Finset.range H,
          |(polylogTailProfile 2 (t + 1) - polylogTailProfile 2 t) *
              max (headCross t b (B r - b)) 0 -
            (polylogTailProfile 2 (t + 1) - polylogTailProfile 2 t) *
              ‖tail t b‖ ^ 2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro t ht
        rw [← mul_sub, abs_mul, abs_of_nonneg
          (sub_nonneg.mpr (polylogTailProfile_monotone 2 (Nat.le_succ t)))]
        exact mul_le_mul_of_nonneg_left (hpoint t)
          (sub_nonneg.mpr (polylogTailProfile_monotone 2 (Nat.le_succ t)))
  exact hsum.trans (layer_abs_tail_inner_B_le H b r)

/-- A quadratic form of the absolute mixed-product estimate. -/
theorem positiveCrossVariation_sub_layer_B_le (H : ℕ) (b r : QHilbert)
    (horth : inner ℝ b (B r - b) = 0) :
    |positiveCrossVariation 2 H b (B r - b) - cappedTailEnergy 2 H b| ≤
      ‖b‖ ^ 2 / 32 + ‖r‖ ^ 2 / 512 := by
  have hc := positiveCrossVariation_sub_layer_B_product_le H b r horth
  have hy := absolute_coordinate_product_young b r
  linarith

end RiemannResearch.RH.QHeadCrossMoments

/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QTriangularWeightedBessel
import RiemannResearch.Analysis.TriangularWeightedBessel
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.RH.QFiniteSupportDualCriterion
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Complete residual screening and exact finite remainders

Source: user-provided Ordered Basis / Head Prediction / Residual Screening
research handoff, 25 October 2026, agenda A2. The proofs use nonnegative
series, orthogonal layer screening, and exact finite summation.
The complete-gain tail estimate does not bound the surviving arithmetic budget.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QResidualScreeningSeries
open QTriangularWeightedBessel ZetaTwoHilbert QShiftedReciprocal QAnnihilatorTailEscape
open QFiniteSupportDualCriterion
open RiemannResearch.Analysis.TriangularWeightedBessel

def weightedResidualLayerGain (f : QHilbert) (k : ℕ) : ℝ :=
  onsetIncrement k * residualLayerGain f k

theorem weightedResidualLayerGain_nonneg (f : QHilbert) (k : ℕ) :
    0 ≤ weightedResidualLayerGain f k :=
  mul_nonneg (onsetIncrement_nonneg k) (residualLayerGain_nonneg f k)

theorem residualGain_range_le (f : QHilbert) (M : ℕ) :
    (∑ k ∈ Finset.range M, weightedResidualLayerGain f k) ≤ ‖f‖ ^ 2 := by
  have h := reciprocal_onset_screened_bessel (ι := Fin 0) f M
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    (by intro i; exact Fin.elim0 i)
    (by intro i; exact Fin.elim0 i)
    (by intro i; exact Fin.elim0 i)
    (by intro i; exact Fin.elim0 i)
  have hg : (∑ k : Fin M, onsetIncrement k * residualLayerGain f k) ≤ ‖f‖ ^ 2 := by
    simpa using h
  rw [Fin.sum_univ_eq_sum_range
    (f := fun k : ℕ => onsetIncrement k * residualLayerGain f k) (n := M)] at hg
  exact hg

theorem residualGain_finset_le (f : QHilbert) (s : Finset ℕ) :
    (∑ k ∈ s, weightedResidualLayerGain f k) ≤ ‖f‖ ^ 2 := by
  classical
  have hsub : s ⊆ Finset.range (s.sup id + 1) := by
    intro k hk
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hk))
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun k _ _ => weightedResidualLayerGain_nonneg f k)).trans
      (residualGain_range_le f (s.sup id + 1))

theorem weightedResidualLayerGain_summable (f : QHilbert) :
    Summable (weightedResidualLayerGain f) :=
  summable_of_sum_le (weightedResidualLayerGain_nonneg f) (residualGain_finset_le f)

def completeResidualGain (f : QHilbert) : ℝ :=
  ∑' k : ℕ, weightedResidualLayerGain f k

theorem completeResidualGain_nonneg (f : QHilbert) : 0 ≤ completeResidualGain f :=
  tsum_nonneg (weightedResidualLayerGain_nonneg f)

theorem completeResidualGain_le (f : QHilbert) : completeResidualGain f ≤ ‖f‖ ^ 2 :=
  Real.tsum_le_of_sum_le (weightedResidualLayerGain_nonneg f) (residualGain_finset_le f)

theorem screening_tail_apply (f : QHilbert) (k n : ℕ) :
    tail k f n = if k ≤ n then f n else 0 := by
  change f n - finiteHead k f n = _
  by_cases hkn : k ≤ n
  · rw [finiteHead_apply_eq_zero _ _ _ hkn, sub_zero, if_pos hkn]
  · rw [finiteHead_apply_of_lt _ _ _ (by omega), sub_self, if_neg hkn]

theorem screening_tail_tail (f : QHilbert) (M k : ℕ) (hMk : M ≤ k) :
    tail k (tail M f) = tail k f := by
  ext n
  by_cases hkn : k ≤ n
  · simp only [screening_tail_apply, if_pos hkn, if_pos (hMk.trans hkn)]
  · simp only [screening_tail_apply, if_neg hkn]

theorem screening_tail_B_tail (f : QHilbert) (M k : ℕ) (hMk : M ≤ k) :
    tail k (B (tail M f)) = tail k (B f) := by
  ext n
  by_cases hkn : k ≤ n
  · simp only [screening_tail_apply, if_pos hkn, B_apply,
      if_pos (hMk.trans hkn)]
  · simp only [screening_tail_apply, if_neg hkn]

theorem residualLayerGain_tail (f : QHilbert) (M k : ℕ) (hMk : M ≤ k) :
    residualLayerGain (tail M f) k = residualLayerGain f k := by
  unfold residualLayerGain
  rw [screening_tail_tail f M k hMk, screening_tail_B_tail f M k hMk]

def residualGainTail (f : QHilbert) (M : ℕ) : ℝ :=
  ∑' k : ℕ, if M ≤ k then weightedResidualLayerGain f k else 0

theorem residualGainTail_summable (f : QHilbert) (M : ℕ) :
    Summable (fun k : ℕ => if M ≤ k then weightedResidualLayerGain f k else 0) := by
  apply Summable.of_nonneg_of_le
    (fun k => by
      split_ifs
      · exact weightedResidualLayerGain_nonneg f k
      · exact le_rfl)
    (fun k => by
      split_ifs
      · exact le_rfl
      · exact weightedResidualLayerGain_nonneg f k)
    (weightedResidualLayerGain_summable f)

theorem residualGainTail_nonneg (f : QHilbert) (M : ℕ) :
    0 ≤ residualGainTail f M := by
  apply tsum_nonneg
  intro k
  split_ifs
  · exact weightedResidualLayerGain_nonneg f k
  · rfl

theorem residualGainTail_le (f : QHilbert) (M : ℕ) :
    residualGainTail f M ≤ ‖tail M f‖ ^ 2 := by
  have hp (k : ℕ) :
      (if M ≤ k then weightedResidualLayerGain f k else 0) ≤
        weightedResidualLayerGain (tail M f) k := by
    by_cases hMk : M ≤ k
    · simp only [if_pos hMk, weightedResidualLayerGain,
        residualLayerGain_tail f M k hMk, le_refl]
    · simpa only [if_neg hMk] using weightedResidualLayerGain_nonneg (tail M f) k
  exact (Summable.tsum_le_tsum hp (residualGainTail_summable f M)
    (weightedResidualLayerGain_summable (tail M f))).trans (completeResidualGain_le (tail M f))

theorem completeResidualGain_eq_finite_add_tail (f : QHilbert) (M : ℕ) :
    completeResidualGain f =
      (∑ k ∈ Finset.range M, weightedResidualLayerGain f k) + residualGainTail f M := by
  let h : ℕ → ℝ := fun k => if k < M then weightedResidualLayerGain f k else 0
  let t : ℕ → ℝ := fun k => if M ≤ k then weightedResidualLayerGain f k else 0
  have hh : Summable h := by
    apply Summable.of_nonneg_of_le
      (fun k => by
        dsimp [h]
        split_ifs
        · exact weightedResidualLayerGain_nonneg f k
        · exact le_rfl)
      (fun k => by
        dsimp [h]
        split_ifs
        · exact le_rfl
        · exact weightedResidualLayerGain_nonneg f k)
      (weightedResidualLayerGain_summable f)
  have ht : Summable t := residualGainTail_summable f M
  have he (k : ℕ) : weightedResidualLayerGain f k = h k + t k := by
    dsimp [h, t]
    by_cases hk : k < M
    · simp [hk, show ¬ M ≤ k by omega]
    · simp [hk, show M ≤ k by omega]
  have hsum : (∑' k : ℕ, h k) = ∑ k ∈ Finset.range M, weightedResidualLayerGain f k := by
    rw [tsum_eq_sum (s := Finset.range M)]
    · apply Finset.sum_congr rfl
      intro k hk
      exact if_pos (Finset.mem_range.mp hk)
    · intro k hk
      exact if_neg (by simpa only [Finset.mem_range] using hk)
  calc
    completeResidualGain f = tsum (fun k : ℕ => h k + t k) := tsum_congr he
    _ = tsum h + tsum t := hh.tsum_add ht
    _ = _ := by rw [hsum]; rfl

theorem completeResidualGain_sub_finite_nonneg (f : QHilbert) (M : ℕ) :
    0 ≤ completeResidualGain f -
      (∑ k : Fin M, onsetIncrement k * residualLayerGain f k) := by
  rw [completeResidualGain_eq_finite_add_tail f M]
  rw [Fin.sum_univ_eq_sum_range
    (f := fun k : ℕ => onsetIncrement k * residualLayerGain f k) (n := M)]
  change 0 ≤ (∑ k ∈ Finset.range M, weightedResidualLayerGain f k) +
    residualGainTail f M - (∑ k ∈ Finset.range M, weightedResidualLayerGain f k)
  linarith [residualGainTail_nonneg f M]

theorem completeResidualGain_sub_finite_le_tail (f : QHilbert) (M : ℕ) :
    completeResidualGain f -
      (∑ k : Fin M, onsetIncrement k * residualLayerGain f k) ≤ ‖tail M f‖ ^ 2 := by
  rw [completeResidualGain_eq_finite_add_tail f M]
  rw [Fin.sum_univ_eq_sum_range
    (f := fun k : ℕ => onsetIncrement k * residualLayerGain f k) (n := M)]
  change (∑ k ∈ Finset.range M, weightedResidualLayerGain f k) +
    residualGainTail f M - (∑ k ∈ Finset.range M, weightedResidualLayerGain f k) ≤ _
  linarith [residualGainTail_le f M]

def reciprocalLayerEnergy (f : QHilbert) (M : ℕ) : ℝ :=
  ∑ k : Fin M, onsetIncrement k * ‖tail k (B f)‖ ^ 2

def reciprocalLayerRemainder (f : QHilbert) (M : ℕ) : ℝ :=
  ‖f‖ ^ 2 - reciprocalLayerEnergy f M

theorem reciprocalLayerRemainder_nonneg (f : QHilbert) (M : ℕ) :
    0 ≤ reciprocalLayerRemainder f M := by
  exact sub_nonneg.mpr (reciprocal_layer_energy_le f M)

theorem reciprocalLayerEnergy_coordinate (f : QHilbert) (M n : ℕ) :
    (∑ k : Fin M, onsetIncrement k * (tail k (B f) n) ^ 2) =
      (∑ k : Fin M, if (k : ℕ) ≤ n then onsetIncrement k else 0) *
        (f n / ((n : ℝ) + 2)) ^ 2 := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [screening_tail_apply]
  by_cases hk : (k : ℕ) ≤ n
  · simp only [if_pos hk, B_apply]
  · simp only [if_neg hk, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul]

theorem reciprocalLayerEnergy_coordinate_le (f : QHilbert) (M n : ℕ) :
    (∑ k : Fin M, onsetIncrement k * (tail k (B f) n) ^ 2) ≤ (f n) ^ 2 := by
  rw [reciprocalLayerEnergy_coordinate]
  calc
    _ ≤ ((n : ℝ) + 2) ^ 2 * (f n / ((n : ℝ) + 2)) ^ 2 :=
      mul_le_mul_of_nonneg_right (onsetIncrement_selected_le M n) (sq_nonneg _)
    _ = (f n) ^ 2 := by
      have hd : (n : ℝ) + 2 ≠ 0 := ne_of_gt (by positivity)
      field_simp

theorem reciprocalLayerEnergy_coordinate_summable (f : QHilbert) (M : ℕ) :
    Summable (fun n : ℕ => ∑ k : Fin M,
      onsetIncrement k * (tail k (B f) n) ^ 2) :=
  Summable.of_nonneg_of_le
    (fun _n => Finset.sum_nonneg (fun k _ =>
      mul_nonneg (onsetIncrement_nonneg k) (sq_nonneg _)))
    (reciprocalLayerEnergy_coordinate_le f M) (qCoordinate_square_summable f)

theorem reciprocalLayerEnergy_eq_tsum (f : QHilbert) (M : ℕ) :
    reciprocalLayerEnergy f M = ∑' n : ℕ,
      ∑ k : Fin M, onsetIncrement k * (tail k (B f) n) ^ 2 := by
  calc
    _ = ∑ k : Fin M, ∑' n : ℕ,
        onsetIncrement k * (tail k (B f) n) ^ 2 := by
      simp only [reciprocalLayerEnergy, qNorm_sq, tsum_mul_left]
    _ = _ := (Summable.tsum_finsetSum (s := Finset.univ)
      (fun (k : Fin M) _ =>
        (qCoordinate_square_summable (tail k (B f))).mul_left
          (onsetIncrement k))).symm

theorem onsetIncrement_selected_eq_after (M n : ℕ) (hM : 0 < M) (hMn : M ≤ n) :
    (∑ k : Fin M, if (k : ℕ) ≤ n then onsetIncrement k else 0) =
      ((M : ℝ) + 1) ^ 2 := by
  have he : (∑ k : Fin M, if (k : ℕ) ≤ n then onsetIncrement k else 0) =
      ∑ k : Fin M, onsetIncrement k := by
    apply Finset.sum_congr rfl
    intro k _
    exact if_pos (by have := k.isLt; omega)
  rw [he]
  cases M with
  | zero => omega
  | succ M =>
    rw [Fin.sum_univ_eq_sum_range, onsetIncrement_sum]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

/-- The complete coordinate remainder; no finite tail is substituted for a Hilbert norm. -/
theorem reciprocalLayerRemainder_eq_tsum (f : QHilbert) (M : ℕ) (hM : 0 < M) :
    reciprocalLayerRemainder f M = ∑' n : ℕ,
      if M ≤ n then
        (1 - ((M : ℝ) + 1) ^ 2 / ((n : ℝ) + 2) ^ 2) * (f n) ^ 2
      else 0 := by
  have he (n : ℕ) : (f n) ^ 2 -
      (∑ k : Fin M, onsetIncrement k * (tail k (B f) n) ^ 2) =
      if M ≤ n then
        (1 - ((M : ℝ) + 1) ^ 2 / ((n : ℝ) + 2) ^ 2) * (f n) ^ 2
      else 0 := by
    rw [reciprocalLayerEnergy_coordinate]
    have hd : (n : ℝ) + 2 ≠ 0 := ne_of_gt (by positivity)
    by_cases hMn : M ≤ n
    · rw [if_pos hMn, onsetIncrement_selected_eq_after M n hM hMn]
      field_simp
    · rw [if_neg hMn, onsetIncrement_selected_eq M n (by omega)]
      field_simp
      <;> ring
  rw [reciprocalLayerRemainder, qNorm_sq, reciprocalLayerEnergy_eq_tsum,
    ← (qCoordinate_square_summable f).tsum_sub
      (reciprocalLayerEnergy_coordinate_summable f M)]
  exact tsum_congr he

def residualLayerSlack {ι : Type*} [Fintype ι]
    (f : QHilbert) (u : ι → QHilbert) (onset : ι → ℕ) (k : ℕ) : ℝ :=
  ‖tail k (B f)‖ ^ 2 - residualLayerGain f k -
    ∑ i, if k ≤ onset i then (inner ℝ (B f) (u i)) ^ 2 else 0

theorem residualLayerSlack_nonneg {ι : Type*} [Fintype ι]
    (f : QHilbert) (u : ι → QHilbert) (onset : ι → ℕ)
    (ho : ∀ i j, i ≠ j → inner ℝ (u i) (u j) = 0)
    (hn : ∀ i, ‖u i‖ ^ 2 ≤ 1)
    (hu : ∀ i n, n < onset i → u i n = 0)
    (hf : ∀ i, inner ℝ f (u i) = 0) (k : ℕ) :
    0 ≤ residualLayerSlack f u onset k := by
  classical
  have h := layered_screened_bessel (κ := Unit) (B f) u
    (fun _ => tail k (B f)) (fun _ => tail k f)
    (fun _ i => k ≤ onset i) (fun _ => (1 : ℝ)) (fun _ => by norm_num) ho hn
    (by
      intro _ i hki
      exact tail_pairing_of_onset (B f) (u i) k
        (fun n hn => hu i n (lt_of_lt_of_le hn hki)))
    (by
      intro _ i hki
      rw [tail_pairing_of_onset f (u i) k
        (fun n hn => hu i n (lt_of_lt_of_le hn hki)), hf i])
  have hb : (∑ i, if k ≤ onset i then (inner ℝ (B f) (u i)) ^ 2 else 0) +
      residualLayerGain f k ≤ ‖tail k (B f)‖ ^ 2 := by
    simpa [residualLayerGain, ite_mul] using h
  unfold residualLayerSlack
  linarith

/-- Exact finite decomposition into coefficient energy, screening gain,
layerwise Bessel slack, and the complete coordinate remainder. -/
theorem residual_screening_full_identity {ι : Type*} [Fintype ι]
    (f : QHilbert) (M : ℕ) (u : ι → QHilbert) (onset : ι → Fin M) :
    (∑ i, (((onset i : ℕ) : ℝ) + 2) ^ 2 * (inner ℝ (B f) (u i)) ^ 2) +
      (∑ k : Fin M, onsetIncrement k * residualLayerGain f k) +
      (∑ k : Fin M, onsetIncrement k *
        residualLayerSlack f u (fun i => (onset i : ℕ)) k) +
      reciprocalLayerRemainder f M = ‖f‖ ^ 2 := by
  classical
  have he : (∑ k : Fin M, onsetIncrement k *
      (∑ i, if (k : ℕ) ≤ (onset i : ℕ) then (inner ℝ (B f) (u i)) ^ 2 else 0)) =
      ∑ i, (((onset i : ℕ) : ℝ) + 2) ^ 2 * (inner ℝ (B f) (u i)) ^ 2 := by
    calc
      _ = ∑ i, (∑ k : Fin M,
          if (k : ℕ) ≤ (onset i : ℕ) then onsetIncrement k else 0) *
            (inner ℝ (B f) (u i)) ^ 2 := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : (k : ℕ) ≤ (onset i : ℕ) <;> simp [hk]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [onsetIncrement_selected_eq M (onset i) (onset i).isLt]
  simp only [residualLayerSlack, mul_sub, Finset.sum_sub_distrib,
    reciprocalLayerRemainder, reciprocalLayerEnergy]
  rw [he]
  ring

end RiemannResearch.RH.QResidualScreeningSeries

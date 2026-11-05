/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPhysicalTailEnergy
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.NearbyDilationGram
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import RiemannResearch.Analysis.PrefixWeightedEnergy
import RiemannResearch.RH.QSquarefreeLogDisplacement
/-!
# Physical mean square, complete tails, and RH
Source: the user's four-criteria paper-proof continuation, 5 November 2026.
All tail estimates are for the complete infinite tail.
The mean-square arithmetic hypothesis remains OPEN.
-/
noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.QMeanSquareDisplacement
open ZetaTwoHilbert ZetaTwoProbability QAnnihilatorTailEscape
open QSquarefreeDisplacementRigidity
open RiemannResearch.Analysis.PrefixWeightedEnergy

def headEnergy (N : ℕ) (f : QHilbert) : ℝ :=
  ∑ k ∈ Finset.range N, (qSequence f (k + 1)) ^ 2

theorem headEnergy_nonneg (N : ℕ) (f : QHilbert) : 0 ≤ headEnergy N f :=
  Finset.sum_nonneg (fun k _ => sq_nonneg _)

theorem headEnergy_mono (f : QHilbert) : Monotone (fun N => headEnergy N f) := by
  intro N M hNM
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNM)
    (fun k _ _ => sq_nonneg _)

theorem scaled_tail_le_of_headEnergy (f : QHilbert) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ N, headEnergy N f ≤ C * (N : ℝ)) (M : ℕ) :
    (M : ℝ) * ‖tail M f‖ ^ 2 ≤ 4 * C / zetaTwo := by
  let a : ℕ → ℝ := fun k => (qSequence f (k + M + 1)) ^ 2
  let w : ℕ → ℝ := fun k => Pareto.positiveWeight (k + M + 1)
  have ha (k : ℕ) : 0 ≤ a k := sq_nonneg _
  have hw0 (k : ℕ) : 0 ≤ w k := Pareto.positiveWeight_nonneg _
  have hw : Antitone w := by
    intro i j hij
    unfold w Pareto.positiveWeight
    apply one_div_le_one_div_of_le (by positivity)
    have hh : ((i + M + 1 : ℕ) : ℝ) ≤ ((j + M + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : i + M + 1 ≤ j + M + 1)
    nlinarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i),
      (Nat.cast_nonneg j : (0 : ℝ) ≤ j), (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  have hs : Summable w := by
    simpa only [w, Nat.add_assoc] using
      (summable_nat_add_iff (f := Pareto.positiveWeight) (M + 1)).mpr
        Pareto.positiveWeight_summable
  have hpre (n : ℕ) : ∑ k ∈ Finset.range n, a k ≤ C * (M : ℝ) + C * (n : ℝ) := by
    have h := hb (M + n)
    unfold headEnergy at h
    rw [Finset.sum_range_add] at h
    have hh := headEnergy_nonneg M f
    simp only [Nat.cast_add, mul_add] at h
    have he : (∑ k ∈ Finset.range n, a k) =
        ∑ k ∈ Finset.range n, (qSequence f (M + k + 1)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [a, Nat.add_comm k M]
    rw [he]
    change 0 ≤ ∑ k ∈ Finset.range M, (qSequence f (k + 1)) ^ 2 at hh
    linarith
  have ht := weighted_tsum_le a w (C * (M : ℝ)) C ha hC hw hw0 hs hpre
  have hsum : (∑' k, w k) = 1 / ((M : ℝ) + 1) := by
    simpa only [w, Nat.add_assoc, Nat.cast_add, Nat.cast_one] using
      Pareto.positiveWeight_tail_tsum (M + 1) (by omega)
  rw [hsum] at ht
  have hden : 0 < (M : ℝ) + 1 := by positivity
  have hden2 : 0 < (M : ℝ) + 2 := by positivity
  have hwbound : (C * (M : ℝ)) * w 0 ≤ C / ((M : ℝ) + 1) := by
    simp only [w, Pareto.positiveWeight, Nat.zero_add, Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add]
    apply (le_div_iff₀ hden).mpr
    field_simp
    nlinarith [hC, (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  have hts : (∑' k, a k * w k) ≤ 2 * C / ((M : ℝ) + 1) := by
    calc
      _ ≤ C * (M : ℝ) * w 0 + C * (1 / ((M : ℝ) + 1)) := ht
      _ ≤ C / ((M : ℝ) + 1) + C * (1 / ((M : ℝ) + 1)) := add_le_add hwbound le_rfl
      _ = _ := by ring
  have hq : Summable (fun k => positiveQWeight (k + M + 1) * a k) := by
    simpa only [a, Nat.add_assoc] using
      (summable_nat_add_iff
        (f := fun k => positiveQWeight k * (qSequence f k) ^ 2) (M + 1)).mpr
        (qSequence_square_summable f)
  have hwa : Summable (fun k => a k * w k) := by
    apply Summable.of_nonneg_of_le (fun k => mul_nonneg (ha k) (hw0 k)) _ (hq.mul_left zetaTwo)
    intro k
    have hp : Pareto.positiveWeight (k + M + 1) ≤
        zetaTwo * positiveQWeight (k + M + 1) := by
      unfold Pareto.positiveWeight positiveQWeight
      have hn : 0 < ((k + M + 1 : ℕ) : ℝ) := by positivity
      have hz := zetaTwo_pos
      field_simp
      nlinarith
    dsimp [w]
    nlinarith [mul_le_mul_of_nonneg_right hp (ha k)]
  have hcmp (k : ℕ) : zetaTwo * (positiveQWeight (k + M + 1) * a k) ≤
      2 * (a k * w k) := by
    have h := ZetaTwoParetoTransfer.zetaTwo_mul_QWeight_le_two_mul_paretoWeight (k + M + 1)
    dsimp [w]
    nlinarith [mul_le_mul_of_nonneg_right h (ha k)]
  have htail := (hq.mul_left zetaTwo).tsum_le_tsum hcmp (hwa.mul_left 2)
  rw [tsum_mul_left, tsum_mul_left] at htail
  have he : (∑' k, positiveQWeight (k + M + 1) * a k) = ‖tail M f‖ ^ 2 := by
    exact (tail_energy_physical M f).symm
  rw [he] at htail
  have hh : zetaTwo * ‖tail M f‖ ^ 2 ≤ 4 * C / ((M : ℝ) + 1) := by
    calc
      _ ≤ 2 * (∑' k, a k * w k) := htail
      _ ≤ 2 * (2 * C / ((M : ℝ) + 1)) := mul_le_mul_of_nonneg_left hts (by norm_num)
      _ = _ := by ring
  have hx := (le_div_iff₀ hden).mp hh
  apply (le_div_iff₀ zetaTwo_pos).mpr
  nlinarith [mul_nonneg zetaTwo_pos.le (sq_nonneg ‖tail M f‖)]

theorem riemannHypothesis_of_bounded_mean_square (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ N, headEnergy N displacement ≤ C * (N : ℝ)) :
    RiemannHypothesis := by
  apply QSquarefreeLogDisplacement.riemannHypothesis_of_frequent_log_displacement_tail 0
  refine ⟨4 * C / zetaTwo, (Eventually.of_forall ?_).frequently⟩
  intro N
  simpa only [pow_zero, div_one] using scaled_tail_le_of_headEnergy displacement C hC hb N

end RiemannResearch.RH.QMeanSquareDisplacement

namespace RiemannResearch.RH.QMeanSquareDisplacement
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeDisplacementRigidity

theorem headEnergy_norm_le (N : ℕ) (f : QHilbert) :
    headEnergy N f ≤ zetaTwo * (N : ℝ) ^ 2 * ‖f‖ ^ 2 := by
  have hz := zetaTwo_pos
  have hterm (k : ℕ) (hk : k ∈ Finset.range N) :
      (qSequence f (k + 1)) ^ 2 ≤ zetaTwo * (N : ℝ) ^ 2 * (f k) ^ 2 := by
    have he := qSequence_weighted_square f k
    have hn : (0 : ℝ) < (k + 1 : ℕ) := by positivity
    have hz := zetaTwo_pos
    have heq : (qSequence f (k + 1)) ^ 2 =
        zetaTwo * ((k + 1 : ℕ) : ℝ) ^ 2 * (f k) ^ 2 := by
      unfold positiveQWeight at he
      field_simp at he
      nlinarith
    rw [heq]
    have hkN : ((k + 1 : ℕ) : ℝ) ≤ N := by
      exact_mod_cast (show k + 1 ≤ N from Finset.mem_range.mp hk)
    have hs : ((k + 1 : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
      nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs hz.le) (sq_nonneg _)
  calc
    headEnergy N f ≤ ∑ k ∈ Finset.range N, zetaTwo * (N : ℝ) ^ 2 * (f k) ^ 2 :=
      Finset.sum_le_sum hterm
    _ = zetaTwo * (N : ℝ) ^ 2 * ∑ k ∈ Finset.range N, (f k) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ zetaTwo * (N : ℝ) ^ 2 * ‖f‖ ^ 2 := by
      rw [qNorm_sq]
      exact mul_le_mul_of_nonneg_left
        ((qCoordinate_square_summable f).sum_le_tsum (Finset.range N)
          (fun k _ => sq_nonneg _)) (by positivity)

theorem headEnergy_exact (N : ℕ) (f g : QHilbert) :
    headEnergy N f = headEnergy N g +
      2 * (∑ k ∈ Finset.range N,
        qSequence g (k + 1) * qSequence (f - g) (k + 1)) + headEnergy N (f - g) := by
  have hphys (k : ℕ) : qSequence (f - g) k = qSequence f k - qSequence g k :=
    congrFun (map_sub qSequenceLinear f g) k
  simp only [headEnergy, Finset.mul_sum, ← Finset.sum_add_distrib, hphys]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem headEnergy_add_error_le (N : ℕ) (f g : QHilbert) :
    headEnergy N f ≤ 2 * headEnergy N g + 2 * headEnergy N (f - g) := by
  have hphys (k : ℕ) : qSequence (f - g) k = qSequence f k - qSequence g k :=
    congrFun (map_sub qSequenceLinear f g) k
  simp only [headEnergy, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  rw [hphys]
  nlinarith [sq_nonneg (qSequence f (k + 1) - 2 * qSequence g (k + 1))]

theorem geometric_head_cover (B N : ℕ) (hB : 2 ≤ B) (hN : 1 ≤ N) :
    ∃ j : ℕ, N ≤ B ^ j ∧ B ^ j ≤ B * N := by
  have hex : ∃ j : ℕ, N ≤ B ^ j := by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt N (by omega : 1 < B)
    exact ⟨j, hj.le⟩
  let j := Nat.find hex
  have hj : N ≤ B ^ j := Nat.find_spec hex
  refine ⟨j, hj, ?_⟩
  cases heq : j with
  | zero => simp only [heq, pow_zero]; nlinarith
  | succ k =>
    have hk : ¬ N ≤ B ^ k := Nat.find_min hex (by omega : k < Nat.find hex)
    have hp : B ^ k < N := Nat.lt_of_not_ge hk
    rw [pow_succ]
    nlinarith

theorem riemannHypothesis_of_geometric_head_means
    (B : ℕ) (hB : 2 ≤ B) (u : ℕ → QHilbert)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hu : ∀ j, headEnergy (B ^ j) (u j) ≤ C * ((B ^ j : ℕ) : ℝ))
    (he : ∀ j, ((B ^ j : ℕ) : ℝ) * ‖displacement - u j‖ ^ 2 ≤ D) :
    RiemannHypothesis := by
  have hz := zetaTwo_pos
  let K := 2 * C + 2 * zetaTwo * D
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hb (j : ℕ) : headEnergy (B ^ j) displacement ≤ K * ((B ^ j : ℕ) : ℝ) := by
    have h1 := headEnergy_add_error_le (B ^ j) displacement (u j)
    have h2 := headEnergy_norm_le (B ^ j) (displacement - u j)
    have h3 := mul_le_mul_of_nonneg_left (he j)
      (show 0 ≤ zetaTwo * ((B ^ j : ℕ) : ℝ) by positivity)
    have h4 := hu j
    dsimp [K]
    nlinarith
  apply riemannHypothesis_of_bounded_mean_square (K * (B : ℝ)) (by positivity)
  intro N
  by_cases hN : N = 0
  · simp [hN, headEnergy]
  · obtain ⟨j, hj1, hj2⟩ := geometric_head_cover B N hB (by omega)
    have hjR : ((B ^ j : ℕ) : ℝ) ≤ (B : ℝ) * (N : ℝ) := by exact_mod_cast hj2
    calc
      headEnergy N displacement ≤ headEnergy (B ^ j) displacement :=
        headEnergy_mono displacement hj1
      _ ≤ K * ((B ^ j : ℕ) : ℝ) := hb j
      _ ≤ K * ((B : ℝ) * (N : ℝ)) := mul_le_mul_of_nonneg_left hjR hK
      _ = _ := by ring

end RiemannResearch.RH.QMeanSquareDisplacement

namespace RiemannResearch.RH.QMeanSquareDisplacement
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeDisplacementRigidity

theorem riemannHypothesis_of_covered_head_means
    (H : ℕ → ℕ) (u : ℕ → QHilbert) (K C D : ℝ)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hcover : ∀ N, 1 ≤ N → ∃ j, N ≤ H j ∧ (H j : ℝ) ≤ K * (N : ℝ))
    (hu : ∀ j, headEnergy (H j) (u j) ≤ C * (H j : ℝ))
    (he : ∀ j, (H j : ℝ) * ‖displacement - u j‖ ^ 2 ≤ D) :
    RiemannHypothesis := by
  have hz := zetaTwo_pos
  let L := 2 * C + 2 * zetaTwo * D
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hb (j : ℕ) : headEnergy (H j) displacement ≤ L * (H j : ℝ) := by
    have h1 := headEnergy_add_error_le (H j) displacement (u j)
    have h2 := headEnergy_norm_le (H j) (displacement - u j)
    have h3 := mul_le_mul_of_nonneg_left (he j)
      (show 0 ≤ zetaTwo * (H j : ℝ) by positivity)
    have h4 := hu j
    dsimp [L]
    nlinarith
  apply riemannHypothesis_of_bounded_mean_square (L * K) (by positivity)
  intro N
  by_cases hN : N = 0
  · simp [hN, headEnergy]
  · obtain ⟨j, hj1, hj2⟩ := hcover N (by omega)
    calc
      headEnergy N displacement ≤ headEnergy (H j) displacement :=
        headEnergy_mono displacement hj1
      _ ≤ L * (H j : ℝ) := hb j
      _ ≤ L * (K * (N : ℝ)) := mul_le_mul_of_nonneg_left hj2 hL
      _ = _ := by ring
end RiemannResearch.RH.QMeanSquareDisplacement

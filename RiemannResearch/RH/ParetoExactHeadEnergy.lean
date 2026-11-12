import RiemannResearch.RH.ParetoCompactHead
import RiemannResearch.RH.NearbyDilationGram
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact-head Pareto error and a nonnegative square remainder

Source: the complete-cost continuation of D_Residue_Density_PQ_Nyman_Beurling_2026-11-11.pdf.
The head has mass H/(H+1). Completing the entire tail square gives the sharp
geometric factor (H+1)/H without an arithmetic or density hypothesis.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.ParetoExactHeadEnergy
open Pareto

theorem compactHead_one_norm_sq (H : ℕ) :
    ‖compactHead H hilbertOne‖ ^ 2 = (H : ℝ)/((H : ℝ)+1) := by
  rw [hilbert_norm_weighted_sq]
  calc
    _ = ∑ k ∈ Finset.range (H+1), positiveWeight k := by
      rw [tsum_eq_sum (s := Finset.range (H+1)) (by
        intro k hk
        have hHk : H < k := by simpa using hk
        rw [compactHead_sequence, if_neg (by omega)]
        simp)]
      apply Finset.sum_congr rfl
      intro k hk
      rw [compactHead_sequence, if_pos (by have := Finset.mem_range.mp hk; omega)]
      by_cases hk0 : k = 0
      · simp [hk0, positiveWeight]
      · rw [hilbertOne_sequence]
        simp [zeroAnchor, hk0]
    _ = _ := by
      rw [positiveWeight_sum_range (H+1) (Nat.succ_pos _)]
      push_cast
      field_simp
      ring

theorem compactHead_eq_of_exact (H : ℕ) (v : ThresholdHilbert)
    (hh : ∀ n ≤ H, hilbertSequence v n = hilbertSequence hilbertOne n) :
    compactHead H v = compactHead H hilbertOne := by
  apply hilbertSequence_injective
  funext n
  rw [compactHead_sequence, compactHead_sequence]
  by_cases hn : n ≤ H
  · simp [hn, hh n hn]
  · simp [hn]

/-- Exact nonnegative remainder; the full physical tail is retained. -/
theorem exact_head_square_identity (H : ℕ) (v : ThresholdHilbert)
    (hh : ∀ n ≤ H, hilbertSequence v n = hilbertSequence hilbertOne n) :
    (H : ℝ)*‖v-hilbertOne‖ ^ 2 +
      ‖(v-compactHead H hilbertOne) +
        (H : ℝ) • (hilbertOne-compactHead H hilbertOne)‖ ^ 2 =
      ((H : ℝ)+1)*‖v‖ ^ 2 := by
  let e := compactHead H hilbertOne
  let t := v-e
  let r := hilbertOne-e
  have hv := compactHead_pythagoras H v
  rw [compactHead_eq_of_exact H v hh] at hv
  have ho := compactHead_pythagoras H hilbertOne
  rw [hilbertOne_norm_sq, compactHead_one_norm_sq] at ho
  rw [compactHead_one_norm_sq] at hv
  have hd : v-hilbertOne = t-r := by dsimp [t,r]; abel
  have hs := norm_sub_sq_real t r
  have ha := norm_add_sq_real t ((H : ℝ) • r)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg H),
    mul_pow, inner_smul_right] at ha
  have hp : ((H : ℝ)+1)*((H : ℝ)/((H : ℝ)+1)) = (H : ℝ) := by field_simp
  change ‖v‖ ^ 2 = (H : ℝ)/((H : ℝ)+1) + ‖t‖ ^ 2 at hv
  change 1 = (H : ℝ)/((H : ℝ)+1) + ‖r‖ ^ 2 at ho
  change (H : ℝ)*‖v-hilbertOne‖ ^ 2 + ‖t+(H : ℝ)•r‖ ^ 2 = _
  rw [hd]
  nlinarith [sq_nonneg (H : ℝ)]

theorem error_norm_sq_le (H : ℕ) (hH : 0 < H) (v : ThresholdHilbert)
    (hh : ∀ n ≤ H, hilbertSequence v n = hilbertSequence hilbertOne n) :
    ‖v-hilbertOne‖ ^ 2 ≤ (((H : ℝ)+1)/(H : ℝ))*‖v‖ ^ 2 := by
  have he := exact_head_square_identity H v hh
  have hr := sq_nonneg ‖(v-compactHead H hilbertOne) +
    (H : ℝ) • (hilbertOne-compactHead H hilbertOne)‖
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hHR).mpr
  nlinarith
end RiemannResearch.RH.ParetoExactHeadEnergy

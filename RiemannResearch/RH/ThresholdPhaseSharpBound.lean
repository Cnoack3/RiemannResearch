import RiemannResearch.RH.ThresholdPhaseConstant

/-!
# The sharp elementary majorant for the actual phase summands

Source: Christian Noack, `RH_Two_Seed_Threshold.tex`, 8 September 2026,
Section 8, Lemma `lem:delta`. The upper bound is proved from the first
three positive logarithm-series terms and an exact rational identity.
No floating-point arithmetic or unproved series coefficient bounds occur.
The paper's matching lower correction and decimal enclosure remain separate.
-/

namespace RiemannResearch.RH.TwoSeedThreshold

open scoped BigOperators
open Pareto

theorem phaseDelta_le_twelfth_weight {k : ℕ} (hk : 0 < k) :
    phaseDelta k ≤ positiveWeight k / 12 := by
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hk0
  let z : ℝ := 1 / (2 * (k : ℝ) + 1)
  let L : ℝ := 2 * (z + z^3 / 3 + z^5 / 5)
  have hd : 0 < 2 * (k : ℝ) + 1 := by positivity
  have hz0 : 0 < z := by dsimp [z]; positivity
  have hz1 : z < 1 := by
    dsimp [z]
    apply (div_lt_one hd).2
    linarith
  have hr : (1 + z) / (1 - z) = 1 + 1 / (k : ℝ) := by
    dsimp [z]
    field_simp
    <;> ring
  have h := Real.sum_range_le_log_div (le_of_lt hz0) hz1 3
  norm_num [Finset.sum_range_succ] at h
  rw [hr] at h
  have hL : L ≤ Real.log (1 + 1 / (k : ℝ)) := by dsimp [L]; linarith
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hsq := (sq_le_sq₀ hL0 (le_trans hL0 hL)).2 hL
  have hid : L^2 -
      (1 / ((k : ℝ) * ((k : ℝ) + 1)) -
        1 / (12 * ((k : ℝ) * ((k : ℝ) + 1))^2)) =
      (225 + 1800 * (k : ℝ) + 9192 * (k : ℝ)^2 +
        35904 * (k : ℝ)^3 + 101472 * (k : ℝ)^4 +
        186240 * (k : ℝ)^5 + 205440 * (k : ℝ)^6 +
        122880 * (k : ℝ)^7 + 30720 * (k : ℝ)^8) /
      (2700 * ((k : ℝ) * ((k : ℝ) + 1))^2 * (2 * (k : ℝ) + 1)^10) := by
    dsimp [L, z]
    field_simp
    <;> ring
  have hnum : 0 ≤ (225 + 1800 * (k : ℝ) + 9192 * (k : ℝ)^2 +
        35904 * (k : ℝ)^3 + 101472 * (k : ℝ)^4 +
        186240 * (k : ℝ)^5 + 205440 * (k : ℝ)^6 +
        122880 * (k : ℝ)^7 + 30720 * (k : ℝ)^8) /
      (2700 * ((k : ℝ) * ((k : ℝ) + 1))^2 * (2 * (k : ℝ) + 1)^10) := by positivity
  have hlower : 1 / ((k : ℝ) * ((k : ℝ) + 1)) -
      1 / (12 * ((k : ℝ) * ((k : ℝ) + 1))^2) ≤
      Real.log (1 + 1 / (k : ℝ))^2 := by linarith
  have hm := mul_le_mul_of_nonneg_left hlower
    (by positivity : 0 ≤ (k : ℝ) * ((k : ℝ) + 1))
  have he : (k : ℝ) * ((k : ℝ) + 1) *
      (1 / ((k : ℝ) * ((k : ℝ) + 1)) -
        1 / (12 * ((k : ℝ) * ((k : ℝ) + 1))^2)) =
      1 - positiveWeight k / 12 := by
    unfold positiveWeight
    field_simp
    <;> ring
  rw [he] at hm
  unfold phaseDelta
  linarith

/-- The paper's sharp upper tail constant, for the entire infinite tail. -/
theorem phaseTail_le_twelfth (N : ℕ) :
    phaseTail N ≤ 1 / (12 * ((N : ℝ) + 1)) := by
  have hw : Summable (fun k : ℕ => positiveWeight (k + N + 1)) :=
    positiveWeight_summable.comp_injective (by
      intro a b h
      exact Nat.add_right_cancel (Nat.add_right_cancel h))
  have hcomp := Summable.tsum_le_tsum
    (fun k => phaseDelta_le_twelfth_weight (k := k + N + 1) (by omega))
    (phaseDelta_shift_summable N) (hw.div_const 12)
  have he : (∑' k : ℕ, positiveWeight (k + N + 1)) = progressionWeight 1 (N + 1) := by
    unfold progressionWeight
    apply tsum_congr
    intro k
    congr 1
    omega
  rw [tsum_div_const, he] at hcomp
  have ht := progressionWeight_tail_upper 1 N (by norm_num)
  norm_num only [Nat.cast_one, one_mul] at ht
  have hd := div_le_div_of_nonneg_right ht (by norm_num : (0 : ℝ) ≤ 12)
  unfold phaseTail
  exact le_trans hcomp (by convert hd using 1 <;> field_simp <;> ring)

theorem universalPhaseConstant_le_twelfth : universalPhaseConstant ≤ 1 / 12 := by
  simpa [phaseTail, universalPhaseConstant] using phaseTail_le_twelfth 0

end RiemannResearch.RH.TwoSeedThreshold

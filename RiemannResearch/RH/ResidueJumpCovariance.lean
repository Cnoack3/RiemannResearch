import RiemannResearch.RH.ParetoResidueDuality
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Exact gcd covariance of residue jumps

Source: user-provided `RH_CRT_Packet_Research_2026-09-09.md`, equation (11).
This is the exact finite average of the actual residue jumps on an arbitrary
common period. The proof telescopes residue differences before expanding the
complete mixed product. It does not substitute uniform CRT weights for the
Pareto norm; its consumer is the separate nearby-dilation limiting theorem.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Exact weighted number of divisibility events, including the last residue. -/
theorem sum_dvd_weight_residue (a N : ℕ) :
    (∑ k ∈ Finset.range N, if a ∣ k + 1 then (a : ℝ) else 0) =
      (N : ℝ) - residue a N := by
  induction N with
  | zero => simp [residue]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have h := residue_difference a (N + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h
    simp only [Nat.cast_succ]
    linarith

theorem sum_dvd_weight_of_period (a Q : ℕ) (haQ : a ∣ Q) :
    (∑ k ∈ Finset.range Q, if a ∣ k + 1 then (a : ℝ) else 0) = (Q : ℝ) := by
  rw [sum_dvd_weight_residue]
  simp [residue, Nat.mod_eq_zero_of_dvd haQ]

/-- Complete pointwise mixed product; the common divisibility term is retained. -/
theorem residueJump_mixed_formula (a b k : ℕ) :
    (residue a (k + 1) - residue a k) *
        (residue b (k + 1) - residue b k) =
      1 - (if a ∣ k + 1 then (a : ℝ) else 0) -
        (if b ∣ k + 1 then (b : ℝ) else 0) +
        (Nat.gcd a b : ℝ) *
          (if Nat.lcm a b ∣ k + 1 then (Nat.lcm a b : ℝ) else 0) := by
  have ha := residue_difference a (k + 1) (by omega)
  have hb := residue_difference b (k + 1) (by omega)
  simp only [Nat.add_sub_cancel] at ha hb
  rw [ha, hb]
  have hmul : (Nat.gcd a b : ℝ) * (Nat.lcm a b : ℝ) = (a : ℝ) * (b : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm a b
  by_cases had : a ∣ k + 1 <;> by_cases hbd : b ∣ k + 1
  all_goals simp only [Nat.lcm_dvd_iff, had, hbd, and_self, and_true, and_false,
    true_and, false_and, if_true, if_false]
  all_goals nlinarith [hmul]

/-- Exact common-period covariance sum for all residue indices. -/
theorem residueJump_covariance_sum (a b Q : ℕ) (haQ : a ∣ Q) (hbQ : b ∣ Q) :
    (∑ k ∈ Finset.range Q,
      (residue a (k + 1) - residue a k) *
        (residue b (k + 1) - residue b k)) =
      (Q : ℝ) * ((Nat.gcd a b : ℝ) - 1) := by
  simp_rw [residueJump_mixed_formula]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, sum_dvd_weight_of_period a Q haQ,
    sum_dvd_weight_of_period b Q hbQ,
    sum_dvd_weight_of_period (Nat.lcm a b) Q (Nat.lcm_dvd haQ hbQ)]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  ring

/-- The finite period mean of the actual residue jumps equals gcd(a,b)-1. -/
theorem residueJump_covariance_mean (a b Q : ℕ) (hQ : 0 < Q)
    (haQ : a ∣ Q) (hbQ : b ∣ Q) :
    (∑ k ∈ Finset.range Q,
      (residue a (k + 1) - residue a k) *
        (residue b (k + 1) - residue b k)) / (Q : ℝ) =
      (Nat.gcd a b : ℝ) - 1 := by
  rw [residueJump_covariance_sum a b Q haQ hbQ]
  have hQ0 : (Q : ℝ) ≠ 0 := by positivity
  field_simp [hQ0]

end
end RiemannResearch.RH.Pareto

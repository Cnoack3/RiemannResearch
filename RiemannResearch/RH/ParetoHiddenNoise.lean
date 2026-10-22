import RiemannResearch.RH.ParetoCovariance
import Mathlib.Tactic.Linarith

/-!
# Finite identities for the hidden-noise family

Source: RH_Noise_Signal_Arithmetic_Repair_2026-09-07.pdf, §6, equations (6.1)–(6.2).

This file proves the underlying exact finite and Pareto-mean identities for the genuine
residue/dilation family. It does not assert the logarithmic asymptotics, conditional-mean
integral limit, or uniform estimates for a growing approximation space.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The square wave obtained from a residue modulo two after an integer dilation. -/
def squareWave (n k : ℕ) : ℝ := ((k / n) % 2 : ℕ)

/-- The actual difference of the two mixed-control residue expressions in §6. -/
def hiddenNoise (n k : ℕ) : ℝ :=
  dilation (n + 2) (residue 2) k - dilation n (residue 2) k

theorem hiddenNoise_residue (n k : ℕ) :
    hiddenNoise n k =
      (residue (2 * (n + 2)) k - residue (n + 2) k - residue 2 k) -
      (residue (2 * n) k - residue n k - residue 2 k) := by
  unfold hiddenNoise
  rw [residue_mul_floor, residue_mul_floor]
  rw [Nat.mul_comm (n + 2) 2, Nat.mul_comm n 2]
  ring

theorem hiddenNoise_squareWave (n k : ℕ) :
    hiddenNoise n k = ((n : ℝ) + 2) * squareWave (n + 2) k -
      (n : ℝ) * squareWave n k := by
  simp only [hiddenNoise, dilation, squareWave, residue, Nat.cast_add, Nat.cast_ofNat]

private theorem residue_two_abs_le (k : ℕ) : |residue 2 k| ≤ 1 := by
  unfold residue
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  have h : k % 2 ≤ 1 := by omega
  exact_mod_cast h

theorem hiddenNoise_abs_le (n k : ℕ) :
    |hiddenNoise n k| ≤ ((n + 2 : ℕ) : ℝ) + (n : ℝ) := by
  simpa only [hiddenNoise, mul_one] using
    bounded_sub (dilation_abs_le residue_two_abs_le (n + 2))
      (dilation_abs_le residue_two_abs_le n) k

/-- The complete Pareto mean vanishes, with all summability obligations discharged. -/
theorem hiddenNoise_mean_zero (n : ℕ) (hn : 0 < n) :
    paretoMean (hiddenNoise n) = 0 := by
  unfold hiddenNoise
  rw [paretoMean_sub (dilation_abs_le residue_two_abs_le (n + 2))
    (dilation_abs_le residue_two_abs_le n),
    paretoMean_dilation residue_two_abs_le (by simp [residue]) (n + 2) (by omega),
    paretoMean_dilation residue_two_abs_le (by simp [residue]) n hn]
  ring

theorem hiddenNoise_head_zero (n k : ℕ) (hk : k < n) :
    hiddenNoise n k = 0 := by
  have hk' : k < n + 2 := by omega
  simp [hiddenNoise, dilation, residue, Nat.div_eq_of_lt hk, Nat.div_eq_of_lt hk']

/-- The first square wave has crossed its jth jump on the mismatch interval. -/
theorem hiddenNoise_interval_div_left (n j k : ℕ) (hj : 0 < j)
    (hjn : 2 * j ≤ n) (hklo : j * n ≤ k) (hkhi : k < j * (n + 2)) :
    k / n = j := by
  apply Nat.div_eq_of_lt_le
  · exact hklo
  · have h : j * (n + 2) ≤ (j + 1) * n := by nlinarith
    exact lt_of_lt_of_le hkhi h

/-- The second square wave has not yet crossed its jth jump. -/
theorem hiddenNoise_interval_div_right (n j k : ℕ) (hj : 0 < j)
    (hjn : 2 * j ≤ n) (hklo : j * n ≤ k) (hkhi : k < j * (n + 2)) :
    k / (n + 2) = j - 1 := by
  have hj1 : j - 1 + 1 = j := Nat.sub_add_cancel hj
  apply Nat.div_eq_of_lt_le
  · have h : (j - 1) * (n + 2) ≤ j * n := by
      have he : (j - 1) * (n + 2) + (n + 2) = j * (n + 2) := by
        calc
          _ = (j - 1 + 1) * (n + 2) := by ring
          _ = _ := by rw [hj1]
      nlinarith
    exact le_trans h hklo
  · simpa only [hj1] using hkhi

/-- On an odd mismatch interval the value is exactly -n. -/
theorem hiddenNoise_interval_odd (n j k : ℕ) (hj : 0 < j)
    (hjn : 2 * j ≤ n) (hklo : j * n ≤ k) (hkhi : k < j * (n + 2))
    (hodd : j % 2 = 1) : hiddenNoise n k = -(n : ℝ) := by
  have hprev : (j - 1) % 2 = 0 := by omega
  simp [hiddenNoise, dilation, residue,
    hiddenNoise_interval_div_left n j k hj hjn hklo hkhi,
    hiddenNoise_interval_div_right n j k hj hjn hklo hkhi, hodd, hprev]

/-- On an even mismatch interval the value is exactly n+2. -/
theorem hiddenNoise_interval_even (n j k : ℕ) (hj : 0 < j)
    (hjn : 2 * j ≤ n) (hklo : j * n ≤ k) (hkhi : k < j * (n + 2))
    (heven : j % 2 = 0) : hiddenNoise n k = (n : ℝ) + 2 := by
  have hprev : (j - 1) % 2 = 1 := by omega
  simp [hiddenNoise, dilation, residue,
    hiddenNoise_interval_div_left n j k hj hjn hklo hkhi,
    hiddenNoise_interval_div_right n j k hj hjn hklo hkhi, heven, hprev]

/-- The exact Pareto probability of the jth mismatch interval. -/
theorem hiddenNoise_interval_mass (n j : ℕ) (hn : 0 < n) (hj : 0 < j) :
    (∑ k ∈ Finset.Ico (j * n) (j * (n + 2)), positiveWeight k) =
      2 / ((j : ℝ) * n * ((n : ℝ) + 2)) := by
  rw [positiveWeight_interval _ _ (Nat.mul_pos hj hn) (Nat.mul_le_mul_left j (by omega))]
  push_cast
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hj0 : (j : ℝ) ≠ 0 := by positivity
  have hnp : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  <;> ring

/-- Exact squared-norm contribution of an odd mismatch interval. -/
theorem hiddenNoise_interval_energy_odd (n j : ℕ) (hj : 0 < j)
    (hjn : 2 * j ≤ n) (hodd : j % 2 = 1) :
    (∑ k ∈ Finset.Ico (j * n) (j * (n + 2)),
      positiveWeight k * (hiddenNoise n k) ^ 2) =
      2 * n / ((j : ℝ) * ((n : ℝ) + 2)) := by
  have hn : 0 < n := by omega
  calc
    _ = (∑ k ∈ Finset.Ico (j * n) (j * (n + 2)), positiveWeight k) * (n : ℝ) ^ 2 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [hiddenNoise_interval_odd n j k hj hjn
        (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2 hodd]
      ring
    _ = _ := by
      rw [hiddenNoise_interval_mass n j hn hj]
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      have hj0 : (j : ℝ) ≠ 0 := by positivity
      have hnp : (n : ℝ) + 2 ≠ 0 := by positivity
      field_simp
      <;> ring

/-- Exact squared-norm contribution of an even mismatch interval. -/
theorem hiddenNoise_interval_energy_even (n j : ℕ) (hj : 0 < j)
    (hjn : 2 * j ≤ n) (heven : j % 2 = 0) :
    (∑ k ∈ Finset.Ico (j * n) (j * (n + 2)),
      positiveWeight k * (hiddenNoise n k) ^ 2) =
      2 * ((n : ℝ) + 2) / ((j : ℝ) * n) := by
  have hn : 0 < n := by omega
  calc
    _ = (∑ k ∈ Finset.Ico (j * n) (j * (n + 2)), positiveWeight k) * ((n : ℝ) + 2) ^ 2 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [hiddenNoise_interval_even n j k hj hjn
        (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2 heven]
    _ = _ := by
      rw [hiddenNoise_interval_mass n j hn hj]
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      have hj0 : (j : ℝ) ≠ 0 := by positivity
      have hnp : (n : ℝ) + 2 ≠ 0 := by positivity
      field_simp
      <;> ring

end
end RiemannResearch.RH.Pareto

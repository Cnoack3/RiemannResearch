import RiemannResearch.RH.OptimizedResidueIdentities

/-!
# Sharp jump-energy lower bound for finite smooth residue seeds

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md, §4.
The actual residue providers are discharged below. The theorem in fact applies
to every finite seed all of whose moduli are divisible by two or three, with a
specified positive common period divisible by six. No RH assumption occurs.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

theorem residue_forwardJump_of_not_dvd (a k : ℕ) (ha : 1 < a)
    (hnot : ¬ a ∣ k + 1) : sequenceForwardJump (residue a) k = 1 := by
  have hnz : (k + 1) % a ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hnot
  have hnext : (k + 1) % a = (k % a + 1) % a := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt ha]
  have hlt := Nat.mod_lt k (by omega : 0 < a)
  have hne : k % a + 1 ≠ a := by
    intro he
    apply hnz
    rw [hnext, he, Nat.mod_self]
  have hinc : (k + 1) % a = k % a + 1 := by
    rw [hnext, Nat.mod_eq_of_lt (show k % a + 1 < a by omega)]
  unfold sequenceForwardJump residue
  rw [hinc]
  push_cast
  ring

theorem sum_forwardJump (f : ℕ → ℝ) (L : ℕ) :
    (∑ k ∈ Finset.range L, sequenceForwardJump f k) = f L - f 0 := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih]
    unfold sequenceForwardJump
    ring

theorem prime_to_six_forward_classes_count (M : ℕ) :
    (∑ k ∈ Finset.range (6 * M),
      if k % 6 = 0 ∨ k % 6 = 4 then (1 : ℝ) else 0) = 2 * (M : ℝ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    have hblock :
        (∑ k ∈ Finset.range 6,
          if (6 * M + k) % 6 = 0 ∨ (6 * M + k) % 6 = 4 then (1 : ℝ) else 0) = 2 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num [Nat.add_mod]
    rw [hblock]
    push_cast
    ring

def finiteResidueCombination (s : Finset ℕ) (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ a ∈ s, c a * residue a k

theorem finiteResidueCombination_forward_class (s : Finset ℕ) (c : ℕ → ℝ)
    (hpos : ∀ a ∈ s, 0 < a) (hdiv : ∀ a ∈ s, 2 ∣ a ∨ 3 ∣ a)
    (hc : ∑ a ∈ s, c a = 1) (k : ℕ) (hk : k % 6 = 0 ∨ k % 6 = 4) :
    sequenceForwardJump (finiteResidueCombination s c) k = 1 := by
  have hj (a : ℕ) (ha : a ∈ s) : sequenceForwardJump (residue a) k = 1 := by
    have ha1 : 1 < a := by
      rcases hdiv a ha with hd | hd
      · have := Nat.le_of_dvd (hpos a ha) hd
        omega
      · have := Nat.le_of_dvd (hpos a ha) hd
        omega
    apply residue_forwardJump_of_not_dvd a k ha1
    intro had
    rcases hdiv a ha with hd | hd
    · have hz := Nat.mod_eq_zero_of_dvd (dvd_trans hd had)
      omega
    · have hz := Nat.mod_eq_zero_of_dvd (dvd_trans hd had)
      omega
  unfold sequenceForwardJump finiteResidueCombination
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ a ∈ s, c a := by
      apply Finset.sum_congr rfl
      intro a ha
      have hja := hj a ha
      unfold sequenceForwardJump at hja
      rw [← mul_sub, hja, mul_one]
    _ = 1 := hc

theorem finiteResidueCombination_forward_sum_zero (s : Finset ℕ) (c : ℕ → ℝ)
    (L : ℕ) (hL : ∀ a ∈ s, a ∣ L) :
    (∑ k ∈ Finset.range L, sequenceForwardJump (finiteResidueCombination s c) k) = 0 := by
  rw [sum_forwardJump]
  have hzero : finiteResidueCombination s c 0 = 0 := by
    simp [finiteResidueCombination, residue]
  have hend : finiteResidueCombination s c L = 0 := by
    unfold finiteResidueCombination
    apply Finset.sum_eq_zero
    intro a ha
    simp [residue, Nat.mod_eq_zero_of_dvd (hL a ha)]
  rw [hzero, hend, sub_self]

/-- Exact square completion for the actual finite residue combination.
All jumps, including their signed mixed contributions, occur in the square. -/
theorem finite_smooth_residue_jump_square_completion
    (s : Finset ℕ) (c : ℕ → ℝ) (M : ℕ) (hM : 0 < M)
    (hpos : ∀ a ∈ s, 0 < a) (hdiv : ∀ a ∈ s, 2 ∣ a ∨ 3 ∣ a)
    (hperiod : ∀ a ∈ s, a ∣ 6 * M) (hc : ∑ a ∈ s, c a = 1) :
    (∑ k ∈ Finset.range (6 * M),
      sequenceForwardJump (finiteResidueCombination s c) k ^ 2) / (6 * (M : ℝ)) =
      1 / 2 + (∑ k ∈ Finset.range (6 * M),
        if k % 6 = 0 ∨ k % 6 = 4 then 0 else
          (sequenceForwardJump (finiteResidueCombination s c) k + 1 / 2) ^ 2) /
        (6 * (M : ℝ)) := by
  have hden : (6 * (M : ℝ)) ≠ 0 := by positivity
  have hw : (∑ k ∈ Finset.range (6 * M), (1 / (6 * (M : ℝ)))) = 1 := by
    simp
    field_simp
  have hf : (∑ k ∈ Finset.range (6 * M),
      (1 / (6 * (M : ℝ))) * sequenceForwardJump (finiteResidueCombination s c) k) = 0 := by
    rw [← Finset.mul_sum, finiteResidueCombination_forward_sum_zero s c _ hperiod,
      mul_zero]
  have hA : (∑ k ∈ Finset.range (6 * M), (1 / (6 * (M : ℝ))) *
      (if k % 6 = 0 ∨ k % 6 = 4 then 1 else 0)) = 1 / 3 := by
    rw [← Finset.mul_sum, prime_to_six_forward_classes_count]
    field_simp
    norm_num
  have h := jump_average_square_completion (Finset.range (6 * M))
    (fun _ => 1 / (6 * (M : ℝ)))
    (sequenceForwardJump (finiteResidueCombination s c))
    (fun k => k % 6 = 0 ∨ k % 6 = 4) hw hf hA
    (fun k _ hk => finiteResidueCombination_forward_class s c hpos hdiv hc k hk)
  simpa only [← Finset.mul_sum, div_eq_mul_inv, one_div, mul_comm, one_mul, mul_one] using h

theorem finite_smooth_residue_jump_energy_ge
    (s : Finset ℕ) (c : ℕ → ℝ) (M : ℕ) (hM : 0 < M)
    (hpos : ∀ a ∈ s, 0 < a) (hdiv : ∀ a ∈ s, 2 ∣ a ∨ 3 ∣ a)
    (hperiod : ∀ a ∈ s, a ∣ 6 * M) (hc : ∑ a ∈ s, c a = 1) :
    1 / 2 ≤ (∑ k ∈ Finset.range (6 * M),
      sequenceForwardJump (finiteResidueCombination s c) k ^ 2) / (6 * (M : ℝ)) := by
  rw [finite_smooth_residue_jump_square_completion s c M hM hpos hdiv hperiod hc]
  have hs : 0 ≤ ∑ k ∈ Finset.range (6 * M),
      if k % 6 = 0 ∨ k % 6 = 4 then (0 : ℝ) else
        (sequenceForwardJump (finiteResidueCombination s c) k + 1 / 2) ^ 2 := by
    apply Finset.sum_nonneg
    intro k hk
    split_ifs <;> positivity
  have hd : 0 ≤ (6 * (M : ℝ)) := by positivity
  linarith [div_nonneg hs hd]

end
end RiemannResearch.RH.Pareto

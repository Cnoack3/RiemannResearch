import RiemannResearch.RH.OptimizedResiduePackets
import Mathlib.NumberTheory.Harmonic.Defs

/-!
# The exact harmonic energy term of the optimized seed

Source: user-provided `RH_CRT_Packet_Research_2026-09-09.md`, equation (17).
All four harmonic terms, including the positive common-divisibility term,
are retained. The identities hold for every finite cutoff.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

private theorem floor_divisor_step (a N : ℕ) (ha : 0 < a) :
    (N + 1) / a = N / a + if a ∣ N + 1 then 1 else 0 := by
  have ha0 : (a : ℝ) ≠ 0 := by positivity
  have hN : (N : ℝ) = residue a N + (a : ℝ) * (N / a : ℕ) := by
    unfold residue
    exact_mod_cast (Nat.mod_add_div N a).symm
  have hS : (N : ℝ) + 1 = residue a (N + 1) + (a : ℝ) * ((N + 1) / a : ℕ) := by
    unfold residue
    exact_mod_cast (Nat.mod_add_div (N + 1) a).symm
  have hd := residue_difference a (N + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hd
  by_cases he : a ∣ N + 1
  · rw [if_pos he] at hd ⊢
    have hp : (a : ℝ) * ((N + 1) / a : ℕ) = (a : ℝ) * ((N / a : ℕ) + 1) := by
      nlinarith
    have hq := mul_left_cancel₀ ha0 hp
    exact_mod_cast hq
  · rw [if_neg he] at hd ⊢
    have hp : (a : ℝ) * ((N + 1) / a : ℕ) = (a : ℝ) * (N / a : ℕ) := by
      nlinarith
    have hq := mul_left_cancel₀ ha0 hp
    simpa only [Nat.add_zero] using (show (N + 1) / a = N / a by exact_mod_cast hq)

/-- Exact reciprocal sum of all multiples up to an arbitrary cutoff. -/
theorem harmonic_divisibility_sum (a N : ℕ) (ha : 0 < a) :
    (∑ k ∈ Finset.range N,
      if a ∣ k + 1 then (a : ℝ) / ((k : ℝ) + 1) else 0) =
      (harmonic (N / a) : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, floor_divisor_step a N ha]
    by_cases hd : a ∣ N + 1
    · rw [if_pos hd, if_pos hd, harmonic_succ]
      push_cast
      congr 1
      have hmul : a * (N / a + 1) = N + 1 := by
        have h := Nat.mul_div_cancel' hd
        rw [floor_divisor_step a N ha, if_pos hd] at h
        exact h
      have hden : (N : ℝ) + 1 = (a : ℝ) * ((N / a : ℕ) + 1) := by
        exact_mod_cast hmul.symm
      rw [hden]
      have ha0 : (a : ℝ) ≠ 0 := by positivity
      have hq0 : ((N / a : ℕ) : ℝ) + 1 ≠ 0 := by positivity
      field_simp [ha0, hq0]
    · simp [hd]

private theorem real_harmonic_partial_sum (N : ℕ) :
    (∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1)) = (harmonic N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, harmonic_succ, ih]
    push_cast
    simp only [one_div]

/-- Actual optimized jump squares, with the intersection correction present. -/
theorem optimizedResidueSeed_jump_square (k : ℕ) :
    sequenceForwardJump optimizedResidueSeed k ^ 2 =
      1 - (3 / 4 : ℝ) * (if 2 ∣ k + 1 then 1 else 0) -
        (3 / 4 : ℝ) * (if 3 ∣ k + 1 then 1 else 0) +
        (3 / 4 : ℝ) * (if 6 ∣ k + 1 then 1 else 0) := by
  rw [optimizedResidueSeed_forwardJump]
  have h2 : (k + 1) % 2 = ((k + 1) % 6) % 2 := by omega
  have h3 : (k + 1) % 3 = ((k + 1) % 6) % 3 := by omega
  have h6 := Nat.mod_lt (k + 1) (by decide : 0 < 6)
  interval_cases hr : (k + 1) % 6 <;>
    norm_num [Nat.dvd_iff_mod_eq_zero, h2, h3, hr]

/-- Exact finite harmonic identity for the improved packet's leading energy. -/
theorem optimizedResidueSeed_harmonic_energy (N : ℕ) :
    (∑ k ∈ Finset.range N,
      sequenceForwardJump optimizedResidueSeed k ^ 2 / ((k : ℝ) + 1)) =
      (harmonic N : ℝ) - (3 / 8 : ℝ) * (harmonic (N / 2) : ℝ) -
        (1 / 4 : ℝ) * (harmonic (N / 3) : ℝ) +
        (1 / 8 : ℝ) * (harmonic (N / 6) : ℝ) := by
  have hk (k : ℕ) :
      sequenceForwardJump optimizedResidueSeed k ^ 2 / ((k : ℝ) + 1) =
        1 / ((k : ℝ) + 1) -
          (3 / 8 : ℝ) * (if 2 ∣ k + 1 then 2 / ((k : ℝ) + 1) else 0) -
          (1 / 4 : ℝ) * (if 3 ∣ k + 1 then 3 / ((k : ℝ) + 1) else 0) +
          (1 / 8 : ℝ) * (if 6 ∣ k + 1 then 6 / ((k : ℝ) + 1) else 0) := by
    rw [optimizedResidueSeed_jump_square]
    split_ifs <;> ring
  simp_rw [hk]
  have h2 : (∑ k ∈ Finset.range N,
      if 2 ∣ k + 1 then (2 : ℝ) / ((k : ℝ) + 1) else 0) =
        (harmonic (N / 2) : ℝ) := by
    simpa using harmonic_divisibility_sum 2 N (by decide)
  have h3 : (∑ k ∈ Finset.range N,
      if 3 ∣ k + 1 then (3 : ℝ) / ((k : ℝ) + 1) else 0) =
        (harmonic (N / 3) : ℝ) := by
    simpa using harmonic_divisibility_sum 3 N (by decide)
  have h6 : (∑ k ∈ Finset.range N,
      if 6 ∣ k + 1 then (6 : ℝ) / ((k : ℝ) + 1) else 0) =
        (harmonic (N / 6) : ℝ) := by
    simpa using harmonic_divisibility_sum 6 N (by decide)
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    real_harmonic_partial_sum, h2, h3, h6]

end
end RiemannResearch.RH.Pareto

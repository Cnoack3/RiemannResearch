/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoDilation
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Finite independence of positive residue sequences

Source: independently derived continuation of Christian Noack's arithmetic
research, 15 September 2026. Evaluation at one and at the smallest nonzero
coefficient's modulus proves independence. The residue at modulus one is
excluded because it is identically zero.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto

/-- Every finite relation among the sequences `residue n`, for `n ≥ 2`, is zero. -/
theorem finite_residue_coefficients_zero (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ n ∈ s, 2 ≤ n)
    (hz : ∀ k : ℕ, ∑ n ∈ s, c n * residue n k = 0) :
    ∀ n ∈ s, c n = 0 := by
  classical
  intro n hn
  by_contra hn0
  let t := s.filter (fun i => c i ≠ 0)
  have ht : t.Nonempty := ⟨n, Finset.mem_filter.mpr ⟨hn, hn0⟩⟩
  let m := t.min' ht
  have hmt : m ∈ t := Finset.min'_mem t ht
  have hms : m ∈ s := (Finset.mem_filter.mp hmt).1
  have hcm : c m ≠ 0 := (Finset.mem_filter.mp hmt).2
  have hm2 : 2 ≤ m := hs m hms
  have hleast (i : ℕ) (hi : i ∈ s) (hci : c i ≠ 0) : m ≤ i :=
    Finset.min'_le t i (Finset.mem_filter.mpr ⟨hi, hci⟩)
  have heval : (∑ i ∈ s, c i * (residue i m - (m:ℝ)*residue i 1)) = 0 := by
    calc
      _ = (∑ i ∈ s, c i * residue i m) -
          (m:ℝ)*(∑ i ∈ s, c i * residue i 1) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [hz m, hz 1]; ring
  have hone : (∑ i ∈ s, c i * (residue i m - (m:ℝ)*residue i 1)) =
      -(m:ℝ)*c m := by
    calc
      _ = c m * (residue m m-(m:ℝ)*residue m 1) := by
        apply Finset.sum_eq_single m
        · intro i hi him
          by_cases hci : c i = 0
          · simp [hci]
          · have hmi : m < i := lt_of_le_of_ne (hleast i hi hci) (Ne.symm him)
            have hi1 : 1 < i := by omega
            simp [residue, Nat.mod_eq_of_lt hmi, Nat.mod_eq_of_lt hi1]
        · intro hm
          exact False.elim (hm hms)
      _ = -(m:ℝ)*c m := by
        simp [residue, Nat.mod_eq_of_lt (show 1 < m by omega)]
        ring
  have hm0 : (m:ℝ) ≠ 0 := by positivity
  have hc0 : c m = 0 := by
    have hmprod : (m:ℝ)*c m = 0 := by linarith [heval, hone]
    exact (mul_eq_zero.mp hmprod).resolve_left hm0
  exact hcm hc0

end RiemannResearch.RH.Pareto

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Finite congruence solvability does not imply an integer solution

Source: the categorical CRT research note of 2026-11-14. This distinguishes
the profinite completion used by the RH program from the original integers.
-/

namespace InfiniteCRT

theorem finite_power_two_and_three_solvable (F : Finset ℕ) :
    ∃ x : ℤ, (∀ n ∈ F, Int.ModEq ((2 : ℤ) ^ n) x 0) ∧ Int.ModEq 3 x 1 := by
  classical
  let N := F.sup id
  refine ⟨(4 : ℤ) ^ N, ?_, ?_⟩
  · intro n hn
    have hnN : n ≤ N := Finset.le_sup (f := id) hn
    have hn2N : n ≤ 2 * N := by omega
    have hd : (2 : ℤ) ^ n ∣ (4 : ℤ) ^ N := by
      have hpow : (4 : ℤ) ^ N = (2 : ℤ) ^ (2 * N) := by
        rw [pow_mul]
        norm_num
      rw [hpow]
      exact pow_dvd_pow 2 hn2N
    apply Int.modEq_of_dvd
    obtain ⟨k, hk⟩ := hd
    refine ⟨-k, ?_⟩
    rw [hk]; ring
  · simpa using (show Int.ModEq (3 : ℤ) 4 1 from by decide).pow N

theorem eq_zero_of_all_power_two_dvd {x : ℤ} (hx : ∀ n : ℕ, (2 : ℤ) ^ n ∣ x) :
    x = 0 := by
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hx x.natAbs)
  simpa using (Nat.lt_two_pow_self (n := x.natAbs))

theorem no_integer_power_two_and_three_solution :
    ¬ ∃ x : ℤ, (∀ n : ℕ, Int.ModEq ((2 : ℤ) ^ n) x 0) ∧ Int.ModEq 3 x 1 := by
  rintro ⟨x, hx, h3⟩
  have hzero : x = 0 := eq_zero_of_all_power_two_dvd (fun n => by
    have h := (hx n).dvd
    simpa using h)
  subst x
  norm_num [Int.ModEq] at h3

end InfiniteCRT

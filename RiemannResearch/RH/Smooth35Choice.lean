import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Explicit smooth scales within a factor of two

Interleaving `3^a` and `5*3^(a-1)` gives a `{3,5}`-smooth number strictly
between `n` and `2*n` for every `n≥3`. The least smooth number above `n`
therefore obeys the same bound. No asymptotic gap theorem is used.
-/

namespace RiemannResearch.RH.Pareto

/-- An elementary smooth-scale choice from two interleaved geometric sequences. -/
def smooth35DyadicChoice (n : ℕ) : ℕ :=
  if n < 5 * 3^(Nat.log 3 n - 1) then 5 * 3^(Nat.log 3 n - 1)
  else 3^(Nat.log 3 n + 1)

/-- The concrete choice is smooth, strictly above `n`, and at most `2*n`. -/
theorem smooth35DyadicChoice_spec (n : ℕ) (hn : 3 ≤ n) :
    (n < smooth35DyadicChoice n ∧ smooth35DyadicChoice n ≤ 2*n) ∧
      ∃ a b : ℕ, smooth35DyadicChoice n = 3^a * 5^b := by
  have hn0 : n ≠ 0 := by omega
  have ha : 0 < Nat.log 3 n := Nat.log_pos (by norm_num) hn
  have hpow : 3^(Nat.log 3 n) = 3 * 3^(Nat.log 3 n - 1) := by
    calc
      _ = 3^((Nat.log 3 n - 1)+1) := by congr 1; omega
      _ = _ := by rw [pow_succ]; ring
  have hpow2 : 3^(Nat.log 3 n + 1) = 9 * 3^(Nat.log 3 n - 1) := by
    rw [pow_succ, hpow]
    ring
  have hlow := Nat.pow_log_le_self 3 hn0
  rw [hpow] at hlow
  have hhigh : n < 3^(Nat.log 3 n + 1) := by
    simpa only [Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (by norm_num : 1 < 3) n
  unfold smooth35DyadicChoice
  split_ifs with hmid
  · refine ⟨⟨hmid, ?_⟩, ?_⟩
    · omega
    · exact ⟨Nat.log 3 n - 1, 1, by simp [Nat.mul_comm]⟩
  · refine ⟨⟨hhigh, ?_⟩, ?_⟩
    · rw [hpow2]
      omega
    · exact ⟨Nat.log 3 n + 1, 0, by simp⟩

/-- Existence for all natural inputs, including those below three. -/
theorem exists_smooth35_above (n : ℕ) :
    ∃ E : ℕ, n < E ∧ ∃ a b : ℕ, E = 3^a * 5^b := by
  have h := smooth35DyadicChoice_spec (max n 3) (le_max_right n 3)
  exact ⟨smooth35DyadicChoice (max n 3),
    lt_of_le_of_lt (le_max_left n 3) h.1.1, h.2⟩

/-- The actual least `{3,5}`-smooth integer strictly above the input. -/
noncomputable def leastSmooth35Above (n : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_smooth35_above n)

theorem leastSmooth35Above_spec (n : ℕ) :
    n < leastSmooth35Above n ∧
      ∃ a b : ℕ, leastSmooth35Above n = 3^a * 5^b := by
  classical
  exact Nat.find_spec (exists_smooth35_above n)

/-- Minimality against every genuine smooth candidate. -/
theorem leastSmooth35Above_le {n E : ℕ}
    (hnE : n < E) (hE : ∃ a b : ℕ, E = 3^a * 5^b) :
    leastSmooth35Above n ≤ E := by
  classical
  exact Nat.find_min' (exists_smooth35_above n) ⟨hnE, hE⟩

/-- In particular, the proposed least smooth scales are within a factor of two. -/
theorem leastSmooth35Above_le_twice (n : ℕ) (hn : 3 ≤ n) :
    leastSmooth35Above n ≤ 2*n := by
  have h := smooth35DyadicChoice_spec n hn
  exact (leastSmooth35Above_le h.1.1 h.2).trans h.1.2

end RiemannResearch.RH.Pareto

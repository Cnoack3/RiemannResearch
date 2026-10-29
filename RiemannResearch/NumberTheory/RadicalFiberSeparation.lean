/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Data.Finset.Disjoint
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Separation of adjacent pairs in a radical fiber

Source: user-provided multi-fiber energy argument, 29 October 2026.
Distinct positive multiples of d >= 2 cannot be consecutive. This proves
physical-coordinate disjointness for arbitrary radical fibers and for powers.
-/

namespace Nat
open UniqueFactorizationMonoid

theorem adjacent_pairs_disjoint_of_common_divisor {d m n : ℕ}
    (hd : 2 ≤ d) (hm : 0 < m) (hn : 0 < n)
    (hdm : d ∣ m) (hdn : d ∣ n) (hmn : m ≠ n) :
    Disjoint ({m - 1, m} : Finset ℕ) {n - 1, n} := by
  have hmn1 : m + 1 ≠ n := by
    intro h
    have hdiv := Nat.dvd_sub hdn hdm
    rw [← h] at hdiv
    have hd1 : d = 1 := Nat.dvd_one.mp (by simpa using hdiv)
    omega
  have hnm1 : n + 1 ≠ m := by
    intro h
    have hdiv := Nat.dvd_sub hdm hdn
    rw [← h] at hdiv
    have hd1 : d = 1 := Nat.dvd_one.mp (by simpa using hdiv)
    omega
  apply Finset.disjoint_left.mpr
  intro x hx hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  omega

theorem radical_fiber_pairs_disjoint {d m n : ℕ}
    (hd : 2 ≤ d) (hm : 0 < m) (hn : 0 < n)
    (hrm : radical m = d) (hrn : radical n = d) (hmn : m ≠ n) :
    Disjoint ({m - 1, m} : Finset ℕ) {n - 1, n} := by
  apply adjacent_pairs_disjoint_of_common_divisor hd hm hn
    (show d ∣ m by rw [← hrm]; exact radical_dvd_self)
    (show d ∣ n by rw [← hrn]; exact radical_dvd_self) hmn

theorem radical_pow_eq_of_squarefree {d k : ℕ}
    (hd : 2 ≤ d) (hs : Squarefree d) (hk : k ≠ 0) :
    radical (d ^ k) = d := by
  rw [radical_pow d hk]
  exact Nat.dvd_antisymm radical_dvd_self
    ((dvd_radical_iff hs.isRadical (by omega : d ≠ 0)).mpr (dvd_refl d))

theorem power_fiber_beyond_head {d k : ℕ} (hd : 2 ≤ d) (hk : 2 ≤ k) :
    d + 1 < d ^ k := by
  have h := Nat.pow_le_pow_right (by omega : 0 < d) hk
  nlinarith

theorem distinct_power_fiber_pairs_disjoint {d k l : ℕ}
    (hd : 2 ≤ d) (hs : Squarefree d) (hk : 2 ≤ k) (hl : 2 ≤ l)
    (hkl : k ≠ l) :
    Disjoint ({d ^ k - 1, d ^ k} : Finset ℕ) {d ^ l - 1, d ^ l} := by
  have hne : d ^ k ≠ d ^ l := by
    intro h
    rcases lt_or_gt_of_ne hkl with hkl | hlk
    · have := Nat.pow_lt_pow_right (by omega : 1 < d) hkl
      omega
    · have := Nat.pow_lt_pow_right (by omega : 1 < d) hlk
      omega
  exact radical_fiber_pairs_disjoint hd (by have := power_fiber_beyond_head hd hk; omega)
    (by have := power_fiber_beyond_head hd hl; omega)
    (radical_pow_eq_of_squarefree hd hs (by omega))
    (radical_pow_eq_of_squarefree hd hs (by omega)) hne

end Nat

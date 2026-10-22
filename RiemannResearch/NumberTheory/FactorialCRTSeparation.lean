/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.ModEq
import Lean.Elab.Tactic.Omega

/-!
# Factorial CRT separation and escaping witnesses

This module formalizes the quantifier distinction in Section 3 of the user's
`RH_CRT_Orbit_Exhaustion_and_Doubling_Invariance_2026-09-20(3).md`:
ordinary integers are separated by their residues modulo all factorials, but
witnesses that agree with a fixed integer at every finite level may escape to
infinity and never equal that integer.

The argument is arithmetic and unconditional. No profinite-space or DPP
construction, and no Riemann-hypothesis premise, is needed.
-/

namespace RiemannResearch.NumberTheory.FactorialCRTSeparation

/-- All factorial congruences determine a natural number uniquely. -/
theorem eq_of_all_factorial_modEq {n m : ℕ}
    (h : ∀ j : ℕ, Nat.ModEq (Nat.factorial j) n m) : n = m := by
  have hfac := Nat.self_le_factorial (n + m + 2)
  exact (h (n + m + 2)).eq_of_lt_of_lt (by omega) (by omega)

/-- The natural-number version of uniqueness of an integer's full CRT data. -/
theorem all_factorial_modEq_iff_eq (n m : ℕ) :
    (∀ j : ℕ, Nat.ModEq (Nat.factorial j) n m) ↔ n = m := by
  constructor
  · exact eq_of_all_factorial_modEq
  · intro h
    subst m
    intro j
    exact Nat.ModEq.refl n

/-- In particular, simultaneous agreement with `1` forces equality with `1`. -/
theorem all_factorial_modEq_one_iff (n : ℕ) :
    (∀ j : ℕ, Nat.ModEq (Nat.factorial j) n 1) ↔ n = 1 :=
  all_factorial_modEq_iff_eq n 1

/-- Explicit witnesses approaching `1` through factorial congruence classes. -/
def escape (j : ℕ) : ℕ := 1 + Nat.factorial j

/-- Each witness is a positive integer distinct from `1`. -/
theorem one_lt_escape (j : ℕ) : 1 < escape j := by
  have hfac := Nat.factorial_pos j
  unfold escape
  omega

theorem escape_ne_one (j : ℕ) : escape j ≠ 1 :=
  ne_of_gt (one_lt_escape j)

/-- The ordinary size of the witnesses grows at least linearly with the index. -/
theorem index_lt_escape (j : ℕ) : j < escape j := by
  have hfac := Nat.self_le_factorial j
  unfold escape
  omega

/-- Once the index reaches `k`, its witness agrees with `1` modulo `k!`. -/
theorem escape_modEq {k j : ℕ} (hkj : k ≤ j) :
    Nat.ModEq (Nat.factorial k) (escape j) 1 := by
  unfold escape
  exact Nat.add_modEq_left_iff.mpr (Nat.factorial_dvd_factorial hkj)

/-- Agreement persists at every later index for each fixed factorial modulus. -/
theorem escape_agrees_eventually (k : ℕ) :
    ∀ j : ℕ, k ≤ j → Nat.ModEq (Nat.factorial k) (escape j) 1 := by
  intro j hkj
  exact escape_modEq hkj

/-- Every finite collection of factorial conditions has a witness other than `1`. -/
theorem finite_factorial_prefix_has_witness (j : ℕ) :
    ∃ n : ℕ, 1 < n ∧
      ∀ k : ℕ, k ≤ j → Nat.ModEq (Nat.factorial k) n 1 := by
  refine ⟨escape j, one_lt_escape j, ?_⟩
  intro k hkj
  exact escape_modEq hkj

/-- Such finite-level witnesses can be chosen beyond any prescribed bound. -/
theorem finite_factorial_prefix_has_arbitrarily_large_witness (j B : ℕ) :
    ∃ n : ℕ, B < n ∧ 1 < n ∧
      ∀ k : ℕ, k ≤ j → Nat.ModEq (Nat.factorial k) n 1 := by
  refine ⟨escape (j + B), ?_, one_lt_escape (j + B), ?_⟩
  · have hsize := index_lt_escape (j + B)
    omega
  · intro k hkj
    exact escape_modEq (by omega)

/-- The weak quantifier order is satisfied by the escaping sequence. -/
theorem forall_exists_factorial_agreement :
    ∀ j : ℕ, ∃ n : ℕ, 1 < n ∧ Nat.ModEq (Nat.factorial j) n 1 := by
  intro j
  exact ⟨escape j, one_lt_escape j, escape_modEq (Nat.le_refl j)⟩

/-- The strong quantifier order fails on the same set of positive integers. -/
theorem not_exists_forall_factorial_agreement :
    ¬ ∃ n : ℕ, 1 < n ∧ ∀ j : ℕ, Nat.ModEq (Nat.factorial j) n 1 := by
  rintro ⟨n, hn, hmod⟩
  have heq : n = 1 := eq_of_all_factorial_modEq hmod
  omega

/-- A concrete unconditional counterexample to exchanging the two quantifiers. -/
theorem factorial_quantifier_distinction :
    (∀ j : ℕ, ∃ n : ℕ, 1 < n ∧ Nat.ModEq (Nat.factorial j) n 1) ∧
      ¬ (∃ n : ℕ, 1 < n ∧ ∀ j : ℕ, Nat.ModEq (Nat.factorial j) n 1) :=
  ⟨forall_exists_factorial_agreement, not_exists_forall_factorial_agreement⟩

end RiemannResearch.NumberTheory.FactorialCRTSeparation

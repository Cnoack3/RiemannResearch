/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.GroupTheory.Solvable
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.GCD

/-!
# Binary-icosahedral arithmetic and nonsolvability guard

The finite order calculations are the numerical backbone of the two-gauge
reduction.  The module also checks the dimension gap and amalgam
Euler-characteristic arithmetic used by the two no-go statements in
Propositions 6.22 and 6.24. The generic perfect-group lemma records why a
prime-cyclic normal tower cannot be invoked for a nontrivial perfect Galois group such as
`SL₂(𝔽₅)`; a separate finite-group certificate is still needed to instantiate
that example in Lean.
-/

namespace RiemannResearch.E8

/-- A nontrivial perfect group is not solvable. This prevents a cyclic-prime
induction from being silently applied to a perfect Galois group. -/
theorem not_solvable_of_nontrivial_perfect
    (G : Type*) [Group G] [Nontrivial G]
    (hperfect : commutator G = ⊤) :
    ¬ Group.IsSolvable G := by
  intro hsolv
  obtain ⟨n, hn⟩ := hsolv.solvable
  have hall : ∀ m : ℕ, derivedSeries G m = ⊤ := by
    intro m
    induction m with
    | zero => exact derivedSeries_zero G
    | succ m ih =>
        rw [show m + 1 = Nat.succ m from rfl, derivedSeries_succ, ih]
        exact hperfect
  rw [hall n] at hn
  exact top_ne_bot hn

/-- For subgroup orders `|H| = 24`, `|K| = 20`, and
`|H ∩ K| = 4` inside a group of order 120, the fixed-field degrees are
5, 6, and 30, and the first two degrees are coprime. -/
theorem binaryIcosahedral_orders_and_indices :
    120 = 2 ^ 3 * 3 * 5 ∧
      24 * 20 = 4 * 120 ∧
      120 / 24 = 5 ∧
      120 / 20 = 6 ∧
      120 / 4 = 30 ∧
      Nat.gcd 5 6 = 1 := by
  norm_num
/-- The elementary order and index calculations in PDF Proposition 6.15. -/
theorem serreIIProgram_binaryIcosahedral_index_arithmetic :
    12 * 10 / 2 = 60 ∧ 24 * 20 / 4 = 120 ∧
      120 / 24 = 5 ∧ 120 / 20 = 6 := by
  norm_num

/-- The source and target degree factors in the Weil-restriction dimension
comparison from Proposition 6.22 of the 5 August 2026 E8 memorandum.

This is the exact numerical kernel of the dimension obstruction.  The
algebraic-geometric facts that dimensions multiply under Weil restriction and
that a lower-dimensional constructible image cannot cover the target remain
separate inputs. -/
theorem binaryIcosahedral_weilRestriction_dimension_gap
    (d : ℕ) (hd : 0 < d) :
    (5 + 6) * d < (5 * 6) * d := by
  exact Nat.mul_lt_mul_of_pos_right (by norm_num) hd

/-- The specialization of the Proposition 6.22 dimension comparison to
dim E8 = 248. -/
theorem serreIIProgram_proposition622_dimension_arithmetic :
    (5 + 6) * 248 = 2728 ∧
      (5 * 6) * 248 = 7440 ∧
      (5 + 6) * 248 < (5 * 6) * 248 := by
  norm_num

/-- The rational Euler-characteristic calculation in Proposition 6.24 of the
5 August 2026 E8 memorandum. -/
theorem serreIIProgram_proposition624_eulerCharacteristic :
    (1 : ℚ) / 24 + 1 / 20 - 1 / 4 = -(19 : ℚ) / 120 := by
  norm_num

/-- Multiplicativity at index 120 turns the displayed amalgam Euler
characteristic into -19; the free-group formula chi(F_r) = 1 - r then gives
rank 20.  Bass--Serre freeness and nonsplitting are not asserted here. -/
theorem serreIIProgram_proposition624_freeKernelRank_arithmetic :
    120 * (-(19 : ℚ) / 120) = -19 ∧
      (1 : ℚ) - 20 = -19 := by
  norm_num

end RiemannResearch.E8

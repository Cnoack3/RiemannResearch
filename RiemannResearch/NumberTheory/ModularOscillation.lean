/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
/-!
# Bounded oscillation on congruence classes

An elementary finite-representative argument: a common oscillation bound on
each residue class of one positive modulus gives a global bound. The proof
retains the explicit finite sum of values at representatives M through 2M-1.
This supplies a weaker arithmetic target than uniform continuity for the
displacement criterion in QSquarefreeCRTContinuity.
Source: user-directed infinite-CRT continuity investigation, 4 November 2026;
the finite-representative argument is standard.
-/

namespace RiemannResearch.NumberTheory.ModularOscillation
open scoped BigOperators
theorem bounded_of_modular_oscillation (a : ℕ → ℝ) (M : ℕ) (hM : 0 < M)
    (C : ℝ) (h : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
      n % M = m % M → |a n - a m| ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, 1 ≤ n → |a n| ≤ D := by
  let S : ℝ := ∑ r ∈ Finset.range M, |a (r + M)|
  refine ⟨max (C + S) 0, le_max_right _ _, ?_⟩
  intro n hn
  have hrep : 1 ≤ n % M + M := by omega
  have hmod : n % M = (n % M + M) % M := by simp
  have hnear := h n (n % M + M) hn hrep hmod
  have hsum : |a (n % M + M)| ≤ S := by
    exact Finset.single_le_sum (f := fun r => |a (r + M)|)
      (fun r hr => abs_nonneg _) (Finset.mem_range.mpr (Nat.mod_lt _ hM))
  calc
    |a n| = |(a n - a (n % M + M)) + a (n % M + M)| := by congr 1; ring
    _ ≤ |a n - a (n % M + M)| + |a (n % M + M)| := abs_add_le _ _
    _ ≤ C + S := add_le_add hnear hsum
    _ ≤ max (C + S) 0 := le_max_left _ _
end RiemannResearch.NumberTheory.ModularOscillation

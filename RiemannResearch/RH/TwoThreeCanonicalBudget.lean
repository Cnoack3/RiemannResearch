/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.FiniteTwoSeedHeadMean
import Mathlib.Tactic.Ring

/-!
# Exact canonical spanning family at every ordinary two-seed budget

Source: independently derived continuation of Christian Noack's arithmetic
research, 15 September 2026. All ternary generators and binary generators at
indices not divisible by three span the original finite budget. Elimination
never enlarges the budget. The dimension and basis-independence conclusions
in the accompanying research note are not asserted by this module.
-/

namespace RiemannResearch.RH.Pareto.FiniteTwoSeedCompletion
noncomputable section

/-- The commuting square eliminates a binary column at an index divisible by three. -/
theorem binary_three_elimination (k : ℕ) :
    dilation (3*k) (residue 2) = dilation (2*k) (residue 3) +
      dilation k (residue 2) - dilation k (residue 3) := by
  funext n
  simp only [Pi.add_apply, Pi.sub_apply, residue_mul_floor]
  simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  ring

/-- Retain every ternary column and exactly the binary columns with 3 ∤ n. -/
def canonicalSpan (M : ℕ) : Submodule ℝ (ℕ → ℝ) :=
  Submodule.span ℝ {f | ∃ n : ℕ, 0 < n ∧ n ≤ M ∧
    (f = dilation n (residue 3) ∨ (¬ 3 ∣ n) ∧ f = dilation n (residue 2))}

theorem canonical_ternary_mem (M n : ℕ) (hn : 0 < n) (hnM : n ≤ M) :
    dilation n (residue 3) ∈ canonicalSpan M :=
  Submodule.subset_span ⟨n, hn, hnM, Or.inl rfl⟩

theorem canonical_binary_mem (M n : ℕ) (hn : 0 < n) (hnM : n ≤ M)
    (h3 : ¬ 3 ∣ n) : dilation n (residue 2) ∈ canonicalSpan M :=
  Submodule.subset_span ⟨n, hn, hnM, Or.inr ⟨h3, rfl⟩⟩

/-- Strong induction implements elimination without exceeding the original budget. -/
theorem every_binary_mem_canonical (M n : ℕ) (hn : 0 < n) (hnM : n ≤ M) :
    dilation n (residue 2) ∈ canonicalSpan M := by
  have hall : ∀ n : ℕ, n ≤ M → 0 < n → dilation n (residue 2) ∈ canonicalSpan M := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hnM hn
      by_cases h3 : 3 ∣ n
      · obtain ⟨k, rfl⟩ := h3
        have hk : 0 < k := by omega
        have hkM : k ≤ M := by omega
        have h2kM : 2*k ≤ M := by omega
        rw [binary_three_elimination]
        exact (canonicalSpan M).sub_mem
          ((canonicalSpan M).add_mem (canonical_ternary_mem M (2*k) (by omega) h2kM)
            (ih k (by omega) hkM hk))
          (canonical_ternary_mem M k hk hkM)
      · exact canonical_binary_mem M n hn hnM h3
  exact hall n hnM hn

/-- This restriction of the generator list leaves the actual finite span unchanged. -/
theorem canonicalSpan_eq_budgetSpan (M : ℕ) : canonicalSpan M = budgetSpan M := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨n, hn, hnM, h⟩
    rcases h with rfl | ⟨h3, rfl⟩
    · exact generator_mem M 3 n (Or.inr rfl) hn hnM
    · exact generator_mem M 2 n (Or.inl rfl) hn hnM
  · apply Submodule.span_le.mpr
    rintro f ⟨a, ha, n, hn, hnM, rfl⟩
    rcases ha with rfl | rfl
    · exact every_binary_mem_canonical M n hn hnM
    · exact canonical_ternary_mem M n hn hnM

end
end RiemannResearch.RH.Pareto.FiniteTwoSeedCompletion

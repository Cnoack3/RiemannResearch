import RiemannResearch.LinearAlgebra.BalancedGridSpan
import RiemannResearch.RH.ThresholdDilationAlgebra
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Exact balanced arithmetic dictionary for the two-seed finite span

Source: RH_Minimal_Seeds_Canonical_Basis_and_Arithmetic_Charge_20260914.md,
Theorem 3.1. The dictionary is indexed by the unique representation
`m = 2^a * 3^b * u`, with positive `u` indivisible by 2 and 3.
The present span theorem does not need uniqueness of that representation.
Every positive dilation is decomposed and its omitted edge recovered by a
finite balancing path. No approximation, norm bound, or RH hypothesis is used.
-/

namespace RiemannResearch.RH.Pareto

open RiemannResearch.LinearAlgebra

noncomputable section

/-- A positive rough part after removing all factors 2 and 3. -/
def IsTwoThreeRough (u : ℕ) : Prop := 0 < u ∧ ¬2 ∣ u ∧ ¬3 ∣ u

/-- Existence of the actual arithmetic decomposition, by factor stripping. -/
theorem exists_twoThree_rough_decomposition (m : ℕ) (hm : 0 < m) :
    ∃ u a b : ℕ, IsTwoThreeRough u ∧ m = 2 ^ a * 3 ^ b * u := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases h2 : 2 ∣ m
    · obtain ⟨d, hd⟩ := h2
      have hdpos : 0 < d := by omega
      have hdm : d < m := by omega
      obtain ⟨u, a, b, hu, he⟩ := ih d hdm hdpos
      refine ⟨u, a + 1, b, hu, ?_⟩
      rw [hd, he, pow_succ]
      ring
    · by_cases h3 : 3 ∣ m
      · obtain ⟨d, hd⟩ := h3
        have hdpos : 0 < d := by omega
        have hdm : d < m := by omega
        obtain ⟨u, a, b, hu, he⟩ := ih d hdm hdpos
        refine ⟨u, a, b + 1, hu, ?_⟩
        rw [hd, he, pow_succ]
        ring
      · exact ⟨m, 0, 0, ⟨hm, h2, h3⟩, by simp⟩

def balancedResidueVertex (u a b : ℕ) : ℕ → ℝ := residue (2 ^ a * 3 ^ b * u)

def balancedResidueEdge (u a b : ℕ) : ℕ → ℝ :=
  balancedGridEdge (balancedResidueVertex u) a b

def balancedResidueDictionary : Set (ℕ → ℝ) :=
  {f | ∃ u a b : ℕ, IsTwoThreeRough u ∧ f = balancedResidueEdge u a b}

def balancedResidueSpan : Submodule ℝ (ℕ → ℝ) :=
  Submodule.span ℝ balancedResidueDictionary

theorem balancedResidue_horizontal (u a b : ℕ) :
    balancedResidueVertex u (a + 1) b - balancedResidueVertex u a b =
      dilation (2 ^ a * 3 ^ b * u) (residue 2) := by
  have he : 2 ^ (a + 1) * 3 ^ b * u = (2 ^ a * 3 ^ b * u) * 2 := by
    rw [pow_succ]
    ring
  funext n
  simp only [balancedResidueVertex, Pi.sub_apply, residue_mul_floor, he]

theorem balancedResidue_vertical (u a b : ℕ) :
    balancedResidueVertex u a (b + 1) - balancedResidueVertex u a b =
      dilation (2 ^ a * 3 ^ b * u) (residue 3) := by
  have he : 2 ^ a * 3 ^ (b + 1) * u = (2 ^ a * 3 ^ b * u) * 3 := by
    rw [pow_succ]
    ring
  funext n
  simp only [balancedResidueVertex, Pi.sub_apply, residue_mul_floor, he]

/-- Exactly one of the original two generators is selected at each grid vertex. -/
theorem balancedResidueEdge_eq (u a b : ℕ) :
    balancedResidueEdge u a b =
      if a ≤ b then dilation (2 ^ a * 3 ^ b * u) (residue 2)
      else dilation (2 ^ a * 3 ^ b * u) (residue 3) := by
  unfold balancedResidueEdge balancedGridEdge
  split_ifs <;> first
    | exact balancedResidue_horizontal u a b
    | exact balancedResidue_vertical u a b

theorem balancedResidueGridSpan_le (u : ℕ) (hu : IsTwoThreeRough u) :
    balancedGridSpan ℝ (balancedResidueVertex u) ≤ balancedResidueSpan := by
  apply Submodule.span_le.mpr
  rintro f ⟨a, b, rfl⟩
  exact Submodule.subset_span ⟨u, a, b, hu, rfl⟩

theorem balancedResidueSpan_le_legal :
    balancedResidueSpan ≤ legalSeedSpan ({2, 3} : Set ℕ) := by
  apply Submodule.span_le.mpr
  rintro f ⟨u, a, b, hu, rfl⟩
  rw [balancedResidueEdge_eq]
  have hm : 0 < 2 ^ a * 3 ^ b * u :=
    Nat.mul_pos (Nat.mul_pos (pow_pos (by decide) a) (pow_pos (by decide) b)) hu.1
  split_ifs
  · exact dilation_generator_mem _ (by simp) hm
  · exact dilation_generator_mem _ (by simp) hm

/-- Both seed generators at every positive integer dilation are recovered. -/
theorem dilation_two_mem_balancedResidueSpan (m : ℕ) (hm : 0 < m) :
    dilation m (residue 2) ∈ balancedResidueSpan := by
  obtain ⟨u, a, b, hu, rfl⟩ := exists_twoThree_rough_decomposition m hm
  rw [← balancedResidue_horizontal]
  exact balancedResidueGridSpan_le u hu
    (balancedGrid_difference_mem (K := ℝ) (balancedResidueVertex u) a b (a + 1) b)

theorem dilation_three_mem_balancedResidueSpan (m : ℕ) (hm : 0 < m) :
    dilation m (residue 3) ∈ balancedResidueSpan := by
  obtain ⟨u, a, b, hu, rfl⟩ := exists_twoThree_rough_decomposition m hm
  rw [← balancedResidue_vertical]
  exact balancedResidueGridSpan_le u hu
    (balancedGrid_difference_mem (K := ℝ) (balancedResidueVertex u) a b a (b + 1))

/-- Unconditional equality of actual finite spans, before taking any closure. -/
theorem balancedResidueSpan_eq_twoSeedSpan :
    balancedResidueSpan = legalSeedSpan ({2, 3} : Set ℕ) := by
  apply le_antisymm balancedResidueSpan_le_legal
  apply Submodule.span_le.mpr
  rintro f ⟨p, hp, m, hm, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact dilation_two_mem_balancedResidueSpan m hm
  · exact dilation_three_mem_balancedResidueSpan m hm

/-- The only positive rough-grid indices at most four. -/
theorem rough_grid_le_four (u a b : ℕ) (hu : IsTwoThreeRough u)
    (h : 2 ^ a * 3 ^ b * u ≤ 4) :
    (u = 1 ∧ a = 0 ∧ b = 0) ∨ (u = 1 ∧ a = 1 ∧ b = 0) ∨
      (u = 1 ∧ a = 0 ∧ b = 1) ∨ (u = 1 ∧ a = 2 ∧ b = 0) := by
  have hu0 := hu.1
  have h2 : 0 < 2 ^ a := pow_pos (by decide) a
  have h3 : 0 < 3 ^ b := pow_pos (by decide) b
  have h23 : 0 < 2 ^ a * 3 ^ b := Nat.mul_pos h2 h3
  have hu4 : u ≤ 4 := by nlinarith
  have h24 : 2 ^ a ≤ 4 := by
    have hle : 2 ^ a ≤ 2 ^ a * 3 ^ b := by nlinarith
    have hle' : 2 ^ a * 3 ^ b ≤ 2 ^ a * 3 ^ b * u := by nlinarith
    omega
  have h34 : 3 ^ b ≤ 4 := by
    have hle : 3 ^ b ≤ 2 ^ a * 3 ^ b := by nlinarith
    have hle' : 2 ^ a * 3 ^ b ≤ 2 ^ a * 3 ^ b * u := by nlinarith
    omega
  have ha : a ≤ 2 := by
    by_contra hn
    have hp : 8 ≤ 2 ^ a := by
      simpa using Nat.pow_le_pow_right (show 0 < 2 by decide) (show 3 ≤ a by omega)
    omega
  have hb : b ≤ 1 := by
    by_contra hn
    have hp : 9 ≤ 3 ^ b := by
      simpa using Nat.pow_le_pow_right (show 0 < 3 by decide) (show 2 ≤ b by omega)
    omega
  interval_cases a <;> interval_cases b <;> interval_cases u <;>
    norm_num [IsTwoThreeRough] at *

end
end RiemannResearch.RH.Pareto

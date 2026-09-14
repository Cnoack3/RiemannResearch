import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

/-!
# Balancing two integer exponents preserves the finite difference span

Source: RH_Minimal_Seeds_Canonical_Basis_and_Arithmetic_Charge_20260914.md,
Theorem 3.1. The path proof is purely algebraic. No density assertion is assumed.
-/

namespace RiemannResearch.LinearAlgebra

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

def balancedGridEdge (x : ℕ → ℕ → E) (a b : ℕ) : E :=
  if a ≤ b then x (a + 1) b - x a b else x a (b + 1) - x a b

def balancedGridSpan (K : Type*) [Field K] [Module K E]
    (x : ℕ → ℕ → E) : Submodule K E :=
  Submodule.span K {v | ∃ a b, v = balancedGridEdge x a b}

theorem balancedGridEdge_mem (x : ℕ → ℕ → E) (a b : ℕ) :
    balancedGridEdge x a b ∈ balancedGridSpan K x :=
  Submodule.subset_span ⟨a, b, rfl⟩

theorem balancedGrid_horizontal_path (x : ℕ → ℕ → E) (a b k : ℕ)
    (h : a + k ≤ b) : x (a + k) b - x a b ∈ balancedGridSpan K x := by
  induction k with
  | zero => simpa using (balancedGridSpan K x).zero_mem
  | succ k ih =>
    have he := balancedGridEdge_mem (K := K) x (a + k) b
    rw [balancedGridEdge, if_pos (by omega)] at he
    have hi := (balancedGridSpan K x).add_mem he (ih (by omega))
    convert hi using 1 <;> simp only [Nat.add_succ] <;> abel

theorem balancedGrid_vertical_path (x : ℕ → ℕ → E) (a b k : ℕ)
    (h : b + k ≤ a) : x a (b + k) - x a b ∈ balancedGridSpan K x := by
  induction k with
  | zero => simpa using (balancedGridSpan K x).zero_mem
  | succ k ih =>
    have he := balancedGridEdge_mem (K := K) x a (b + k)
    rw [balancedGridEdge, if_neg (by omega)] at he
    have hi := (balancedGridSpan K x).add_mem he (ih (by omega))
    convert hi using 1 <;> simp only [Nat.add_succ] <;> abel

theorem balancedGrid_diagonal_step (x : ℕ → ℕ → E) (a : ℕ) :
    x (a + 1) (a + 1) - x a a ∈ balancedGridSpan K x := by
  have hh := balancedGridEdge_mem (K := K) x a a
  have hv := balancedGridEdge_mem (K := K) x (a + 1) a
  rw [balancedGridEdge, if_pos (le_refl a)] at hh
  rw [balancedGridEdge, if_neg (by omega)] at hv
  convert (balancedGridSpan K x).add_mem hv hh using 1 <;> abel

theorem balancedGrid_diagonal_path (x : ℕ → ℕ → E) (a k : ℕ) :
    x (a + k) (a + k) - x a a ∈ balancedGridSpan K x := by
  induction k with
  | zero => simpa using (balancedGridSpan K x).zero_mem
  | succ k ih =>
    have he := balancedGrid_diagonal_step (K := K) x (a + k)
    convert (balancedGridSpan K x).add_mem he ih using 1 <;>
      simp only [Nat.add_succ] <;> abel

theorem balancedGrid_to_diagonal (x : ℕ → ℕ → E) (a b L : ℕ)
    (ha : a ≤ L) (hb : b ≤ L) :
    x L L - x a b ∈ balancedGridSpan K x := by
  by_cases hab : a ≤ b
  · have h1 := balancedGrid_horizontal_path (K := K) x a b (b - a) (by omega)
    have h2 := balancedGrid_diagonal_path (K := K) x b (L - b)
    have he1 : a + (b - a) = b := by omega
    have he2 : b + (L - b) = L := by omega
    rw [he1] at h1
    rw [he2] at h2
    convert (balancedGridSpan K x).add_mem h2 h1 using 1 <;> abel
  · have h1 := balancedGrid_vertical_path (K := K) x a b (a - b) (by omega)
    have h2 := balancedGrid_diagonal_path (K := K) x a (L - a)
    have he1 : b + (a - b) = a := by omega
    have he2 : a + (L - a) = L := by omega
    rw [he1] at h1
    rw [he2] at h2
    convert (balancedGridSpan K x).add_mem h2 h1 using 1 <;> abel

/-- Every difference of two vertices is a finite signed sum of selected edges. -/
theorem balancedGrid_difference_mem (x : ℕ → ℕ → E) (a b c d : ℕ) :
    x c d - x a b ∈ balancedGridSpan K x := by
  let L := max (max a b) (max c d)
  have ha : a ≤ L := le_trans (le_max_left a b) (le_max_left _ _)
  have hb : b ≤ L := le_trans (le_max_right a b) (le_max_left _ _)
  have hc : c ≤ L := le_trans (le_max_left c d) (le_max_right _ _)
  have hd : d ≤ L := le_trans (le_max_right c d) (le_max_right _ _)
  have h1 := balancedGrid_to_diagonal (K := K) x a b L ha hb
  have h2 := balancedGrid_to_diagonal (K := K) x c d L hc hd
  convert (balancedGridSpan K x).sub_mem h1 h2 using 1 <;> abel

end RiemannResearch.LinearAlgebra

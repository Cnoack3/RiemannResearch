import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Real.Basic
import Lean.Elab.Tactic.Omega

/-!
# The finite cuts of the balanced two-prime forest

Source: RH_Minimal_Seeds_Canonical_Basis_and_Arithmetic_Charge_20260914.md,
Section 4. These are the actual rectangle and row/column cut formulas in exponent
coordinates. The incidence identity is proved from inequalities, not assumed.
-/

namespace RiemannResearch.LinearAlgebra

def balancedGridNext (i j : ℕ) : ℕ × ℕ :=
  if i ≤ j then (i + 1, j) else (i, j + 1)

def balancedGridCut (a b : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (a + 1)).product (Finset.range (b + 1))).filter
    (fun ij => (a < b → ij.2 = b) ∧ (b + 1 < a → ij.1 = a))

theorem mem_balancedGridCut (a b i j : ℕ) :
    (i, j) ∈ balancedGridCut a b ↔
      i ≤ a ∧ j ≤ b ∧ (a < b → j = b) ∧ (b + 1 < a → i = a) := by
  constructor
  · intro h
    have hf := Finset.mem_filter.mp h
    have hp := Finset.mem_product.mp hf.1
    exact ⟨by have := Finset.mem_range.mp hp.1; omega,
      by have := Finset.mem_range.mp hp.2; omega, hf.2.1, hf.2.2⟩
  · rintro ⟨hi, hj, h1, h2⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, h1, h2⟩

theorem balancedGridCut_self (a b : ℕ) : (a, b) ∈ balancedGridCut a b := by
  rw [mem_balancedGridCut]
  simp

/-- The selected edge leaves this finite cut exactly at its named root. -/
theorem balancedGridNext_mem_cut_iff (a b i j : ℕ) :
    balancedGridNext i j ∈ balancedGridCut a b ↔
      (i, j) ∈ balancedGridCut a b ∧ (i, j) ≠ (a, b) := by
  unfold balancedGridNext
  split_ifs with hij
  · rw [mem_balancedGridCut, mem_balancedGridCut]
    simp only [ne_eq, Prod.mk.injEq]
    omega
  · rw [mem_balancedGridCut, mem_balancedGridCut]
    simp only [ne_eq, Prod.mk.injEq]
    omega

/-- Normalized divergence on the cut is the coordinate Kronecker delta. -/
theorem balancedGridCut_incidence (a b i j : ℕ) :
    ((if (i, j) ∈ balancedGridCut a b then 1 else 0 : ℝ) -
      (if balancedGridNext i j ∈ balancedGridCut a b then 1 else 0)) =
      if (i, j) = (a, b) then 1 else 0 := by
  simp only [balancedGridNext_mem_cut_iff]
  by_cases he : (i, j) = (a, b)
  · cases he
    simp [balancedGridCut_self]
  · by_cases hm : (i, j) ∈ balancedGridCut a b <;> simp [he, hm]

end RiemannResearch.LinearAlgebra

import RiemannResearch.RH.BalancedScalarDictionary
import RiemannResearch.LinearAlgebra.BalancedGridCuts
import RiemannResearch.RH.FiniteSeedComponentCharge

/-!
# Genuine finite arithmetic cuts and their biorthogonality

Source: RH_Minimal_Seeds_Canonical_Basis_and_Arithmetic_Charge_20260914.md,
Section 4. The cuts are explicit finite sets of positive integers. Their charge
is the existing genuine Möbius difference, and the incidence formula is proved.
-/

namespace RiemannResearch.RH.Pareto

open RiemannResearch.LinearAlgebra
open RiemannResearch.RH.FiniteSeedComponentCharge
open RiemannResearch.RH.TwoSeedThreshold

noncomputable section

def balancedArithmeticCut (u a b : ℕ) : Finset ℕ :=
  (balancedGridCut a b).image (fun ij => 2 ^ ij.1 * 3 ^ ij.2 * u)

theorem balancedArithmeticCut_pos (u a b : ℕ) (hu : IsTwoThreeRough u)
    (n : ℕ) (hn : n ∈ balancedArithmeticCut u a b) : 0 < n := by
  obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hn
  have := hu.1
  positivity

theorem mem_balancedArithmeticCut_grid (u a b v c d : ℕ)
    (hu : IsTwoThreeRough u) (hv : IsTwoThreeRough v) :
    2 ^ c * 3 ^ d * v ∈ balancedArithmeticCut u a b ↔
      u = v ∧ (c, d) ∈ balancedGridCut a b := by
  constructor
  · intro hm
    obtain ⟨⟨i, j⟩, hij, he⟩ := Finset.mem_image.mp hm
    obtain ⟨huv, hic, hjd⟩ := rough_grid_decomposition_unique u i j v c d hu hv he
    subst i
    subst j
    exact ⟨huv, hij⟩
  · rintro ⟨rfl, hcd⟩
    exact Finset.mem_image.mpr ⟨(c, d), hcd, rfl⟩

private theorem componentCharge_dilation (S : Finset ℕ) (p m : ℕ)
    (hS : ∀ n ∈ S, 0 < n) (hp : 0 < p) (hm : 0 < m) :
    componentCharge S (dilation m (residue p)) =
      (if m ∈ S then 1 else 0) - (if p * m ∈ S then 1 else 0) := by
  have he : dilation m (residue p) = certificateGenerator p m := by
    funext n
    rw [residue_mul_floor]
    simp only [certificateGenerator, residue, Nat.mul_comm m p]
  rw [he]
  exact componentCharge_generator S p m hS hp hm

/-- The actual Möbius cut functional is biorthogonal to the selected generators. -/
theorem balancedArithmeticCut_biorthogonal (u a b v c d : ℕ)
    (hu : IsTwoThreeRough u) (hv : IsTwoThreeRough v) :
    componentCharge (balancedArithmeticCut u a b) (balancedResidueEdge v c d) =
      if u = v ∧ a = c ∧ b = d then 1 else 0 := by
  have hS := balancedArithmeticCut_pos u a b hu
  have hm : 0 < 2 ^ c * 3 ^ d * v := by have := hv.1; positivity
  rw [balancedResidueEdge_eq]
  by_cases hcd : c ≤ d
  · rw [if_pos hcd, componentCharge_dilation _ 2 _ hS (by decide) hm]
    have he : 2 * (2 ^ c * 3 ^ d * v) = 2 ^ (c + 1) * 3 ^ d * v := by
      rw [pow_succ]
      ring
    simp only [he, mem_balancedArithmeticCut_grid u a b v c d hu hv,
      mem_balancedArithmeticCut_grid u a b v (c + 1) d hu hv]
    by_cases huv : u = v
    · simp only [huv, true_and]
      have ht := balancedGridCut_incidence a b c d
      rw [balancedGridNext, if_pos hcd] at ht
      simpa only [Prod.mk.injEq, eq_comm] using ht
    · simp [huv]
  · rw [if_neg hcd, componentCharge_dilation _ 3 _ hS (by decide) hm]
    have he : 3 * (2 ^ c * 3 ^ d * v) = 2 ^ c * 3 ^ (d + 1) * v := by
      rw [pow_succ]
      ring
    simp only [he, mem_balancedArithmeticCut_grid u a b v c d hu hv,
      mem_balancedArithmeticCut_grid u a b v c (d + 1) hu hv]
    by_cases huv : u = v
    · simp only [huv, true_and]
      have ht := balancedGridCut_incidence a b c d
      rw [balancedGridNext, if_neg hcd] at ht
      simpa only [Prod.mk.injEq, eq_comm] using ht
    · simp [huv]

end
end RiemannResearch.RH.Pareto

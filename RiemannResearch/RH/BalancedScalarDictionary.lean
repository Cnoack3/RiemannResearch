import RiemannResearch.RH.BalancedResidueDictionary
import Mathlib.Data.Nat.Factorization.Defs

/-!
# One actual selected seed at every positive integer dilation

Source: RH_Minimal_Seeds_Canonical_Basis_and_Arithmetic_Charge_20260914.md,
Theorem 3.1. This connects the rough-grid path proof to the literal valuation
definition of `h_m`. Both factorization coordinates are computed explicitly.
-/

namespace RiemannResearch.RH.Pareto

noncomputable section

theorem rough_grid_factorization (u a b : ℕ) (hu : IsTwoThreeRough u) :
    (2 ^ a * 3 ^ b * u).factorization =
      Finsupp.single 2 a + Finsupp.single 3 b + u.factorization := by
  rw [Nat.factorization_mul (by positivity) (ne_of_gt hu.1),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.prime_two.factorization_pow, Nat.prime_three.factorization_pow]

theorem rough_grid_factorization_two (u a b : ℕ) (hu : IsTwoThreeRough u) :
    (2 ^ a * 3 ^ b * u).factorization 2 = a := by
  rw [rough_grid_factorization u a b hu]
  simp [Nat.factorization_eq_zero_of_not_dvd hu.2.1]

theorem rough_grid_factorization_three (u a b : ℕ) (hu : IsTwoThreeRough u) :
    (2 ^ a * 3 ^ b * u).factorization 3 = b := by
  rw [rough_grid_factorization u a b hu]
  simp [Nat.factorization_eq_zero_of_not_dvd hu.2.2]

def balancedSelectedSeed (m : ℕ) : ℕ :=
  if m.factorization 2 ≤ m.factorization 3 then 2 else 3

/-- The scalar-index dictionary requested in the source, with no duplicate grids. -/
def balancedSelected (m : ℕ) : ℕ → ℝ := dilation m (residue (balancedSelectedSeed m))

theorem balancedSelected_eq_rough (u a b : ℕ) (hu : IsTwoThreeRough u) :
    balancedSelected (2 ^ a * 3 ^ b * u) = balancedResidueEdge u a b := by
  rw [balancedSelected, balancedSelectedSeed, rough_grid_factorization_two u a b hu,
    rough_grid_factorization_three u a b hu, balancedResidueEdge_eq]
  split_ifs <;> rfl

/-- The original valuation rule and the rough-grid dictionary are exactly identical. -/
theorem balancedResidueDictionary_eq_scalar :
    balancedResidueDictionary =
      {f | ∃ m : ℕ, 0 < m ∧ f = balancedSelected m} := by
  ext f
  constructor
  · rintro ⟨u, a, b, hu, rfl⟩
    exact ⟨2 ^ a * 3 ^ b * u, by have := hu.1; positivity,
      (balancedSelected_eq_rough u a b hu).symm⟩
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨u, a, b, hu, rfl⟩ := exists_twoThree_rough_decomposition m hm
    exact ⟨u, a, b, hu, balancedSelected_eq_rough u a b hu⟩

/-- Choosing just one original generator per positive dilation preserves the finite span. -/
theorem balancedSelected_span_eq_twoSeedSpan :
    Submodule.span ℝ {f | ∃ m : ℕ, 0 < m ∧ f = balancedSelected m} =
      legalSeedSpan ({2, 3} : Set ℕ) := by
  rw [← balancedResidueDictionary_eq_scalar]
  exact balancedResidueSpan_eq_twoSeedSpan

theorem rough_grid_decomposition_unique (u a b v c d : ℕ)
    (hu : IsTwoThreeRough u) (hv : IsTwoThreeRough v)
    (he : 2 ^ a * 3 ^ b * u = 2 ^ c * 3 ^ d * v) :
    u = v ∧ a = c ∧ b = d := by
  have ha := congrArg (fun n : ℕ => n.factorization 2) he
  rw [rough_grid_factorization_two u a b hu,
    rough_grid_factorization_two v c d hv] at ha
  have hb := congrArg (fun n : ℕ => n.factorization 3) he
  rw [rough_grid_factorization_three u a b hu,
    rough_grid_factorization_three v c d hv] at hb
  subst c
  subst d
  have hp : 0 < 2 ^ a * 3 ^ b := by positivity
  exact ⟨by nlinarith, rfl, rfl⟩

end
end RiemannResearch.RH.Pareto

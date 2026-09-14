import RiemannResearch.RH.BalancedContinuousCoordinates
import Mathlib.Data.PNat.Basic

/-!
# The literal scalar-index balanced family is an algebraic basis

Source: RH_Minimal_Seeds_Canonical_Basis_and_Arithmetic_Charge_20260914.md,
Theorem 3.1. Existence of the arithmetic index and its uniqueness are proved
before choosing the inverse parametrization. Positive integer dilations are
the entire index set.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

theorem exists_balancedIndex_of_positive (m : ℕ) (hm : 0 < m) :
    ∃ i : BalancedArithmeticIndex, balancedIndexValue i = m := by
  obtain ⟨u, a, b, hu, he⟩ := exists_twoThree_rough_decomposition m hm
  exact ⟨⟨u, a, b, hu⟩, he.symm⟩

def scalarBalancedIndex (m : ℕ+) : BalancedArithmeticIndex :=
  Classical.choose (exists_balancedIndex_of_positive m m.pos)

theorem scalarBalancedIndex_value (m : ℕ+) : balancedIndexValue (scalarBalancedIndex m) = m :=
  Classical.choose_spec (exists_balancedIndex_of_positive m m.pos)

theorem scalarBalancedIndex_injective : Function.Injective scalarBalancedIndex := by
  intro m n he
  apply Subtype.ext
  have h := congrArg balancedIndexValue he
  rw [scalarBalancedIndex_value, scalarBalancedIndex_value] at h
  exact h

def scalarBalancedHilbert (m : ℕ+) : ThresholdHilbert :=
  balancedIndexHilbert (scalarBalancedIndex m)

theorem hilbertSequence_scalarBalanced (m : ℕ+) :
    hilbertSequence (scalarBalancedHilbert m) = balancedSelected m := by
  rw [scalarBalancedHilbert, hilbertSequence_balancedIndex]
  have h := balancedSelected_eq_rough (scalarBalancedIndex m).u
    (scalarBalancedIndex m).a (scalarBalancedIndex m).b (scalarBalancedIndex m).rough
  change balancedSelected (balancedIndexValue (scalarBalancedIndex m)) = _ at h
  rw [scalarBalancedIndex_value] at h
  exact h.symm

def scalarBalancedCoefficient (m : ℕ+) : ThresholdHilbert →L[ℝ] ℝ :=
  balancedCoefficientCLM (scalarBalancedIndex m)

theorem scalarBalancedCoefficient_biorthogonal (m n : ℕ+) :
    scalarBalancedCoefficient m (scalarBalancedHilbert n) = if m = n then 1 else 0 := by
  rw [scalarBalancedCoefficient, scalarBalancedHilbert, balancedCoefficientCLM_biorthogonal]
  simp only [scalarBalancedIndex_injective.eq_iff]

theorem scalarBalancedHilbert_linearIndependent : LinearIndependent ℝ scalarBalancedHilbert := by
  classical
  exact RiemannResearch.Analysis.continuous_biorthogonal_linearIndependent
    scalarBalancedHilbert scalarBalancedCoefficient scalarBalancedCoefficient_biorthogonal

end
end RiemannResearch.RH.Pareto

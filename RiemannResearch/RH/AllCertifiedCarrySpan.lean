import RiemannResearch.RH.UniversalAtomCarryPresentation
import Mathlib.Data.Fin.VecNotation

/-!
# Algebraic synthesis by all certified floor carries

For any conductor `d > 1`, two certificates on the same inputs and output
have charges zero and one. Subtracting their actual floor carries recovers
`d` times the atom at `d`.
-/

noncomputable section

open scoped BigOperators

namespace RiemannResearch.RH.UniversalAtomCarry

open ArithmeticCumulative

private theorem adjacent_output_gt_one (d : ℕ) (hd : 1 < d) : 1 < d * (d + 1) := by
  nlinarith

/-- The adjacent pair with coefficients `(1,-1)` has reciprocal charge zero. -/
def adjacentMinus (d : ℕ) (hd : 1 < d) : Certificate where
  arity := 2
  input := ![d, d + 1]
  input_gt_one := by
    intro i
    fin_cases i <;> simp [hd]
    omega
  coeff := ![(1 : ℤ), -1]
  output := d * (d + 1)
  output_gt_one := adjacent_output_gt_one d hd
  charge := 0
  reciprocal := by
    have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hs : (d : ℝ) + 1 ≠ 0 := by linarith
    simp [Fin.sum_univ_two, Nat.cast_add, Nat.cast_mul]
    field_simp [ne_of_gt hd', hs]
    ring

/-- Increasing the first coefficient by `d` gives reciprocal charge one. -/
def adjacentPlus (d : ℕ) (hd : 1 < d) : Certificate where
  arity := 2
  input := ![d, d + 1]
  input_gt_one := by
    intro i
    fin_cases i <;> simp [hd]
    omega
  coeff := ![(d : ℤ) + 1, -1]
  output := d * (d + 1)
  output_gt_one := adjacent_output_gt_one d hd
  charge := 1
  reciprocal := by
    have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hs : (d : ℝ) + 1 ≠ 0 := by linarith
    simp [Fin.sum_univ_two, Nat.cast_add, Nat.cast_mul]
    field_simp [ne_of_gt hd', hs]
    ring

theorem adjacentMinus_floor_identity (d : ℕ) (hd : 1 < d) (n : ℕ) :
    (adjacentMinus d hd).carry n =
      residueFraction d n - residueFraction (d + 1) n - residueFraction (d * (d + 1)) n := by
  rw [Certificate.carry_eq]
  change (∑ i : Fin 2, ((![1, -1] i : ℤ) : ℝ) * residueFraction (![d, d + 1] i) n) -
    residueFraction (d * (d + 1)) n = _
  simp [Fin.sum_univ_two, sub_eq_add_neg]

theorem adjacentPlus_floor_identity (d : ℕ) (hd : 1 < d) (n : ℕ) :
    (adjacentPlus d hd).carry n =
      ((d : ℝ) + 1) * residueFraction d n -
        residueFraction (d + 1) n - residueFraction (d * (d + 1)) n := by
  rw [Certificate.carry_eq]
  change (∑ i : Fin 2, ((![(d : ℤ) + 1, -1] i : ℤ) : ℝ) * residueFraction (![d, d + 1] i) n) -
    residueFraction (d * (d + 1)) n = _
  simp [Fin.sum_univ_two, sub_eq_add_neg]

theorem adjacent_carry_difference (d : ℕ) (hd : 1 < d) :
    (adjacentPlus d hd).carry - (adjacentMinus d hd).carry =
      (d : ℝ) • residueFraction d := by
  funext n
  change (adjacentPlus d hd).carry n - (adjacentMinus d hd).carry n =
    (d : ℝ) * residueFraction d n
  rw [adjacentPlus_floor_identity, adjacentMinus_floor_identity]
  ring

/-- Algebraic span of the literal floor carries, with every certificate allowed. -/
def allCarrySpan : Submodule ℝ (ℕ → ℝ) :=
  Submodule.span ℝ (Set.range Certificate.carry)

theorem Certificate.carry_mem_atomSpan (c : Certificate) : c.carry ∈ atomSpan := by
  have h : c.carry = (∑ i : Fin c.arity,
      (c.coeff i : ℝ) • residueFraction (c.input i)) - residueFraction c.output := by
    funext n
    simpa [Finset.sum_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using c.carry_eq n
  rw [h]
  apply atomSpan.sub_mem
  · apply Submodule.sum_mem
    intro i _
    exact atomSpan.smul_mem _ (Submodule.subset_span ⟨⟨c.input i, c.input_gt_one i⟩, rfl⟩)
  · exact Submodule.subset_span ⟨⟨c.output, c.output_gt_one⟩, rfl⟩

theorem residueFraction_mem_allCarrySpan (d : ℕ) (hd : 1 < d) :
    residueFraction d ∈ allCarrySpan := by
  have h (c : Certificate) : c.carry ∈ allCarrySpan := Submodule.subset_span ⟨c, rfl⟩
  have hdiff := allCarrySpan.sub_mem (h (adjacentPlus d hd)) (h (adjacentMinus d hd))
  rw [adjacent_carry_difference] at hdiff
  have hd' : (d : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (show 0 < d by omega))
  simpa [smul_smul, hd'] using allCarrySpan.smul_mem (d : ℝ)⁻¹ hdiff

/-- Allowing all reciprocal charges and all coefficient representatives spans every atom. -/
theorem allCarrySpan_eq_atomSpan : allCarrySpan = atomSpan := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨c, rfl⟩
    exact c.carry_mem_atomSpan
  · apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    exact residueFraction_mem_allCarrySpan d.val d.property

end RiemannResearch.RH.UniversalAtomCarry

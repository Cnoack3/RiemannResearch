import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A strictly positive three-block optimizer-gluing obstruction

Source: Christian Noack, Audited Cross-Route Synthesis for the RH Master
Manuscript, proposition "Rational counterexample to the discarded formula",
Drive file 1Z-FVYsCfc-gg5WPg2rLQSffi9mc0MO4W. The source gives a semidefinite
counterexample. Adding the identity to all three Gram blocks strengthens
the obstruction: every block has quadratic lower bound the identity, yet
the symmetric pairwise formula remains false. The complete square
remainder identifies the actual common optimizer without spectral guesses.

This protects the Nyman--Beurling Mellin-block gluing agenda from dropping
its noncommutative defect. It is not a bound for the actual arithmetic fit.
-/

noncomputable section
open scoped BigOperators Matrix

namespace RiemannResearch.LinearAlgebra.ThreeBlockOptimizerObstruction

abbrev Vec := Fin 2 → ℝ
abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ

def gram (j : Fin 3) : Mat := Matrix.of fun i k =>
  if j.val = 0 then
    if i.val = 0 ∧ k.val = 0 then 2 else if i.val = 1 ∧ k.val = 1 then 1 else 0
  else if j.val = 1 then
    if i.val = 0 ∧ k.val = 0 then 1 else if i.val = 1 ∧ k.val = 1 then 2 else 0
  else if i.val = k.val then 2 else 1

def localFit (j : Fin 3) (i : Fin 2) : ℝ :=
  if j.val = 0 then 0 else if j.val = 1 then (if i.val = 0 then 0 else 1) else 1

def totalGram : Mat := Matrix.of fun i k => ∑ j, gram j i k

def inverseGram : Mat := Matrix.of fun i j => if i.val = j.val then 5 / 24 else -1 / 24

def commonFit (i : Fin 2) : ℝ := if i.val = 0 then 5 / 12 else 11 / 12

def quadratic (M : Mat) (u : Vec) : ℝ := dotProduct u (M *ᵥ u)

def loss (c : Vec) : ℝ := ∑ j, quadratic (gram j) (localFit j - c)

def discardedPairwise : ℝ :=
  (1 / 2) * ∑ i, ∑ j,
    quadratic (gram i * inverseGram * gram j) (localFit i - localFit j)

theorem gram_symmetric (j : Fin 3) : (gram j).transpose = gram j := by
  ext i k
  fin_cases j <;> fin_cases i <;> fin_cases k <;> norm_num [gram, Matrix.of_apply]

/-- All blocks dominate the identity; degeneracy cannot explain the failure. -/
theorem gram_lower_bound (j : Fin 3) (u : Vec) :
    u 0 ^ 2 + u 1 ^ 2 ≤ quadratic (gram j) u := by
  fin_cases j <;>
    simp [quadratic, gram, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.of_apply, Finset.sum_apply] <;>
    nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 0 + u 1)]

/-- The blocks are also uniformly bounded above: no ill-conditioning is used. -/
theorem gram_upper_bound (j : Fin 3) (u : Vec) :
    quadratic (gram j) u ≤ 3 * (u 0 ^ 2 + u 1 ^ 2) := by
  fin_cases j <;>
    simp [quadratic, gram, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.of_apply, Finset.sum_apply] <;>
    nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 0 - u 1)]

theorem gram_strictly_positive (j : Fin 3) (u : Vec) (hu : u ≠ 0) :
    0 < quadratic (gram j) u := by
  have hp : 0 < u 0 ^ 2 + u 1 ^ 2 := by
    by_contra hn
    have h0 : u 0 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
    have h1 : u 1 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
    apply hu
    ext i
    fin_cases i <;> simp [h0, h1]
  exact lt_of_lt_of_le hp (gram_lower_bound j u)

theorem inverseGram_mul_totalGram : inverseGram * totalGram = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [inverseGram, totalGram, gram, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.of_apply, Finset.sum_apply]

theorem totalGram_mul_inverseGram : totalGram * inverseGram = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [inverseGram, totalGram, gram, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.of_apply, Finset.sum_apply]

theorem common_normal :
    totalGram *ᵥ commonFit = ∑ j, gram j *ᵥ localFit j := by
  ext i
  fin_cases i <;>
    norm_num [totalGram, gram, localFit, commonFit, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Matrix.of_apply, Finset.sum_apply]

/-- Exact positive completion before any minimization inequality. -/
theorem loss_completion (c : Vec) :
    loss c = 13 / 6 +
      4 * (c 0 - 5 / 12) ^ 2 + 4 * (c 1 - 11 / 12) ^ 2 +
      ((c 0 - 5 / 12) + (c 1 - 11 / 12)) ^ 2 := by
  norm_num [loss, quadratic, gram, localFit, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Matrix.of_apply, Finset.sum_apply]
  ring

theorem common_loss : loss commonFit = 13 / 6 := by
  rw [loss_completion]
  norm_num [commonFit]

theorem common_minimizes (c : Vec) : loss commonFit ≤ loss c := by
  rw [common_loss, loss_completion]
  nlinarith [sq_nonneg (c 0 - 5 / 12), sq_nonneg (c 1 - 11 / 12),
    sq_nonneg ((c 0 - 5 / 12) + (c 1 - 11 / 12))]

theorem discardedPairwise_value : discardedPairwise = 55 / 24 := by
  norm_num [discardedPairwise, quadratic, gram, inverseGram, localFit,
    Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_succ, Matrix.of_apply, Finset.sum_apply]

/-- The exact missing signed defect survives strict positivity of every block. -/
theorem exact_defect : loss commonFit - discardedPairwise = -(1 / 8) := by
  rw [common_loss, discardedPairwise_value]
  norm_num

theorem pairwise_formula_false : loss commonFit ≠ discardedPairwise := by
  rw [common_loss, discardedPairwise_value]
  norm_num

end RiemannResearch.LinearAlgebra.ThreeBlockOptimizerObstruction

/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.LinearAlgebra.FiniteConstrainedMatrixMinimum
import Mathlib.Tactic.Ring

/-!
# Signed constrained energies under coefficient reparametrization

The complete quadratic form and the head constraints transform together.
Surjectivity of the coefficient map is sufficient; the new coordinates may
even be redundant. No entrywise sign assumption or discarded cross term is
used. An invertible matrix is a special case.

Source: the user-requested symbolic CRT and matrix-transform investigation,
29 October 2026. The existing finite constrained minimum supplies the optimizer;
this module proves exact invariance under changes of coefficient coordinates.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.LinearAlgebra.FiniteConstrainedMatrix

variable {ι κ ν : Type*} [Fintype ι] [Fintype ν]

/-- Exact evaluation of a composite coefficient/head matrix. -/
theorem reparam_mulVec (A : Matrix κ ι ℝ) (S : Matrix ι ν ℝ)
    (z : ν → ℝ) :
    (A * S).mulVec z = A.mulVec (S.mulVec z) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Congruence preserves the entire signed quadratic expression exactly. -/
theorem reparam_quadratic (G : Matrix ι ι ℝ) (S : Matrix ι ν ℝ)
    (z : ν → ℝ) :
    dotProduct z ((S.transpose * G * S).mulVec z) =
      dotProduct (S.mulVec z) (G.mulVec (S.mulVec z)) := by
  rw [reparam_mulVec, reparam_mulVec]
  simpa only [Matrix.transpose_transpose] using
    dot_transpose S.transpose z (G.mulVec (S.mulVec z))

def feasibleEnergies (G : Matrix ι ι ℝ) (A : Matrix κ ι ℝ)
    (b : κ → ℝ) : Set ℝ :=
  {E | ∃ c : ι → ℝ, A.mulVec c = b ∧ dotProduct c (G.mulVec c) = E}

/-- The feasible complete-energy set is unchanged, including its infimum
and any attained minimum. No positive-definiteness hypothesis is needed. -/
theorem feasibleEnergies_reparam (G : Matrix ι ι ℝ)
    (A : Matrix κ ι ℝ) (S : Matrix ι ν ℝ) (b : κ → ℝ)
    (hS : Function.Surjective S.mulVec) :
    feasibleEnergies (S.transpose * G * S) (A * S) b =
      feasibleEnergies G A b := by
  ext E
  constructor
  · rintro ⟨z, hz, he⟩
    refine ⟨S.mulVec z, ?_, ?_⟩
    · simpa only [reparam_mulVec] using hz
    · simpa only [reparam_quadratic] using he
  · rintro ⟨c, hc, he⟩
    obtain ⟨z, rfl⟩ := hS c
    refine ⟨z, ?_, ?_⟩
    · simpa only [reparam_mulVec] using hc
    · simpa only [reparam_quadratic] using he

variable [Fintype κ]

/-- Reparametrization preserves the actual attained constrained minimum. -/
theorem inverseCompressed_isLeast_reparam (G : Matrix ι ι ℝ)
    (hG : G.PosDef) (A : Matrix κ ι ℝ)
    (hA : Function.Surjective A.mulVec)
    (S : Matrix ι ν ℝ) (hS : Function.Surjective S.mulVec)
    (b : κ → ℝ) :
    IsLeast (feasibleEnergies (S.transpose * G * S) (A * S) b)
      (dotProduct b (multiplier G hG A hA b)) := by
  rw [feasibleEnergies_reparam G A S b hS]
  exact inverseCompressed_isLeast G hG A hA b

/-- Every transformed optimal coefficient vector synthesizes the old unique
minimum in the original coordinates; redundant new coordinates do not matter. -/
theorem minimumCoefficients_reparam_image (G : Matrix ι ι ℝ)
    (hG : G.PosDef) (A : Matrix κ ι ℝ)
    (hA : Function.Surjective A.mulVec) (S : Matrix ι ν ℝ)
    (b : κ → ℝ) (z : ν → ℝ)
    (hz : (A * S).mulVec z = b)
    (he : dotProduct z ((S.transpose * G * S).mulVec z) =
      dotProduct b (multiplier G hG A hA b)) :
    S.mulVec z = minimumCoefficients G hG A hA b := by
  apply minimumCoefficients_unique G hG A hA b (S.mulVec z)
  · simpa only [reparam_mulVec] using hz
  · simpa only [reparam_quadratic] using he

end RiemannResearch.LinearAlgebra.FiniteConstrainedMatrix

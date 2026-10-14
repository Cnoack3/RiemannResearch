import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rank obstruction for finite-feature kernels

Source: user-provided finite-rank argument, 13 October 2026.
This module formalizes the finite-feature rank obstruction.
The Q divisor DPP is the identified consumer.
-/

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.FiniteFeature

variable {K : Type*} [Field K]

def featureKernel {α : Type*} {N : ℕ} (v : α → Fin N → K) (i j : α) : K :=
  ∑ r, v i r * v j r

theorem principal_eq_mul_transpose {α : Type*} {N m : ℕ}
    (v : α → Fin N → K) (e : Fin m → α) :
    Matrix.of (fun i j => featureKernel v (e i) (e j)) =
      (Matrix.of (fun i r => v (e i) r)) *
        (Matrix.of (fun i r => v (e i) r)).transpose := by
  ext i j
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, featureKernel]

/-- Repeated sites are allowed in the algebraic rank statement. -/
theorem principal_rank_le {α : Type*} {N m : ℕ}
    (v : α → Fin N → K) (e : Fin m → α) :
    (Matrix.of (fun i j => featureKernel v (e i) (e j))).rank ≤ N := by
  let B : Matrix (Fin m) (Fin N) K := Matrix.of (fun i r => v (e i) r)
  have he : Matrix.of (fun i j => featureKernel v (e i) (e j)) =
      B * B.transpose := principal_eq_mul_transpose v e
  rw [he]
  exact (Matrix.rank_mul_le_left B B.transpose).trans (Matrix.rank_le_width B)

theorem principal_det_eq_zero {α : Type*} {N m : ℕ}
    (v : α → Fin N → K) (e : Fin m → α) (hm : N < m) :
    (Matrix.of (fun i j => featureKernel v (e i) (e j))).det = 0 := by
  by_contra hdet
  have hr := Matrix.rank_of_det_ne_zero hdet
  have hle := principal_rank_le v e
  rw [hr, Fintype.card_fin] at hle
  exact (Nat.not_lt_of_ge hle) hm

end RiemannResearch.Analysis.FiniteFeature

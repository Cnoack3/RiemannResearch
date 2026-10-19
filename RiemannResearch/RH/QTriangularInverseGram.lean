/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/

import RiemannResearch.RH.QTriangularCharge
import RiemannResearch.RH.QCovarianceInvertibility

/-!
# Triangular charge in a finite inverse-Gram direction

The triangular dual estimate bounds the inverse-Gram quadratic form in
`v_d = 1 - 1/d` for every finite distinct legal dictionary below `N`.
This controls a dual direction; it does not assert squarefree closure.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QTriangularCharge
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QCovarianceInverse QCovarianceInvertibility
open RiemannResearch.LinearAlgebra.CenteredNormalEquations

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem charge_qSynthesis (N : ℕ) (d : ι → ℕ) (c : ι → ℝ)
    (hd : ∀ i, 2 ≤ d i ∧ d i ≤ N) :
    charge N (qSynthesis d c) =
      (N : ℝ)⁻¹ * ∑ i, c i * (1 - 1 / (d i : ℝ)) := by
  unfold charge qSynthesis
  change inner ℝ (triangularChargeRiesz N)
    (toParetoLinear (∑ i, c i • qResidue (d i))) = _
  rw [map_sum, inner_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, real_inner_smul_right]
  change c i * charge N (qResidue (d i)) = _
  rw [charge_qResidue N (d i) (hd i).1 (hd i).2]
  ring

/-- The actual inverse-Gram bound for the collective direction 1-1/d.
Distinct squarefree dictionaries and primorial divisor dictionaries satisfy
these hypotheses, but squarefreeness itself is unnecessary for this estimate. -/
theorem inverseGram_direction_le (N : ℕ) (hN : 0 < N) (d : ι → ℕ)
    (hd : ∀ i, 2 ≤ d i ∧ d i ≤ N) (hinj : Function.Injective d) :
    dotProduct (fun i => 1 - 1 / (d i : ℝ))
      ((residueGramMatrix d)⁻¹.mulVec (fun i => 1 - 1 / (d i : ℝ))) ≤
        zetaTwo * (N : ℝ) ^ 2 * reciprocalMobiusCesaroEnergy N := by
  let v : ι → ℝ := fun i => 1 - 1 / (d i : ℝ)
  let u : ι → ℝ := (residueGramMatrix d)⁻¹.mulVec v
  let A : ℝ := dotProduct v u
  let K : ℝ := zetaTwo * (N : ℝ) ^ 2 * reciprocalMobiusCesaroEnergy N
  change A ≤ K
  have hdet : IsUnit (residueGramMatrix d).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt
      (qGram_posDef d (fun i => by have := (hd i).1; omega) hinj).det_pos)
  have hn : (residueGramMatrix d).mulVec u = v := by
    dsimp [u]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have he : ‖qSynthesis d u‖ ^ 2 = A := by
    rw [qSynthesis_norm_sq]
    change dot u ((residueGramMatrix d).mulVec u) = A
    rw [hn]
    exact dot_comm u v
  have hc : charge N (qSynthesis d u) = (N : ℝ)⁻¹ * A := by
    rw [charge_qSynthesis N d u hd]
    congr 1
    change dot u v = dot v u
    exact dot_comm u v
  have hA : 0 ≤ A := by rw [← he]; exact sq_nonneg _
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg zetaTwo_pos.le (sq_nonneg _))
      (reciprocalMobiusCesaroEnergy_nonneg N)
  have hb := charge_sq_le N (qSynthesis d u)
  rw [hc, sq_abs, mul_pow, he] at hb
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg (N : ℝ))
  field_simp [hN0] at hm
  have hAA : A ^ 2 ≤ K * A := by dsimp [K]; nlinarith
  by_cases ha : A = 0
  · simpa only [ha] using hK
  · have hp : 0 < A := lt_of_le_of_ne hA (Ne.symm ha)
    exact (mul_le_mul_iff_right₀ hp).mp (by simpa only [pow_two, mul_comm] using hAA)

end RiemannResearch.RH.QTriangularCharge

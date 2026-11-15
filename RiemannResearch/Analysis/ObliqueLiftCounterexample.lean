/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A small source and a bounded inverse physical Gram do not bound an oblique lift

Source: CanonicalPrimePowerUpdatesResearch20261107.md, Section 4.
All quantities below come from the actual displayed Hilbert-space vectors.
The example concerns general oblique geometry, not the arithmetic canonical sequence.
-/

noncomputable section
namespace InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem oblique_example_energy (u v w : H)
    (hu : ‖u‖ ^ 2 = 1) (hv : ‖v‖ ^ 2 = 1) (hw : ‖w‖ ^ 2 = 1)
    (huv : inner ℝ u v = 0) (huw : inner ℝ u w = 0)
    (hvw : inner ℝ v w = 0) (A ε : ℝ) :
    ‖u + ε • (v + A • w)‖ ^ 2 = 1 + ε ^ 2 * (1 + A ^ 2) ∧
      ‖v + A • w‖ ^ 2 = 1 + A ^ 2 ∧
      1 / ‖v + A • w‖ ^ 2 ≤ 1 := by
  have hnew : ‖v + A • w‖ ^ 2 = 1 + A ^ 2 := by
    rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      hv, hw, real_inner_smul_right, hvw]
    ring
  have horth : inner ℝ u (v + A • w) = 0 := by
    rw [inner_add_right, real_inner_smul_right, huv, huw]
    ring
  refine ⟨?_, hnew, ?_⟩
  · rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      hu, hnew, real_inner_smul_right, horth]
    ring
  · rw [hnew]
    have h : (1 : ℝ) / (1 + A ^ 2) ≤ 1 / 1 :=
      one_div_le_one_div_of_le (by norm_num) (by nlinarith [sq_nonneg A])
    simpa using h

theorem oblique_example_test_pairings (u v w : H)
    (hu : ‖u‖ ^ 2 = 1) (hv : ‖v‖ ^ 2 = 1)
    (huv : inner ℝ u v = 0) (huw : inner ℝ u w = 0)
    (hvw : inner ℝ v w = 0) (A ε : ℝ) :
    inner ℝ u (u + ε • (v + A • w)) = 1 ∧
      inner ℝ v (u + ε • (v + A • w)) = ε := by
  have hvu : inner ℝ v u = 0 := by rw [real_inner_comm, huv]
  constructor <;>
    simp only [inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hu, hv, huv, huw, hvw, hvu] <;> ring

end InnerProductSpace

namespace RiemannResearch.Analysis.ObliqueLiftCounterexample

def basisVector (i : Fin 3) : EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.basisFun (ι := Fin 3) (𝕜 := ℝ)) i

theorem basisVector_norm_sq (i : Fin 3) : ‖basisVector i‖ ^ 2 = 1 := by
  simp [basisVector]

theorem basisVector_inner_zero (i j : Fin 3) (hij : i ≠ j) :
    inner ℝ (basisVector i) (basisVector j) = 0 := by
  simp [basisVector, EuclideanSpace.inner_single_left, hij, Ne.symm hij]

/-- An actual three-dimensional realization of the paper's example. -/
theorem actual_oblique_example (A ε : ℝ) :
    ‖basisVector 0 + ε • (basisVector 1 + A • basisVector 2)‖ ^ 2 =
        1 + ε ^ 2 * (1 + A ^ 2) ∧
      1 / ‖basisVector 1 + A • basisVector 2‖ ^ 2 ≤ 1 := by
  have h := InnerProductSpace.oblique_example_energy
    (basisVector 0) (basisVector 1) (basisVector 2)
    (basisVector_norm_sq _) (basisVector_norm_sq _) (basisVector_norm_sq _)
    (basisVector_inner_zero _ _ (by decide))
    (basisVector_inner_zero _ _ (by decide))
    (basisVector_inner_zero _ _ (by decide)) A ε
  exact ⟨h.1, h.2.2⟩

/-- Complete lift energies are arbitrarily large while the inverse physical
Gram remains at most one, even with a fixed unit new test source. -/
theorem actual_oblique_energies_unbounded (C : ℝ) (hC : 0 ≤ C) :
    ∃ A : ℝ,
      C < ‖basisVector 0 + (basisVector 1 + A • basisVector 2)‖ ^ 2 ∧
        1 / ‖basisVector 1 + A • basisVector 2‖ ^ 2 ≤ 1 := by
  have h := actual_oblique_example (C + 1) 1
  simp only [one_smul, one_pow, one_mul] at h
  refine ⟨C + 1, ?_, h.2⟩
  rw [h.1]
  nlinarith [sq_nonneg C]

end RiemannResearch.Analysis.ObliqueLiftCounterexample

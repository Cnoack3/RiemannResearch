/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QFiniteEighthMoment
import RiemannResearch.RH.QSquarefreeEvaluationBasis

/-! # Reconstruction-diagonal estimates for the matched finite displacement

The ordered physical evaluation basis and the reciprocal Bessel estimate
are from `QSquarefreeEvaluationBasis` and `QTriangularWeightedBessel`.
Here the forcing is the matched finite Pareto residual.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QSquarefreeFiniteDisplacement
open ZetaTwoHilbert ZetaTwoOptimizerStage QShiftedReciprocal
open QSquarefreeEvaluationBasis QTriangularWeightedBessel

/-- The reciprocal-weighted coefficient budget for the actual displacement. -/
theorem finiteDisplacement_weighted_coefficients (N : ℕ) :
    (∑ i : Fin (N + 1), ((i.val : ℝ) + 2) ^ 2 *
      (inner ℝ (finiteDisplacement N) (orderedVector N i)) ^ 2) ≤
      ‖qOne - finitePFit N‖ ^ 2 := by
  have he (i : Fin (N + 1)) :
      inner ℝ (B (qOne - finitePFit N)) (orderedVector N i) =
      inner ℝ (finiteDisplacement N) (orderedVector N i) := by
    have hz := Submodule.inner_right_of_mem_orthogonal
      (orderedVector_mem_stage N i) (finite_witness_mem_orthogonal N)
    rw [inner_sub_right] at hz
    calc
      _ = inner ℝ (orderedVector N i) (B (qOne - finitePFit N)) :=
        real_inner_comm _ _
      _ = inner ℝ (orderedVector N i) (finiteDisplacement N) := sub_eq_zero.mp hz
      _ = _ := real_inner_comm _ _
  have h := reciprocal_onset_bessel (qOne - finitePFit N) (N + 1)
    (orderedVector N) id (orderedVector_orthogonal N) (orderedVector_norm_sq_le N)
    (orderedVector_onset N)
  simpa only [id_eq, he] using h

/-- Physical Cauchy--Schwarz using the actual matched residual energy. -/
theorem finiteDisplacement_sq_le_pareto_reconstructionDiagonal (N n : ℕ) :
    (qSequence (finiteDisplacement N) n) ^ 2 ≤
      ‖qOne - finitePFit N‖ ^ 2 * reconstructionDiagonal N n := by
  let a : Fin (N + 1) → ℝ := fun i =>
    ((i.val : ℝ) + 2) * inner ℝ (finiteDisplacement N) (orderedVector N i)
  let v : Fin (N + 1) → ℝ := fun i =>
    qSequence (orderedVector N i) n / ((i.val : ℝ) + 2)
  have he : qSequence (finiteDisplacement N) n = ∑ i, a i * v i := by
    rw [stage_physical_synthesis N n _ (finiteDisplacement_mem N)]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [a, v]
    have hw : (i.val : ℝ) + 2 ≠ 0 := ne_of_gt (by positivity)
    field_simp
  have ha : (∑ i, (a i) ^ 2) ≤ ‖qOne - finitePFit N‖ ^ 2 := by
    simpa only [a, mul_pow] using finiteDisplacement_weighted_coefficients N
  rw [he]
  exact (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a v).trans
    (mul_le_mul_of_nonneg_right ha (reconstructionDiagonal_nonneg N n))

theorem finiteDisplacement_sq_le_reconstructionDiagonal (N n : ℕ) :
    (qSequence (finiteDisplacement N) n) ^ 2 ≤
      ((9 / 8 : ℝ) * error N) * reconstructionDiagonal N n :=
  (finiteDisplacement_sq_le_pareto_reconstructionDiagonal N n).trans
    (mul_le_mul_of_nonneg_right (finitePareto_residual_energy_bound N)
      (reconstructionDiagonal_nonneg N n))

/-- Fourth physical moment of the weighted reconstruction diagonal on the aligned head. -/
def reconstructionFourthHead (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), (reconstructionDiagonal N n) ^ 4 / (n : ℝ) ^ 2

theorem eighthHead_finiteDisplacement_le_pareto_reconstruction (N : ℕ) :
    eighthHead (finiteDisplacement N) N ≤
      ‖qOne - finitePFit N‖ ^ 8 * reconstructionFourthHead N := by
  let c := ‖qOne - finitePFit N‖ ^ 2
  calc
    _ ≤ ∑ n ∈ Finset.range (N + 1),
        c ^ 4 * ((reconstructionDiagonal N n) ^ 4 / (n : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro n _
      have h := finiteDisplacement_sq_le_pareto_reconstructionDiagonal N n
      have h4 := pow_le_pow_left₀ (sq_nonneg (qSequence (finiteDisplacement N) n)) h 4
      have h8 : |qSequence (finiteDisplacement N) n| ^ 8 ≤
          c ^ 4 * (reconstructionDiagonal N n) ^ 4 := by
        rw [Even.pow_abs (by decide : Even 8)]
        simpa only [← pow_mul, mul_pow, c] using h4
      simpa only [mul_div_assoc] using div_le_div_of_nonneg_right h8 (sq_nonneg (n : ℝ))
    _ = c ^ 4 * reconstructionFourthHead N := by rw [reconstructionFourthHead, Finset.mul_sum]
    _ = _ := by simp only [c, ← pow_mul]

theorem eighthHead_finiteDisplacement_le_reconstruction (N : ℕ) :
    eighthHead (finiteDisplacement N) N ≤
      (9 / 8 : ℝ) ^ 4 * ((error N) ^ 4 * reconstructionFourthHead N) := by
  have h := pow_le_pow_left₀ (sq_nonneg ‖qOne - finitePFit N‖)
    (finitePareto_residual_energy_bound N) 4
  have h8 : ‖qOne - finitePFit N‖ ^ 8 ≤ (9 / 8 : ℝ) ^ 4 * (error N) ^ 4 := by
    simpa only [← pow_mul, mul_pow, error] using h
  have hd : 0 ≤ reconstructionFourthHead N := Finset.sum_nonneg (fun n _ => by positivity)
  exact (eighthHead_finiteDisplacement_le_pareto_reconstruction N).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right h8 hd)

/-- A cofinal test involving the finite Q error and its stage geometry. -/
theorem riemannHypothesis_of_frequent_reconstruction_product
    (happrox : HasSubcriticalApproximation) (C : ℝ)
    (h : ∃ᶠ N : ℕ in atTop, (error N) ^ 4 * reconstructionFourthHead N ≤ C) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_displacement_eighth happrox
  apply summable_eighth_of_frequent_diagonal finiteDisplacement_tendsto ((9 / 8 : ℝ) ^ 4 * C)
  exact h.mono fun N hN => (eighthHead_finiteDisplacement_le_reconstruction N).trans
    (mul_le_mul_of_nonneg_left hN (by positivity))

end RiemannResearch.RH.QSquarefreeFiniteDisplacement

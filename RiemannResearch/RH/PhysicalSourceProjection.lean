/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PhysicalSchurCoupling

/-!
# Actual physical rank-two projection and ordinary-mean dual

The scalar source projection charge is identified with the actual full Pareto
Gram solve. The explicit projection and ordinary-mean dual satisfy their
normal equations with no supplied inverse equation. The complete projection
error retains its nonnegative Gram remainder; the mean-one error difference
retains the full signed-source square.

Source: user-directed continuation of PhysicalArithmeticObservations20261008.md.
The finite algebra is developed from the already proved physical core identity,
inertia and signed Schur coupling. No RH or analytic limit is assumed here.
-/

noncomputable section
open Matrix Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.PhysicalSourceProjection
open PhysicalPacketCore PhysicalSchurCoupling
open RiemannResearch.LinearAlgebra.RankTwoWoodbury
open RiemannResearch.LinearAlgebra.MeanOneSchurCoupling

def coreLambda (s : Finset ℕ) : s → ℝ :=
  (derivedCore s)⁻¹ *ᵥ ramanujanVonMangoldtVector s

def coreTotient (s : Finset ℕ) : s → ℝ :=
  (derivedCore s)⁻¹ *ᵥ ramanujanTotientVector s

def projectionCoefficients (s : Finset ℕ) : s → ℝ :=
  (2 / shiftedDeterminant s) •
    (logarithmicCharge s • coreTotient s -
      (2 * Real.pi + mixedCharge s) • coreLambda s)

def totientDual (s : Finset ℕ) : s → ℝ :=
  (2 / shiftedDeterminant s) •
    (inverseCharge s • coreLambda s -
      (2 * Real.pi + mixedCharge s) • coreTotient s)

theorem coreLambda_totient_pair (s : Finset ℕ) :
    ramanujanTotientVector s ⬝ᵥ coreLambda s = mixedCharge s := by
  unfold coreLambda mixedCharge
  simpa only [inverseCore_transpose s] using
    Matrix.dotProduct_transpose_mulVec (derivedCore s)⁻¹
      (ramanujanTotientVector s) (ramanujanVonMangoldtVector s)

theorem coreLambda_action (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    ramanujanGramMatrix s *ᵥ coreLambda s =
      (Real.pi + mixedCharge s / 2) • ramanujanVonMangoldtVector s +
        (logarithmicCharge s / 2) • ramanujanTotientVector s := by
  have hF : derivedCore s *ᵥ coreLambda s = ramanujanVonMangoldtVector s := by
    rw [coreLambda, Matrix.mulVec_mulVec, derivedCore_mul_inverse s hs ho,
      Matrix.one_mulVec]
  rw [gram_eq_rankTwo_derivedCore, rankTwoMatrix_mulVec, hF,
    coreLambda_totient_pair]
  change Real.pi • ramanujanVonMangoldtVector s +
    (mixedCharge s / 2) • ramanujanVonMangoldtVector s +
    (logarithmicCharge s / 2) • ramanujanTotientVector s = _
  rw [add_smul]

theorem coreTotient_action (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    ramanujanGramMatrix s *ᵥ coreTotient s =
      (inverseCharge s / 2) • ramanujanVonMangoldtVector s +
        (Real.pi + mixedCharge s / 2) • ramanujanTotientVector s := by
  have hF : derivedCore s *ᵥ coreTotient s = ramanujanTotientVector s := by
    rw [coreTotient, Matrix.mulVec_mulVec, derivedCore_mul_inverse s hs ho,
      Matrix.one_mulVec]
  rw [gram_eq_rankTwo_derivedCore, rankTwoMatrix_mulVec, hF]
  change Real.pi • ramanujanTotientVector s +
    (inverseCharge s / 2) • ramanujanVonMangoldtVector s +
    (mixedCharge s / 2) • ramanujanTotientVector s = _
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem projection_normalEquation (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    ramanujanGramMatrix s *ᵥ projectionCoefficients s = ramanujanVonMangoldtVector s := by
  have hT := ne_of_gt (shiftedDeterminant_pos s hs ho)
  rw [projectionCoefficients, Matrix.mulVec_smul, Matrix.mulVec_sub,
    Matrix.mulVec_smul, Matrix.mulVec_smul,
    coreTotient_action s hs ho, coreLambda_action s hs ho]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hT]
  unfold shiftedDeterminant
  ring

theorem totientDual_normalEquation (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    ramanujanGramMatrix s *ᵥ totientDual s = ramanujanTotientVector s := by
  have hT := ne_of_gt (shiftedDeterminant_pos s hs ho)
  rw [totientDual, Matrix.mulVec_smul, Matrix.mulVec_sub,
    Matrix.mulVec_smul, Matrix.mulVec_smul,
    coreLambda_action s hs ho, coreTotient_action s hs ho]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hT]
  unfold shiftedDeterminant
  ring

theorem projection_pairing (s : Finset ℕ) :
    ramanujanVonMangoldtVector s ⬝ᵥ projectionCoefficients s = sourceProjectionCharge s := by
  rw [projectionCoefficients]
  simp only [dotProduct_smul, dotProduct_sub, smul_eq_mul]
  change (2 / shiftedDeterminant s) *
    (logarithmicCharge s * mixedCharge s -
      (2 * Real.pi + mixedCharge s) * logarithmicCharge s) = _
  unfold sourceProjectionCharge
  ring

theorem totientDual_pairing (s : Finset ℕ) :
    ramanujanTotientVector s ⬝ᵥ totientDual s =
      -4 * Real.pi * inverseCharge s / shiftedDeterminant s := by
  rw [totientDual]
  simp only [dotProduct_smul, dotProduct_sub, smul_eq_mul, coreLambda_totient_pair]
  change (2 / shiftedDeterminant s) *
    (inverseCharge s * mixedCharge s -
      (2 * Real.pi + mixedCharge s) * inverseCharge s) = _
  ring

theorem gram_transpose (s : Finset ℕ) : (ramanujanGramMatrix s)ᵀ = ramanujanGramMatrix s := by
  ext i j
  exact paretoInner_comm _ _

theorem gram_pair_symm (s : Finset ℕ) (u v : s → ℝ) :
    u ⬝ᵥ (ramanujanGramMatrix s *ᵥ v) = v ⬝ᵥ (ramanujanGramMatrix s *ᵥ u) := by
  simpa only [gram_transpose] using
    Matrix.dotProduct_transpose_mulVec (ramanujanGramMatrix s) u v

theorem gram_quadratic_nonneg (s : Finset ℕ) (c : s → ℝ) :
    0 ≤ c ⬝ᵥ (ramanujanGramMatrix s *ᵥ c) := by
  rw [← synthesis_gram]
  exact paretoInner_self_nonneg _

theorem projection_error (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    paretoError (synthesis s (projectionCoefficients s)) = 1 - sourceProjectionCharge s := by
  rw [synthesis_error, projection_normalEquation s hs ho,
    dotProduct_comm (projectionCoefficients s), projection_pairing]
  ring

/-- Complete optimal error plus the actual full Gram square of the displacement. -/
theorem projection_error_decomposition (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) (c : s → ℝ) :
    paretoError (synthesis s c) = 1 - sourceProjectionCharge s +
      (c - projectionCoefficients s) ⬝ᵥ
        (ramanujanGramMatrix s *ᵥ (c - projectionCoefficients s)) := by
  rw [synthesis_error, Matrix.mulVec_sub, dotProduct_sub,
    sub_dotProduct, sub_dotProduct, projection_normalEquation s hs ho,
    gram_pair_symm s (projectionCoefficients s) c,
    projection_normalEquation s hs ho,
    dotProduct_comm (projectionCoefficients s) (ramanujanVonMangoldtVector s), projection_pairing]
  rw [dotProduct_comm c (ramanujanVonMangoldtVector s)]
  ring

theorem sourceProjectionCharge_le_one (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    sourceProjectionCharge s ≤ 1 := by
  have he : 0 ≤ paretoError (synthesis s (projectionCoefficients s)) :=
    paretoInner_self_nonneg _
  rw [projection_error s hs ho] at he
  linarith

theorem logarithmicCharge_control (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    4 * Real.pi * (-logarithmicCharge s) ≤ shiftedDeterminant s := by
  have hq := sourceProjectionCharge_le_one s hs ho
  exact (div_le_one (shiftedDeterminant_pos s hs ho)).mp hq

theorem totient_cauchy (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) (c : s → ℝ) :
    (ramanujanTotientVector s ⬝ᵥ c) ^ 2 ≤
      (-4 * Real.pi * inverseCharge s / shiftedDeterminant s) *
        (c ⬝ᵥ (ramanujanGramMatrix s *ᵥ c)) := by
  have h := source_pair_cauchy (ramanujanGramMatrix s) c (totientDual s)
    (gram_transpose s) (gram_quadratic_nonneg s)
  rw [totientDual_normalEquation s hs ho, dotProduct_comm c,
    dotProduct_comm (totientDual s),
    totientDual_pairing] at h
  nlinarith only [h]

/-- Identification with the existing inverse obtained from actual packet independence. -/
theorem projection_eq_actual_gramSolve (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    projectionCoefficients s = ramanujanGramSolve s hs (ramanujanVonMangoldtVector s) := by
  apply sub_eq_zero.mp
  apply ramanujanGramAction_eq_zero s hs
  rw [← ramanujanGramMatrix_mulVec, Matrix.mulVec_sub,
    projection_normalEquation s hs ho, ramanujanGramMatrix_mulVec_solve, sub_self]

theorem projectionCharge_eq_actual_inverse_gram (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    sourceProjectionCharge s = ramanujanVonMangoldtVector s ⬝ᵥ
      ramanujanGramSolve s hs (ramanujanVonMangoldtVector s) := by
  rw [← projection_eq_actual_gramSolve s hs ho]
  exact (projection_pairing s).symm

/-- Exact finite ordinary-mean penalty, including its complete source square. -/
theorem meanOne_projection_error_gap (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    paretoError (synthesis s (constrainedOptimizer s)) -
      paretoError (synthesis s (projectionCoefficients s)) =
        4 * Real.pi * (2 * Real.pi + mixedCharge s) ^ 2 /
          ((-inverseCharge s) * shiftedDeterminant s) := by
  have hC := ne_of_lt (inverseCharge_neg s hs ho)
  have hT := ne_of_gt (shiftedDeterminant_pos s hs ho)
  rw [constrainedOptimizer_error s hs ho, projection_error s hs ho]
  unfold sourceProjectionCharge
  field_simp [hC, hT]
  unfold shiftedDeterminant
  ring

end RiemannResearch.RH.Pareto.PhysicalSourceProjection

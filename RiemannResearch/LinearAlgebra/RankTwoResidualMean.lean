/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.LinearAlgebra.RankTwoWoodbury

/-!
# Exact rank-two residual means and mean-one cancellation

Source: user-directed Pareto/CRT research continuation, 8 October 2026.
The actual arithmetic Gram and core inverse must be supplied by an application.
These finite algebraic theorems do not provide an RH asymptotic estimate.
-/

noncomputable section
open Matrix
namespace RiemannResearch.LinearAlgebra.RankTwoResidualMean
open RankTwoWoodbury

theorem scalar_residual_moments
    (p A C D m Q : ℝ)
    (hDelta : D ^ 2 - A * C ≠ 0)
    (hQ : D * Q = 2 * A * m)
    (hm : 2 * D * m - C * Q = 4 * p) :
    m = 2 * p * D / (D ^ 2 - A * C) ∧
      Q = 4 * p * A / (D ^ 2 - A * C) := by
  constructor
  · apply (eq_div_iff hDelta).2
    nlinarith only [congrArg (fun x : ℝ => D * x) hm,
      congrArg (fun x : ℝ => C * x) hQ]
  · apply (eq_div_iff hDelta).2
    nlinarith only [congrArg (fun x : ℝ => D * x) hQ,
      congrArg (fun x : ℝ => A * x) hm]

section FiniteMatrices
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solved_residual_moments_system
    (p : ℝ) (F R Xi : Matrix ι ι ℝ) (phi L y : ι → ℝ)
    (hRF : R * F = 1) (hR : Rᵀ = R)
    (hXi : Xi = rankTwoMatrix p F L phi)
    (hy : Xi *ᵥ y = L) :
    (2 * p + L ⬝ᵥ (R *ᵥ phi)) * (L ⬝ᵥ y) =
        2 * (L ⬝ᵥ (R *ᵥ L)) * (1 - (phi ⬝ᵥ y) / 2) ∧
      2 * (2 * p + L ⬝ᵥ (R *ᵥ phi)) *
          (1 - (phi ⬝ᵥ y) / 2) -
        (phi ⬝ᵥ (R *ᵥ phi)) * (L ⬝ᵥ y) = 4 * p := by
  let s : ℝ := phi ⬝ᵥ y
  let t : ℝ := L ⬝ᵥ y
  have hpair (r z : ι → ℝ) :
      r ⬝ᵥ (R *ᵥ z) = z ⬝ᵥ (R *ᵥ r) := by
    simpa only [hR] using Matrix.dotProduct_transpose_mulVec R r z
  have hleft (x : ι → ℝ) : R *ᵥ (F *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, hRF, Matrix.one_mulVec]
  have hvec : p • y + (s / 2) • (R *ᵥ L) +
      (t / 2) • (R *ᵥ phi) = R *ᵥ L := by
    have h := congrArg (fun x : ι → ℝ => R *ᵥ x) hy
    rw [hXi, rankTwoMatrix_mulVec] at h
    simpa only [Matrix.mulVec_add, Matrix.mulVec_smul,
      hleft, s, t] using h
  have hphi := congrArg (fun x : ι → ℝ => phi ⬝ᵥ x) hvec
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at hphi
  rw [hpair phi L] at hphi
  have hL := congrArg (fun x : ι → ℝ => L ⬝ᵥ x) hvec
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at hL
  dsimp only [s, t] at hphi hL
  constructor
  · nlinarith only [hL]
  · nlinarith only [hphi]

theorem solved_residual_moments
    (p : ℝ) (F R Xi : Matrix ι ι ℝ) (phi L y : ι → ℝ)
    (hRF : R * F = 1) (hR : Rᵀ = R)
    (hXi : Xi = rankTwoMatrix p F L phi)
    (hy : Xi *ᵥ y = L)
    (hDelta : (2 * p + L ⬝ᵥ (R *ᵥ phi)) ^ 2 -
      (L ⬝ᵥ (R *ᵥ L)) * (phi ⬝ᵥ (R *ᵥ phi)) ≠ 0) :
    1 - (phi ⬝ᵥ y) / 2 =
        2 * p * (2 * p + L ⬝ᵥ (R *ᵥ phi)) /
          ((2 * p + L ⬝ᵥ (R *ᵥ phi)) ^ 2 -
            (L ⬝ᵥ (R *ᵥ L)) * (phi ⬝ᵥ (R *ᵥ phi))) ∧
      L ⬝ᵥ y = 4 * p * (L ⬝ᵥ (R *ᵥ L)) /
          ((2 * p + L ⬝ᵥ (R *ᵥ phi)) ^ 2 -
            (L ⬝ᵥ (R *ᵥ L)) * (phi ⬝ᵥ (R *ᵥ phi))) := by
  obtain ⟨hQ, hm⟩ :=
    solved_residual_moments_system p F R Xi phi L y hRF hR hXi hy
  exact scalar_residual_moments p (L ⬝ᵥ (R *ᵥ L))
    (phi ⬝ᵥ (R *ᵥ phi)) (2 * p + L ⬝ᵥ (R *ᵥ phi))
    (1 - (phi ⬝ᵥ y) / 2) (L ⬝ᵥ y) hDelta hQ hm

/-- Complete error before cancellation, including both logarithmic terms. -/
def fullError (p : ℝ) (F : Matrix ι ι ℝ) (L phi y : ι → ℝ) : ℝ :=
  1 - 2 * (L ⬝ᵥ y) + y ⬝ᵥ (rankTwoMatrix p F L phi *ᵥ y)

omit [DecidableEq ι] in
/-- The mean-one affine constraint cancels the complete logarithmic rank two. -/
theorem fullError_eq_core_of_mean_one
    (p : ℝ) (F : Matrix ι ι ℝ) (L phi y : ι → ℝ)
    (hmean : phi ⬝ᵥ y = 2) :
    fullError p F L phi y = 1 + p * (y ⬝ᵥ (F *ᵥ y)) := by
  unfold fullError
  rw [rankTwoMatrix_mulVec]
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul,
    hmean, dotProduct_comm y L, dotProduct_comm y phi]
  ring

/-- Exact square completion on the affine mean-one constraint.
Positivity of the core on `phi`-orthogonal vectors is an application input. -/
theorem constrained_mean_completion
    (p : ℝ) (F R Xi : Matrix ι ι ℝ) (phi L y : ι → ℝ)
    (hFR : F * R = 1) (hF : Fᵀ = F)
    (hXi : Xi = rankTwoMatrix p F L phi)
    (hC : phi ⬝ᵥ (R *ᵥ phi) ≠ 0)
    (hy : phi ⬝ᵥ y = 2) :
    let C : ℝ := phi ⬝ᵥ (R *ᵥ phi)
    let c0 : ι → ℝ := (2 / C) • (R *ᵥ phi)
    phi ⬝ᵥ c0 = 2 ∧
      1 - 2 * (L ⬝ᵥ y) + y ⬝ᵥ (Xi *ᵥ y) =
        1 + 4 * p / C +
          p * ((y - c0) ⬝ᵥ (F *ᵥ (y - c0))) := by
  let C : ℝ := phi ⬝ᵥ (R *ᵥ phi)
  let c0 : ι → ℝ := (2 / C) • (R *ᵥ phi)
  change phi ⬝ᵥ c0 = 2 ∧
    1 - 2 * (L ⬝ᵥ y) + y ⬝ᵥ (Xi *ᵥ y) =
      1 + 4 * p / C +
        p * ((y - c0) ⬝ᵥ (F *ᵥ (y - c0)))
  have hC' : C ≠ 0 := hC
  have hmean : phi ⬝ᵥ c0 = 2 := by
    change phi ⬝ᵥ ((2 / C) • (R *ᵥ phi)) = 2
    rw [dotProduct_smul, smul_eq_mul]
    change (2 / C) * C = 2
    exact div_mul_cancel₀ 2 hC'
  have hmul : F *ᵥ (R *ᵥ phi) = phi := by
    rw [Matrix.mulVec_mulVec, hFR, Matrix.one_mulVec]
  have hFc0 : F *ᵥ c0 = (2 / C) • phi := by
    dsimp only [c0]
    rw [Matrix.mulVec_smul, hmul]
  have hpair (r z : ι → ℝ) :
      r ⬝ᵥ (F *ᵥ z) = z ⬝ᵥ (F *ᵥ r) := by
    simpa only [hF] using Matrix.dotProduct_transpose_mulVec F r z
  have hyc0 : y ⬝ᵥ (F *ᵥ c0) = 4 / C := by
    rw [hFc0, dotProduct_smul, smul_eq_mul,
      dotProduct_comm y phi, hy]
    ring
  have hc0y : c0 ⬝ᵥ (F *ᵥ y) = 4 / C := by
    rw [hpair c0 y]
    exact hyc0
  have hc0Fc0 : c0 ⬝ᵥ (F *ᵥ c0) = 4 / C := by
    rw [hFc0, dotProduct_smul, smul_eq_mul,
      dotProduct_comm c0 phi, hmean]
    ring
  have hdiff : (y - c0) ⬝ᵥ (F *ᵥ (y - c0)) =
      y ⬝ᵥ (F *ᵥ y) - 4 / C := by
    simp only [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub,
      hyc0, hc0y, hc0Fc0]
    ring
  have hGram : y ⬝ᵥ (Xi *ᵥ y) =
      p * (y ⬝ᵥ (F *ᵥ y)) + 2 * (L ⬝ᵥ y) := by
    rw [hXi, rankTwoMatrix_mulVec]
    simp only [hy, dotProduct_add, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm y L, dotProduct_comm y phi, hy]
    ring
  constructor
  · exact hmean
  · rw [hGram, hdiff]
    ring

end FiniteMatrices

/-- Exact signed error numerator; no absolute-value estimate is used. -/
theorem residualError_reparam (p alpha gamma D : ℝ)
    (hT : alpha * gamma - D ^ 2 ≠ 0) :
    1 - 4 * p * alpha / (alpha * gamma - D ^ 2) =
      -(D ^ 2 + alpha * (4 * p - gamma)) /
        (alpha * gamma - D ^ 2) := by
  field_simp [hT]
  ring

theorem residualError_abs_le_iff (p alpha gamma D epsilon : ℝ)
    (hT : 0 < alpha * gamma - D ^ 2) :
    |1 - 4 * p * alpha / (alpha * gamma - D ^ 2)| ≤ epsilon ↔
      |D ^ 2 + alpha * (4 * p - gamma)| ≤
        epsilon * (alpha * gamma - D ^ 2) := by
  rw [residualError_reparam p alpha gamma D (ne_of_gt hT),
    abs_div, abs_neg, abs_of_pos hT]
  exact div_le_iff₀ hT

/-- Exact extra error imposed by mean one; the correction square is retained. -/
theorem mean_one_error_gap (p alpha gamma D : ℝ)
    (hgamma : gamma ≠ 0) (hT : alpha * gamma - D ^ 2 ≠ 0) :
    (1 - 4 * p / gamma) -
        (1 - 4 * p * alpha / (alpha * gamma - D ^ 2)) =
      4 * p * D ^ 2 / (gamma * (alpha * gamma - D ^ 2)) := by
  have hT' : gamma * alpha - D ^ 2 ≠ 0 := by
    simpa only [mul_comm gamma alpha] using hT
  field_simp [hgamma, hT, hT']
  ring

end RiemannResearch.LinearAlgebra.RankTwoResidualMean

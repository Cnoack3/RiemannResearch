/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.LinearAlgebra.RankTwoResidualMean

/-!
# Full finite block Schur updates with the signed mean correction

The old and new blocks may have arbitrary finite dimensions. The old inverse
and Schur inverse are genuine matrix inverse equations, not formal symbols.
The mixed source update is retained along with both diagonal updates.
Arithmetic identification, inertia, and limiting saturation are separate.

Source: elementary block elimination for the user-directed complete
mean-one Schur calculation, 8 October 2026.
-/

noncomputable section
open Matrix
namespace RiemannResearch.LinearAlgebra.MeanOneBlockSchur
open RiemannResearch.LinearAlgebra.RankTwoWoodbury

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

def screenedSource (R : Matrix ι ι ℝ) (J : Matrix ι κ ℝ)
    (a : ι → ℝ) (b : κ → ℝ) : κ → ℝ :=
  b - Jᵀ *ᵥ (R *ᵥ a)

def schurMatrix (R : Matrix ι ι ℝ) (J : Matrix ι κ ℝ)
    (K : Matrix κ κ ℝ) : Matrix κ κ ℝ := K - Jᵀ * R * J

/-- Derived solution formulas for both blocks, with no inverse of the enlarged
matrix assumed. -/
theorem solved_block_system
    (F R : Matrix ι ι ℝ) (J : Matrix ι κ ℝ)
    (K S Z : Matrix κ κ ℝ)
    (a x : ι → ℝ) (b y : κ → ℝ)
    (hRF : R * F = 1) (hS : S = schurMatrix R J K) (hZS : Z * S = 1)
    (hold : F *ᵥ x + J *ᵥ y = a)
    (hnew : Jᵀ *ᵥ x + K *ᵥ y = b) :
    x = R *ᵥ a - R *ᵥ (J *ᵥ y) ∧
      y = Z *ᵥ screenedSource R J a b := by
  have hleft (u : ι → ℝ) : R *ᵥ (F *ᵥ u) = u := by
    rw [Matrix.mulVec_mulVec, hRF, Matrix.one_mulVec]
  have holdR := congrArg (fun u : ι → ℝ => R *ᵥ u) hold
  simp only [Matrix.mulVec_add, hleft] at holdR
  have hx : x = R *ᵥ a - R *ᵥ (J *ᵥ y) := eq_sub_of_add_eq holdR
  have hsy : S *ᵥ y = screenedSource R J a b := by
    rw [hx] at hnew
    simp only [Matrix.mulVec_sub] at hnew
    rw [hS, schurMatrix, Matrix.sub_mulVec]
    simp only [← Matrix.mulVec_mulVec]
    unfold screenedSource
    ext i
    have hi := congrFun hnew i
    simp only [Pi.sub_apply, Pi.add_apply] at hi ⊢
    linarith only [hi]
  have hZ := congrArg (fun u : κ → ℝ => Z *ᵥ u) hsy
  rw [Matrix.mulVec_mulVec, hZS, Matrix.one_mulVec] at hZ
  exact ⟨hx, hZ⟩

/-- Complete bilinear inverse-core update. In particular this retains the
mixed signed source `U^T S^{-1} V`. -/
theorem solved_block_bilinear_update
    (F R : Matrix ι ι ℝ) (J : Matrix ι κ ℝ)
    (K S Z : Matrix κ κ ℝ)
    (a c x : ι → ℝ) (b d y : κ → ℝ)
    (hRF : R * F = 1) (hR : Rᵀ = R)
    (hS : S = schurMatrix R J K) (hZS : Z * S = 1)
    (hold : F *ᵥ x + J *ᵥ y = c)
    (hnew : Jᵀ *ᵥ x + K *ᵥ y = d) :
    a ⬝ᵥ x + b ⬝ᵥ y = a ⬝ᵥ (R *ᵥ c) +
      screenedSource R J a b ⬝ᵥ (Z *ᵥ screenedSource R J c d) := by
  obtain ⟨hx, hy⟩ := solved_block_system F R J K S Z c x d y hRF hS hZS hold hnew
  have hpair (u v : ι → ℝ) : u ⬝ᵥ (R *ᵥ v) = v ⬝ᵥ (R *ᵥ u) := by
    simpa only [hR] using Matrix.dotProduct_transpose_mulVec R u v
  have hcross : a ⬝ᵥ (R *ᵥ (J *ᵥ y)) =
      (Jᵀ *ᵥ (R *ᵥ a)) ⬝ᵥ y := by
    calc
      _ = (J *ᵥ y) ⬝ᵥ (R *ᵥ a) := hpair a (J *ᵥ y)
      _ = (R *ᵥ a) ⬝ᵥ (J *ᵥ y) := dotProduct_comm _ _
      _ = y ⬝ᵥ (Jᵀ *ᵥ (R *ᵥ a)) :=
        (Matrix.dotProduct_transpose_mulVec J y (R *ᵥ a)).symm
      _ = _ := dotProduct_comm _ _
  rw [hx, dotProduct_sub, hcross]
  change a ⬝ᵥ (R *ᵥ c) - (Jᵀ *ᵥ (R *ᵥ a)) ⬝ᵥ y + b ⬝ᵥ y =
    a ⬝ᵥ (R *ᵥ c) + (b - Jᵀ *ᵥ (R *ᵥ a)) ⬝ᵥ
      (Z *ᵥ screenedSource R J c d)
  rw [← hy, sub_dotProduct]
  ring

/-- The full coupled updates of the two diagonal charges and their mixed
charge, derived from the two actual block solution systems. -/
theorem coupled_source_updates
    (F R : Matrix ι ι ℝ) (J : Matrix ι κ ℝ)
    (K S Z : Matrix κ κ ℝ)
    (lam phi xLam xPhi : ι → ℝ) (lamNew phiNew yLam yPhi : κ → ℝ)
    (hRF : R * F = 1) (hR : Rᵀ = R)
    (hS : S = schurMatrix R J K) (hZS : Z * S = 1)
    (hLamOld : F *ᵥ xLam + J *ᵥ yLam = lam)
    (hLamNew : Jᵀ *ᵥ xLam + K *ᵥ yLam = lamNew)
    (hPhiOld : F *ᵥ xPhi + J *ᵥ yPhi = phi)
    (hPhiNew : Jᵀ *ᵥ xPhi + K *ᵥ yPhi = phiNew) :
    (lam ⬝ᵥ xLam + lamNew ⬝ᵥ yLam =
      lam ⬝ᵥ (R *ᵥ lam) + screenedSource R J lam lamNew ⬝ᵥ
        (Z *ᵥ screenedSource R J lam lamNew)) ∧
    (lam ⬝ᵥ xPhi + lamNew ⬝ᵥ yPhi =
      lam ⬝ᵥ (R *ᵥ phi) + screenedSource R J lam lamNew ⬝ᵥ
        (Z *ᵥ screenedSource R J phi phiNew)) ∧
    (phi ⬝ᵥ xPhi + phiNew ⬝ᵥ yPhi =
      phi ⬝ᵥ (R *ᵥ phi) + screenedSource R J phi phiNew ⬝ᵥ
        (Z *ᵥ screenedSource R J phi phiNew)) := by
  exact ⟨solved_block_bilinear_update F R J K S Z lam lam xLam lamNew lamNew yLam
      hRF hR hS hZS hLamOld hLamNew,
    solved_block_bilinear_update F R J K S Z lam phi xPhi lamNew phiNew yPhi
      hRF hR hS hZS hPhiOld hPhiNew,
    solved_block_bilinear_update F R J K S Z phi phi xPhi phiNew phiNew yPhi
      hRF hR hS hZS hPhiOld hPhiNew⟩

/-- Positive complete inverse Schur form makes the inverse-core charge
increase. This is a finite monotonicity fact, with no saturation conclusion. -/
theorem inverse_charge_mono
    (F R : Matrix ι ι ℝ) (J : Matrix ι κ ℝ)
    (K S Z : Matrix κ κ ℝ)
    (phi x : ι → ℝ) (phiNew y : κ → ℝ)
    (hRF : R * F = 1) (hR : Rᵀ = R)
    (hS : S = schurMatrix R J K) (hZS : Z * S = 1)
    (hold : F *ᵥ x + J *ᵥ y = phi)
    (hnew : Jᵀ *ᵥ x + K *ᵥ y = phiNew)
    (hZpos : ∀ z : κ → ℝ, 0 ≤ z ⬝ᵥ (Z *ᵥ z)) :
    phi ⬝ᵥ (R *ᵥ phi) ≤ phi ⬝ᵥ x + phiNew ⬝ᵥ y := by
  rw [solved_block_bilinear_update F R J K S Z phi phi x phiNew phiNew y
    hRF hR hS hZS hold hnew]
  exact le_add_of_nonneg_right (hZpos _)

theorem inverse_charge_strict_mono
    (F R : Matrix ι ι ℝ) (J : Matrix ι κ ℝ)
    (K S Z : Matrix κ κ ℝ)
    (phi x : ι → ℝ) (phiNew y : κ → ℝ)
    (hRF : R * F = 1) (hR : Rᵀ = R)
    (hS : S = schurMatrix R J K) (hZS : Z * S = 1)
    (hold : F *ᵥ x + J *ᵥ y = phi)
    (hnew : Jᵀ *ᵥ x + K *ᵥ y = phiNew)
    (hZpos : ∀ z : κ → ℝ, z ≠ 0 → 0 < z ⬝ᵥ (Z *ᵥ z))
    (hV : screenedSource R J phi phiNew ≠ 0) :
    phi ⬝ᵥ (R *ᵥ phi) < phi ⬝ᵥ x + phiNew ⬝ᵥ y := by
  rw [solved_block_bilinear_update F R J K S Z phi phi x phiNew phiNew y
    hRF hR hS hZS hold hnew]
  exact lt_add_of_pos_right _ (hZpos _ hV)

/-- The negative rank-one correction is part of the complete tangent Gram. -/
def meanTangentSchur (S : Matrix κ κ ℝ) (V : κ → ℝ) (C : ℝ) : Matrix κ κ ℝ :=
  S + (1 / C) • vecMulVec V V

omit [DecidableEq κ] in
theorem meanTangentSchur_mulVec (S : Matrix κ κ ℝ) (V y : κ → ℝ) (C : ℝ) :
    meanTangentSchur S V C *ᵥ y =
      S *ᵥ y + ((V ⬝ᵥ y) / C) • V := by
  rw [meanTangentSchur, Matrix.add_mulVec, Matrix.smul_mulVec,
    outer_mulVec_real, smul_smul]
  congr 1
  congr 1
  ring

omit [DecidableEq κ] in
theorem meanTangentSchur_quadratic (S : Matrix κ κ ℝ) (V y : κ → ℝ) (C : ℝ) :
    y ⬝ᵥ (meanTangentSchur S V C *ᵥ y) =
      y ⬝ᵥ (S *ᵥ y) + (V ⬝ᵥ y) ^ 2 / C := by
  rw [meanTangentSchur_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul, dotProduct_comm y V]
  ring

/-- Old block of a fresh mean-zero tangent; its correction uses the entire
screened source. -/
def tangentOld (R : Matrix ι ι ℝ) (J : Matrix ι κ ℝ)
    (phi : ι → ℝ) (V y : κ → ℝ) (C : ℝ) : ι → ℝ :=
  -(R *ᵥ (J *ᵥ y)) - ((V ⬝ᵥ y) / C) • (R *ᵥ phi)

omit [DecidableEq ι] [DecidableEq κ] in
theorem tangent_mean_zero
    (R : Matrix ι ι ℝ) (J : Matrix ι κ ℝ)
    (phi : ι → ℝ) (phiNew y : κ → ℝ)
    (hR : Rᵀ = R) (hC : phi ⬝ᵥ (R *ᵥ phi) ≠ 0) :
    let C := phi ⬝ᵥ (R *ᵥ phi)
    let V := screenedSource R J phi phiNew
    phi ⬝ᵥ tangentOld R J phi V y C + phiNew ⬝ᵥ y = 0 := by
  dsimp only
  have hcross : phi ⬝ᵥ (R *ᵥ (J *ᵥ y)) =
      (Jᵀ *ᵥ (R *ᵥ phi)) ⬝ᵥ y := by
    calc
      _ = (J *ᵥ y) ⬝ᵥ (R *ᵥ phi) := by
        simpa only [hR] using Matrix.dotProduct_transpose_mulVec R phi (J *ᵥ y)
      _ = (R *ᵥ phi) ⬝ᵥ (J *ᵥ y) := dotProduct_comm _ _
      _ = y ⬝ᵥ (Jᵀ *ᵥ (R *ᵥ phi)) :=
        (Matrix.dotProduct_transpose_mulVec J y (R *ᵥ phi)).symm
      _ = _ := dotProduct_comm _ _
  unfold tangentOld screenedSource
  simp only [dotProduct_sub, dotProduct_neg,
    dotProduct_smul, smul_eq_mul, sub_dotProduct]
  rw [hcross]
  field_simp [hC]
  ring

/-- Full tangent Gram. Both cross-block orientations and the entire negative
rank-one term remain in the result. -/
theorem tangent_core_quadratic
    (F R : Matrix ι ι ℝ) (J : Matrix ι κ ℝ)
    (K S : Matrix κ κ ℝ) (phi : ι → ℝ) (V y : κ → ℝ)
    (hFR : F * R = 1) (hR : Rᵀ = R) (hS : S = schurMatrix R J K)
    (hC : phi ⬝ᵥ (R *ᵥ phi) ≠ 0) :
    let C := phi ⬝ᵥ (R *ᵥ phi)
    let x := tangentOld R J phi V y C
    x ⬝ᵥ (F *ᵥ x + J *ᵥ y) +
      y ⬝ᵥ (Jᵀ *ᵥ x + K *ᵥ y) =
        y ⬝ᵥ (meanTangentSchur S V C *ᵥ y) := by
  let C : ℝ := phi ⬝ᵥ (R *ᵥ phi)
  have hC0 : C ≠ 0 := hC
  let t : ℝ := (V ⬝ᵥ y) / C
  let x := tangentOld R J phi V y C
  have hright (u : ι → ℝ) : F *ᵥ (R *ᵥ u) = u := by
    rw [Matrix.mulVec_mulVec, hFR, Matrix.one_mulVec]
  have hOld : F *ᵥ x + J *ᵥ y = -t • phi := by
    dsimp only [x, tangentOld, t]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_neg,
      Matrix.mulVec_smul, hright]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hNew : Jᵀ *ᵥ x + K *ᵥ y = S *ᵥ y - t • (Jᵀ *ᵥ (R *ᵥ phi)) := by
    dsimp only [x, tangentOld, t]
    rw [hS, schurMatrix, Matrix.sub_mulVec]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_neg, Matrix.mulVec_smul,
      ← Matrix.mulVec_mulVec]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hcross : (R *ᵥ (J *ᵥ y)) ⬝ᵥ phi =
      y ⬝ᵥ (Jᵀ *ᵥ (R *ᵥ phi)) := by
    calc
      _ = phi ⬝ᵥ (R *ᵥ (J *ᵥ y)) := dotProduct_comm _ _
      _ = (J *ᵥ y) ⬝ᵥ (R *ᵥ phi) := by
        simpa only [hR] using Matrix.dotProduct_transpose_mulVec R phi (J *ᵥ y)
      _ = (R *ᵥ phi) ⬝ᵥ (J *ᵥ y) := dotProduct_comm _ _
      _ = _ := (Matrix.dotProduct_transpose_mulVec J y (R *ᵥ phi)).symm
  change x ⬝ᵥ (F *ᵥ x + J *ᵥ y) + y ⬝ᵥ (Jᵀ *ᵥ x + K *ᵥ y) =
    y ⬝ᵥ (meanTangentSchur S V C *ᵥ y)
  rw [hOld, hNew, meanTangentSchur_quadratic]
  dsimp only [x, tangentOld]
  simp only [dotProduct_smul, smul_eq_mul, sub_dotProduct, neg_dotProduct,
    smul_dotProduct, dotProduct_sub]
  rw [hcross, dotProduct_comm (R *ᵥ phi) phi]
  change -t * (- (y ⬝ᵥ (Jᵀ *ᵥ (R *ᵥ phi))) - t * C) +
    (y ⬝ᵥ (S *ᵥ y) - t * (y ⬝ᵥ (Jᵀ *ᵥ (R *ᵥ phi)))) =
      y ⬝ᵥ (S *ᵥ y) + (V ⬝ᵥ y) ^ 2 / C
  dsimp only [t]
  field_simp [hC0]
  ring

end RiemannResearch.LinearAlgebra.MeanOneBlockSchur

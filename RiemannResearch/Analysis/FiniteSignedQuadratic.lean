/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Signed finite quadratic completion
Source: user-provided Conditional_IID_Cesaro_Mathematical_Completion_2026-09-17.md,
Section 11. Exact matrix algebra for its concrete Cesaro-tail application.
Inverse existence is not asserted by the completion lemma.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteSignedQuadratic
def quadratic {D : ℕ} (T : Matrix (Fin D) (Fin D) ℝ) (c : Fin D → ℝ) : ℝ :=
  ∑ d, ∑ e, c d * T d e * c e


def correctionMatrix {D r : ℕ} (T : Matrix (Fin D) (Fin D) ℝ)
    (N : Matrix (Fin D) (Fin r) ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  N.transpose * T * N


def correlation {D r : ℕ} (T : Matrix (Fin D) (Fin D) ℝ)
    (N : Matrix (Fin D) (Fin r) ℝ) (c : Fin D → ℝ) : Fin r → ℝ :=
  N.transpose.mulVec (T.mulVec c)


theorem quadratic_add {D : ℕ} (T : Matrix (Fin D) (Fin D) ℝ)
    (hT : ∀ i j, T i j = T j i) (c z : Fin D → ℝ) :
    quadratic T (c + z) = quadratic T c +
      2 * (∑ i, ∑ j, z i * T i j * c j) + quadratic T z := by
  have hc : (∑ i, ∑ j, c i * T i j * z j) = ∑ i, ∑ j, z i * T i j * c j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hT j i]
    ring
  unfold quadratic
  simp only [Pi.add_apply]
  simp_rw [show ∀ i j, (c i + z i) * T i j * (c j + z j) =
    c i * T i j * c j + c i * T i j * z j +
      z i * T i j * c j + z i * T i j * z j by intros; ring]
  simp only [Finset.sum_add_distrib]
  rw [hc]
  ring


/-- Exact signed Schur square completion for an invertible correction Gram.
All assumptions are finite algebra: symmetry and the displayed normal equation. -/
theorem schur_completion {r : ℕ} (S : Matrix (Fin r) (Fin r) ℝ)
    (hS : ∀ i j, S i j = S j i) (h x z : Fin r → ℝ)
    (hx : S.mulVec x = h) (a : ℝ) :
    a + 2 * (∑ i, z i * h i) + quadratic S z =
      a - (∑ i, x i * h i) + quadratic S (z + x) := by
  have hcross (v : Fin r → ℝ) :
      (∑ i, ∑ j, v i * S i j * x j) = ∑ i, v i * h i := by
    apply Finset.sum_congr rfl
    intro i _
    have hn := congrFun hx i
    change (∑ j, S i j * x j) = h i at hn
    rw [← hn, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hq : quadratic S x = ∑ i, x i * h i := hcross x
  have hc := quadratic_add S hS x z
  rw [hcross z, hq, add_comm x z] at hc
  linarith


/-- A genuine two-sided inverse supplies the normal equation; no inverse is
silently assumed to exist for a singular matrix. -/
theorem schur_completion_of_inverse {r : ℕ}
    (S B : Matrix (Fin r) (Fin r) ℝ)
    (hS : ∀ i j, S i j = S j i) (hSB : S * B = 1)
    (h z : Fin r → ℝ) (a : ℝ) :
    a + 2 * (∑ i, z i * h i) + quadratic S z =
      a - (∑ i, B.mulVec h i * h i) + quadratic S (z + B.mulVec h) := by
  apply schur_completion S hS h (B.mulVec h) z
  rw [Matrix.mulVec_mulVec, hSB, Matrix.one_mulVec]



theorem quadratic_mulVec {D : ℕ} (T : Matrix (Fin D) (Fin D) ℝ) (c : Fin D → ℝ) :
    quadratic T c = ∑ i, c i * T.mulVec c i := by
  unfold quadratic Matrix.mulVec dotProduct
  simp only [Finset.mul_sum, mul_assoc]


theorem transpose_pairing {D r : ℕ} (N : Matrix (Fin D) (Fin r) ℝ)
    (z : Fin r → ℝ) (v : Fin D → ℝ) :
    (∑ i, N.mulVec z i * v i) = ∑ j, z j * N.transpose.mulVec v j := by
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring


theorem correction_quadratic {D r : ℕ} (T : Matrix (Fin D) (Fin D) ℝ)
    (N : Matrix (Fin D) (Fin r) ℝ) (z : Fin r → ℝ) :
    quadratic T (N.mulVec z) = quadratic (correctionMatrix T N) z := by
  rw [quadratic_mulVec, transpose_pairing, quadratic_mulVec]
  simp only [correctionMatrix, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-! Source: user-directed exact-head certificate calculations, 24 October 2026.
The following bounds propagate logarithmic source intervals through the complete
signed quadratic expansion above. -/

/-- Coordinate intervals bound a finite quadratic expression without any
positivity or symmetry assumption on its matrix. -/
theorem abs_quadratic_le_of_abs_le {D : ℕ}
    (B : Matrix (Fin D) (Fin D) ℝ) (e ε : Fin D → ℝ)
    (he : ∀ i, |e i| ≤ ε i) :
    |quadratic B e| ≤ ∑ i, ∑ j, |B i j| * ε i * ε j := by
  simp only [← Real.norm_eq_abs] at he ⊢
  have hε (i) : 0 ≤ ε i := (norm_nonneg _).trans (he i)
  unfold quadratic
  calc
    _ ≤ ∑ i, ∑ j, ‖e i * B i j * e j‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ ≤ ∑ i, ∑ j, ‖B i j‖ * ε i * ε j := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, norm_mul]
      calc
        ‖e i‖ * ‖B i j‖ * ‖e j‖ = ‖B i j‖ * ‖e i‖ * ‖e j‖ := by ring
        _ ≤ ‖B i j‖ * ε i * ‖e j‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (he i) (norm_nonneg _)) (norm_nonneg _)
        _ ≤ ‖B i j‖ * ε i * ε j :=
          mul_le_mul_of_nonneg_left (he j) (mul_nonneg (norm_nonneg _) (hε i))

/-- Two-sided source interval error, retaining both terms of the exact
symmetric quadratic expansion: the linear error and the quadratic remainder. -/
theorem quadratic_source_error_bound {D : ℕ}
    (B : Matrix (Fin D) (Fin D) ℝ)
    (hB : ∀ i j, B i j = B j i) (h e ε : Fin D → ℝ)
    (he : ∀ i, |e i| ≤ ε i) :
    |quadratic B (h + e) - quadratic B h| ≤
      2 * (∑ i, |B.mulVec h i| * ε i) +
        ∑ i, ∑ j, |B i j| * ε i * ε j := by
  have hquad := abs_quadratic_le_of_abs_le B e ε he
  simp only [← Real.norm_eq_abs] at he hquad ⊢
  have hlin : ‖∑ i, ∑ j, e i * B i j * h j‖ ≤
      ∑ i, ‖B.mulVec h i‖ * ε i := by
    have hcross : (∑ i, ∑ j, e i * B i j * h j) =
        ∑ i, e i * B.mulVec h i := by
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    rw [hcross]
    calc
      _ ≤ ∑ i, ‖e i * B.mulVec h i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖B.mulVec h i‖ * ε i := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_left (he i) (norm_nonneg _)
  have hexact : quadratic B (h + e) - quadratic B h =
      2 * (∑ i, ∑ j, e i * B i j * h j) + quadratic B e := by
    rw [quadratic_add B hB h e]
    ring
  rw [hexact]
  calc
    _ ≤ ‖2 * (∑ i, ∑ j, e i * B i j * h j)‖ + ‖quadratic B e‖ :=
      norm_add_le _ _
    _ = 2 * ‖∑ i, ∑ j, e i * B i j * h j‖ + ‖quadratic B e‖ := by
      rw [norm_mul]
      norm_num
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hlin (by norm_num)) hquad

/-- An upper certificate suitable for exact rational enclosures of a real
source vector. No positive definiteness of the matrix is required. -/
theorem quadratic_source_upper_bound {D : ℕ}
    (B : Matrix (Fin D) (Fin D) ℝ)
    (hB : ∀ i j, B i j = B j i) (h e ε : Fin D → ℝ)
    (he : ∀ i, |e i| ≤ ε i) :
    quadratic B (h + e) ≤ quadratic B h +
      2 * (∑ i, |B.mulVec h i| * ε i) +
        ∑ i, ∑ j, |B i j| * ε i * ε j := by
  have herr := quadratic_source_error_bound B hB h e ε he
  have hle := le_abs_self (quadratic B (h + e) - quadratic B h)
  linarith


end RiemannResearch.Analysis.FiniteSignedQuadratic

/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact four-site reciprocal certificates

Source: user-provided positive-definite matrix argument, 28 October 2026,
refining the four-site estimate at
https://github.com/Cnoack3/RiemannResearch/commit/457e8cd0362fd6c7cf383f61b28fb893ac83913b.
The 59/120 statement is from that argument. The 29/59 certificate is a direct
rational refinement of the same calculation. Exact matrix identities, leading
principal minors, and sum-of-squares decompositions are retained.
The infinite-tail and actual squarefree-vector applications belong to
QSquarefreeDisplacementEnergy.
-/

noncomputable section
open scoped BigOperators Matrix
namespace RiemannResearch.RH.QFourSiteReciprocalCertificate

/-- Matrix of the constrained four-site norm gap, with f₀ = 2x + 3y - 4z. -/
def headMatrix (lam : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![5 * lam - 7 / 3, 6 * lam - 3, 4 - 8 * lam;
     6 * lam - 3, 10 * lam - 19 / 4, 6 - 12 * lam;
     4 - 8 * lam, 6 - 12 * lam, 17 * lam - 41 / 5]

/-- The exact constrained head gap before estimating either the head or tail. -/
def headGap (lam x y z : ℝ) : ℝ :=
  lam * ((2 * x + 3 * y - 4 * z) ^ 2 + x ^ 2 + y ^ 2 + z ^ 2) -
    ((2 * x + 3 * y - 4 * z) ^ 2 / 2 + x ^ 2 / 3 + y ^ 2 / 4 + z ^ 2 / 5)

theorem headMatrix_quadratic (lam : ℝ) (v : Fin 3 → ℝ) :
    v ⬝ᵥ (headMatrix lam *ᵥ v) = headGap lam (v 0) (v 1) (v 2) := by
  simp [headMatrix, headGap, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem headMatrix_59_120 : headMatrix (59 / 120) =
    !![(1 / 8 : ℝ), -1 / 20, 1 / 15;
       -1 / 20, 1 / 6, 1 / 10;
       1 / 15, 1 / 10, 19 / 120] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [headMatrix]

/-- The generalized characteristic polynomial of the constrained head. -/
theorem headMatrix_det (lam : ℝ) :
    (headMatrix lam).det = (1800 * lam ^ 3 - 1873 * lam ^ 2 + 618 * lam - 65) / 60 := by
  rw [Matrix.det_fin_three]
  simp [headMatrix]
  ring

/-- Exact LDL sum of squares for the user-provided 59 / 120 certificate. -/
theorem headGap_sos_59_120 (x y z : ℝ) :
    headGap (59 / 120) x y z =
      (1 / 8 : ℝ) * (x - 2 * y / 5 + 8 * z / 15) ^ 2 +
      (11 / 75 : ℝ) * (y + 19 * z / 22) ^ 2 + (53 / 3960 : ℝ) * z ^ 2 := by
  unfold headGap
  ring

theorem headGap_pos_59_120 (x y z : ℝ) (h : ¬ (x = 0 ∧ y = 0 ∧ z = 0)) :
    0 < headGap (59 / 120) x y z := by
  rw [headGap_sos_59_120]
  have h₁ := sq_nonneg (x - 2 * y / 5 + 8 * z / 15)
  have h₂ := sq_nonneg (y + 19 * z / 22)
  have h₃ := sq_nonneg z
  by_contra hn
  have hz : z = 0 := by nlinarith
  subst z
  have hy : y = 0 := by nlinarith
  subst y
  have hx : x = 0 := by nlinarith
  exact h ⟨hx, rfl, rfl⟩

/-- Exact LDL sum of squares for the further clean bound 29 / 59. -/
theorem headGap_sos_29_59 (x y z : ℝ) :
    headGap (29 / 59) x y z =
      (22 / 177 : ℝ) * (x - 9 * y / 22 + 6 * z / 11) ^ 2 +
      (375 / 2596 : ℝ) * (y + 112 * z / 125) ^ 2 + (22 / 7375 : ℝ) * z ^ 2 := by
  unfold headGap
  ring

theorem headMatrix_isHermitian (lam : ℝ) : (headMatrix lam).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [headMatrix, Matrix.conjTranspose_apply]

theorem headMatrix_posDef_of_gap_pos (lam : ℝ)
    (h : ∀ x y z : ℝ, ¬ (x = 0 ∧ y = 0 ∧ z = 0) → 0 < headGap lam x y z) :
    (headMatrix lam).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (headMatrix_isHermitian lam)
  intro v hv
  simp only [star_trivial, headMatrix_quadratic]
  apply h
  rintro ⟨h0, h1, h2⟩
  apply hv
  funext i
  fin_cases i <;> assumption

theorem headMatrix_posDef_59_120 : (headMatrix (59 / 120)).PosDef :=
  headMatrix_posDef_of_gap_pos _ headGap_pos_59_120

theorem headGap_pos_29_59 (x y z : ℝ) (h : ¬ (x = 0 ∧ y = 0 ∧ z = 0)) :
    0 < headGap (29 / 59) x y z := by
  rw [headGap_sos_29_59]
  have h₁ := sq_nonneg (x - 9 * y / 22 + 6 * z / 11)
  have h₂ := sq_nonneg (y + 112 * z / 125)
  have h₃ := sq_nonneg z
  by_contra hn
  have hz : z = 0 := by nlinarith
  subst z
  have hy : y = 0 := by nlinarith
  subst y
  have hx : x = 0 := by nlinarith
  exact h ⟨hx, rfl, rfl⟩

theorem headMatrix_posDef_29_59 : (headMatrix (29 / 59)).PosDef :=
  headMatrix_posDef_of_gap_pos _ headGap_pos_29_59

/-- Exact leading principal minors of the user's rational certificate. -/
theorem headMatrix_leadingMinors_59_120 :
    (headMatrix (59 / 120)) 0 0 = (1 / 8 : ℝ) ∧
    ((headMatrix (59 / 120)).submatrix
      (Fin.castLE (by decide : 2 ≤ 3)) (Fin.castLE (by decide : 2 ≤ 3))).det = (11 / 600 : ℝ) ∧
    (headMatrix (59 / 120)).det = (53 / 216000 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [headMatrix]
  · rw [Matrix.det_fin_two]
    change (5 * (59 / 120 : ℝ) - 7 / 3) * (10 * (59 / 120) - 19 / 4) -
      (6 * (59 / 120) - 3) * (6 * (59 / 120) - 3) = 11 / 600
    norm_num
  · rw [headMatrix_det]
    norm_num

/-- Exact leading principal minors of the stronger rational certificate. -/
theorem headMatrix_leadingMinors_29_59 :
    (headMatrix (29 / 59)) 0 0 = (22 / 177 : ℝ) ∧
    ((headMatrix (29 / 59)).submatrix
      (Fin.castLE (by decide : 2 ≤ 3)) (Fin.castLE (by decide : 2 ≤ 3))).det = (125 / 6962 : ℝ) ∧
    (headMatrix (29 / 59)).det = (11 / 205379 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [headMatrix]
  · rw [Matrix.det_fin_two]
    change (5 * (29 / 59 : ℝ) - 7 / 3) * (10 * (29 / 59) - 19 / 4) -
      (6 * (29 / 59) - 3) * (6 * (29 / 59) - 3) = 125 / 6962
    norm_num
  · rw [headMatrix_det]
    norm_num


/-- A sharper rational certificate, with its complete positive remainder. -/
theorem headGap_sos_983_2000 (x y z : ℝ) :
    headGap (983 / 2000) x y z =
      (149 / 1200 : ℝ) * (x - 306*y/745 + 408*z/745)^2 +
      (107319 / 745000 : ℝ) * (y + 32266*z/35773)^2 +
      (15271 / 14309200 : ℝ) * z^2 := by
  unfold headGap
  ring

end RiemannResearch.RH.QFourSiteReciprocalCertificate

/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QResidueGramNumerical
import RiemannResearch.Analysis.GramSchmidtTriangular
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Certified first four squarefree residue change-of-basis columns

The conductor order is 2, 3, 5, 6. Every interval controls the full Q inner
product, through QResidueGramNumerical. Displayed decimal strings are exact
rational centers; the certificate claims absolute error at most 10^(-6),
not correctness of all originally printed digits.

The formulas apply to any linearly independent continuation of these four
atoms. They certify the actual Gram--Schmidt forward and reverse matrices,
and explicit eigenvectors whose last nonzero coordinate is one.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QResidueMatrixNumerical
open InnerProductSpace ZetaTwoHilbert
open RiemannResearch RatInterval
open QResidueGramNumerical
open RiemannResearch.Analysis.FiniteHilbertGram (gramMatrix)
open RiemannResearch.Analysis.GramSchmidtCofactors
open RiemannResearch.Analysis.GramSchmidtTriangular
open RiemannResearch.TriangularEigenvectors

private theorem succAbove_finFour : ∀ (j : Fin 4) (i : Fin 3),
    (j.succAbove i).val = if i.val < j.val then i.val else i.val + 1 := by decide

private theorem succAbove_finThree : ∀ (j : Fin 3) (i : Fin 2),
    (j.succAbove i).val = if i.val < j.val then i.val else i.val + 1 := by decide

private theorem succAbove_finTwo : ∀ (j : Fin 2) (i : Fin 1),
    (j.succAbove i).val = if i.val < j.val then i.val else i.val + 1 := by decide

def g (v : ℕ → QHilbert) (i j : ℕ) : ℝ := inner ℝ (v i) (v j)

def detExpr_0 (v : ℕ → QHilbert) : ℝ := (1 : ℝ)
def detRawInterval_0 : RatInterval := (RatInterval.point (1 : ℚ))
def detInterval_0 : RatInterval := ⟨(1 : ℚ), (1 : ℚ)⟩
theorem det_formula_0 (v : ℕ → QHilbert) :
    (gram v 0).det = detExpr_0 v := by
  norm_num [detExpr_0, g, gram, initialFamily, gramMatrix,
    Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.det_fin_two,
    Matrix.det_fin_one, Fin.sum_univ_succ, Matrix.submatrix_apply, succAbove_finFour, succAbove_finThree, succAbove_finTwo, Fin.succ] <;>
    (try simp only [Fin.lt_def]) <;> norm_num <;> ring

def detExpr_1 (v : ℕ → QHilbert) : ℝ := (g v 0 0)
def detRawInterval_1 : RatInterval := gram_2_2_interval
def detInterval_1 : RatInterval := ⟨(187499999999 / 1000000000000 : ℚ), (187500000001 / 1000000000000 : ℚ)⟩
theorem det_formula_1 (v : ℕ → QHilbert) :
    (gram v 1).det = detExpr_1 v := by
  norm_num [detExpr_1, g, gram, initialFamily, gramMatrix,
    Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.det_fin_two,
    Matrix.det_fin_one, Fin.sum_univ_succ, Matrix.submatrix_apply, succAbove_finFour, succAbove_finThree, succAbove_finTwo, Fin.succ] <;>
    (try simp only [Fin.lt_def]) <;> norm_num <;> ring

def detExpr_2 (v : ℕ → QHilbert) : ℝ := (((g v 0 0) * (g v 1 1)) - ((g v 0 1) * (g v 1 0)))
def detRawInterval_2 : RatInterval := (RatInterval.sub (RatInterval.mul gram_2_2_interval gram_3_3_interval) (RatInterval.mul gram_2_3_interval gram_2_3_interval))
def detInterval_2 : RatInterval := ⟨(17719807636018113 / 1000000000000000000 : ℚ), (17719807636775497 / 1000000000000000000 : ℚ)⟩
theorem det_formula_2 (v : ℕ → QHilbert) :
    (gram v 2).det = detExpr_2 v := by
  norm_num [detExpr_2, g, gram, initialFamily, gramMatrix,
    Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.det_fin_two,
    Matrix.det_fin_one, Fin.sum_univ_succ, Matrix.submatrix_apply, succAbove_finFour, succAbove_finThree, succAbove_finTwo, Fin.succ] <;>
    (try simp only [Fin.lt_def]) <;> norm_num <;> ring

def detExpr_3 (v : ℕ → QHilbert) : ℝ := ((((g v 0 0) * (((g v 1 1) * (g v 2 2)) - ((g v 1 2) * (g v 2 1)))) - ((g v 0 1) * (((g v 1 0) * (g v 2 2)) - ((g v 1 2) * (g v 2 0))))) + ((g v 0 2) * (((g v 1 0) * (g v 2 1)) - ((g v 1 1) * (g v 2 0)))))
def detRawInterval_3 : RatInterval := (RatInterval.add (RatInterval.sub (RatInterval.mul gram_2_2_interval (RatInterval.sub (RatInterval.mul gram_3_3_interval gram_5_5_interval) (RatInterval.mul gram_3_5_interval gram_3_5_interval))) (RatInterval.mul gram_2_3_interval (RatInterval.sub (RatInterval.mul gram_2_3_interval gram_5_5_interval) (RatInterval.mul gram_3_5_interval gram_2_5_interval)))) (RatInterval.mul gram_2_5_interval (RatInterval.sub (RatInterval.mul gram_2_3_interval gram_3_5_interval) (RatInterval.mul gram_3_3_interval gram_2_5_interval))))
def detInterval_3 : RatInterval := ⟨(23332166879717 / 25000000000000000 : ℚ), (233321668851047 / 250000000000000000 : ℚ)⟩
theorem det_formula_3 (v : ℕ → QHilbert) :
    (gram v 3).det = detExpr_3 v := by
  norm_num [detExpr_3, g, gram, initialFamily, gramMatrix,
    Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.det_fin_two,
    Matrix.det_fin_one, Fin.sum_univ_succ, Matrix.submatrix_apply, succAbove_finFour, succAbove_finThree, succAbove_finTwo, Fin.succ] <;>
    (try simp only [Fin.lt_def]) <;> norm_num <;> ring

def detExpr_4 (v : ℕ → QHilbert) : ℝ := (((((g v 0 0) * ((((g v 1 1) * (((g v 2 2) * (g v 3 3)) - ((g v 2 3) * (g v 3 2)))) - ((g v 1 2) * (((g v 2 1) * (g v 3 3)) - ((g v 2 3) * (g v 3 1))))) + ((g v 1 3) * (((g v 2 1) * (g v 3 2)) - ((g v 2 2) * (g v 3 1)))))) - ((g v 0 1) * ((((g v 1 0) * (((g v 2 2) * (g v 3 3)) - ((g v 2 3) * (g v 3 2)))) - ((g v 1 2) * (((g v 2 0) * (g v 3 3)) - ((g v 2 3) * (g v 3 0))))) + ((g v 1 3) * (((g v 2 0) * (g v 3 2)) - ((g v 2 2) * (g v 3 0))))))) + ((g v 0 2) * ((((g v 1 0) * (((g v 2 1) * (g v 3 3)) - ((g v 2 3) * (g v 3 1)))) - ((g v 1 1) * (((g v 2 0) * (g v 3 3)) - ((g v 2 3) * (g v 3 0))))) + ((g v 1 3) * (((g v 2 0) * (g v 3 1)) - ((g v 2 1) * (g v 3 0))))))) - ((g v 0 3) * ((((g v 1 0) * (((g v 2 1) * (g v 3 2)) - ((g v 2 2) * (g v 3 1)))) - ((g v 1 1) * (((g v 2 0) * (g v 3 2)) - ((g v 2 2) * (g v 3 0))))) + ((g v 1 2) * (((g v 2 0) * (g v 3 1)) - ((g v 2 1) * (g v 3 0)))))))
def detRawInterval_4 : RatInterval := (RatInterval.sub (RatInterval.add (RatInterval.sub (RatInterval.mul gram_2_2_interval (RatInterval.add (RatInterval.sub (RatInterval.mul gram_3_3_interval (RatInterval.sub (RatInterval.mul gram_5_5_interval gram_6_6_interval) (RatInterval.mul gram_5_6_interval gram_5_6_interval))) (RatInterval.mul gram_3_5_interval (RatInterval.sub (RatInterval.mul gram_3_5_interval gram_6_6_interval) (RatInterval.mul gram_5_6_interval gram_3_6_interval)))) (RatInterval.mul gram_3_6_interval (RatInterval.sub (RatInterval.mul gram_3_5_interval gram_5_6_interval) (RatInterval.mul gram_5_5_interval gram_3_6_interval))))) (RatInterval.mul gram_2_3_interval (RatInterval.add (RatInterval.sub (RatInterval.mul gram_2_3_interval (RatInterval.sub (RatInterval.mul gram_5_5_interval gram_6_6_interval) (RatInterval.mul gram_5_6_interval gram_5_6_interval))) (RatInterval.mul gram_3_5_interval (RatInterval.sub (RatInterval.mul gram_2_5_interval gram_6_6_interval) (RatInterval.mul gram_5_6_interval gram_2_6_interval)))) (RatInterval.mul gram_3_6_interval (RatInterval.sub (RatInterval.mul gram_2_5_interval gram_5_6_interval) (RatInterval.mul gram_5_5_interval gram_2_6_interval)))))) (RatInterval.mul gram_2_5_interval (RatInterval.add (RatInterval.sub (RatInterval.mul gram_2_3_interval (RatInterval.sub (RatInterval.mul gram_3_5_interval gram_6_6_interval) (RatInterval.mul gram_5_6_interval gram_3_6_interval))) (RatInterval.mul gram_3_3_interval (RatInterval.sub (RatInterval.mul gram_2_5_interval gram_6_6_interval) (RatInterval.mul gram_5_6_interval gram_2_6_interval)))) (RatInterval.mul gram_3_6_interval (RatInterval.sub (RatInterval.mul gram_2_5_interval gram_3_6_interval) (RatInterval.mul gram_3_5_interval gram_2_6_interval)))))) (RatInterval.mul gram_2_6_interval (RatInterval.add (RatInterval.sub (RatInterval.mul gram_2_3_interval (RatInterval.sub (RatInterval.mul gram_3_5_interval gram_5_6_interval) (RatInterval.mul gram_5_5_interval gram_3_6_interval))) (RatInterval.mul gram_3_3_interval (RatInterval.sub (RatInterval.mul gram_2_5_interval gram_5_6_interval) (RatInterval.mul gram_5_5_interval gram_2_6_interval)))) (RatInterval.mul gram_3_5_interval (RatInterval.sub (RatInterval.mul gram_2_5_interval gram_3_6_interval) (RatInterval.mul gram_3_5_interval gram_2_6_interval))))))
def detInterval_4 : RatInterval := ⟨(2236776923383 / 100000000000000000 : ℚ), (11183884655157 / 500000000000000000 : ℚ)⟩
theorem det_formula_4 (v : ℕ → QHilbert) :
    (gram v 4).det = detExpr_4 v := by
  norm_num [detExpr_4, g, gram, initialFamily, gramMatrix,
    Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.det_fin_two,
    Matrix.det_fin_one, Fin.sum_univ_succ, Matrix.submatrix_apply, succAbove_finFour, succAbove_finThree, succAbove_finTwo, Fin.succ] <;>
    (try simp only [Fin.lt_def]) <;> norm_num <;> ring

def cofactorExpr_0_0 (v : ℕ → QHilbert) : ℝ := (1 : ℝ)
def cofactorRawInterval_0_0 : RatInterval := (RatInterval.point (1 : ℚ))
def cofactorInterval_0_0 : RatInterval := ⟨(1 : ℚ), (1 : ℚ)⟩
theorem forward_formula_0_0 {v : ℕ → QHilbert}
    (hv : LinearIndependent ℝ v) :
    forward v 4 0 0 = cofactorExpr_0_0 v /
      Real.sqrt ((gram v 0).det * (gram v 1).det) := by
  change coefficient v 0 (⟨0, by decide⟩ : Fin 1) = _
  rw [coefficient_eq_cofactor hv]
  congr 1
  norm_num [cofactorExpr_0_0, g, gram, initialFamily, gramMatrix,
    Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.det_fin_two,
    Matrix.det_fin_one, Fin.sum_univ_succ, Matrix.submatrix_apply, succAbove_finFour, succAbove_finThree, succAbove_finTwo, Fin.succ] <;>
    (try simp only [Fin.lt_def]) <;> norm_num <;> ring

def cofactorExpr_0_1 (v : ℕ → QHilbert) : ℝ := (-(g v 0 1))
def cofactorRawInterval_0_1 : RatInterval := (RatInterval.neg gram_2_3_interval)
def cofactorInterval_0_1 : RatInterval := ⟨(-117190113381 / 1000000000000 : ℚ), (-5859505669 / 50000000000 : ℚ)⟩
theorem forward_formula_0_1 {v : ℕ → QHilbert}
    (hv : LinearIndependent ℝ v) :
    forward v 4 0 1 = cofactorExpr_0_1 v /
      Real.sqrt ((gram v 1).det * (gram v 2).det) := by
  change coefficient v 1 (⟨0, by decide⟩ : Fin 2) = _
  rw [coefficient_eq_cofactor hv]
  congr 1
  norm_num [cofactorExpr_0_1, g, gram, initialFamily, gramMatrix,
    Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.det_fin_two,
    Matrix.det_fin_one, Fin.sum_univ_succ, Matrix.submatrix_apply, succAbove_finFour, succAbove_finThree, succAbove_finTwo, Fin.succ] <;>
    (try simp only [Fin.lt_def]) <;> norm_num <;> ring

def cofactorExpr_1_1 (v : ℕ → QHilbert) : ℝ := (g v 0 0)
def cofactorRawInterval_1_1 : RatInterval := gram_2_2_interval
def cofactorInterval_1_1 : RatInterval := ⟨(187499999999 / 1000000000000 : ℚ), (187500000001 / 1000000000000 : ℚ)⟩
theorem forward_formula_1_1 {v : ℕ → QHilbert}
    (hv : LinearIndependent ℝ v) :
    forward v 4 1 1 = cofactorExpr_1_1 v /
      Real.sqrt ((gram v 1).det * (gram v 2).det) := by
  change coefficient v 1 (⟨1, by decide⟩ : Fin 2) = _
  rw [coefficient_eq_cofactor hv]
  congr 1
  norm_num [cofactorExpr_1_1, g, gram, initialFamily, gramMatrix,
    Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.det_fin_two,
    Matrix.det_fin_one, Fin.sum_univ_succ, Matrix.submatrix_apply, succAbove_finFour, succAbove_finThree, succAbove_finTwo, Fin.succ] <;>
    (try simp only [Fin.lt_def]) <;> norm_num <;> ring

def cofactorExpr_0_2 (v : ℕ → QHilbert) : ℝ := (((g v 0 1) * (g v 1 2)) - ((g v 0 2) * (g v 1 1)))
def cofactorRawInterval_0_2 : RatInterval := (RatInterval.sub (RatInterval.mul gram_2_3_interval gram_3_5_interval) (RatInterval.mul gram_2_5_interval gram_3_3_interval))
def cofactorInterval_0_2 : RatInterval := ⟨(-158859920175597 / 50000000000000000 : ℚ), (-317719840303013 / 100000000000000000 : ℚ)⟩
theorem forward_formula_0_2 {v : ℕ → QHilbert}
    (hv : LinearIndependent ℝ v) :
    forward v 4 0 2 = cofactorExpr_0_2 v /
      Real.sqrt ((gram v 2).det * (gram v 3).det) := by
  change coefficient v 2 (⟨0, by decide⟩ : Fin 3) = _
  rw [coefficient_eq_cofactor hv]
  congr 1
  norm_num [cofactorExpr_0_2, g, gram, initialFamily, gramMatrix,
    Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.det_fin_two,
    Matrix.det_fin_one, Fin.sum_univ_succ, Matrix.submatrix_apply, succAbove_finFour, succAbove_finThree, succAbove_finTwo, Fin.succ] <;>
    (try simp only [Fin.lt_def]) <;> norm_num <;> ring

def cofactorExpr_1_2 (v : ℕ → QHilbert) : ℝ := (-(((g v 0 0) * (g v 1 2)) - ((g v 0 2) * (g v 1 0))))
def cofactorRawInterval_1_2 : RatInterval := (RatInterval.neg (RatInterval.sub (RatInterval.mul gram_2_2_interval gram_3_5_interval) (RatInterval.mul gram_2_5_interval gram_2_3_interval)))
def cofactorInterval_1_2 : RatInterval := ⟨(-8845322846612637 / 1000000000000000000 : ℚ), (-1105665355750791 / 125000000000000000 : ℚ)⟩
theorem forward_formula_1_2 {v : ℕ → QHilbert}
    (hv : LinearIndependent ℝ v) :
    forward v 4 1 2 = cofactorExpr_1_2 v /
      Real.sqrt ((gram v 2).det * (gram v 3).det) := by
  change coefficient v 2 (⟨1, by decide⟩ : Fin 3) = _
  rw [coefficient_eq_cofactor hv]
  congr 1
  norm_num [cofactorExpr_1_2, g, gram, initialFamily, gramMatrix,
    Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.det_fin_two,
    Matrix.det_fin_one, Fin.sum_univ_succ, Matrix.submatrix_apply, succAbove_finFour, succAbove_finThree, succAbove_finTwo, Fin.succ] <;>
    (try simp only [Fin.lt_def]) <;> norm_num <;> ring

def cofactorExpr_2_2 (v : ℕ → QHilbert) : ℝ := (((g v 0 0) * (g v 1 1)) - ((g v 0 1) * (g v 1 0)))
def cofactorRawInterval_2_2 : RatInterval := (RatInterval.sub (RatInterval.mul gram_2_2_interval gram_3_3_interval) (RatInterval.mul gram_2_3_interval gram_2_3_interval))
def cofactorInterval_2_2 : RatInterval := ⟨(17719807636018113 / 1000000000000000000 : ℚ), (17719807636775497 / 1000000000000000000 : ℚ)⟩
theorem forward_formula_2_2 {v : ℕ → QHilbert}
    (hv : LinearIndependent ℝ v) :
    forward v 4 2 2 = cofactorExpr_2_2 v /
      Real.sqrt ((gram v 2).det * (gram v 3).det) := by
  change coefficient v 2 (⟨2, by decide⟩ : Fin 3) = _
  rw [coefficient_eq_cofactor hv]
  congr 1
  norm_num [cofactorExpr_2_2, g, gram, initialFamily, gramMatrix,
    Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.det_fin_two,
    Matrix.det_fin_one, Fin.sum_univ_succ, Matrix.submatrix_apply, succAbove_finFour, succAbove_finThree, succAbove_finTwo, Fin.succ] <;>
    (try simp only [Fin.lt_def]) <;> norm_num <;> ring

def cofactorExpr_0_3 (v : ℕ → QHilbert) : ℝ := (-((((g v 0 1) * (((g v 1 2) * (g v 2 3)) - ((g v 1 3) * (g v 2 2)))) - ((g v 0 2) * (((g v 1 1) * (g v 2 3)) - ((g v 1 3) * (g v 2 1))))) + ((g v 0 3) * (((g v 1 1) * (g v 2 2)) - ((g v 1 2) * (g v 2 1))))))
def cofactorRawInterval_0_3 : RatInterval := (RatInterval.neg (RatInterval.add (RatInterval.sub (RatInterval.mul gram_2_3_interval (RatInterval.sub (RatInterval.mul gram_3_5_interval gram_5_6_interval) (RatInterval.mul gram_3_6_interval gram_5_5_interval))) (RatInterval.mul gram_2_5_interval (RatInterval.sub (RatInterval.mul gram_3_3_interval gram_5_6_interval) (RatInterval.mul gram_3_6_interval gram_3_5_interval)))) (RatInterval.mul gram_2_6_interval (RatInterval.sub (RatInterval.mul gram_3_3_interval gram_5_5_interval) (RatInterval.mul gram_3_5_interval gram_3_5_interval)))))
def cofactorInterval_0_3 : RatInterval := ⟨(-12453038619373 / 250000000000000000 : ℚ), (-194578727823 / 3906250000000000 : ℚ)⟩
theorem forward_formula_0_3 {v : ℕ → QHilbert}
    (hv : LinearIndependent ℝ v) :
    forward v 4 0 3 = cofactorExpr_0_3 v /
      Real.sqrt ((gram v 3).det * (gram v 4).det) := by
  change coefficient v 3 (⟨0, by decide⟩ : Fin 4) = _
  rw [coefficient_eq_cofactor hv]
  congr 1
  norm_num [cofactorExpr_0_3, g, gram, initialFamily, gramMatrix,
    Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.det_fin_two,
    Matrix.det_fin_one, Fin.sum_univ_succ, Matrix.submatrix_apply, succAbove_finFour, succAbove_finThree, succAbove_finTwo, Fin.succ] <;>
    (try simp only [Fin.lt_def]) <;> norm_num <;> ring

def cofactorExpr_1_3 (v : ℕ → QHilbert) : ℝ := ((((g v 0 0) * (((g v 1 2) * (g v 2 3)) - ((g v 1 3) * (g v 2 2)))) - ((g v 0 2) * (((g v 1 0) * (g v 2 3)) - ((g v 1 3) * (g v 2 0))))) + ((g v 0 3) * (((g v 1 0) * (g v 2 2)) - ((g v 1 2) * (g v 2 0)))))
def cofactorRawInterval_1_3 : RatInterval := (RatInterval.add (RatInterval.sub (RatInterval.mul gram_2_2_interval (RatInterval.sub (RatInterval.mul gram_3_5_interval gram_5_6_interval) (RatInterval.mul gram_3_6_interval gram_5_5_interval))) (RatInterval.mul gram_2_5_interval (RatInterval.sub (RatInterval.mul gram_2_3_interval gram_5_6_interval) (RatInterval.mul gram_3_6_interval gram_2_5_interval)))) (RatInterval.mul gram_2_6_interval (RatInterval.sub (RatInterval.mul gram_2_3_interval gram_5_5_interval) (RatInterval.mul gram_3_5_interval gram_2_5_interval))))
def cofactorInterval_1_3 : RatInterval := ⟨(-246030617683139 / 1000000000000000000 : ℚ), (-246030617515377 / 1000000000000000000 : ℚ)⟩
theorem forward_formula_1_3 {v : ℕ → QHilbert}
    (hv : LinearIndependent ℝ v) :
    forward v 4 1 3 = cofactorExpr_1_3 v /
      Real.sqrt ((gram v 3).det * (gram v 4).det) := by
  change coefficient v 3 (⟨1, by decide⟩ : Fin 4) = _
  rw [coefficient_eq_cofactor hv]
  congr 1
  norm_num [cofactorExpr_1_3, g, gram, initialFamily, gramMatrix,
    Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.det_fin_two,
    Matrix.det_fin_one, Fin.sum_univ_succ, Matrix.submatrix_apply, succAbove_finFour, succAbove_finThree, succAbove_finTwo, Fin.succ] <;>
    (try simp only [Fin.lt_def]) <;> norm_num <;> ring

def cofactorExpr_2_3 (v : ℕ → QHilbert) : ℝ := (-((((g v 0 0) * (((g v 1 1) * (g v 2 3)) - ((g v 1 3) * (g v 2 1)))) - ((g v 0 1) * (((g v 1 0) * (g v 2 3)) - ((g v 1 3) * (g v 2 0))))) + ((g v 0 3) * (((g v 1 0) * (g v 2 1)) - ((g v 1 1) * (g v 2 0))))))
def cofactorRawInterval_2_3 : RatInterval := (RatInterval.neg (RatInterval.add (RatInterval.sub (RatInterval.mul gram_2_2_interval (RatInterval.sub (RatInterval.mul gram_3_3_interval gram_5_6_interval) (RatInterval.mul gram_3_6_interval gram_3_5_interval))) (RatInterval.mul gram_2_3_interval (RatInterval.sub (RatInterval.mul gram_2_3_interval gram_5_6_interval) (RatInterval.mul gram_3_6_interval gram_2_5_interval)))) (RatInterval.mul gram_2_6_interval (RatInterval.sub (RatInterval.mul gram_2_3_interval gram_3_5_interval) (RatInterval.mul gram_3_3_interval gram_2_5_interval)))))
def cofactorInterval_2_3 : RatInterval := ⟨(-12068112087747 / 25000000000000000 : ℚ), (-48272448331587 / 100000000000000000 : ℚ)⟩
theorem forward_formula_2_3 {v : ℕ → QHilbert}
    (hv : LinearIndependent ℝ v) :
    forward v 4 2 3 = cofactorExpr_2_3 v /
      Real.sqrt ((gram v 3).det * (gram v 4).det) := by
  change coefficient v 3 (⟨2, by decide⟩ : Fin 4) = _
  rw [coefficient_eq_cofactor hv]
  congr 1
  norm_num [cofactorExpr_2_3, g, gram, initialFamily, gramMatrix,
    Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.det_fin_two,
    Matrix.det_fin_one, Fin.sum_univ_succ, Matrix.submatrix_apply, succAbove_finFour, succAbove_finThree, succAbove_finTwo, Fin.succ] <;>
    (try simp only [Fin.lt_def]) <;> norm_num <;> ring

def cofactorExpr_3_3 (v : ℕ → QHilbert) : ℝ := ((((g v 0 0) * (((g v 1 1) * (g v 2 2)) - ((g v 1 2) * (g v 2 1)))) - ((g v 0 1) * (((g v 1 0) * (g v 2 2)) - ((g v 1 2) * (g v 2 0))))) + ((g v 0 2) * (((g v 1 0) * (g v 2 1)) - ((g v 1 1) * (g v 2 0)))))
def cofactorRawInterval_3_3 : RatInterval := (RatInterval.add (RatInterval.sub (RatInterval.mul gram_2_2_interval (RatInterval.sub (RatInterval.mul gram_3_3_interval gram_5_5_interval) (RatInterval.mul gram_3_5_interval gram_3_5_interval))) (RatInterval.mul gram_2_3_interval (RatInterval.sub (RatInterval.mul gram_2_3_interval gram_5_5_interval) (RatInterval.mul gram_3_5_interval gram_2_5_interval)))) (RatInterval.mul gram_2_5_interval (RatInterval.sub (RatInterval.mul gram_2_3_interval gram_3_5_interval) (RatInterval.mul gram_3_3_interval gram_2_5_interval))))
def cofactorInterval_3_3 : RatInterval := ⟨(23332166879717 / 25000000000000000 : ℚ), (233321668851047 / 250000000000000000 : ℚ)⟩
theorem forward_formula_3_3 {v : ℕ → QHilbert}
    (hv : LinearIndependent ℝ v) :
    forward v 4 3 3 = cofactorExpr_3_3 v /
      Real.sqrt ((gram v 3).det * (gram v 4).det) := by
  change coefficient v 3 (⟨3, by decide⟩ : Fin 4) = _
  rw [coefficient_eq_cofactor hv]
  congr 1
  norm_num [cofactorExpr_3_3, g, gram, initialFamily, gramMatrix,
    Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.det_fin_two,
    Matrix.det_fin_one, Fin.sum_univ_succ, Matrix.submatrix_apply, succAbove_finFour, succAbove_finThree, succAbove_finTwo, Fin.succ] <;>
    (try simp only [Fin.lt_def]) <;> norm_num <;> ring

def denominatorInterval_0 : RatInterval := ⟨(216506350945532311 / 500000000000000000 : ℚ), (54126587736671753 / 125000000000000000 : ℚ)⟩
def denominatorInterval_1 : RatInterval := ⟨(14410204569452849 / 250000000000000000 : ℚ), (57640818279350663 / 1000000000000000000 : ℚ)⟩
def denominatorInterval_2 : RatInterval := ⟨(2033326114621209 / 500000000000000000 : ℚ), (4066652229798849 / 1000000000000000000 : ℚ)⟩
def denominatorInterval_3 : RatInterval := ⟨(144483704893073 / 1000000000000000000 : ℚ), (144483705156779 / 1000000000000000000 : ℚ)⟩
def a_0_0_interval : RatInterval := ⟨(144337567297 / 62500000000 : ℚ), (461880215353 / 200000000000 : ℚ)⟩
def a_0_1_interval : RatInterval := ⟨(-2033109814927 / 1000000000000 : ℚ), (-1016554907427 / 500000000000 : ℚ)⟩
def a_0_2_interval : RatInterval := ⟨(-781281069639 / 1000000000000 : ℚ), (-781281069413 / 1000000000000 : ℚ)⟩
def a_0_3_interval : RatInterval := ⟨(-344759670403 / 1000000000000 : ℚ), (-344759668701 / 1000000000000 : ℚ)⟩
def a_1_0_interval : RatInterval := ⟨(0 : ℚ), (0 : ℚ)⟩
def a_1_1_interval : RatInterval := ⟨(813225790317 / 250000000000 : ℚ), (3252903161391 / 1000000000000 : ℚ)⟩
def a_1_2_interval : RatInterval := ⟨(-543771777619 / 250000000000 : ℚ), (-2175087110029 / 1000000000000 : ℚ)⟩
def a_1_3_interval : RatInterval := ⟨(-851413029121 / 500000000000 : ℚ), (-425706513493 / 250000000000 : ℚ)⟩
def a_2_0_interval : RatInterval := ⟨(0 : ℚ), (0 : ℚ)⟩
def a_2_1_interval : RatInterval := ⟨(0 : ℚ), (0 : ℚ)⟩
def a_2_2_interval : RatInterval := ⟨(544668151919 / 125000000000 : ℚ), (544668152017 / 125000000000 : ℚ)⟩
def a_2_3_interval : RatInterval := ⟨(-334103062949 / 100000000000 : ℚ), (-104407206939 / 31250000000 : ℚ)⟩
def a_3_0_interval : RatInterval := ⟨(0 : ℚ), (0 : ℚ)⟩
def a_3_1_interval : RatInterval := ⟨(0 : ℚ), (0 : ℚ)⟩
def a_3_2_interval : RatInterval := ⟨(0 : ℚ), (0 : ℚ)⟩
def a_3_3_interval : RatInterval := ⟨(1614864932651 / 250000000000 : ℚ), (3229729871943 / 500000000000 : ℚ)⟩

def reverseExpr_0_0 (v : ℕ → QHilbert) : ℝ := (((((forward v 4 0 0) * (g v 0 0)) + ((forward v 4 1 0) * (g v 1 0))) + ((forward v 4 2 0) * (g v 2 0))) + ((forward v 4 3 0) * (g v 3 0)))
def reverseRawInterval_0_0 : RatInterval := (RatInterval.add (RatInterval.add (RatInterval.add (RatInterval.mul a_0_0_interval gram_2_2_interval) (RatInterval.mul a_1_0_interval gram_2_3_interval)) (RatInterval.mul a_2_0_interval gram_2_5_interval)) (RatInterval.mul a_3_0_interval gram_2_6_interval))
def reverseExpr_0_1 (v : ℕ → QHilbert) : ℝ := (((((forward v 4 0 0) * (g v 0 1)) + ((forward v 4 1 0) * (g v 1 1))) + ((forward v 4 2 0) * (g v 2 1))) + ((forward v 4 3 0) * (g v 3 1)))
def reverseRawInterval_0_1 : RatInterval := (RatInterval.add (RatInterval.add (RatInterval.add (RatInterval.mul a_0_0_interval gram_2_3_interval) (RatInterval.mul a_1_0_interval gram_3_3_interval)) (RatInterval.mul a_2_0_interval gram_3_5_interval)) (RatInterval.mul a_3_0_interval gram_3_6_interval))
def reverseExpr_0_2 (v : ℕ → QHilbert) : ℝ := (((((forward v 4 0 0) * (g v 0 2)) + ((forward v 4 1 0) * (g v 1 2))) + ((forward v 4 2 0) * (g v 2 2))) + ((forward v 4 3 0) * (g v 3 2)))
def reverseRawInterval_0_2 : RatInterval := (RatInterval.add (RatInterval.add (RatInterval.add (RatInterval.mul a_0_0_interval gram_2_5_interval) (RatInterval.mul a_1_0_interval gram_3_5_interval)) (RatInterval.mul a_2_0_interval gram_5_5_interval)) (RatInterval.mul a_3_0_interval gram_5_6_interval))
def reverseExpr_0_3 (v : ℕ → QHilbert) : ℝ := (((((forward v 4 0 0) * (g v 0 3)) + ((forward v 4 1 0) * (g v 1 3))) + ((forward v 4 2 0) * (g v 2 3))) + ((forward v 4 3 0) * (g v 3 3)))
def reverseRawInterval_0_3 : RatInterval := (RatInterval.add (RatInterval.add (RatInterval.add (RatInterval.mul a_0_0_interval gram_2_6_interval) (RatInterval.mul a_1_0_interval gram_3_6_interval)) (RatInterval.mul a_2_0_interval gram_5_6_interval)) (RatInterval.mul a_3_0_interval gram_6_6_interval))
def reverseExpr_1_1 (v : ℕ → QHilbert) : ℝ := (((((forward v 4 0 1) * (g v 0 1)) + ((forward v 4 1 1) * (g v 1 1))) + ((forward v 4 2 1) * (g v 2 1))) + ((forward v 4 3 1) * (g v 3 1)))
def reverseRawInterval_1_1 : RatInterval := (RatInterval.add (RatInterval.add (RatInterval.add (RatInterval.mul a_0_1_interval gram_2_3_interval) (RatInterval.mul a_1_1_interval gram_3_3_interval)) (RatInterval.mul a_2_1_interval gram_3_5_interval)) (RatInterval.mul a_3_1_interval gram_3_6_interval))
def reverseExpr_1_2 (v : ℕ → QHilbert) : ℝ := (((((forward v 4 0 1) * (g v 0 2)) + ((forward v 4 1 1) * (g v 1 2))) + ((forward v 4 2 1) * (g v 2 2))) + ((forward v 4 3 1) * (g v 3 2)))
def reverseRawInterval_1_2 : RatInterval := (RatInterval.add (RatInterval.add (RatInterval.add (RatInterval.mul a_0_1_interval gram_2_5_interval) (RatInterval.mul a_1_1_interval gram_3_5_interval)) (RatInterval.mul a_2_1_interval gram_5_5_interval)) (RatInterval.mul a_3_1_interval gram_5_6_interval))
def reverseExpr_1_3 (v : ℕ → QHilbert) : ℝ := (((((forward v 4 0 1) * (g v 0 3)) + ((forward v 4 1 1) * (g v 1 3))) + ((forward v 4 2 1) * (g v 2 3))) + ((forward v 4 3 1) * (g v 3 3)))
def reverseRawInterval_1_3 : RatInterval := (RatInterval.add (RatInterval.add (RatInterval.add (RatInterval.mul a_0_1_interval gram_2_6_interval) (RatInterval.mul a_1_1_interval gram_3_6_interval)) (RatInterval.mul a_2_1_interval gram_5_6_interval)) (RatInterval.mul a_3_1_interval gram_6_6_interval))
def reverseExpr_2_2 (v : ℕ → QHilbert) : ℝ := (((((forward v 4 0 2) * (g v 0 2)) + ((forward v 4 1 2) * (g v 1 2))) + ((forward v 4 2 2) * (g v 2 2))) + ((forward v 4 3 2) * (g v 3 2)))
def reverseRawInterval_2_2 : RatInterval := (RatInterval.add (RatInterval.add (RatInterval.add (RatInterval.mul a_0_2_interval gram_2_5_interval) (RatInterval.mul a_1_2_interval gram_3_5_interval)) (RatInterval.mul a_2_2_interval gram_5_5_interval)) (RatInterval.mul a_3_2_interval gram_5_6_interval))
def reverseExpr_2_3 (v : ℕ → QHilbert) : ℝ := (((((forward v 4 0 2) * (g v 0 3)) + ((forward v 4 1 2) * (g v 1 3))) + ((forward v 4 2 2) * (g v 2 3))) + ((forward v 4 3 2) * (g v 3 3)))
def reverseRawInterval_2_3 : RatInterval := (RatInterval.add (RatInterval.add (RatInterval.add (RatInterval.mul a_0_2_interval gram_2_6_interval) (RatInterval.mul a_1_2_interval gram_3_6_interval)) (RatInterval.mul a_2_2_interval gram_5_6_interval)) (RatInterval.mul a_3_2_interval gram_6_6_interval))
def reverseExpr_3_3 (v : ℕ → QHilbert) : ℝ := (((((forward v 4 0 3) * (g v 0 3)) + ((forward v 4 1 3) * (g v 1 3))) + ((forward v 4 2 3) * (g v 2 3))) + ((forward v 4 3 3) * (g v 3 3)))
def reverseRawInterval_3_3 : RatInterval := (RatInterval.add (RatInterval.add (RatInterval.add (RatInterval.mul a_0_3_interval gram_2_6_interval) (RatInterval.mul a_1_3_interval gram_3_6_interval)) (RatInterval.mul a_2_3_interval gram_5_6_interval)) (RatInterval.mul a_3_3_interval gram_6_6_interval))
def r_0_0_interval : RatInterval := ⟨(6765823467 / 15625000000 : ℚ), (54126587737 / 125000000000 : ℚ)⟩
def r_0_1_interval : RatInterval := ⟨(33829871753 / 125000000000 : ℚ), (270638974029 / 1000000000000 : ℚ)⟩
def r_0_2_interval : RatInterval := ⟨(212736867263 / 1000000000000 : ℚ), (212736867267 / 1000000000000 : ℚ)⟩
def r_0_3_interval : RatInterval := ⟨(8179611641 / 40000000000 : ℚ), (20449029103 / 100000000000 : ℚ)⟩
def r_1_0_interval : RatInterval := ⟨(0 : ℚ), (0 : ℚ)⟩
def r_1_1_interval : RatInterval := ⟨(76854424367 / 250000000000 : ℚ), (9606803047 / 31250000000 : ℚ)⟩
def r_1_2_interval : RatInterval := ⟨(153455886119 / 1000000000000 : ℚ), (30691177229 / 200000000000 : ℚ)⟩
def r_1_3_interval : RatInterval := ⟨(80206373499 / 500000000000 : ℚ), (10025796689 / 62500000000 : ℚ)⟩
def r_2_0_interval : RatInterval := ⟨(0 : ℚ), (0 : ℚ)⟩
def r_2_1_interval : RatInterval := ⟨(0 : ℚ), (0 : ℚ)⟩
def r_2_2_interval : RatInterval := ⟨(229497538091 / 1000000000000 : ℚ), (114748769131 / 500000000000 : ℚ)⟩
def r_2_3_interval : RatInterval := ⟨(59351581579 / 500000000000 : ℚ), (29675790827 / 250000000000 : ℚ)⟩
def r_3_0_interval : RatInterval := ⟨(0 : ℚ), (0 : ℚ)⟩
def r_3_1_interval : RatInterval := ⟨(0 : ℚ), (0 : ℚ)⟩
def r_3_2_interval : RatInterval := ⟨(0 : ℚ), (0 : ℚ)⟩
def r_3_3_interval : RatInterval := ⟨(77405853731 / 500000000000 : ℚ), (30962342037 / 200000000000 : ℚ)⟩
def vectorExpr_0_0 (v : ℕ → QHilbert) : ℝ := (1 : ℝ)
def vectorRawInterval_0_0 : RatInterval := (RatInterval.point (1 : ℚ))
def vectorInterval_0_0 : RatInterval := ⟨(1 : ℚ), (1 : ℚ)⟩
def vectorExpr_0_1 (v : ℕ → QHilbert) : ℝ := ((forward v 4 0 1) / ((forward v 4 1 1) - (forward v 4 0 0)))
def vectorRawInterval_0_1 : RatInterval := (RatInterval.div a_0_1_interval (RatInterval.sub a_1_1_interval a_0_0_interval))
def vectorInterval_0_1 : RatInterval := ⟨(-2154854608507 / 1000000000000 : ℚ), (-1077427304059 / 500000000000 : ℚ)⟩
def vectorExpr_0_2 (v : ℕ → QHilbert) : ℝ := ((((forward v 4 0 1) * ((forward v 4 1 2) / ((forward v 4 2 2) - (forward v 4 1 1)))) + (forward v 4 0 2)) / ((forward v 4 2 2) - (forward v 4 0 0)))
def vectorRawInterval_0_2 : RatInterval := (RatInterval.div (RatInterval.add (RatInterval.mul a_0_1_interval (RatInterval.div a_1_2_interval (RatInterval.sub a_2_2_interval a_1_1_interval))) a_0_2_interval) (RatInterval.sub a_2_2_interval a_0_0_interval))
def vectorInterval_0_2 : RatInterval := ⟨(1573638344349 / 1000000000000 : ℚ), (1573638347151 / 1000000000000 : ℚ)⟩
def vectorExpr_0_3 (v : ℕ → QHilbert) : ℝ := (((((forward v 4 0 1) * ((((forward v 4 1 2) * ((forward v 4 2 3) / ((forward v 4 3 3) - (forward v 4 2 2)))) + (forward v 4 1 3)) / ((forward v 4 3 3) - (forward v 4 1 1)))) + ((forward v 4 0 2) * ((forward v 4 2 3) / ((forward v 4 3 3) - (forward v 4 2 2))))) + (forward v 4 0 3)) / ((forward v 4 3 3) - (forward v 4 0 0)))
def vectorRawInterval_0_3 : RatInterval := (RatInterval.div (RatInterval.add (RatInterval.add (RatInterval.mul a_0_1_interval (RatInterval.div (RatInterval.add (RatInterval.mul a_1_2_interval (RatInterval.div a_2_3_interval (RatInterval.sub a_3_3_interval a_2_2_interval))) a_1_3_interval) (RatInterval.sub a_3_3_interval a_1_1_interval))) (RatInterval.mul a_0_2_interval (RatInterval.div a_2_3_interval (RatInterval.sub a_3_3_interval a_2_2_interval)))) a_0_3_interval) (RatInterval.sub a_3_3_interval a_0_0_interval))
def vectorInterval_0_3 : RatInterval := ⟨(-25933905621 / 500000000000 : ℚ), (-12966950327 / 250000000000 : ℚ)⟩
def vectorExpr_1_0 (v : ℕ → QHilbert) : ℝ := (0 : ℝ)
def vectorRawInterval_1_0 : RatInterval := (RatInterval.point (0 : ℚ))
def vectorInterval_1_0 : RatInterval := ⟨(0 : ℚ), (0 : ℚ)⟩
def vectorExpr_1_1 (v : ℕ → QHilbert) : ℝ := (1 : ℝ)
def vectorRawInterval_1_1 : RatInterval := (RatInterval.point (1 : ℚ))
def vectorInterval_1_1 : RatInterval := ⟨(1 : ℚ), (1 : ℚ)⟩
def vectorExpr_1_2 (v : ℕ → QHilbert) : ℝ := ((forward v 4 1 2) / ((forward v 4 2 2) - (forward v 4 1 1)))
def vectorRawInterval_1_2 : RatInterval := (RatInterval.div a_1_2_interval (RatInterval.sub a_2_2_interval a_1_1_interval))
def vectorInterval_1_2 : RatInterval := ⟨(-1969399030647 / 1000000000000 : ℚ), (-123087439289 / 62500000000 : ℚ)⟩
def vectorExpr_1_3 (v : ℕ → QHilbert) : ℝ := ((((forward v 4 1 2) * ((forward v 4 2 3) / ((forward v 4 3 3) - (forward v 4 2 2)))) + (forward v 4 1 3)) / ((forward v 4 3 3) - (forward v 4 1 1)))
def vectorRawInterval_1_3 : RatInterval := (RatInterval.div (RatInterval.add (RatInterval.mul a_1_2_interval (RatInterval.div a_2_3_interval (RatInterval.sub a_3_3_interval a_2_2_interval))) a_1_3_interval) (RatInterval.sub a_3_3_interval a_1_1_interval))
def vectorInterval_1_3 : RatInterval := ⟨(547061841071 / 1000000000000 : ℚ), (547061854527 / 1000000000000 : ℚ)⟩
def vectorExpr_2_0 (v : ℕ → QHilbert) : ℝ := (0 : ℝ)
def vectorRawInterval_2_0 : RatInterval := (RatInterval.point (0 : ℚ))
def vectorInterval_2_0 : RatInterval := ⟨(0 : ℚ), (0 : ℚ)⟩
def vectorExpr_2_1 (v : ℕ → QHilbert) : ℝ := (0 : ℝ)
def vectorRawInterval_2_1 : RatInterval := (RatInterval.point (0 : ℚ))
def vectorInterval_2_1 : RatInterval := ⟨(0 : ℚ), (0 : ℚ)⟩
def vectorExpr_2_2 (v : ℕ → QHilbert) : ℝ := (1 : ℝ)
def vectorRawInterval_2_2 : RatInterval := (RatInterval.point (1 : ℚ))
def vectorInterval_2_2 : RatInterval := ⟨(1 : ℚ), (1 : ℚ)⟩
def vectorExpr_2_3 (v : ℕ → QHilbert) : ℝ := ((forward v 4 2 3) / ((forward v 4 3 3) - (forward v 4 2 2)))
def vectorRawInterval_2_3 : RatInterval := (RatInterval.div a_2_3_interval (RatInterval.sub a_3_3_interval a_2_2_interval))
def vectorInterval_2_3 : RatInterval := ⟨(-794683307331 / 500000000000 : ℚ), (-317873320097 / 200000000000 : ℚ)⟩
def vectorExpr_3_0 (v : ℕ → QHilbert) : ℝ := (0 : ℝ)
def vectorRawInterval_3_0 : RatInterval := (RatInterval.point (0 : ℚ))
def vectorInterval_3_0 : RatInterval := ⟨(0 : ℚ), (0 : ℚ)⟩
def vectorExpr_3_1 (v : ℕ → QHilbert) : ℝ := (0 : ℝ)
def vectorRawInterval_3_1 : RatInterval := (RatInterval.point (0 : ℚ))
def vectorInterval_3_1 : RatInterval := ⟨(0 : ℚ), (0 : ℚ)⟩
def vectorExpr_3_2 (v : ℕ → QHilbert) : ℝ := (0 : ℝ)
def vectorRawInterval_3_2 : RatInterval := (RatInterval.point (0 : ℚ))
def vectorInterval_3_2 : RatInterval := ⟨(0 : ℚ), (0 : ℚ)⟩
def vectorExpr_3_3 (v : ℕ → QHilbert) : ℝ := (1 : ℝ)
def vectorRawInterval_3_3 : RatInterval := (RatInterval.point (1 : ℚ))
def vectorInterval_3_3 : RatInterval := ⟨(1 : ℚ), (1 : ℚ)⟩
def explicitEigenvector (v : ℕ → QHilbert) (j : Fin 4) (i : Fin 4) : ℝ :=
  (!![vectorExpr_0_0 v, vectorExpr_0_1 v, vectorExpr_0_2 v, vectorExpr_0_3 v; vectorExpr_1_0 v, vectorExpr_1_1 v, vectorExpr_1_2 v, vectorExpr_1_3 v; vectorExpr_2_0 v, vectorExpr_2_1 v, vectorExpr_2_2 v, vectorExpr_2_3 v; vectorExpr_3_0 v, vectorExpr_3_1 v, vectorExpr_3_2 v, vectorExpr_3_3 v]) i j
def displayedA : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(11547005383792517 / 5000000000000000 : ℚ), (-508277453725063 / 250000000000000 : ℚ), (-1562562139092541 / 2000000000000000 : ℚ), (-3447596695168509 / 10000000000000000 : ℚ); (0 : ℚ), (16264515806674231 / 5000000000000000 : ℚ), (-1087543555108087 / 500000000000000 : ℚ), (-8514130280792217 / 5000000000000000 : ℚ); (0 : ℚ), (0 : ℚ), (1089336303931479 / 250000000000000 : ℚ), (-1670515312899323 / 500000000000000 : ℚ); (0 : ℚ), (0 : ℚ), (0 : ℚ), (1614864934325203 / 250000000000000 : ℚ)]
def displayedR : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(10825317547305481 / 25000000000000000 : ℚ), (2706389740272153 / 10000000000000000 : ℚ), (1329605420412751 / 6250000000000000 : ℚ), (10224514551357433 / 50000000000000000 : ℚ); (0 : ℚ), (3074176974852349 / 10000000000000000 : ℚ), (7672794306487757 / 50000000000000000 : ℚ), (8020637350575527 / 50000000000000000 : ℚ); (0 : ℚ), (0 : ℚ), (2294975381778201 / 10000000000000000 : ℚ), (11870316323356991 / 100000000000000000 : ℚ); (0 : ℚ), (0 : ℚ), (0 : ℚ), (15481170882224057 / 100000000000000000 : ℚ)]
def displayedEigenvectors : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(1 : ℚ), (-1077427304155439 / 500000000000000 : ℚ), (15736383457722583 / 10000000000000000 : ℚ), (-6483475778995257 / 125000000000000000 : ℚ); (0 : ℚ), (1 : ℚ), (-9846995148221701 / 5000000000000000 : ℚ), (2735309238639201 / 5000000000000000 : ℚ); (0 : ℚ), (0 : ℚ), (1 : ℚ), (-3178733215063429 / 2000000000000000 : ℚ); (0 : ℚ), (0 : ℚ), (0 : ℚ), (1 : ℚ)]

variable {v : ℕ → QHilbert} (hv : LinearIndependent ℝ v)
  (h0 : v 0 = qResidue 2) (h1 : v 1 = qResidue 3)
  (h2 : v 2 = qResidue 5) (h3 : v 3 = qResidue 6)
include hv h0 h1 h2 h3

theorem g_0_0_bounds : gram_2_2_interval.Contains (g v 0 0) := by
  simpa only [g, h0, h1, h2, h3] using gram_2_2_bounds

theorem g_0_1_bounds : gram_2_3_interval.Contains (g v 0 1) := by
  simpa only [g, h0, h1, h2, h3] using gram_2_3_bounds

theorem g_0_2_bounds : gram_2_5_interval.Contains (g v 0 2) := by
  simpa only [g, h0, h1, h2, h3] using gram_2_5_bounds

theorem g_0_3_bounds : gram_2_6_interval.Contains (g v 0 3) := by
  simpa only [g, h0, h1, h2, h3] using gram_2_6_bounds

theorem g_1_0_bounds : gram_2_3_interval.Contains (g v 1 0) := by
  simpa only [g, h0, h1, h2, h3, real_inner_comm] using gram_2_3_bounds

theorem g_1_1_bounds : gram_3_3_interval.Contains (g v 1 1) := by
  simpa only [g, h0, h1, h2, h3] using gram_3_3_bounds

theorem g_1_2_bounds : gram_3_5_interval.Contains (g v 1 2) := by
  simpa only [g, h0, h1, h2, h3] using gram_3_5_bounds

theorem g_1_3_bounds : gram_3_6_interval.Contains (g v 1 3) := by
  simpa only [g, h0, h1, h2, h3] using gram_3_6_bounds

theorem g_2_0_bounds : gram_2_5_interval.Contains (g v 2 0) := by
  simpa only [g, h0, h1, h2, h3, real_inner_comm] using gram_2_5_bounds

theorem g_2_1_bounds : gram_3_5_interval.Contains (g v 2 1) := by
  simpa only [g, h0, h1, h2, h3, real_inner_comm] using gram_3_5_bounds

theorem g_2_2_bounds : gram_5_5_interval.Contains (g v 2 2) := by
  simpa only [g, h0, h1, h2, h3] using gram_5_5_bounds

theorem g_2_3_bounds : gram_5_6_interval.Contains (g v 2 3) := by
  simpa only [g, h0, h1, h2, h3] using gram_5_6_bounds

theorem g_3_0_bounds : gram_2_6_interval.Contains (g v 3 0) := by
  simpa only [g, h0, h1, h2, h3, real_inner_comm] using gram_2_6_bounds

theorem g_3_1_bounds : gram_3_6_interval.Contains (g v 3 1) := by
  simpa only [g, h0, h1, h2, h3, real_inner_comm] using gram_3_6_bounds

theorem g_3_2_bounds : gram_5_6_interval.Contains (g v 3 2) := by
  simpa only [g, h0, h1, h2, h3, real_inner_comm] using gram_5_6_bounds

theorem g_3_3_bounds : gram_6_6_interval.Contains (g v 3 3) := by
  simpa only [g, h0, h1, h2, h3] using gram_6_6_bounds

theorem det_0_bounds : detInterval_0.Contains ((gram v 0).det) := by
  rw [det_formula_0]
  have h : detRawInterval_0.Contains (detExpr_0 v) := by
    simpa [detRawInterval_0, detExpr_0] using (contains_point (1 : ℚ))
  exact contains_weaken h
    (by norm_num [detRawInterval_0, detInterval_0, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])
    (by norm_num [detRawInterval_0, detInterval_0, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])

theorem det_1_bounds : detInterval_1.Contains ((gram v 1).det) := by
  rw [det_formula_1]
  have h : detRawInterval_1.Contains (detExpr_1 v) := by
    simpa [detRawInterval_1, detExpr_1] using (g_0_0_bounds hv h0 h1 h2 h3)
  exact contains_weaken h
    (by norm_num [detRawInterval_1, detInterval_1, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, gram_2_2_interval])
    (by norm_num [detRawInterval_1, detInterval_1, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, gram_2_2_interval])

theorem det_2_bounds : detInterval_2.Contains ((gram v 2).det) := by
  rw [det_formula_2]
  have h : detRawInterval_2.Contains (detExpr_2 v) := by
    simpa [detRawInterval_2, detExpr_2] using (contains_sub (contains_mul (g_0_0_bounds hv h0 h1 h2 h3) (g_1_1_bounds hv h0 h1 h2 h3)) (contains_mul (g_0_1_bounds hv h0 h1 h2 h3) (g_1_0_bounds hv h0 h1 h2 h3)))
  exact contains_weaken h
    (by norm_num [detRawInterval_2, detInterval_2, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, gram_2_2_interval, gram_2_3_interval, gram_3_3_interval])
    (by norm_num [detRawInterval_2, detInterval_2, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, gram_2_2_interval, gram_2_3_interval, gram_3_3_interval])

theorem det_3_bounds : detInterval_3.Contains ((gram v 3).det) := by
  rw [det_formula_3]
  have h : detRawInterval_3.Contains (detExpr_3 v) := by
    simpa [detRawInterval_3, detExpr_3] using (contains_add (contains_sub (contains_mul (g_0_0_bounds hv h0 h1 h2 h3) (contains_sub (contains_mul (g_1_1_bounds hv h0 h1 h2 h3) (g_2_2_bounds hv h0 h1 h2 h3)) (contains_mul (g_1_2_bounds hv h0 h1 h2 h3) (g_2_1_bounds hv h0 h1 h2 h3)))) (contains_mul (g_0_1_bounds hv h0 h1 h2 h3) (contains_sub (contains_mul (g_1_0_bounds hv h0 h1 h2 h3) (g_2_2_bounds hv h0 h1 h2 h3)) (contains_mul (g_1_2_bounds hv h0 h1 h2 h3) (g_2_0_bounds hv h0 h1 h2 h3))))) (contains_mul (g_0_2_bounds hv h0 h1 h2 h3) (contains_sub (contains_mul (g_1_0_bounds hv h0 h1 h2 h3) (g_2_1_bounds hv h0 h1 h2 h3)) (contains_mul (g_1_1_bounds hv h0 h1 h2 h3) (g_2_0_bounds hv h0 h1 h2 h3)))))
  exact contains_weaken h
    (by norm_num [detRawInterval_3, detInterval_3, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, gram_2_2_interval, gram_2_3_interval, gram_2_5_interval, gram_3_3_interval, gram_3_5_interval, gram_5_5_interval])
    (by norm_num [detRawInterval_3, detInterval_3, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, gram_2_2_interval, gram_2_3_interval, gram_2_5_interval, gram_3_3_interval, gram_3_5_interval, gram_5_5_interval])

theorem det_4_bounds : detInterval_4.Contains ((gram v 4).det) := by
  rw [det_formula_4]
  have h : detRawInterval_4.Contains (detExpr_4 v) := by
    simpa [detRawInterval_4, detExpr_4] using (contains_sub (contains_add (contains_sub (contains_mul (g_0_0_bounds hv h0 h1 h2 h3) (contains_add (contains_sub (contains_mul (g_1_1_bounds hv h0 h1 h2 h3) (contains_sub (contains_mul (g_2_2_bounds hv h0 h1 h2 h3) (g_3_3_bounds hv h0 h1 h2 h3)) (contains_mul (g_2_3_bounds hv h0 h1 h2 h3) (g_3_2_bounds hv h0 h1 h2 h3)))) (contains_mul (g_1_2_bounds hv h0 h1 h2 h3) (contains_sub (contains_mul (g_2_1_bounds hv h0 h1 h2 h3) (g_3_3_bounds hv h0 h1 h2 h3)) (contains_mul (g_2_3_bounds hv h0 h1 h2 h3) (g_3_1_bounds hv h0 h1 h2 h3))))) (contains_mul (g_1_3_bounds hv h0 h1 h2 h3) (contains_sub (contains_mul (g_2_1_bounds hv h0 h1 h2 h3) (g_3_2_bounds hv h0 h1 h2 h3)) (contains_mul (g_2_2_bounds hv h0 h1 h2 h3) (g_3_1_bounds hv h0 h1 h2 h3)))))) (contains_mul (g_0_1_bounds hv h0 h1 h2 h3) (contains_add (contains_sub (contains_mul (g_1_0_bounds hv h0 h1 h2 h3) (contains_sub (contains_mul (g_2_2_bounds hv h0 h1 h2 h3) (g_3_3_bounds hv h0 h1 h2 h3)) (contains_mul (g_2_3_bounds hv h0 h1 h2 h3) (g_3_2_bounds hv h0 h1 h2 h3)))) (contains_mul (g_1_2_bounds hv h0 h1 h2 h3) (contains_sub (contains_mul (g_2_0_bounds hv h0 h1 h2 h3) (g_3_3_bounds hv h0 h1 h2 h3)) (contains_mul (g_2_3_bounds hv h0 h1 h2 h3) (g_3_0_bounds hv h0 h1 h2 h3))))) (contains_mul (g_1_3_bounds hv h0 h1 h2 h3) (contains_sub (contains_mul (g_2_0_bounds hv h0 h1 h2 h3) (g_3_2_bounds hv h0 h1 h2 h3)) (contains_mul (g_2_2_bounds hv h0 h1 h2 h3) (g_3_0_bounds hv h0 h1 h2 h3))))))) (contains_mul (g_0_2_bounds hv h0 h1 h2 h3) (contains_add (contains_sub (contains_mul (g_1_0_bounds hv h0 h1 h2 h3) (contains_sub (contains_mul (g_2_1_bounds hv h0 h1 h2 h3) (g_3_3_bounds hv h0 h1 h2 h3)) (contains_mul (g_2_3_bounds hv h0 h1 h2 h3) (g_3_1_bounds hv h0 h1 h2 h3)))) (contains_mul (g_1_1_bounds hv h0 h1 h2 h3) (contains_sub (contains_mul (g_2_0_bounds hv h0 h1 h2 h3) (g_3_3_bounds hv h0 h1 h2 h3)) (contains_mul (g_2_3_bounds hv h0 h1 h2 h3) (g_3_0_bounds hv h0 h1 h2 h3))))) (contains_mul (g_1_3_bounds hv h0 h1 h2 h3) (contains_sub (contains_mul (g_2_0_bounds hv h0 h1 h2 h3) (g_3_1_bounds hv h0 h1 h2 h3)) (contains_mul (g_2_1_bounds hv h0 h1 h2 h3) (g_3_0_bounds hv h0 h1 h2 h3))))))) (contains_mul (g_0_3_bounds hv h0 h1 h2 h3) (contains_add (contains_sub (contains_mul (g_1_0_bounds hv h0 h1 h2 h3) (contains_sub (contains_mul (g_2_1_bounds hv h0 h1 h2 h3) (g_3_2_bounds hv h0 h1 h2 h3)) (contains_mul (g_2_2_bounds hv h0 h1 h2 h3) (g_3_1_bounds hv h0 h1 h2 h3)))) (contains_mul (g_1_1_bounds hv h0 h1 h2 h3) (contains_sub (contains_mul (g_2_0_bounds hv h0 h1 h2 h3) (g_3_2_bounds hv h0 h1 h2 h3)) (contains_mul (g_2_2_bounds hv h0 h1 h2 h3) (g_3_0_bounds hv h0 h1 h2 h3))))) (contains_mul (g_1_2_bounds hv h0 h1 h2 h3) (contains_sub (contains_mul (g_2_0_bounds hv h0 h1 h2 h3) (g_3_1_bounds hv h0 h1 h2 h3)) (contains_mul (g_2_1_bounds hv h0 h1 h2 h3) (g_3_0_bounds hv h0 h1 h2 h3)))))))
  exact contains_weaken h
    (by norm_num [detRawInterval_4, detInterval_4, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, gram_2_2_interval, gram_2_3_interval, gram_2_5_interval, gram_2_6_interval, gram_3_3_interval, gram_3_5_interval, gram_3_6_interval, gram_5_5_interval, gram_5_6_interval, gram_6_6_interval])
    (by norm_num [detRawInterval_4, detInterval_4, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, gram_2_2_interval, gram_2_3_interval, gram_2_5_interval, gram_2_6_interval, gram_3_3_interval, gram_3_5_interval, gram_3_6_interval, gram_5_5_interval, gram_5_6_interval, gram_6_6_interval])

theorem cofactor_0_0_bounds :
    cofactorInterval_0_0.Contains (cofactorExpr_0_0 v) := by
  have h : cofactorRawInterval_0_0.Contains (cofactorExpr_0_0 v) := by
    simpa [cofactorRawInterval_0_0, cofactorExpr_0_0] using (contains_point (1 : ℚ))
  exact contains_weaken h
    (by norm_num [cofactorRawInterval_0_0, cofactorInterval_0_0, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])
    (by norm_num [cofactorRawInterval_0_0, cofactorInterval_0_0, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])

theorem cofactor_0_1_bounds :
    cofactorInterval_0_1.Contains (cofactorExpr_0_1 v) := by
  have h : cofactorRawInterval_0_1.Contains (cofactorExpr_0_1 v) := by
    simpa [cofactorRawInterval_0_1, cofactorExpr_0_1] using (contains_neg (g_0_1_bounds hv h0 h1 h2 h3))
  exact contains_weaken h
    (by norm_num [cofactorRawInterval_0_1, cofactorInterval_0_1, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, gram_2_3_interval])
    (by norm_num [cofactorRawInterval_0_1, cofactorInterval_0_1, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, gram_2_3_interval])

theorem cofactor_1_1_bounds :
    cofactorInterval_1_1.Contains (cofactorExpr_1_1 v) := by
  have h : cofactorRawInterval_1_1.Contains (cofactorExpr_1_1 v) := by
    simpa [cofactorRawInterval_1_1, cofactorExpr_1_1] using (g_0_0_bounds hv h0 h1 h2 h3)
  exact contains_weaken h
    (by norm_num [cofactorRawInterval_1_1, cofactorInterval_1_1, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, gram_2_2_interval])
    (by norm_num [cofactorRawInterval_1_1, cofactorInterval_1_1, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, gram_2_2_interval])

theorem cofactor_0_2_bounds :
    cofactorInterval_0_2.Contains (cofactorExpr_0_2 v) := by
  have h : cofactorRawInterval_0_2.Contains (cofactorExpr_0_2 v) := by
    simpa [cofactorRawInterval_0_2, cofactorExpr_0_2] using (contains_sub (contains_mul (g_0_1_bounds hv h0 h1 h2 h3) (g_1_2_bounds hv h0 h1 h2 h3)) (contains_mul (g_0_2_bounds hv h0 h1 h2 h3) (g_1_1_bounds hv h0 h1 h2 h3)))
  exact contains_weaken h
    (by norm_num [cofactorRawInterval_0_2, cofactorInterval_0_2, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, gram_2_3_interval, gram_2_5_interval, gram_3_3_interval, gram_3_5_interval])
    (by norm_num [cofactorRawInterval_0_2, cofactorInterval_0_2, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, gram_2_3_interval, gram_2_5_interval, gram_3_3_interval, gram_3_5_interval])

theorem cofactor_1_2_bounds :
    cofactorInterval_1_2.Contains (cofactorExpr_1_2 v) := by
  have h : cofactorRawInterval_1_2.Contains (cofactorExpr_1_2 v) := by
    simpa [cofactorRawInterval_1_2, cofactorExpr_1_2] using (contains_neg (contains_sub (contains_mul (g_0_0_bounds hv h0 h1 h2 h3) (g_1_2_bounds hv h0 h1 h2 h3)) (contains_mul (g_0_2_bounds hv h0 h1 h2 h3) (g_1_0_bounds hv h0 h1 h2 h3))))
  exact contains_weaken h
    (by norm_num [cofactorRawInterval_1_2, cofactorInterval_1_2, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, gram_2_2_interval, gram_2_3_interval, gram_2_5_interval, gram_3_5_interval])
    (by norm_num [cofactorRawInterval_1_2, cofactorInterval_1_2, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, gram_2_2_interval, gram_2_3_interval, gram_2_5_interval, gram_3_5_interval])

theorem cofactor_2_2_bounds :
    cofactorInterval_2_2.Contains (cofactorExpr_2_2 v) := by
  have h : cofactorRawInterval_2_2.Contains (cofactorExpr_2_2 v) := by
    simpa [cofactorRawInterval_2_2, cofactorExpr_2_2] using (contains_sub (contains_mul (g_0_0_bounds hv h0 h1 h2 h3) (g_1_1_bounds hv h0 h1 h2 h3)) (contains_mul (g_0_1_bounds hv h0 h1 h2 h3) (g_1_0_bounds hv h0 h1 h2 h3)))
  exact contains_weaken h
    (by norm_num [cofactorRawInterval_2_2, cofactorInterval_2_2, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, gram_2_2_interval, gram_2_3_interval, gram_3_3_interval])
    (by norm_num [cofactorRawInterval_2_2, cofactorInterval_2_2, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, gram_2_2_interval, gram_2_3_interval, gram_3_3_interval])

theorem cofactor_0_3_bounds :
    cofactorInterval_0_3.Contains (cofactorExpr_0_3 v) := by
  have h : cofactorRawInterval_0_3.Contains (cofactorExpr_0_3 v) := by
    simpa [cofactorRawInterval_0_3, cofactorExpr_0_3] using (contains_neg (contains_add (contains_sub (contains_mul (g_0_1_bounds hv h0 h1 h2 h3) (contains_sub (contains_mul (g_1_2_bounds hv h0 h1 h2 h3) (g_2_3_bounds hv h0 h1 h2 h3)) (contains_mul (g_1_3_bounds hv h0 h1 h2 h3) (g_2_2_bounds hv h0 h1 h2 h3)))) (contains_mul (g_0_2_bounds hv h0 h1 h2 h3) (contains_sub (contains_mul (g_1_1_bounds hv h0 h1 h2 h3) (g_2_3_bounds hv h0 h1 h2 h3)) (contains_mul (g_1_3_bounds hv h0 h1 h2 h3) (g_2_1_bounds hv h0 h1 h2 h3))))) (contains_mul (g_0_3_bounds hv h0 h1 h2 h3) (contains_sub (contains_mul (g_1_1_bounds hv h0 h1 h2 h3) (g_2_2_bounds hv h0 h1 h2 h3)) (contains_mul (g_1_2_bounds hv h0 h1 h2 h3) (g_2_1_bounds hv h0 h1 h2 h3))))))
  exact contains_weaken h
    (by norm_num [cofactorRawInterval_0_3, cofactorInterval_0_3, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, gram_2_3_interval, gram_2_5_interval, gram_2_6_interval, gram_3_3_interval, gram_3_5_interval, gram_3_6_interval, gram_5_5_interval, gram_5_6_interval])
    (by norm_num [cofactorRawInterval_0_3, cofactorInterval_0_3, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, gram_2_3_interval, gram_2_5_interval, gram_2_6_interval, gram_3_3_interval, gram_3_5_interval, gram_3_6_interval, gram_5_5_interval, gram_5_6_interval])

theorem cofactor_1_3_bounds :
    cofactorInterval_1_3.Contains (cofactorExpr_1_3 v) := by
  have h : cofactorRawInterval_1_3.Contains (cofactorExpr_1_3 v) := by
    simpa [cofactorRawInterval_1_3, cofactorExpr_1_3] using (contains_add (contains_sub (contains_mul (g_0_0_bounds hv h0 h1 h2 h3) (contains_sub (contains_mul (g_1_2_bounds hv h0 h1 h2 h3) (g_2_3_bounds hv h0 h1 h2 h3)) (contains_mul (g_1_3_bounds hv h0 h1 h2 h3) (g_2_2_bounds hv h0 h1 h2 h3)))) (contains_mul (g_0_2_bounds hv h0 h1 h2 h3) (contains_sub (contains_mul (g_1_0_bounds hv h0 h1 h2 h3) (g_2_3_bounds hv h0 h1 h2 h3)) (contains_mul (g_1_3_bounds hv h0 h1 h2 h3) (g_2_0_bounds hv h0 h1 h2 h3))))) (contains_mul (g_0_3_bounds hv h0 h1 h2 h3) (contains_sub (contains_mul (g_1_0_bounds hv h0 h1 h2 h3) (g_2_2_bounds hv h0 h1 h2 h3)) (contains_mul (g_1_2_bounds hv h0 h1 h2 h3) (g_2_0_bounds hv h0 h1 h2 h3)))))
  exact contains_weaken h
    (by norm_num [cofactorRawInterval_1_3, cofactorInterval_1_3, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, gram_2_2_interval, gram_2_3_interval, gram_2_5_interval, gram_2_6_interval, gram_3_5_interval, gram_3_6_interval, gram_5_5_interval, gram_5_6_interval])
    (by norm_num [cofactorRawInterval_1_3, cofactorInterval_1_3, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, gram_2_2_interval, gram_2_3_interval, gram_2_5_interval, gram_2_6_interval, gram_3_5_interval, gram_3_6_interval, gram_5_5_interval, gram_5_6_interval])

theorem cofactor_2_3_bounds :
    cofactorInterval_2_3.Contains (cofactorExpr_2_3 v) := by
  have h : cofactorRawInterval_2_3.Contains (cofactorExpr_2_3 v) := by
    simpa [cofactorRawInterval_2_3, cofactorExpr_2_3] using (contains_neg (contains_add (contains_sub (contains_mul (g_0_0_bounds hv h0 h1 h2 h3) (contains_sub (contains_mul (g_1_1_bounds hv h0 h1 h2 h3) (g_2_3_bounds hv h0 h1 h2 h3)) (contains_mul (g_1_3_bounds hv h0 h1 h2 h3) (g_2_1_bounds hv h0 h1 h2 h3)))) (contains_mul (g_0_1_bounds hv h0 h1 h2 h3) (contains_sub (contains_mul (g_1_0_bounds hv h0 h1 h2 h3) (g_2_3_bounds hv h0 h1 h2 h3)) (contains_mul (g_1_3_bounds hv h0 h1 h2 h3) (g_2_0_bounds hv h0 h1 h2 h3))))) (contains_mul (g_0_3_bounds hv h0 h1 h2 h3) (contains_sub (contains_mul (g_1_0_bounds hv h0 h1 h2 h3) (g_2_1_bounds hv h0 h1 h2 h3)) (contains_mul (g_1_1_bounds hv h0 h1 h2 h3) (g_2_0_bounds hv h0 h1 h2 h3))))))
  exact contains_weaken h
    (by norm_num [cofactorRawInterval_2_3, cofactorInterval_2_3, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, gram_2_2_interval, gram_2_3_interval, gram_2_5_interval, gram_2_6_interval, gram_3_3_interval, gram_3_5_interval, gram_3_6_interval, gram_5_6_interval])
    (by norm_num [cofactorRawInterval_2_3, cofactorInterval_2_3, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, gram_2_2_interval, gram_2_3_interval, gram_2_5_interval, gram_2_6_interval, gram_3_3_interval, gram_3_5_interval, gram_3_6_interval, gram_5_6_interval])

theorem cofactor_3_3_bounds :
    cofactorInterval_3_3.Contains (cofactorExpr_3_3 v) := by
  have h : cofactorRawInterval_3_3.Contains (cofactorExpr_3_3 v) := by
    simpa [cofactorRawInterval_3_3, cofactorExpr_3_3] using (contains_add (contains_sub (contains_mul (g_0_0_bounds hv h0 h1 h2 h3) (contains_sub (contains_mul (g_1_1_bounds hv h0 h1 h2 h3) (g_2_2_bounds hv h0 h1 h2 h3)) (contains_mul (g_1_2_bounds hv h0 h1 h2 h3) (g_2_1_bounds hv h0 h1 h2 h3)))) (contains_mul (g_0_1_bounds hv h0 h1 h2 h3) (contains_sub (contains_mul (g_1_0_bounds hv h0 h1 h2 h3) (g_2_2_bounds hv h0 h1 h2 h3)) (contains_mul (g_1_2_bounds hv h0 h1 h2 h3) (g_2_0_bounds hv h0 h1 h2 h3))))) (contains_mul (g_0_2_bounds hv h0 h1 h2 h3) (contains_sub (contains_mul (g_1_0_bounds hv h0 h1 h2 h3) (g_2_1_bounds hv h0 h1 h2 h3)) (contains_mul (g_1_1_bounds hv h0 h1 h2 h3) (g_2_0_bounds hv h0 h1 h2 h3)))))
  exact contains_weaken h
    (by norm_num [cofactorRawInterval_3_3, cofactorInterval_3_3, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, gram_2_2_interval, gram_2_3_interval, gram_2_5_interval, gram_3_3_interval, gram_3_5_interval, gram_5_5_interval])
    (by norm_num [cofactorRawInterval_3_3, cofactorInterval_3_3, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, gram_2_2_interval, gram_2_3_interval, gram_2_5_interval, gram_3_3_interval, gram_3_5_interval, gram_5_5_interval])

theorem denominator_0_bounds : denominatorInterval_0.Contains
    (Real.sqrt ((gram v 0).det * (gram v 1).det)) := by
  exact contains_sqrt (contains_mul (det_0_bounds hv h0 h1 h2 h3) (det_1_bounds hv h0 h1 h2 h3))
    (216506350945532311 / 500000000000000000 : ℚ) (54126587736671753 / 125000000000000000 : ℚ)
    (by norm_num)
    (by norm_num [RatInterval.mul, detInterval_0, detInterval_1])
    (by norm_num [RatInterval.mul, detInterval_0, detInterval_1])

theorem denominator_1_bounds : denominatorInterval_1.Contains
    (Real.sqrt ((gram v 1).det * (gram v 2).det)) := by
  exact contains_sqrt (contains_mul (det_1_bounds hv h0 h1 h2 h3) (det_2_bounds hv h0 h1 h2 h3))
    (14410204569452849 / 250000000000000000 : ℚ) (57640818279350663 / 1000000000000000000 : ℚ)
    (by norm_num)
    (by norm_num [RatInterval.mul, detInterval_1, detInterval_2])
    (by norm_num [RatInterval.mul, detInterval_1, detInterval_2])

theorem denominator_2_bounds : denominatorInterval_2.Contains
    (Real.sqrt ((gram v 2).det * (gram v 3).det)) := by
  exact contains_sqrt (contains_mul (det_2_bounds hv h0 h1 h2 h3) (det_3_bounds hv h0 h1 h2 h3))
    (2033326114621209 / 500000000000000000 : ℚ) (4066652229798849 / 1000000000000000000 : ℚ)
    (by norm_num)
    (by norm_num [RatInterval.mul, detInterval_2, detInterval_3])
    (by norm_num [RatInterval.mul, detInterval_2, detInterval_3])

theorem denominator_3_bounds : denominatorInterval_3.Contains
    (Real.sqrt ((gram v 3).det * (gram v 4).det)) := by
  exact contains_sqrt (contains_mul (det_3_bounds hv h0 h1 h2 h3) (det_4_bounds hv h0 h1 h2 h3))
    (144483704893073 / 1000000000000000000 : ℚ) (144483705156779 / 1000000000000000000 : ℚ)
    (by norm_num)
    (by norm_num [RatInterval.mul, detInterval_3, detInterval_4])
    (by norm_num [RatInterval.mul, detInterval_3, detInterval_4])

theorem a_0_0_bounds : a_0_0_interval.Contains (forward v 4 0 0) := by
  rw [forward_formula_0_0 hv]
  exact contains_weaken
    (contains_div_pos (cofactor_0_0_bounds hv h0 h1 h2 h3) (denominator_0_bounds hv h0 h1 h2 h3)
      (by norm_num [denominatorInterval_0]))
    (by norm_num [a_0_0_interval, cofactorInterval_0_0, denominatorInterval_0, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])
    (by norm_num [a_0_0_interval, cofactorInterval_0_0, denominatorInterval_0, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])

theorem a_0_1_bounds : a_0_1_interval.Contains (forward v 4 0 1) := by
  rw [forward_formula_0_1 hv]
  exact contains_weaken
    (contains_div_pos (cofactor_0_1_bounds hv h0 h1 h2 h3) (denominator_1_bounds hv h0 h1 h2 h3)
      (by norm_num [denominatorInterval_1]))
    (by norm_num [a_0_1_interval, cofactorInterval_0_1, denominatorInterval_1, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])
    (by norm_num [a_0_1_interval, cofactorInterval_0_1, denominatorInterval_1, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])

theorem a_0_2_bounds : a_0_2_interval.Contains (forward v 4 0 2) := by
  rw [forward_formula_0_2 hv]
  exact contains_weaken
    (contains_div_pos (cofactor_0_2_bounds hv h0 h1 h2 h3) (denominator_2_bounds hv h0 h1 h2 h3)
      (by norm_num [denominatorInterval_2]))
    (by norm_num [a_0_2_interval, cofactorInterval_0_2, denominatorInterval_2, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])
    (by norm_num [a_0_2_interval, cofactorInterval_0_2, denominatorInterval_2, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])

theorem a_0_3_bounds : a_0_3_interval.Contains (forward v 4 0 3) := by
  rw [forward_formula_0_3 hv]
  exact contains_weaken
    (contains_div_pos (cofactor_0_3_bounds hv h0 h1 h2 h3) (denominator_3_bounds hv h0 h1 h2 h3)
      (by norm_num [denominatorInterval_3]))
    (by norm_num [a_0_3_interval, cofactorInterval_0_3, denominatorInterval_3, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])
    (by norm_num [a_0_3_interval, cofactorInterval_0_3, denominatorInterval_3, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])

theorem a_1_0_bounds : a_1_0_interval.Contains (forward v 4 1 0) := by
  simp [a_1_0_interval, Contains, forward, entry]

theorem a_1_1_bounds : a_1_1_interval.Contains (forward v 4 1 1) := by
  rw [forward_formula_1_1 hv]
  exact contains_weaken
    (contains_div_pos (cofactor_1_1_bounds hv h0 h1 h2 h3) (denominator_1_bounds hv h0 h1 h2 h3)
      (by norm_num [denominatorInterval_1]))
    (by norm_num [a_1_1_interval, cofactorInterval_1_1, denominatorInterval_1, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])
    (by norm_num [a_1_1_interval, cofactorInterval_1_1, denominatorInterval_1, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])

theorem a_1_2_bounds : a_1_2_interval.Contains (forward v 4 1 2) := by
  rw [forward_formula_1_2 hv]
  exact contains_weaken
    (contains_div_pos (cofactor_1_2_bounds hv h0 h1 h2 h3) (denominator_2_bounds hv h0 h1 h2 h3)
      (by norm_num [denominatorInterval_2]))
    (by norm_num [a_1_2_interval, cofactorInterval_1_2, denominatorInterval_2, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])
    (by norm_num [a_1_2_interval, cofactorInterval_1_2, denominatorInterval_2, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])

theorem a_1_3_bounds : a_1_3_interval.Contains (forward v 4 1 3) := by
  rw [forward_formula_1_3 hv]
  exact contains_weaken
    (contains_div_pos (cofactor_1_3_bounds hv h0 h1 h2 h3) (denominator_3_bounds hv h0 h1 h2 h3)
      (by norm_num [denominatorInterval_3]))
    (by norm_num [a_1_3_interval, cofactorInterval_1_3, denominatorInterval_3, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])
    (by norm_num [a_1_3_interval, cofactorInterval_1_3, denominatorInterval_3, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])

theorem a_2_0_bounds : a_2_0_interval.Contains (forward v 4 2 0) := by
  simp [a_2_0_interval, Contains, forward, entry]

theorem a_2_1_bounds : a_2_1_interval.Contains (forward v 4 2 1) := by
  simp [a_2_1_interval, Contains, forward, entry]

theorem a_2_2_bounds : a_2_2_interval.Contains (forward v 4 2 2) := by
  rw [forward_formula_2_2 hv]
  exact contains_weaken
    (contains_div_pos (cofactor_2_2_bounds hv h0 h1 h2 h3) (denominator_2_bounds hv h0 h1 h2 h3)
      (by norm_num [denominatorInterval_2]))
    (by norm_num [a_2_2_interval, cofactorInterval_2_2, denominatorInterval_2, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])
    (by norm_num [a_2_2_interval, cofactorInterval_2_2, denominatorInterval_2, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])

theorem a_2_3_bounds : a_2_3_interval.Contains (forward v 4 2 3) := by
  rw [forward_formula_2_3 hv]
  exact contains_weaken
    (contains_div_pos (cofactor_2_3_bounds hv h0 h1 h2 h3) (denominator_3_bounds hv h0 h1 h2 h3)
      (by norm_num [denominatorInterval_3]))
    (by norm_num [a_2_3_interval, cofactorInterval_2_3, denominatorInterval_3, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])
    (by norm_num [a_2_3_interval, cofactorInterval_2_3, denominatorInterval_3, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])

theorem a_3_0_bounds : a_3_0_interval.Contains (forward v 4 3 0) := by
  simp [a_3_0_interval, Contains, forward, entry]

theorem a_3_1_bounds : a_3_1_interval.Contains (forward v 4 3 1) := by
  simp [a_3_1_interval, Contains, forward, entry]

theorem a_3_2_bounds : a_3_2_interval.Contains (forward v 4 3 2) := by
  simp [a_3_2_interval, Contains, forward, entry]

theorem a_3_3_bounds : a_3_3_interval.Contains (forward v 4 3 3) := by
  rw [forward_formula_3_3 hv]
  exact contains_weaken
    (contains_div_pos (cofactor_3_3_bounds hv h0 h1 h2 h3) (denominator_3_bounds hv h0 h1 h2 h3)
      (by norm_num [denominatorInterval_3]))
    (by norm_num [a_3_3_interval, cofactorInterval_3_3, denominatorInterval_3, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])
    (by norm_num [a_3_3_interval, cofactorInterval_3_3, denominatorInterval_3, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])

theorem reverse_formula : reverse v 4 = (forward v 4).transpose * gram v 4 := by
  rw [← forward_inverse hv, inverse_eq_transpose_mul_gram hv]

theorem r_0_0_bounds : r_0_0_interval.Contains (reverse v 4 0 0) := by
  have he : reverse v 4 0 0 = reverseExpr_0_0 v := by
    rw [reverse_formula hv h0 h1 h2 h3]
    norm_num [reverseExpr_0_0, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_succ, Fin.succ, forward, g, gram, initialFamily, gramMatrix] <;> ring
  rw [he]
  have h : reverseRawInterval_0_0.Contains (reverseExpr_0_0 v) := by
    simpa [reverseRawInterval_0_0, reverseExpr_0_0] using (contains_add (contains_add (contains_add (contains_mul (a_0_0_bounds hv h0 h1 h2 h3) (g_0_0_bounds hv h0 h1 h2 h3)) (contains_mul (a_1_0_bounds hv h0 h1 h2 h3) (g_1_0_bounds hv h0 h1 h2 h3))) (contains_mul (a_2_0_bounds hv h0 h1 h2 h3) (g_2_0_bounds hv h0 h1 h2 h3))) (contains_mul (a_3_0_bounds hv h0 h1 h2 h3) (g_3_0_bounds hv h0 h1 h2 h3)))
  exact contains_weaken h
    (by norm_num [reverseRawInterval_0_0, r_0_0_interval, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_0_0_interval, a_1_0_interval, a_2_0_interval, a_3_0_interval, gram_2_2_interval, gram_2_3_interval, gram_2_5_interval, gram_2_6_interval])
    (by norm_num [reverseRawInterval_0_0, r_0_0_interval, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_0_0_interval, a_1_0_interval, a_2_0_interval, a_3_0_interval, gram_2_2_interval, gram_2_3_interval, gram_2_5_interval, gram_2_6_interval])

theorem r_0_1_bounds : r_0_1_interval.Contains (reverse v 4 0 1) := by
  have he : reverse v 4 0 1 = reverseExpr_0_1 v := by
    rw [reverse_formula hv h0 h1 h2 h3]
    norm_num [reverseExpr_0_1, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_succ, Fin.succ, forward, g, gram, initialFamily, gramMatrix] <;> ring
  rw [he]
  have h : reverseRawInterval_0_1.Contains (reverseExpr_0_1 v) := by
    simpa [reverseRawInterval_0_1, reverseExpr_0_1] using (contains_add (contains_add (contains_add (contains_mul (a_0_0_bounds hv h0 h1 h2 h3) (g_0_1_bounds hv h0 h1 h2 h3)) (contains_mul (a_1_0_bounds hv h0 h1 h2 h3) (g_1_1_bounds hv h0 h1 h2 h3))) (contains_mul (a_2_0_bounds hv h0 h1 h2 h3) (g_2_1_bounds hv h0 h1 h2 h3))) (contains_mul (a_3_0_bounds hv h0 h1 h2 h3) (g_3_1_bounds hv h0 h1 h2 h3)))
  exact contains_weaken h
    (by norm_num [reverseRawInterval_0_1, r_0_1_interval, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_0_0_interval, a_1_0_interval, a_2_0_interval, a_3_0_interval, gram_2_3_interval, gram_3_3_interval, gram_3_5_interval, gram_3_6_interval])
    (by norm_num [reverseRawInterval_0_1, r_0_1_interval, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_0_0_interval, a_1_0_interval, a_2_0_interval, a_3_0_interval, gram_2_3_interval, gram_3_3_interval, gram_3_5_interval, gram_3_6_interval])

theorem r_0_2_bounds : r_0_2_interval.Contains (reverse v 4 0 2) := by
  have he : reverse v 4 0 2 = reverseExpr_0_2 v := by
    rw [reverse_formula hv h0 h1 h2 h3]
    norm_num [reverseExpr_0_2, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_succ, Fin.succ, forward, g, gram, initialFamily, gramMatrix] <;> ring
  rw [he]
  have h : reverseRawInterval_0_2.Contains (reverseExpr_0_2 v) := by
    simpa [reverseRawInterval_0_2, reverseExpr_0_2] using (contains_add (contains_add (contains_add (contains_mul (a_0_0_bounds hv h0 h1 h2 h3) (g_0_2_bounds hv h0 h1 h2 h3)) (contains_mul (a_1_0_bounds hv h0 h1 h2 h3) (g_1_2_bounds hv h0 h1 h2 h3))) (contains_mul (a_2_0_bounds hv h0 h1 h2 h3) (g_2_2_bounds hv h0 h1 h2 h3))) (contains_mul (a_3_0_bounds hv h0 h1 h2 h3) (g_3_2_bounds hv h0 h1 h2 h3)))
  exact contains_weaken h
    (by norm_num [reverseRawInterval_0_2, r_0_2_interval, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_0_0_interval, a_1_0_interval, a_2_0_interval, a_3_0_interval, gram_2_5_interval, gram_3_5_interval, gram_5_5_interval, gram_5_6_interval])
    (by norm_num [reverseRawInterval_0_2, r_0_2_interval, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_0_0_interval, a_1_0_interval, a_2_0_interval, a_3_0_interval, gram_2_5_interval, gram_3_5_interval, gram_5_5_interval, gram_5_6_interval])

theorem r_0_3_bounds : r_0_3_interval.Contains (reverse v 4 0 3) := by
  have he : reverse v 4 0 3 = reverseExpr_0_3 v := by
    rw [reverse_formula hv h0 h1 h2 h3]
    norm_num [reverseExpr_0_3, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_succ, Fin.succ, forward, g, gram, initialFamily, gramMatrix] <;> ring
  rw [he]
  have h : reverseRawInterval_0_3.Contains (reverseExpr_0_3 v) := by
    simpa [reverseRawInterval_0_3, reverseExpr_0_3] using (contains_add (contains_add (contains_add (contains_mul (a_0_0_bounds hv h0 h1 h2 h3) (g_0_3_bounds hv h0 h1 h2 h3)) (contains_mul (a_1_0_bounds hv h0 h1 h2 h3) (g_1_3_bounds hv h0 h1 h2 h3))) (contains_mul (a_2_0_bounds hv h0 h1 h2 h3) (g_2_3_bounds hv h0 h1 h2 h3))) (contains_mul (a_3_0_bounds hv h0 h1 h2 h3) (g_3_3_bounds hv h0 h1 h2 h3)))
  exact contains_weaken h
    (by norm_num [reverseRawInterval_0_3, r_0_3_interval, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_0_0_interval, a_1_0_interval, a_2_0_interval, a_3_0_interval, gram_2_6_interval, gram_3_6_interval, gram_5_6_interval, gram_6_6_interval])
    (by norm_num [reverseRawInterval_0_3, r_0_3_interval, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_0_0_interval, a_1_0_interval, a_2_0_interval, a_3_0_interval, gram_2_6_interval, gram_3_6_interval, gram_5_6_interval, gram_6_6_interval])

theorem r_1_0_bounds : r_1_0_interval.Contains (reverse v 4 1 0) := by
  have hz : reverse v 4 1 0 = 0 := reverse_upper hv 4 (by decide)
  simp [r_1_0_interval, Contains, hz]

theorem r_1_1_bounds : r_1_1_interval.Contains (reverse v 4 1 1) := by
  have he : reverse v 4 1 1 = reverseExpr_1_1 v := by
    rw [reverse_formula hv h0 h1 h2 h3]
    norm_num [reverseExpr_1_1, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_succ, Fin.succ, forward, g, gram, initialFamily, gramMatrix] <;> ring
  rw [he]
  have h : reverseRawInterval_1_1.Contains (reverseExpr_1_1 v) := by
    simpa [reverseRawInterval_1_1, reverseExpr_1_1] using (contains_add (contains_add (contains_add (contains_mul (a_0_1_bounds hv h0 h1 h2 h3) (g_0_1_bounds hv h0 h1 h2 h3)) (contains_mul (a_1_1_bounds hv h0 h1 h2 h3) (g_1_1_bounds hv h0 h1 h2 h3))) (contains_mul (a_2_1_bounds hv h0 h1 h2 h3) (g_2_1_bounds hv h0 h1 h2 h3))) (contains_mul (a_3_1_bounds hv h0 h1 h2 h3) (g_3_1_bounds hv h0 h1 h2 h3)))
  exact contains_weaken h
    (by norm_num [reverseRawInterval_1_1, r_1_1_interval, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_0_1_interval, a_1_1_interval, a_2_1_interval, a_3_1_interval, gram_2_3_interval, gram_3_3_interval, gram_3_5_interval, gram_3_6_interval])
    (by norm_num [reverseRawInterval_1_1, r_1_1_interval, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_0_1_interval, a_1_1_interval, a_2_1_interval, a_3_1_interval, gram_2_3_interval, gram_3_3_interval, gram_3_5_interval, gram_3_6_interval])

theorem r_1_2_bounds : r_1_2_interval.Contains (reverse v 4 1 2) := by
  have he : reverse v 4 1 2 = reverseExpr_1_2 v := by
    rw [reverse_formula hv h0 h1 h2 h3]
    norm_num [reverseExpr_1_2, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_succ, Fin.succ, forward, g, gram, initialFamily, gramMatrix] <;> ring
  rw [he]
  have h : reverseRawInterval_1_2.Contains (reverseExpr_1_2 v) := by
    simpa [reverseRawInterval_1_2, reverseExpr_1_2] using (contains_add (contains_add (contains_add (contains_mul (a_0_1_bounds hv h0 h1 h2 h3) (g_0_2_bounds hv h0 h1 h2 h3)) (contains_mul (a_1_1_bounds hv h0 h1 h2 h3) (g_1_2_bounds hv h0 h1 h2 h3))) (contains_mul (a_2_1_bounds hv h0 h1 h2 h3) (g_2_2_bounds hv h0 h1 h2 h3))) (contains_mul (a_3_1_bounds hv h0 h1 h2 h3) (g_3_2_bounds hv h0 h1 h2 h3)))
  exact contains_weaken h
    (by norm_num [reverseRawInterval_1_2, r_1_2_interval, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_0_1_interval, a_1_1_interval, a_2_1_interval, a_3_1_interval, gram_2_5_interval, gram_3_5_interval, gram_5_5_interval, gram_5_6_interval])
    (by norm_num [reverseRawInterval_1_2, r_1_2_interval, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_0_1_interval, a_1_1_interval, a_2_1_interval, a_3_1_interval, gram_2_5_interval, gram_3_5_interval, gram_5_5_interval, gram_5_6_interval])

theorem r_1_3_bounds : r_1_3_interval.Contains (reverse v 4 1 3) := by
  have he : reverse v 4 1 3 = reverseExpr_1_3 v := by
    rw [reverse_formula hv h0 h1 h2 h3]
    norm_num [reverseExpr_1_3, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_succ, Fin.succ, forward, g, gram, initialFamily, gramMatrix] <;> ring
  rw [he]
  have h : reverseRawInterval_1_3.Contains (reverseExpr_1_3 v) := by
    simpa [reverseRawInterval_1_3, reverseExpr_1_3] using (contains_add (contains_add (contains_add (contains_mul (a_0_1_bounds hv h0 h1 h2 h3) (g_0_3_bounds hv h0 h1 h2 h3)) (contains_mul (a_1_1_bounds hv h0 h1 h2 h3) (g_1_3_bounds hv h0 h1 h2 h3))) (contains_mul (a_2_1_bounds hv h0 h1 h2 h3) (g_2_3_bounds hv h0 h1 h2 h3))) (contains_mul (a_3_1_bounds hv h0 h1 h2 h3) (g_3_3_bounds hv h0 h1 h2 h3)))
  exact contains_weaken h
    (by norm_num [reverseRawInterval_1_3, r_1_3_interval, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_0_1_interval, a_1_1_interval, a_2_1_interval, a_3_1_interval, gram_2_6_interval, gram_3_6_interval, gram_5_6_interval, gram_6_6_interval])
    (by norm_num [reverseRawInterval_1_3, r_1_3_interval, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_0_1_interval, a_1_1_interval, a_2_1_interval, a_3_1_interval, gram_2_6_interval, gram_3_6_interval, gram_5_6_interval, gram_6_6_interval])

theorem r_2_0_bounds : r_2_0_interval.Contains (reverse v 4 2 0) := by
  have hz : reverse v 4 2 0 = 0 := reverse_upper hv 4 (by decide)
  simp [r_2_0_interval, Contains, hz]

theorem r_2_1_bounds : r_2_1_interval.Contains (reverse v 4 2 1) := by
  have hz : reverse v 4 2 1 = 0 := reverse_upper hv 4 (by decide)
  simp [r_2_1_interval, Contains, hz]

theorem r_2_2_bounds : r_2_2_interval.Contains (reverse v 4 2 2) := by
  have he : reverse v 4 2 2 = reverseExpr_2_2 v := by
    rw [reverse_formula hv h0 h1 h2 h3]
    norm_num [reverseExpr_2_2, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_succ, Fin.succ, forward, g, gram, initialFamily, gramMatrix] <;> ring
  rw [he]
  have h : reverseRawInterval_2_2.Contains (reverseExpr_2_2 v) := by
    simpa [reverseRawInterval_2_2, reverseExpr_2_2] using (contains_add (contains_add (contains_add (contains_mul (a_0_2_bounds hv h0 h1 h2 h3) (g_0_2_bounds hv h0 h1 h2 h3)) (contains_mul (a_1_2_bounds hv h0 h1 h2 h3) (g_1_2_bounds hv h0 h1 h2 h3))) (contains_mul (a_2_2_bounds hv h0 h1 h2 h3) (g_2_2_bounds hv h0 h1 h2 h3))) (contains_mul (a_3_2_bounds hv h0 h1 h2 h3) (g_3_2_bounds hv h0 h1 h2 h3)))
  exact contains_weaken h
    (by norm_num [reverseRawInterval_2_2, r_2_2_interval, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_0_2_interval, a_1_2_interval, a_2_2_interval, a_3_2_interval, gram_2_5_interval, gram_3_5_interval, gram_5_5_interval, gram_5_6_interval])
    (by norm_num [reverseRawInterval_2_2, r_2_2_interval, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_0_2_interval, a_1_2_interval, a_2_2_interval, a_3_2_interval, gram_2_5_interval, gram_3_5_interval, gram_5_5_interval, gram_5_6_interval])

theorem r_2_3_bounds : r_2_3_interval.Contains (reverse v 4 2 3) := by
  have he : reverse v 4 2 3 = reverseExpr_2_3 v := by
    rw [reverse_formula hv h0 h1 h2 h3]
    norm_num [reverseExpr_2_3, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_succ, Fin.succ, forward, g, gram, initialFamily, gramMatrix] <;> ring
  rw [he]
  have h : reverseRawInterval_2_3.Contains (reverseExpr_2_3 v) := by
    simpa [reverseRawInterval_2_3, reverseExpr_2_3] using (contains_add (contains_add (contains_add (contains_mul (a_0_2_bounds hv h0 h1 h2 h3) (g_0_3_bounds hv h0 h1 h2 h3)) (contains_mul (a_1_2_bounds hv h0 h1 h2 h3) (g_1_3_bounds hv h0 h1 h2 h3))) (contains_mul (a_2_2_bounds hv h0 h1 h2 h3) (g_2_3_bounds hv h0 h1 h2 h3))) (contains_mul (a_3_2_bounds hv h0 h1 h2 h3) (g_3_3_bounds hv h0 h1 h2 h3)))
  exact contains_weaken h
    (by norm_num [reverseRawInterval_2_3, r_2_3_interval, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_0_2_interval, a_1_2_interval, a_2_2_interval, a_3_2_interval, gram_2_6_interval, gram_3_6_interval, gram_5_6_interval, gram_6_6_interval])
    (by norm_num [reverseRawInterval_2_3, r_2_3_interval, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_0_2_interval, a_1_2_interval, a_2_2_interval, a_3_2_interval, gram_2_6_interval, gram_3_6_interval, gram_5_6_interval, gram_6_6_interval])

theorem r_3_0_bounds : r_3_0_interval.Contains (reverse v 4 3 0) := by
  have hz : reverse v 4 3 0 = 0 := reverse_upper hv 4 (by decide)
  simp [r_3_0_interval, Contains, hz]

theorem r_3_1_bounds : r_3_1_interval.Contains (reverse v 4 3 1) := by
  have hz : reverse v 4 3 1 = 0 := reverse_upper hv 4 (by decide)
  simp [r_3_1_interval, Contains, hz]

theorem r_3_2_bounds : r_3_2_interval.Contains (reverse v 4 3 2) := by
  have hz : reverse v 4 3 2 = 0 := reverse_upper hv 4 (by decide)
  simp [r_3_2_interval, Contains, hz]

theorem r_3_3_bounds : r_3_3_interval.Contains (reverse v 4 3 3) := by
  have he : reverse v 4 3 3 = reverseExpr_3_3 v := by
    rw [reverse_formula hv h0 h1 h2 h3]
    norm_num [reverseExpr_3_3, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_succ, Fin.succ, forward, g, gram, initialFamily, gramMatrix] <;> ring
  rw [he]
  have h : reverseRawInterval_3_3.Contains (reverseExpr_3_3 v) := by
    simpa [reverseRawInterval_3_3, reverseExpr_3_3] using (contains_add (contains_add (contains_add (contains_mul (a_0_3_bounds hv h0 h1 h2 h3) (g_0_3_bounds hv h0 h1 h2 h3)) (contains_mul (a_1_3_bounds hv h0 h1 h2 h3) (g_1_3_bounds hv h0 h1 h2 h3))) (contains_mul (a_2_3_bounds hv h0 h1 h2 h3) (g_2_3_bounds hv h0 h1 h2 h3))) (contains_mul (a_3_3_bounds hv h0 h1 h2 h3) (g_3_3_bounds hv h0 h1 h2 h3)))
  exact contains_weaken h
    (by norm_num [reverseRawInterval_3_3, r_3_3_interval, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_0_3_interval, a_1_3_interval, a_2_3_interval, a_3_3_interval, gram_2_6_interval, gram_3_6_interval, gram_5_6_interval, gram_6_6_interval])
    (by norm_num [reverseRawInterval_3_3, r_3_3_interval, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_0_3_interval, a_1_3_interval, a_2_3_interval, a_3_3_interval, gram_2_6_interval, gram_3_6_interval, gram_5_6_interval, gram_6_6_interval])

theorem vector_0_0_bounds :
    vectorInterval_0_0.Contains (explicitEigenvector v 0 0) := by
  have h : vectorRawInterval_0_0.Contains (vectorExpr_0_0 v) := by
    simpa [vectorRawInterval_0_0, vectorExpr_0_0] using (contains_point (1 : ℚ))
  change vectorInterval_0_0.Contains (vectorExpr_0_0 v)
  exact contains_weaken h
    (by norm_num [vectorRawInterval_0_0, vectorInterval_0_0, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])
    (by norm_num [vectorRawInterval_0_0, vectorInterval_0_0, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])

theorem vector_0_1_bounds :
    vectorInterval_0_1.Contains (explicitEigenvector v 1 0) := by
  have h : vectorRawInterval_0_1.Contains (vectorExpr_0_1 v) := by
    simpa [vectorRawInterval_0_1, vectorExpr_0_1] using (contains_div_pos (a_0_1_bounds hv h0 h1 h2 h3) (contains_sub (a_1_1_bounds hv h0 h1 h2 h3) (a_0_0_bounds hv h0 h1 h2 h3)) (by norm_num [RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_0_0_interval, a_1_1_interval]))
  change vectorInterval_0_1.Contains (vectorExpr_0_1 v)
  exact contains_weaken h
    (by norm_num [vectorRawInterval_0_1, vectorInterval_0_1, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_0_0_interval, a_0_1_interval, a_1_1_interval])
    (by norm_num [vectorRawInterval_0_1, vectorInterval_0_1, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_0_0_interval, a_0_1_interval, a_1_1_interval])

theorem vector_0_2_bounds :
    vectorInterval_0_2.Contains (explicitEigenvector v 2 0) := by
  have h : vectorRawInterval_0_2.Contains (vectorExpr_0_2 v) := by
    simpa [vectorRawInterval_0_2, vectorExpr_0_2] using (contains_div_pos (contains_add (contains_mul (a_0_1_bounds hv h0 h1 h2 h3) (contains_div_pos (a_1_2_bounds hv h0 h1 h2 h3) (contains_sub (a_2_2_bounds hv h0 h1 h2 h3) (a_1_1_bounds hv h0 h1 h2 h3)) (by norm_num [RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_1_1_interval, a_2_2_interval]))) (a_0_2_bounds hv h0 h1 h2 h3)) (contains_sub (a_2_2_bounds hv h0 h1 h2 h3) (a_0_0_bounds hv h0 h1 h2 h3)) (by norm_num [RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_0_0_interval, a_2_2_interval]))
  change vectorInterval_0_2.Contains (vectorExpr_0_2 v)
  exact contains_weaken h
    (by norm_num [vectorRawInterval_0_2, vectorInterval_0_2, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_0_0_interval, a_0_1_interval, a_0_2_interval, a_1_1_interval, a_1_2_interval, a_2_2_interval])
    (by norm_num [vectorRawInterval_0_2, vectorInterval_0_2, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_0_0_interval, a_0_1_interval, a_0_2_interval, a_1_1_interval, a_1_2_interval, a_2_2_interval])

theorem vector_0_3_bounds :
    vectorInterval_0_3.Contains (explicitEigenvector v 3 0) := by
  have h : vectorRawInterval_0_3.Contains (vectorExpr_0_3 v) := by
    simpa [vectorRawInterval_0_3, vectorExpr_0_3] using (contains_div_pos (contains_add (contains_add (contains_mul (a_0_1_bounds hv h0 h1 h2 h3) (contains_div_pos (contains_add (contains_mul (a_1_2_bounds hv h0 h1 h2 h3) (contains_div_pos (a_2_3_bounds hv h0 h1 h2 h3) (contains_sub (a_3_3_bounds hv h0 h1 h2 h3) (a_2_2_bounds hv h0 h1 h2 h3)) (by norm_num [RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_2_2_interval, a_3_3_interval]))) (a_1_3_bounds hv h0 h1 h2 h3)) (contains_sub (a_3_3_bounds hv h0 h1 h2 h3) (a_1_1_bounds hv h0 h1 h2 h3)) (by norm_num [RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_1_1_interval, a_3_3_interval]))) (contains_mul (a_0_2_bounds hv h0 h1 h2 h3) (contains_div_pos (a_2_3_bounds hv h0 h1 h2 h3) (contains_sub (a_3_3_bounds hv h0 h1 h2 h3) (a_2_2_bounds hv h0 h1 h2 h3)) (by norm_num [RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_2_2_interval, a_3_3_interval])))) (a_0_3_bounds hv h0 h1 h2 h3)) (contains_sub (a_3_3_bounds hv h0 h1 h2 h3) (a_0_0_bounds hv h0 h1 h2 h3)) (by norm_num [RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_0_0_interval, a_3_3_interval]))
  change vectorInterval_0_3.Contains (vectorExpr_0_3 v)
  exact contains_weaken h
    (by norm_num [vectorRawInterval_0_3, vectorInterval_0_3, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_0_0_interval, a_0_1_interval, a_0_2_interval, a_0_3_interval, a_1_1_interval, a_1_2_interval, a_1_3_interval, a_2_2_interval, a_2_3_interval, a_3_3_interval])
    (by norm_num [vectorRawInterval_0_3, vectorInterval_0_3, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_0_0_interval, a_0_1_interval, a_0_2_interval, a_0_3_interval, a_1_1_interval, a_1_2_interval, a_1_3_interval, a_2_2_interval, a_2_3_interval, a_3_3_interval])

theorem vector_1_0_bounds :
    vectorInterval_1_0.Contains (explicitEigenvector v 0 1) := by
  have h : vectorRawInterval_1_0.Contains (vectorExpr_1_0 v) := by
    simpa [vectorRawInterval_1_0, vectorExpr_1_0] using (contains_point (0 : ℚ))
  change vectorInterval_1_0.Contains (vectorExpr_1_0 v)
  exact contains_weaken h
    (by norm_num [vectorRawInterval_1_0, vectorInterval_1_0, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])
    (by norm_num [vectorRawInterval_1_0, vectorInterval_1_0, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])

theorem vector_1_1_bounds :
    vectorInterval_1_1.Contains (explicitEigenvector v 1 1) := by
  have h : vectorRawInterval_1_1.Contains (vectorExpr_1_1 v) := by
    simpa [vectorRawInterval_1_1, vectorExpr_1_1] using (contains_point (1 : ℚ))
  change vectorInterval_1_1.Contains (vectorExpr_1_1 v)
  exact contains_weaken h
    (by norm_num [vectorRawInterval_1_1, vectorInterval_1_1, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])
    (by norm_num [vectorRawInterval_1_1, vectorInterval_1_1, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])

theorem vector_1_2_bounds :
    vectorInterval_1_2.Contains (explicitEigenvector v 2 1) := by
  have h : vectorRawInterval_1_2.Contains (vectorExpr_1_2 v) := by
    simpa [vectorRawInterval_1_2, vectorExpr_1_2] using (contains_div_pos (a_1_2_bounds hv h0 h1 h2 h3) (contains_sub (a_2_2_bounds hv h0 h1 h2 h3) (a_1_1_bounds hv h0 h1 h2 h3)) (by norm_num [RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_1_1_interval, a_2_2_interval]))
  change vectorInterval_1_2.Contains (vectorExpr_1_2 v)
  exact contains_weaken h
    (by norm_num [vectorRawInterval_1_2, vectorInterval_1_2, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_1_1_interval, a_1_2_interval, a_2_2_interval])
    (by norm_num [vectorRawInterval_1_2, vectorInterval_1_2, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_1_1_interval, a_1_2_interval, a_2_2_interval])

theorem vector_1_3_bounds :
    vectorInterval_1_3.Contains (explicitEigenvector v 3 1) := by
  have h : vectorRawInterval_1_3.Contains (vectorExpr_1_3 v) := by
    simpa [vectorRawInterval_1_3, vectorExpr_1_3] using (contains_div_pos (contains_add (contains_mul (a_1_2_bounds hv h0 h1 h2 h3) (contains_div_pos (a_2_3_bounds hv h0 h1 h2 h3) (contains_sub (a_3_3_bounds hv h0 h1 h2 h3) (a_2_2_bounds hv h0 h1 h2 h3)) (by norm_num [RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_2_2_interval, a_3_3_interval]))) (a_1_3_bounds hv h0 h1 h2 h3)) (contains_sub (a_3_3_bounds hv h0 h1 h2 h3) (a_1_1_bounds hv h0 h1 h2 h3)) (by norm_num [RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_1_1_interval, a_3_3_interval]))
  change vectorInterval_1_3.Contains (vectorExpr_1_3 v)
  exact contains_weaken h
    (by norm_num [vectorRawInterval_1_3, vectorInterval_1_3, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_1_1_interval, a_1_2_interval, a_1_3_interval, a_2_2_interval, a_2_3_interval, a_3_3_interval])
    (by norm_num [vectorRawInterval_1_3, vectorInterval_1_3, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_1_1_interval, a_1_2_interval, a_1_3_interval, a_2_2_interval, a_2_3_interval, a_3_3_interval])

theorem vector_2_0_bounds :
    vectorInterval_2_0.Contains (explicitEigenvector v 0 2) := by
  have h : vectorRawInterval_2_0.Contains (vectorExpr_2_0 v) := by
    simpa [vectorRawInterval_2_0, vectorExpr_2_0] using (contains_point (0 : ℚ))
  change vectorInterval_2_0.Contains (vectorExpr_2_0 v)
  exact contains_weaken h
    (by norm_num [vectorRawInterval_2_0, vectorInterval_2_0, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])
    (by norm_num [vectorRawInterval_2_0, vectorInterval_2_0, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])

theorem vector_2_1_bounds :
    vectorInterval_2_1.Contains (explicitEigenvector v 1 2) := by
  have h : vectorRawInterval_2_1.Contains (vectorExpr_2_1 v) := by
    simpa [vectorRawInterval_2_1, vectorExpr_2_1] using (contains_point (0 : ℚ))
  change vectorInterval_2_1.Contains (vectorExpr_2_1 v)
  exact contains_weaken h
    (by norm_num [vectorRawInterval_2_1, vectorInterval_2_1, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])
    (by norm_num [vectorRawInterval_2_1, vectorInterval_2_1, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])

theorem vector_2_2_bounds :
    vectorInterval_2_2.Contains (explicitEigenvector v 2 2) := by
  have h : vectorRawInterval_2_2.Contains (vectorExpr_2_2 v) := by
    simpa [vectorRawInterval_2_2, vectorExpr_2_2] using (contains_point (1 : ℚ))
  change vectorInterval_2_2.Contains (vectorExpr_2_2 v)
  exact contains_weaken h
    (by norm_num [vectorRawInterval_2_2, vectorInterval_2_2, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])
    (by norm_num [vectorRawInterval_2_2, vectorInterval_2_2, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])

theorem vector_2_3_bounds :
    vectorInterval_2_3.Contains (explicitEigenvector v 3 2) := by
  have h : vectorRawInterval_2_3.Contains (vectorExpr_2_3 v) := by
    simpa [vectorRawInterval_2_3, vectorExpr_2_3] using (contains_div_pos (a_2_3_bounds hv h0 h1 h2 h3) (contains_sub (a_3_3_bounds hv h0 h1 h2 h3) (a_2_2_bounds hv h0 h1 h2 h3)) (by norm_num [RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_2_2_interval, a_3_3_interval]))
  change vectorInterval_2_3.Contains (vectorExpr_2_3 v)
  exact contains_weaken h
    (by norm_num [vectorRawInterval_2_3, vectorInterval_2_3, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_2_2_interval, a_2_3_interval, a_3_3_interval])
    (by norm_num [vectorRawInterval_2_3, vectorInterval_2_3, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point, a_2_2_interval, a_2_3_interval, a_3_3_interval])

theorem vector_3_0_bounds :
    vectorInterval_3_0.Contains (explicitEigenvector v 0 3) := by
  have h : vectorRawInterval_3_0.Contains (vectorExpr_3_0 v) := by
    simpa [vectorRawInterval_3_0, vectorExpr_3_0] using (contains_point (0 : ℚ))
  change vectorInterval_3_0.Contains (vectorExpr_3_0 v)
  exact contains_weaken h
    (by norm_num [vectorRawInterval_3_0, vectorInterval_3_0, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])
    (by norm_num [vectorRawInterval_3_0, vectorInterval_3_0, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])

theorem vector_3_1_bounds :
    vectorInterval_3_1.Contains (explicitEigenvector v 1 3) := by
  have h : vectorRawInterval_3_1.Contains (vectorExpr_3_1 v) := by
    simpa [vectorRawInterval_3_1, vectorExpr_3_1] using (contains_point (0 : ℚ))
  change vectorInterval_3_1.Contains (vectorExpr_3_1 v)
  exact contains_weaken h
    (by norm_num [vectorRawInterval_3_1, vectorInterval_3_1, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])
    (by norm_num [vectorRawInterval_3_1, vectorInterval_3_1, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])

theorem vector_3_2_bounds :
    vectorInterval_3_2.Contains (explicitEigenvector v 2 3) := by
  have h : vectorRawInterval_3_2.Contains (vectorExpr_3_2 v) := by
    simpa [vectorRawInterval_3_2, vectorExpr_3_2] using (contains_point (0 : ℚ))
  change vectorInterval_3_2.Contains (vectorExpr_3_2 v)
  exact contains_weaken h
    (by norm_num [vectorRawInterval_3_2, vectorInterval_3_2, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])
    (by norm_num [vectorRawInterval_3_2, vectorInterval_3_2, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])

theorem vector_3_3_bounds :
    vectorInterval_3_3.Contains (explicitEigenvector v 3 3) := by
  have h : vectorRawInterval_3_3.Contains (vectorExpr_3_3 v) := by
    simpa [vectorRawInterval_3_3, vectorExpr_3_3] using (contains_point (1 : ℚ))
  change vectorInterval_3_3.Contains (vectorExpr_3_3 v)
  exact contains_weaken h
    (by norm_num [vectorRawInterval_3_3, vectorInterval_3_3, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])
    (by norm_num [vectorRawInterval_3_3, vectorInterval_3_3, RatInterval.add, RatInterval.sub, RatInterval.neg, RatInterval.mul, RatInterval.inv, RatInterval.div, RatInterval.point])

omit hv h0 h1 h2 h3 in
private theorem interval_separated {I J : RatInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) (h : I.hi < J.lo) : x < y := by
  have h' : (I.hi : ℝ) < (J.lo : ℝ) := by exact_mod_cast h
  exact lt_of_le_of_lt hx.2 (lt_of_lt_of_le h' hy.1)

theorem diagonal_strict (i j : Fin 4) (hij : i < j) :
    forward v 4 i i < forward v 4 j j := by
  fin_cases i <;> fin_cases j <;> norm_num at hij
  · exact interval_separated (a_0_0_bounds hv h0 h1 h2 h3) (a_1_1_bounds hv h0 h1 h2 h3) (by norm_num [a_0_0_interval, a_1_1_interval])
  · exact interval_separated (a_0_0_bounds hv h0 h1 h2 h3) (a_2_2_bounds hv h0 h1 h2 h3) (by norm_num [a_0_0_interval, a_2_2_interval])
  · exact interval_separated (a_0_0_bounds hv h0 h1 h2 h3) (a_3_3_bounds hv h0 h1 h2 h3) (by norm_num [a_0_0_interval, a_3_3_interval])
  · exact interval_separated (a_1_1_bounds hv h0 h1 h2 h3) (a_2_2_bounds hv h0 h1 h2 h3) (by norm_num [a_1_1_interval, a_2_2_interval])
  · exact interval_separated (a_1_1_bounds hv h0 h1 h2 h3) (a_3_3_bounds hv h0 h1 h2 h3) (by norm_num [a_1_1_interval, a_3_3_interval])
  · exact interval_separated (a_2_2_bounds hv h0 h1 h2 h3) (a_3_3_bounds hv h0 h1 h2 h3) (by norm_num [a_2_2_interval, a_3_3_interval])

theorem explicitEigenvector_hasEigenvector (j : Fin 4) :
    Module.End.HasEigenvector (forward v 4).mulVecLin
      (forward v 4 j j) (explicitEigenvector v j) := by
  apply backSubstitution_isEigenvector (forward v 4) (forward_upper v 4) j
  · intro i hi
    fin_cases i <;> fin_cases j <;> norm_num at hi
    all_goals norm_num [explicitEigenvector, vectorExpr_0_0, vectorExpr_0_1, vectorExpr_0_2, vectorExpr_0_3, vectorExpr_1_0, vectorExpr_1_1, vectorExpr_1_2, vectorExpr_1_3, vectorExpr_2_0, vectorExpr_2_1, vectorExpr_2_2, vectorExpr_2_3, vectorExpr_3_0, vectorExpr_3_1, vectorExpr_3_2, vectorExpr_3_3]
  · fin_cases j <;> norm_num [explicitEigenvector, vectorExpr_0_0, vectorExpr_0_1, vectorExpr_0_2, vectorExpr_0_3, vectorExpr_1_0, vectorExpr_1_1, vectorExpr_1_2, vectorExpr_1_3, vectorExpr_2_0, vectorExpr_2_1, vectorExpr_2_2, vectorExpr_2_3, vectorExpr_3_0, vectorExpr_3_1, vectorExpr_3_2, vectorExpr_3_3]
  · intro i hi
    exact ne_of_lt (diagonal_strict hv h0 h1 h2 h3 i j hi)
  · intro i hi
    fin_cases i <;> fin_cases j <;> norm_num at hi
    all_goals simp [explicitEigenvector, upperTail, Fin.sum_univ_succ, add_assoc, vectorExpr_0_0, vectorExpr_0_1, vectorExpr_0_2, vectorExpr_0_3, vectorExpr_1_0, vectorExpr_1_1, vectorExpr_1_2, vectorExpr_1_3, vectorExpr_2_0, vectorExpr_2_1, vectorExpr_2_2, vectorExpr_2_3, vectorExpr_3_0, vectorExpr_3_1, vectorExpr_3_2, vectorExpr_3_3]

theorem forward_table_error (i j : Fin 4) :
    |forward v 4 i j - (displayedA i j : ℝ)| ≤ (1 / 1000000 : ℝ) := by
  fin_cases i <;> fin_cases j
  · simpa [displayedA] using
      (abs_error_le (a_0_0_bounds hv h0 h1 h2 h3) (11547005383792517 / 5000000000000000 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [a_0_0_interval]) (by norm_num [a_0_0_interval]))
  · simpa [displayedA] using
      (abs_error_le (a_0_1_bounds hv h0 h1 h2 h3) (-508277453725063 / 250000000000000 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [a_0_1_interval]) (by norm_num [a_0_1_interval]))
  · simpa [displayedA] using
      (abs_error_le (a_0_2_bounds hv h0 h1 h2 h3) (-1562562139092541 / 2000000000000000 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [a_0_2_interval]) (by norm_num [a_0_2_interval]))
  · simpa [displayedA] using
      (abs_error_le (a_0_3_bounds hv h0 h1 h2 h3) (-3447596695168509 / 10000000000000000 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [a_0_3_interval]) (by norm_num [a_0_3_interval]))
  · simpa [displayedA] using
      (abs_error_le (a_1_0_bounds hv h0 h1 h2 h3) (0 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [a_1_0_interval]) (by norm_num [a_1_0_interval]))
  · simpa [displayedA] using
      (abs_error_le (a_1_1_bounds hv h0 h1 h2 h3) (16264515806674231 / 5000000000000000 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [a_1_1_interval]) (by norm_num [a_1_1_interval]))
  · simpa [displayedA] using
      (abs_error_le (a_1_2_bounds hv h0 h1 h2 h3) (-1087543555108087 / 500000000000000 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [a_1_2_interval]) (by norm_num [a_1_2_interval]))
  · simpa [displayedA] using
      (abs_error_le (a_1_3_bounds hv h0 h1 h2 h3) (-8514130280792217 / 5000000000000000 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [a_1_3_interval]) (by norm_num [a_1_3_interval]))
  · simpa [displayedA] using
      (abs_error_le (a_2_0_bounds hv h0 h1 h2 h3) (0 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [a_2_0_interval]) (by norm_num [a_2_0_interval]))
  · simpa [displayedA] using
      (abs_error_le (a_2_1_bounds hv h0 h1 h2 h3) (0 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [a_2_1_interval]) (by norm_num [a_2_1_interval]))
  · simpa [displayedA] using
      (abs_error_le (a_2_2_bounds hv h0 h1 h2 h3) (1089336303931479 / 250000000000000 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [a_2_2_interval]) (by norm_num [a_2_2_interval]))
  · simpa [displayedA] using
      (abs_error_le (a_2_3_bounds hv h0 h1 h2 h3) (-1670515312899323 / 500000000000000 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [a_2_3_interval]) (by norm_num [a_2_3_interval]))
  · simpa [displayedA] using
      (abs_error_le (a_3_0_bounds hv h0 h1 h2 h3) (0 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [a_3_0_interval]) (by norm_num [a_3_0_interval]))
  · simpa [displayedA] using
      (abs_error_le (a_3_1_bounds hv h0 h1 h2 h3) (0 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [a_3_1_interval]) (by norm_num [a_3_1_interval]))
  · simpa [displayedA] using
      (abs_error_le (a_3_2_bounds hv h0 h1 h2 h3) (0 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [a_3_2_interval]) (by norm_num [a_3_2_interval]))
  · simpa [displayedA] using
      (abs_error_le (a_3_3_bounds hv h0 h1 h2 h3) (1614864934325203 / 250000000000000 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [a_3_3_interval]) (by norm_num [a_3_3_interval]))

theorem reverse_table_error (i j : Fin 4) :
    |reverse v 4 i j - (displayedR i j : ℝ)| ≤ (1 / 1000000 : ℝ) := by
  fin_cases i <;> fin_cases j
  · simpa [displayedR] using
      (abs_error_le (r_0_0_bounds hv h0 h1 h2 h3) (10825317547305481 / 25000000000000000 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [r_0_0_interval]) (by norm_num [r_0_0_interval]))
  · simpa [displayedR] using
      (abs_error_le (r_0_1_bounds hv h0 h1 h2 h3) (2706389740272153 / 10000000000000000 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [r_0_1_interval]) (by norm_num [r_0_1_interval]))
  · simpa [displayedR] using
      (abs_error_le (r_0_2_bounds hv h0 h1 h2 h3) (1329605420412751 / 6250000000000000 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [r_0_2_interval]) (by norm_num [r_0_2_interval]))
  · simpa [displayedR] using
      (abs_error_le (r_0_3_bounds hv h0 h1 h2 h3) (10224514551357433 / 50000000000000000 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [r_0_3_interval]) (by norm_num [r_0_3_interval]))
  · simpa [displayedR] using
      (abs_error_le (r_1_0_bounds hv h0 h1 h2 h3) (0 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [r_1_0_interval]) (by norm_num [r_1_0_interval]))
  · simpa [displayedR] using
      (abs_error_le (r_1_1_bounds hv h0 h1 h2 h3) (3074176974852349 / 10000000000000000 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [r_1_1_interval]) (by norm_num [r_1_1_interval]))
  · simpa [displayedR] using
      (abs_error_le (r_1_2_bounds hv h0 h1 h2 h3) (7672794306487757 / 50000000000000000 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [r_1_2_interval]) (by norm_num [r_1_2_interval]))
  · simpa [displayedR] using
      (abs_error_le (r_1_3_bounds hv h0 h1 h2 h3) (8020637350575527 / 50000000000000000 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [r_1_3_interval]) (by norm_num [r_1_3_interval]))
  · simpa [displayedR] using
      (abs_error_le (r_2_0_bounds hv h0 h1 h2 h3) (0 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [r_2_0_interval]) (by norm_num [r_2_0_interval]))
  · simpa [displayedR] using
      (abs_error_le (r_2_1_bounds hv h0 h1 h2 h3) (0 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [r_2_1_interval]) (by norm_num [r_2_1_interval]))
  · simpa [displayedR] using
      (abs_error_le (r_2_2_bounds hv h0 h1 h2 h3) (2294975381778201 / 10000000000000000 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [r_2_2_interval]) (by norm_num [r_2_2_interval]))
  · simpa [displayedR] using
      (abs_error_le (r_2_3_bounds hv h0 h1 h2 h3) (11870316323356991 / 100000000000000000 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [r_2_3_interval]) (by norm_num [r_2_3_interval]))
  · simpa [displayedR] using
      (abs_error_le (r_3_0_bounds hv h0 h1 h2 h3) (0 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [r_3_0_interval]) (by norm_num [r_3_0_interval]))
  · simpa [displayedR] using
      (abs_error_le (r_3_1_bounds hv h0 h1 h2 h3) (0 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [r_3_1_interval]) (by norm_num [r_3_1_interval]))
  · simpa [displayedR] using
      (abs_error_le (r_3_2_bounds hv h0 h1 h2 h3) (0 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [r_3_2_interval]) (by norm_num [r_3_2_interval]))
  · simpa [displayedR] using
      (abs_error_le (r_3_3_bounds hv h0 h1 h2 h3) (15481170882224057 / 100000000000000000 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [r_3_3_interval]) (by norm_num [r_3_3_interval]))

theorem eigenvector_table_error (i j : Fin 4) :
    |explicitEigenvector v j i - (displayedEigenvectors i j : ℝ)| ≤ (1 / 1000000 : ℝ) := by
  fin_cases i <;> fin_cases j
  · simpa [displayedEigenvectors] using
      (abs_error_le (vector_0_0_bounds hv h0 h1 h2 h3) (1 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [vectorInterval_0_0]) (by norm_num [vectorInterval_0_0]))
  · simpa [displayedEigenvectors] using
      (abs_error_le (vector_0_1_bounds hv h0 h1 h2 h3) (-1077427304155439 / 500000000000000 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [vectorInterval_0_1]) (by norm_num [vectorInterval_0_1]))
  · simpa [displayedEigenvectors] using
      (abs_error_le (vector_0_2_bounds hv h0 h1 h2 h3) (15736383457722583 / 10000000000000000 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [vectorInterval_0_2]) (by norm_num [vectorInterval_0_2]))
  · simpa [displayedEigenvectors] using
      (abs_error_le (vector_0_3_bounds hv h0 h1 h2 h3) (-6483475778995257 / 125000000000000000 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [vectorInterval_0_3]) (by norm_num [vectorInterval_0_3]))
  · simpa [displayedEigenvectors] using
      (abs_error_le (vector_1_0_bounds hv h0 h1 h2 h3) (0 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [vectorInterval_1_0]) (by norm_num [vectorInterval_1_0]))
  · simpa [displayedEigenvectors] using
      (abs_error_le (vector_1_1_bounds hv h0 h1 h2 h3) (1 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [vectorInterval_1_1]) (by norm_num [vectorInterval_1_1]))
  · simpa [displayedEigenvectors] using
      (abs_error_le (vector_1_2_bounds hv h0 h1 h2 h3) (-9846995148221701 / 5000000000000000 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [vectorInterval_1_2]) (by norm_num [vectorInterval_1_2]))
  · simpa [displayedEigenvectors] using
      (abs_error_le (vector_1_3_bounds hv h0 h1 h2 h3) (2735309238639201 / 5000000000000000 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [vectorInterval_1_3]) (by norm_num [vectorInterval_1_3]))
  · simpa [displayedEigenvectors] using
      (abs_error_le (vector_2_0_bounds hv h0 h1 h2 h3) (0 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [vectorInterval_2_0]) (by norm_num [vectorInterval_2_0]))
  · simpa [displayedEigenvectors] using
      (abs_error_le (vector_2_1_bounds hv h0 h1 h2 h3) (0 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [vectorInterval_2_1]) (by norm_num [vectorInterval_2_1]))
  · simpa [displayedEigenvectors] using
      (abs_error_le (vector_2_2_bounds hv h0 h1 h2 h3) (1 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [vectorInterval_2_2]) (by norm_num [vectorInterval_2_2]))
  · simpa [displayedEigenvectors] using
      (abs_error_le (vector_2_3_bounds hv h0 h1 h2 h3) (-3178733215063429 / 2000000000000000 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [vectorInterval_2_3]) (by norm_num [vectorInterval_2_3]))
  · simpa [displayedEigenvectors] using
      (abs_error_le (vector_3_0_bounds hv h0 h1 h2 h3) (0 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [vectorInterval_3_0]) (by norm_num [vectorInterval_3_0]))
  · simpa [displayedEigenvectors] using
      (abs_error_le (vector_3_1_bounds hv h0 h1 h2 h3) (0 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [vectorInterval_3_1]) (by norm_num [vectorInterval_3_1]))
  · simpa [displayedEigenvectors] using
      (abs_error_le (vector_3_2_bounds hv h0 h1 h2 h3) (0 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [vectorInterval_3_2]) (by norm_num [vectorInterval_3_2]))
  · simpa [displayedEigenvectors] using
      (abs_error_le (vector_3_3_bounds hv h0 h1 h2 h3) (1 : ℚ) (1 / 1000000 : ℚ)
        (by norm_num [vectorInterval_3_3]) (by norm_num [vectorInterval_3_3]))

theorem diagonal_isEigenvalue (j : Fin 4) :
    Module.End.HasEigenvalue (forward v 4).mulVecLin (forward v 4 j j) :=
  (hasEigenvalue_iff_diagonal (forward v 4) (forward_upper v 4) _).mpr ⟨j, rfl⟩

end RiemannResearch.RH.QResidueMatrixNumerical

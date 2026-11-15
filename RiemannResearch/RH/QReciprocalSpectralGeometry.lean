/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QResidueGramCertificates
import RiemannResearch.RH.QDivisibilityDensity
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Exact complete-Q geometry of finite reciprocal-head repair matrices

Source: `ReciprocalHeadQuantitativeResearch20261107.md`, Section 5.
The matrix whose spectrum is certified is the exact complete-Q Gram of the
finite normalized-head repair map; it is not a truncated physical Gram.
-/

noncomputable section
open scoped BigOperators
open Matrix
namespace RiemannResearch.RH.QReciprocalSpectralGeometry
open ZetaTwoHilbert ZetaTwoProbability QResidueGramCertificates
open RiemannResearch.Analysis.FiniteHilbertGram

def rawGram (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => zetaTwo * inner ℝ (qResidue (i.val + 2)) (qResidue (j.val + 2))

theorem rawGram_isHermitian (N : ℕ) : (rawGram N).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  simp only [Matrix.conjTranspose_apply, rawGram, star_trivial]
  rw [real_inner_comm]

def castMatrix {N : ℕ} (T : Matrix (Fin N) (Fin N) ℚ) :
    Matrix (Fin N) (Fin N) ℝ := fun i j => (T i j : ℝ)

theorem castMatrix_mul {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℚ) :
    castMatrix (A * B) = castMatrix A * castMatrix B := by
  ext i j
  simp only [castMatrix, Matrix.mul_apply, Rat.cast_sum, Rat.cast_mul]

theorem castMatrix_transpose {N : ℕ} (T : Matrix (Fin N) (Fin N) ℚ) :
    castMatrix T.transpose = (castMatrix T).transpose := rfl

theorem castMatrix_diagonal {N : ℕ} (d : Fin N → ℚ) :
    castMatrix (Matrix.diagonal d) = Matrix.diagonal (fun i => (d i : ℝ)) := by
  ext i j
  by_cases h : i = j <;> simp only [castMatrix, Matrix.diagonal_apply, h, if_true,
    if_false, Rat.cast_zero]

def physicalHeadMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  fun i j => rationalResidue (j.val + 2) (i.val + 1)

def operatorGram {N : ℕ} (T : Matrix (Fin N) (Fin N) ℚ) :
    Matrix (Fin N) (Fin N) ℝ :=
  castMatrix T * rawGram N * star (castMatrix T)

theorem operatorGram_isHermitian {N : ℕ} (T : Matrix (Fin N) (Fin N) ℚ) :
    (operatorGram T).IsHermitian := by
  simpa only [operatorGram, Matrix.star_eq_conjTranspose] using
    Matrix.isHermitian_mul_mul_conjTranspose (castMatrix T) (rawGram_isHermitian N)

/-- The repair map on normalized physical-head coordinates. With the checked
head-matrix inverse, its output has the requested reciprocal physical head. -/
def repairVector {N : ℕ} (T : Matrix (Fin N) (Fin N) ℚ) (v : Fin N → ℝ) :
    QHilbert :=
  Real.sqrt zetaTwo • Fintype.linearCombination ℝ (fun i : Fin N => qResidue (i.val + 2))
    ((castMatrix T).transpose.mulVec v)

def repairLinear {N : ℕ} (T : Matrix (Fin N) (Fin N) ℚ) :
    (Fin N → ℝ) →ₗ[ℝ] QHilbert :=
  Real.sqrt zetaTwo • ((Fintype.linearCombination ℝ
    (fun i : Fin N => qResidue (i.val + 2))).comp
      (Matrix.mulVecLin (castMatrix T).transpose))

/-- The actual finite repair on the Euclidean normalized-head input space. -/
def repairCLM {N : ℕ} (T : Matrix (Fin N) (Fin N) ℚ) :
    EuclideanSpace ℝ (Fin N) →L[ℝ] QHilbert :=
  ((repairLinear T).comp
    (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).toLinearMap).toContinuousLinearMap

@[simp] theorem repairCLM_apply {N : ℕ} (T : Matrix (Fin N) (Fin N) ℚ)
    (v : EuclideanSpace ℝ (Fin N)) :
    repairCLM T v = repairVector T v.ofLp := rfl

theorem repairVector_site {N : ℕ} (T : Matrix (Fin N) (Fin N) ℚ)
    (v : Fin N → ℝ) (n : ℕ) :
    qSequence (repairVector T v) n = Real.sqrt zetaTwo *
      (∑ j : Fin N, ((castMatrix T).transpose.mulVec v) j *
        ArithmeticCumulative.residueFraction (j.val + 2) n) := by
  change qSequenceLinear (Real.sqrt zetaTwo •
    Fintype.linearCombination ℝ (fun i : Fin N => qResidue (i.val + 2))
      ((castMatrix T).transpose.mulVec v)) n = _
  rw [map_smul]
  change Real.sqrt zetaTwo * qSequenceLinear
    (Fintype.linearCombination ℝ (fun i : Fin N => qResidue (i.val + 2))
      ((castMatrix T).transpose.mulVec v)) n = _
  congr 1
  rw [Fintype.linearCombination_apply, map_sum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  change ((castMatrix T).transpose.mulVec v) j * qSequence (qResidue (j.val + 2)) n = _
  rw [qSequence_qResidue]

/-- The checked rational head-inverse equation identifies this finite map
with the actual triangular reciprocal-head repair, in normalized inputs. -/
theorem repairVector_head {N : ℕ} (T : Matrix (Fin N) (Fin N) ℚ)
    (hhead : physicalHeadMatrix N * T.transpose =
      Matrix.diagonal (fun i : Fin N => (i.val + 1 : ℚ) / (i.val + 2 : ℚ)))
    (v : Fin N → ℝ) (i : Fin N) :
    qSequence (repairVector T v) (i.val + 1) =
      Real.sqrt zetaTwo * (((i.val + 1 : ℚ) / (i.val + 2 : ℚ) : ℚ) : ℝ) * v i := by
  have hr := congrArg (castMatrix (N := N)) hhead
  rw [castMatrix_mul, castMatrix_transpose, castMatrix_diagonal] at hr
  have hv := congrArg (fun A : Matrix (Fin N) (Fin N) ℝ => A.mulVec v) hr
  rw [← Matrix.mulVec_mulVec] at hv
  have hi := congrArg (fun w : Fin N → ℝ => w i) hv
  simp only [Matrix.mulVec_diagonal] at hi
  rw [repairVector_site]
  have hs : (∑ j : Fin N, ((castMatrix T).transpose.mulVec v) j *
      ArithmeticCumulative.residueFraction (j.val + 2) (i.val + 1)) =
      ((castMatrix (physicalHeadMatrix N)).mulVec
        ((castMatrix T).transpose.mulVec v)) i := by
    simp only [Matrix.mulVec, dotProduct, castMatrix, physicalHeadMatrix,
      rationalResidue_cast]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs, hi]
  ring

theorem qSequence_normalized_coordinate (f : QHilbert) (n : ℕ) :
    qSequence f (n + 1) = Real.sqrt zetaTwo * ((n + 1 : ℕ) : ℝ) * f n := by
  rw [qSequence_succ]
  have hq : 0 < Real.sqrt (qWeight n) := Real.sqrt_pos.mpr (qWeight_pos n)
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hs : Real.sqrt (qWeight n) *
      (Real.sqrt zetaTwo * ((n + 1 : ℕ) : ℝ)) = 1 := by
    rw [← mul_assoc, QDivisibilityDensity.sqrt_qWeight_mul_sqrt_zetaTwo]
    field_simp [hn]
  apply (div_eq_iff (ne_of_gt hq)).2
  calc
    f n = 1 * f n := by ring
    _ = (Real.sqrt (qWeight n) *
        (Real.sqrt zetaTwo * ((n + 1 : ℕ) : ℝ))) * f n := by rw [hs]
    _ = _ := by ring

/-- The finite map really repairs the reciprocal physical head of an
arbitrary full Q vector. The reciprocal is `1/(n+1)` at physical site `n`. -/
theorem repairVector_reciprocal_head {N : ℕ}
    (T : Matrix (Fin N) (Fin N) ℚ)
    (hhead : physicalHeadMatrix N * T.transpose =
      Matrix.diagonal (fun i : Fin N => (i.val + 1 : ℚ) / (i.val + 2 : ℚ)))
    (f : QHilbert) (i : Fin N) :
    qSequence (repairVector T (fun j : Fin N => f j.val)) (i.val + 1) =
      qSequence f (i.val + 1) / ((i.val + 2 : ℕ) : ℝ) := by
  rw [repairVector_head T hhead, qSequence_normalized_coordinate]
  push_cast
  ring

/-- Exact matrix norm identity, including the complete physical tail. -/
theorem repairVector_norm_sq {N : ℕ} (T : Matrix (Fin N) (Fin N) ℚ)
    (v : Fin N → ℝ) :
    ‖repairVector T v‖ ^ 2 = dotProduct v ((operatorGram T).mulVec v) := by
  rw [repairVector, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt zetaTwo_pos.le, gramMatrix_quadratic]
  have hG : rawGram N = zetaTwo •
      gramMatrix (fun i : Fin N => qResidue (i.val + 2)) := rfl
  have hz : zetaTwo * dotProduct ((castMatrix T).transpose.mulVec v)
      ((gramMatrix (fun i : Fin N => qResidue (i.val + 2))).mulVec
        ((castMatrix T).transpose.mulVec v)) =
      dotProduct ((castMatrix T).transpose.mulVec v)
        ((rawGram N).mulVec ((castMatrix T).transpose.mulVec v)) := by
    rw [hG, Matrix.smul_mulVec, dotProduct_smul]
    rfl
  rw [hz]
  rw [dotProduct_comm ((castMatrix T).transpose.mulVec v),
    Matrix.dotProduct_transpose_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  simp only [operatorGram, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]

/-- A positive-definite upper shift controls the actual repair for every
normalized input head. It does not assert uniformity as `N` grows. -/
theorem repairVector_norm_sq_le_of_posDef_shift {N : ℕ}
    (T : Matrix (Fin N) (Fin N) ℚ) (u : ℝ)
    (hupper : (u ^ 2 • (1 : Matrix (Fin N) (Fin N) ℝ) - operatorGram T).PosDef)
    (v : Fin N → ℝ) :
    ‖repairVector T v‖ ^ 2 ≤ u ^ 2 * (∑ i, (v i) ^ 2) := by
  rw [repairVector_norm_sq]
  by_cases hv : v = 0
  · subst v
    simp
  · have hp := hupper.dotProduct_mulVec_pos hv
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hp
    have hdot : dotProduct v v = ∑ i, (v i) ^ 2 := by
      simp only [dotProduct, pow_two]
    rw [hdot] at hp
    linarith

theorem repairCLM_norm_le_of_posDef_shift {N : ℕ}
    (T : Matrix (Fin N) (Fin N) ℚ) (u : ℝ) (hu : 0 ≤ u)
    (hupper : (u ^ 2 • (1 : Matrix (Fin N) (Fin N) ℝ) - operatorGram T).PosDef) :
    ‖repairCLM T‖ ≤ u := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hu
  intro v hv
  have hb := repairVector_norm_sq_le_of_posDef_shift T u hupper v.ofLp
  have hs : (∑ i, (v.ofLp i) ^ 2) = 1 := by
    simpa only [hv, one_pow] using (EuclideanSpace.real_norm_sq_eq v).symm
  rw [hs, mul_one] at hb
  exact (sq_le_sq₀ (norm_nonneg _) hu).mp hb

/-- A rational Rayleigh witness gives the matching lower bound for the
actual Euclidean-source repair operator norm. -/
theorem repairCLM_norm_lower_of_witness {N : ℕ}
    (T : Matrix (Fin N) (Fin N) ℚ) (l : ℝ) (hl : 0 ≤ l) (v : Fin N → ℝ)
    (hwitness : l ^ 2 * (∑ i, (v i) ^ 2) < ‖repairVector T v‖ ^ 2) :
    l < ‖repairCLM T‖ := by
  let x : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 v
  have hhead : ‖x‖ ^ 2 = ∑ i, (v i) ^ 2 := EuclideanSpace.real_norm_sq_eq x
  have hw : l ^ 2 * ‖x‖ ^ 2 < ‖repairCLM T x‖ ^ 2 := by
    simpa only [hhead, repairCLM_apply, x, WithLp.ofLp_toLp] using hwitness
  by_contra hnot
  have hn : ‖repairCLM T‖ ≤ l := le_of_not_gt hnot
  have hnsq : ‖repairCLM T‖ ^ 2 ≤ l ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hl).mpr hn
  have hmul := mul_le_mul_of_nonneg_right hnsq (sq_nonneg ‖x‖)
  have hop := (repairCLM T).le_opNorm x
  have hopSq := (sq_le_sq₀ (norm_nonneg (repairCLM T x))
    (mul_nonneg (norm_nonneg (repairCLM T)) (norm_nonneg x))).mpr hop
  rw [mul_pow] at hopSq
  linarith

end RiemannResearch.RH.QReciprocalSpectralGeometry
